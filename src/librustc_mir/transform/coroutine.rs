use def_use::DefUseAnalysis;
use rustc::mir::*;
use rustc::mir::transform::{MirPass, MirSource, Pass};
use rustc::ty::TyCtxt;
use rustc::middle::const_val::ConstVal;
use rustc_const_math::ConstInt;
use syntax::ast;
use syntax_pos::DUMMY_SP;
use rustc::ty::TypeVariants::TyClosure;

use rustc_data_structures::indexed_vec::Idx;
use rustc_data_structures::control_flow_graph::reachable::{reachable, Reachability};

pub struct CoroutineTransform;
const RESERVED_VARIANTS : usize = 3;

const START_VARIANT : u64 = 0;
const STOP_VARIANT : u64 = 1;
const PANIC_VARIANT : u64 = 2;

struct YieldPoint<'tcx> {
    discr: u64,
    predecessor: BasicBlock,
    target: BasicBlock,
    save: Vec<Statement<'tcx>>,
    restore: Vec<Statement<'tcx>>,
    source_info: SourceInfo,
}

fn live_locals<'tcx, 'a>(mir: &'a Mir<'tcx>,
                         def_use_analysis: &'a DefUseAnalysis<'tcx>,
                         reachability: &'a Reachability<BasicBlock>,
                         block: BasicBlock)
    -> impl Iterator<Item=(Local, &'a LocalDecl<'tcx>)> + 'a
{
    // TODO: replace this with proper liveness analysis
    mir.local_decls.iter_enumerated().skip(2).filter(move |&(local, _)| {
        let info = def_use_analysis.local_info(local);
        let mut defined = false;
        let mut used = false;
        for def_or_use in info.defs_and_uses.iter() {
            if def_or_use.context.is_mutating_use() {
                let def_block = def_or_use.location.block;
                let is_defined = block == def_block || reachability.can_reach(def_block, block);

                defined = defined || is_defined;
            }

            if def_or_use.context.is_nonmutating_use() {
                let use_block = def_or_use.location.block;
                let is_used = block == use_block || reachability.can_reach(block, use_block);

                used = used || is_used;
            }
        }

        used && defined
    })
}

impl Pass for CoroutineTransform {}
impl<'tcx> MirPass<'tcx> for CoroutineTransform {
    fn run_pass<'a>(&mut self,
                    tcx: TyCtxt<'a, 'tcx, 'tcx>,
                    source: MirSource,
                    mir: &mut Mir<'tcx>) {

        let def_id = match source {
            MirSource::Const(_) => {
                return
            }
            MirSource::Static(..) | MirSource::Promoted(..) => {
                return
            }
            MirSource::Fn(node_id) => {
                tcx.map.local_def_id(node_id)
            },
        };

        let ty = tcx.item_type(def_id);
        let substs = match ty.sty {
            TyClosure(_, ref substs) => substs,
            _ => return,
        };
        let upvars_count = substs.upvar_tys(def_id, tcx).count();

        let mut variants = vec![vec![]; RESERVED_VARIANTS];
        let mut yield_points = vec![];

        let mut def_use_analysis = DefUseAnalysis::new(mir);
        def_use_analysis.analyze(mir);
        let reachability = reachable(mir);

        for (block_idx, bb) in mir.basic_blocks().iter_enumerated() {
            if let &Terminator { kind: TerminatorKind::Yield { target }, source_info } = bb.terminator() {
                let mut point = YieldPoint {
                    source_info: source_info,
                    discr: variants.len() as u64,
                    predecessor: block_idx,
                    target: target,
                    save: vec![],
                    restore: vec![],
                };

                point.save.push(Statement {
                    source_info: source_info,
                    kind: StatementKind::SetDiscriminant {
                        lvalue: Lvalue::Local(Local::new(1)).deref(),
                        variant_index: point.discr as usize,
                    }
                });

                let mut variant = vec![];

                let mut field = upvars_count;
                for (local, decl) in live_locals(mir, &def_use_analysis, &reachability, block_idx) {
                    variant.push(decl.ty);

                    let coroutine = Lvalue::Local(Local::new(1));
                    let downcasted = coroutine.deref().elem(ProjectionElem::Downcast(point.discr as usize));
                    let lhs = downcasted.field(Field::new(field), decl.ty);
                    let rhs = Rvalue::Use(Operand::Consume(Lvalue::Local(local)));
                    point.save.push(Statement {
                        source_info: source_info,
                        kind: StatementKind::Assign(lhs, rhs),
                    });

                    let coroutine = Lvalue::Local(Local::new(1));
                    let downcasted = coroutine.deref().elem(ProjectionElem::Downcast(point.discr as usize));
                    let lhs = Lvalue::Local(local);
                    let rhs = Rvalue::Use(Operand::Consume(downcasted.field(Field::new(field), decl.ty)));
                    point.restore.push(Statement {
                        source_info: source_info,
                        kind: StatementKind::Assign(lhs, rhs),
                    });

                    field += 1;
                }

                point.restore.push(Statement {
                    source_info: source_info,
                    kind: StatementKind::SetDiscriminant {
                        lvalue: Lvalue::Local(Local::new(1)).deref(),
                        variant_index: PANIC_VARIANT as usize,
                    }
                });

                variants.push(variant);
                yield_points.push(point);
            }
        }

        tcx.tables.borrow_mut().coroutine_variants.insert(def_id, variants);

        if yield_points.len() > 0 {
            let mut values = vec![];
            let mut targets = vec![];

            for point in yield_points {
                mir[point.predecessor].statements.extend(point.save);
                mir[point.predecessor].terminator_mut().kind = TerminatorKind::Return;

                let restore = mir.basic_blocks_mut().push(BasicBlockData {
                    is_cleanup: false,
                    statements: point.restore,
                    terminator: Some(Terminator {
                        source_info: point.source_info,
                        kind: TerminatorKind::Goto { target: point.target },
                    })
                });

                targets.push(restore);
                values.push(ConstInt::U64(point.discr as u64));
            }

            let source_info = mir[START_BLOCK].terminator().source_info;

            let body_bb = ::std::mem::replace(&mut mir[START_BLOCK], BasicBlockData::new(None));
            let body = mir.basic_blocks_mut().push(body_bb);

            let unreachable = mir.basic_blocks_mut().push(BasicBlockData::new(Some(Terminator {
                source_info: source_info,
                kind: TerminatorKind::Unreachable,
            })));

            let abort = mir.basic_blocks_mut().push(BasicBlockData::new(Some(Terminator {
                source_info: source_info,
                kind: TerminatorKind::Assert {
                    cond: Operand::Constant(Constant { 
                        span: DUMMY_SP,
                        ty: tcx.mk_bool(),
                        literal: Literal::Value {
                            value: ConstVal::Bool(false)
                        },
                    }),
                    expected: true,
                    msg: AssertMessage::CoroutineError,
                    target: unreachable,
                    cleanup: None,
                },
                // TODO
            })));

            values.push(ConstInt::U64(START_VARIANT));
            targets.push(body);

            values.push(ConstInt::U64(STOP_VARIANT));
            targets.push(abort);

            values.push(ConstInt::U64(PANIC_VARIANT));
            targets.push(abort);

            mir[START_BLOCK].terminator = Some(Terminator {
                source_info: source_info,
                kind: TerminatorKind::Switch {
                    discr: Lvalue::Local(Local::new(1)).deref(),
                    values: values,
                    targets: targets,
                }
            });
        }
    }
}
