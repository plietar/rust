use def_use::DefUseAnalysis;
use rustc::mir::*;
use rustc::mir::transform::{MirPass, MirSource, Pass};
use rustc::ty::TyCtxt;
use rustc::middle::const_val::ConstVal;
use rustc_const_math::ConstInt;
use syntax::ast;
use syntax_pos::DUMMY_SP;

use rustc_data_structures::indexed_vec::{IndexVec, Idx};
use rustc_data_structures::control_flow_graph::reachable::{reachable, Reachability};

pub struct CoroutineTransform;

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
        for def_or_use in info.defs_and_uses.iter() {
            if def_or_use.context.is_mutating_use() {
                let def_block = def_or_use.location.block;
                let is_defined = block == def_block || reachability.can_reach(def_block, block);

                defined = defined || is_defined;
            }
        }

        defined
    })
}

impl Pass for CoroutineTransform {}
impl<'tcx> MirPass<'tcx> for CoroutineTransform {
    fn run_pass<'a>(&mut self,
                    tcx: TyCtxt<'a, 'tcx, 'tcx>,
                    source: MirSource,
                    mir: &mut Mir<'tcx>) {

        match source {
            MirSource::Const(_) => {
                return
            }
            MirSource::Static(..) | MirSource::Promoted(..) => {
                return
            }
            MirSource::Fn(_) => (),
        }

        let source_info = mir[START_BLOCK].terminator().source_info;
        let mut suspend_points : IndexVec<usize, (BasicBlock, BasicBlock, Vec<Statement>, Vec<Statement>)> = IndexVec::new();

        let mut def_use_analysis = DefUseAnalysis::new(mir);
        def_use_analysis.analyze(mir);
        let reachability = reachable(mir);

        for (block_idx, bb) in mir.basic_blocks().iter_enumerated() {
            if let &Terminator { kind: TerminatorKind::Yield { target }, .. } = bb.terminator() {
                suspend_points.push_with(|discr_value| {
                    let mut saves = vec![];
                    let mut restores = vec![];

                    let discr_ty = tcx.mk_mach_uint(ast::UintTy::U64);
                    let coroutine = Lvalue::Local(Local::new(1));
                    let lhs = coroutine.deref().field(Field::new(0), discr_ty);
                    let rhs = Rvalue::Use(Operand::Constant(Constant {
                        span: DUMMY_SP,
                        ty: discr_ty,
                        literal: Literal::Value {
                            value: ConstVal::Integral(ConstInt::U64(discr_value as u64 + 1))
                        }
                    }));

                    saves.push(Statement {
                        source_info: source_info,
                        kind: StatementKind::Assign(lhs, rhs),
                    });

                    let mut field = 1;
                    for (local, decl) in live_locals(mir, &def_use_analysis, &reachability, block_idx) {
                        let coroutine = Lvalue::Local(Local::new(1));
                        let lhs = coroutine.deref().field(Field::new(field), decl.ty);
                        let rhs = Rvalue::Use(Operand::Consume(Lvalue::Local(local)));
                        saves.push(Statement {
                            source_info: source_info,
                            kind: StatementKind::Assign(lhs, rhs),
                        });

                        let coroutine = Lvalue::Local(Local::new(1));
                        let lhs = Lvalue::Local(local);
                        let rhs = Rvalue::Use(Operand::Consume(coroutine.deref().field(Field::new(field), decl.ty)));
                        restores.push(Statement {
                            source_info: source_info,
                            kind: StatementKind::Assign(lhs, rhs),
                        });

                        field += 1;
                    }

                    (target, block_idx, saves, restores)
                });
            }
        }

        if suspend_points.len() > 0 {
            let mut values = vec![];
            let mut targets = vec![];
            for (discr_value, (target, predecessor, saves, restores)) in suspend_points.into_iter().enumerate() {
                mir[predecessor].statements.extend(saves);
                mir[predecessor].terminator_mut().kind = TerminatorKind::Return;

                let restore = mir.basic_blocks_mut().push(BasicBlockData {
                    is_cleanup: false,
                    statements: restores,
                    terminator: Some(Terminator {
                        source_info: source_info,
                        kind: TerminatorKind::Goto { target: target },
                    })
                });

                targets.push(restore);
                values.push(ConstVal::Integral(ConstInt::U64(discr_value as u64 + 1)));
            }

            let body_bb = ::std::mem::replace(&mut mir[START_BLOCK], BasicBlockData::new(None));
            let body = mir.basic_blocks_mut().push(body_bb);

            let fail = mir.basic_blocks_mut().push(BasicBlockData::new(Some(Terminator {
                source_info: source_info,
                kind: TerminatorKind::Unreachable,
            })));

            values.push(ConstVal::Integral(ConstInt::U64(0)));
            targets.push(body);

            targets.push(fail);

            let coroutine = Lvalue::Local(Local::new(1));
            let switch_ty = tcx.mk_mach_uint(ast::UintTy::U64);
            let discr = coroutine.deref().field(Field::new(0), switch_ty);

            mir[START_BLOCK].terminator = Some(Terminator {
                source_info: source_info,
                kind: TerminatorKind::SwitchInt {
                    discr: discr,
                    switch_ty: switch_ty,
                    values: values,
                    targets: targets,
                }
            });
        }
    }
}
