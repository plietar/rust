#![feature(conservative_impl_trait)]

pub enum CoResult<Y,R> {
    Return(R),
    Yield(Y),
}

pub fn repeat<T: Clone>(x: T) -> impl FnMut() -> CoResult<T, ()> {
    proc move || {
        loop {
            yield CoResult::Yield(x.clone());
        }
    }
}

pub fn limit<F, T>(n: u32, mut f: F) -> impl FnMut() -> CoResult<T, ()>
    where F: FnMut() -> CoResult<T, ()>
{
    proc move || {
        for _ in 0..n {
            match f() {
                CoResult::Yield(i) => yield CoResult::Yield(i),
                CoResult::Return(()) => yield CoResult::Return(()),
            }
        }
        return CoResult::Return(());
    }
}

fn main() {
    let mut g = limit(5, repeat('A'));
    while let CoResult::Yield(i) = g() {
        println!("{}", i);
    }
}
