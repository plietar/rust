// Copyright 2015 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

#![allow(non_snake_case)]

register_long_diagnostics! {

E0010: r##"
The value of statics and constants must be known at compile time, and they live
for the entire lifetime of a program. Creating a boxed value allocates memory on
the heap at runtime, and therefore cannot be done at compile time. Erroneous
code example:

```compile_fail,E0010
#![feature(box_syntax)]

const CON : Box<i32> = box 0;
```
"##,

E0013: r##"
Static and const variables can refer to other const variables. But a const
variable cannot refer to a static variable. For example, `Y` cannot refer to
`X` here:

```compile_fail,E0013
static X: i32 = 42;
const Y: i32 = X;
```

To fix this, the value can be extracted as a const and then used:

```
const A: i32 = 42;
static X: i32 = A;
const Y: i32 = A;
```
"##,

// FIXME(#24111) Change the language here when const fn stabilizes
E0015: r##"
The only functions that can be called in static or constant expressions are
`const` functions, and struct/enum constructors. `const` functions are only
available on a nightly compiler. Rust currently does not support more general
compile-time function execution.

```
const FOO: Option<u8> = Some(1); // enum constructor
struct Bar {x: u8}
const BAR: Bar = Bar {x: 1}; // struct constructor
```

See [RFC 911] for more details on the design of `const fn`s.

[RFC 911]: https://github.com/rust-lang/rfcs/blob/master/text/0911-const-fn.md
"##,

E0016: r##"
Blocks in constants may only contain items (such as constant, function
definition, etc...) and a tail expression. Erroneous code example:

```compile_fail,E0016
const FOO: i32 = { let x = 0; x }; // 'x' isn't an item!
```

To avoid it, you have to replace the non-item object:

```
const FOO: i32 = { const X : i32 = 0; X };
```
"##,

E0017: r##"
References in statics and constants may only refer to immutable values.
Erroneous code example:

```compile_fail,E0017
static X: i32 = 1;
const C: i32 = 2;

// these three are not allowed:
const CR: &'static mut i32 = &mut C;
static STATIC_REF: &'static mut i32 = &mut X;
static CONST_REF: &'static mut i32 = &mut C;
```

Statics are shared everywhere, and if they refer to mutable data one might
violate memory safety since holding multiple mutable references to shared data
is not allowed.

If you really want global mutable state, try using `static mut` or a global
`UnsafeCell`.
"##,

E0018: r##"

The value of static and constant integers must be known at compile time. You
can't cast a pointer to an integer because the address of a pointer can
vary.

For example, if you write:

```compile_fail,E0018
static MY_STATIC: u32 = 42;
static MY_STATIC_ADDR: usize = &MY_STATIC as *const _ as usize;
static WHAT: usize = (MY_STATIC_ADDR^17) + MY_STATIC_ADDR;
```

Then `MY_STATIC_ADDR` would contain the address of `MY_STATIC`. However,
the address can change when the program is linked, as well as change
between different executions due to ASLR, and many linkers would
not be able to calculate the value of `WHAT`.

On the other hand, static and constant pointers can point either to
a known numeric address or to the address of a symbol.

```
static MY_STATIC: u32 = 42;
static MY_STATIC_ADDR: &'static u32 = &MY_STATIC;
const CONST_ADDR: *const u8 = 0x5f3759df as *const u8;
```

This does not pose a problem by itself because they can't be
accessed directly.
"##,

E0019: r##"
A function call isn't allowed in the const's initialization expression
because the expression's value must be known at compile-time. Erroneous code
example:

```compile_fail
enum Test {
    V1
}

impl Test {
    fn test(&self) -> i32 {
        12
    }
}

fn main() {
    const FOO: Test = Test::V1;

    const A: i32 = FOO.test(); // You can't call Test::func() here!
}
```

Remember: you can't use a function call inside a const's initialization
expression! However, you can totally use it anywhere else:

```
enum Test {
    V1
}

impl Test {
    fn func(&self) -> i32 {
        12
    }
}

fn main() {
    const FOO: Test = Test::V1;

    FOO.func(); // here is good
    let x = FOO.func(); // or even here!
}
```
"##,

E0022: r##"
Constant functions are not allowed to mutate anything. Thus, binding to an
argument with a mutable pattern is not allowed. For example,

```compile_fail
const fn foo(mut x: u8) {
    // do stuff
}
```

Is incorrect because the function body may not mutate `x`.

Remove any mutable bindings from the argument list to fix this error. In case
you need to mutate the argument, try lazily initializing a global variable
instead of using a `const fn`, or refactoring the code to a functional style to
avoid mutation if possible.
"##,

E0133: r##"
Unsafe code was used outside of an unsafe function or block.

Erroneous code example:

```compile_fail,E0133
unsafe fn f() { return; } // This is the unsafe code

fn main() {
    f(); // error: call to unsafe function requires unsafe function or block
}
```

Using unsafe functionality is potentially dangerous and disallowed by safety
checks. Examples:

* Dereferencing raw pointers
* Calling functions via FFI
* Calling functions marked unsafe

These safety checks can be relaxed for a section of the code by wrapping the
unsafe instructions with an `unsafe` block. For instance:

```
unsafe fn f() { return; }

fn main() {
    unsafe { f(); } // ok!
}
```

See also https://doc.rust-lang.org/book/first-edition/unsafe.html
"##,

E0373: r##"
This error occurs when an attempt is made to use data captured by a closure,
when that data may no longer exist. It's most commonly seen when attempting to
return a closure:

```compile_fail,E0373
fn foo() -> Box<Fn(u32) -> u32> {
    let x = 0u32;
    Box::new(|y| x + y)
}
```

Notice that `x` is stack-allocated by `foo()`. By default, Rust captures
closed-over data by reference. This means that once `foo()` returns, `x` no
longer exists. An attempt to access `x` within the closure would thus be
unsafe.

Another situation where this might be encountered is when spawning threads:

```compile_fail,E0373
fn foo() {
    let x = 0u32;
    let y = 1u32;

    let thr = std::thread::spawn(|| {
        x + y
    });
}
```

Since our new thread runs in parallel, the stack frame containing `x` and `y`
may well have disappeared by the time we try to use them. Even if we call
`thr.join()` within foo (which blocks until `thr` has completed, ensuring the
stack frame won't disappear), we will not succeed: the compiler cannot prove
that this behaviour is safe, and so won't let us do it.

The solution to this problem is usually to switch to using a `move` closure.
This approach moves (or copies, where possible) data into the closure, rather
than taking references to it. For example:

```
fn foo() -> Box<Fn(u32) -> u32> {
    let x = 0u32;
    Box::new(move |y| x + y)
}
```

Now that the closure has its own copy of the data, there's no need to worry
about safety.
"##,

E0381: r##"
It is not allowed to use or capture an uninitialized variable. For example:

```compile_fail,E0381
fn main() {
    let x: i32;
    let y = x; // error, use of possibly uninitialized variable
}
```

To fix this, ensure that any declared variables are initialized before being
used. Example:

```
fn main() {
    let x: i32 = 0;
    let y = x; // ok!
}
```
"##,

E0382: r##"
This error occurs when an attempt is made to use a variable after its contents
have been moved elsewhere. For example:

```compile_fail,E0382
struct MyStruct { s: u32 }

fn main() {
    let mut x = MyStruct{ s: 5u32 };
    let y = x;
    x.s = 6;
    println!("{}", x.s);
}
```

Since `MyStruct` is a type that is not marked `Copy`, the data gets moved out
of `x` when we set `y`. This is fundamental to Rust's ownership system: outside
of workarounds like `Rc`, a value cannot be owned by more than one variable.

Sometimes we don't need to move the value. Using a reference, we can let another
function borrow the value without changing its ownership. In the example below,
we don't actually have to move our string to `calculate_length`, we can give it
a reference to it with `&` instead.

```
fn main() {
    let s1 = String::from("hello");

    let len = calculate_length(&s1);

    println!("The length of '{}' is {}.", s1, len);
}

fn calculate_length(s: &String) -> usize {
    s.len()
}
```

A mutable reference can be created with `&mut`.

Sometimes we don't want a reference, but a duplicate. All types marked `Clone`
can be duplicated by calling `.clone()`. Subsequent changes to a clone do not
affect the original variable.

Most types in the standard library are marked `Clone`. The example below
demonstrates using `clone()` on a string. `s1` is first set to "many", and then
copied to `s2`. Then the first character of `s1` is removed, without affecting
`s2`. "any many" is printed to the console.

```
fn main() {
    let mut s1 = String::from("many");
    let s2 = s1.clone();
    s1.remove(0);
    println!("{} {}", s1, s2);
}
```

If we control the definition of a type, we can implement `Clone` on it ourselves
with `#[derive(Clone)]`.

Some types have no ownership semantics at all and are trivial to duplicate. An
example is `i32` and the other number types. We don't have to call `.clone()` to
clone them, because they are marked `Copy` in addition to `Clone`.  Implicit
cloning is more convenient in this case. We can mark our own types `Copy` if
all their members also are marked `Copy`.

In the example below, we implement a `Point` type. Because it only stores two
integers, we opt-out of ownership semantics with `Copy`. Then we can
`let p2 = p1` without `p1` being moved.

```
#[derive(Copy, Clone)]
struct Point { x: i32, y: i32 }

fn main() {
    let mut p1 = Point{ x: -1, y: 2 };
    let p2 = p1;
    p1.x = 1;
    println!("p1: {}, {}", p1.x, p1.y);
    println!("p2: {}, {}", p2.x, p2.y);
}
```

Alternatively, if we don't control the struct's definition, or mutable shared
ownership is truly required, we can use `Rc` and `RefCell`:

```
use std::cell::RefCell;
use std::rc::Rc;

struct MyStruct { s: u32 }

fn main() {
    let mut x = Rc::new(RefCell::new(MyStruct{ s: 5u32 }));
    let y = x.clone();
    x.borrow_mut().s = 6;
    println!("{}", x.borrow().s);
}
```

With this approach, x and y share ownership of the data via the `Rc` (reference
count type). `RefCell` essentially performs runtime borrow checking: ensuring
that at most one writer or multiple readers can access the data at any one time.

If you wish to learn more about ownership in Rust, start with the chapter in the
Book:

https://doc.rust-lang.org/book/first-edition/ownership.html
"##,

E0383: r##"
This error occurs when an attempt is made to partially reinitialize a
structure that is currently uninitialized.

For example, this can happen when a drop has taken place:

```compile_fail,E0383
struct Foo {
    a: u32,
}
impl Drop for Foo {
    fn drop(&mut self) { /* ... */ }
}

let mut x = Foo { a: 1 };
drop(x); // `x` is now uninitialized
x.a = 2; // error, partial reinitialization of uninitialized structure `t`
```

This error can be fixed by fully reinitializing the structure in question:

```
struct Foo {
    a: u32,
}
impl Drop for Foo {
    fn drop(&mut self) { /* ... */ }
}

let mut x = Foo { a: 1 };
drop(x);
x = Foo { a: 2 };
```
"##,

E0384: r##"
This error occurs when an attempt is made to reassign an immutable variable.
For example:

```compile_fail,E0384
fn main() {
    let x = 3;
    x = 5; // error, reassignment of immutable variable
}
```

By default, variables in Rust are immutable. To fix this error, add the keyword
`mut` after the keyword `let` when declaring the variable. For example:

```
fn main() {
    let mut x = 3;
    x = 5;
}
```
"##,

/*E0386: r##"
This error occurs when an attempt is made to mutate the target of a mutable
reference stored inside an immutable container.

For example, this can happen when storing a `&mut` inside an immutable `Box`:

```compile_fail,E0386
let mut x: i64 = 1;
let y: Box<_> = Box::new(&mut x);
**y = 2; // error, cannot assign to data in an immutable container
```

This error can be fixed by making the container mutable:

```
let mut x: i64 = 1;
let mut y: Box<_> = Box::new(&mut x);
**y = 2;
```

It can also be fixed by using a type with interior mutability, such as `Cell`
or `RefCell`:

```
use std::cell::Cell;

let x: i64 = 1;
let y: Box<Cell<_>> = Box::new(Cell::new(x));
y.set(2);
```
"##,*/

E0387: r##"
This error occurs when an attempt is made to mutate or mutably reference data
that a closure has captured immutably. Examples of this error are shown below:

```compile_fail,E0387
// Accepts a function or a closure that captures its environment immutably.
// Closures passed to foo will not be able to mutate their closed-over state.
fn foo<F: Fn()>(f: F) { }

// Attempts to mutate closed-over data. Error message reads:
// `cannot assign to data in a captured outer variable...`
fn mutable() {
    let mut x = 0u32;
    foo(|| x = 2);
}

// Attempts to take a mutable reference to closed-over data.  Error message
// reads: `cannot borrow data mutably in a captured outer variable...`
fn mut_addr() {
    let mut x = 0u32;
    foo(|| { let y = &mut x; });
}
```

The problem here is that foo is defined as accepting a parameter of type `Fn`.
Closures passed into foo will thus be inferred to be of type `Fn`, meaning that
they capture their context immutably.

If the definition of `foo` is under your control, the simplest solution is to
capture the data mutably. This can be done by defining `foo` to take FnMut
rather than Fn:

```
fn foo<F: FnMut()>(f: F) { }
```

Alternatively, we can consider using the `Cell` and `RefCell` types to achieve
interior mutability through a shared reference. Our example's `mutable`
function could be redefined as below:

```
use std::cell::Cell;

fn foo<F: Fn()>(f: F) { }

fn mutable() {
    let x = Cell::new(0u32);
    foo(|| x.set(2));
}
```

You can read more about cell types in the API documentation:

https://doc.rust-lang.org/std/cell/
"##,

E0388: r##"
E0388 was removed and is no longer issued.
"##,

E0389: r##"
An attempt was made to mutate data using a non-mutable reference. This
commonly occurs when attempting to assign to a non-mutable reference of a
mutable reference (`&(&mut T)`).

Example of erroneous code:

```compile_fail,E0389
struct FancyNum {
    num: u8,
}

fn main() {
    let mut fancy = FancyNum{ num: 5 };
    let fancy_ref = &(&mut fancy);
    fancy_ref.num = 6; // error: cannot assign to data in a `&` reference
    println!("{}", fancy_ref.num);
}
```

Here, `&mut fancy` is mutable, but `&(&mut fancy)` is not. Creating an
immutable reference to a value borrows it immutably. There can be multiple
references of type `&(&mut T)` that point to the same value, so they must be
immutable to prevent multiple mutable references to the same value.

To fix this, either remove the outer reference:

```
struct FancyNum {
    num: u8,
}

fn main() {
    let mut fancy = FancyNum{ num: 5 };

    let fancy_ref = &mut fancy;
    // `fancy_ref` is now &mut FancyNum, rather than &(&mut FancyNum)

    fancy_ref.num = 6; // No error!

    println!("{}", fancy_ref.num);
}
```

Or make the outer reference mutable:

```
struct FancyNum {
    num: u8
}

fn main() {
    let mut fancy = FancyNum{ num: 5 };

    let fancy_ref = &mut (&mut fancy);
    // `fancy_ref` is now &mut(&mut FancyNum), rather than &(&mut FancyNum)

    fancy_ref.num = 6; // No error!

    println!("{}", fancy_ref.num);
}
```
"##,

E0394: r##"
A static was referred to by value by another static.

Erroneous code examples:

```compile_fail,E0394
static A: u32 = 0;
static B: u32 = A; // error: cannot refer to other statics by value, use the
                   //        address-of operator or a constant instead
```

A static cannot be referred by value. To fix this issue, either use a
constant:

```
const A: u32 = 0; // `A` is now a constant
static B: u32 = A; // ok!
```

Or refer to `A` by reference:

```
static A: u32 = 0;
static B: &'static u32 = &A; // ok!
```
"##,

E0395: r##"
The value assigned to a constant scalar must be known at compile time,
which is not the case when comparing raw pointers.

Erroneous code example:

```compile_fail,E0395
static FOO: i32 = 42;
static BAR: i32 = 42;

static BAZ: bool = { (&FOO as *const i32) == (&BAR as *const i32) };
// error: raw pointers cannot be compared in statics!
```

The address assigned by the linker to `FOO` and `BAR` may or may not
be identical, so the value of `BAZ` can't be determined.

If you want to do the comparison, please do it at run-time.

For example:

```
static FOO: i32 = 42;
static BAR: i32 = 42;

let baz: bool = { (&FOO as *const i32) == (&BAR as *const i32) };
// baz isn't a constant expression so it's ok
```
"##,

E0161: r##"
A value was moved. However, its size was not known at compile time, and only
values of a known size can be moved.

Erroneous code example:

```compile_fail
#![feature(box_syntax)]

fn main() {
    let array: &[isize] = &[1, 2, 3];
    let _x: Box<[isize]> = box *array;
    // error: cannot move a value of type [isize]: the size of [isize] cannot
    //        be statically determined
}
```

In Rust, you can only move a value when its size is known at compile time.

To work around this restriction, consider "hiding" the value behind a reference:
either `&x` or `&mut x`. Since a reference has a fixed size, this lets you move
it around as usual. Example:

```
#![feature(box_syntax)]

fn main() {
    let array: &[isize] = &[1, 2, 3];
    let _x: Box<&[isize]> = box array; // ok!
}
```
"##,

E0396: r##"
The value behind a raw pointer can't be determined at compile-time
(or even link-time), which means it can't be used in a constant
expression. Erroneous code example:

```compile_fail,E0396
const REG_ADDR: *const u8 = 0x5f3759df as *const u8;

const VALUE: u8 = unsafe { *REG_ADDR };
// error: raw pointers cannot be dereferenced in constants
```

A possible fix is to dereference your pointer at some point in run-time.

For example:

```
const REG_ADDR: *const u8 = 0x5f3759df as *const u8;

let reg_value = unsafe { *REG_ADDR };
```
"##,

E0492: r##"
A borrow of a constant containing interior mutability was attempted. Erroneous
code example:

```compile_fail,E0492
use std::sync::atomic::{AtomicUsize, ATOMIC_USIZE_INIT};

const A: AtomicUsize = ATOMIC_USIZE_INIT;
static B: &'static AtomicUsize = &A;
// error: cannot borrow a constant which may contain interior mutability,
//        create a static instead
```

A `const` represents a constant value that should never change. If one takes
a `&` reference to the constant, then one is taking a pointer to some memory
location containing the value. Normally this is perfectly fine: most values
can't be changed via a shared `&` pointer, but interior mutability would allow
it. That is, a constant value could be mutated. On the other hand, a `static` is
explicitly a single memory location, which can be mutated at will.

So, in order to solve this error, either use statics which are `Sync`:

```
use std::sync::atomic::{AtomicUsize, ATOMIC_USIZE_INIT};

static A: AtomicUsize = ATOMIC_USIZE_INIT;
static B: &'static AtomicUsize = &A; // ok!
```

You can also have this error while using a cell type:

```compile_fail,E0492
use std::cell::Cell;

const A: Cell<usize> = Cell::new(1);
const B: &'static Cell<usize> = &A;
// error: cannot borrow a constant which may contain interior mutability,
//        create a static instead

// or:
struct C { a: Cell<usize> }

const D: C = C { a: Cell::new(1) };
const E: &'static Cell<usize> = &D.a; // error

// or:
const F: &'static C = &D; // error
```

This is because cell types do operations that are not thread-safe. Due to this,
they don't implement Sync and thus can't be placed in statics. In this
case, `StaticMutex` would work just fine, but it isn't stable yet:
https://doc.rust-lang.org/nightly/std/sync/struct.StaticMutex.html

However, if you still wish to use these types, you can achieve this by an unsafe
wrapper:

```
use std::cell::Cell;
use std::marker::Sync;

struct NotThreadSafe<T> {
    value: Cell<T>,
}

unsafe impl<T> Sync for NotThreadSafe<T> {}

static A: NotThreadSafe<usize> = NotThreadSafe { value : Cell::new(1) };
static B: &'static NotThreadSafe<usize> = &A; // ok!
```

Remember this solution is unsafe! You will have to ensure that accesses to the
cell are synchronized.
"##,

E0494: r##"
A reference of an interior static was assigned to another const/static.
Erroneous code example:

```compile_fail,E0494
struct Foo {
    a: u32
}

static S : Foo = Foo { a : 0 };
static A : &'static u32 = &S.a;
// error: cannot refer to the interior of another static, use a
//        constant instead
```

The "base" variable has to be a const if you want another static/const variable
to refer to one of its fields. Example:

```
struct Foo {
    a: u32
}

const S : Foo = Foo { a : 0 };
static A : &'static u32 = &S.a; // ok!
```
"##,

E0499: r##"
A variable was borrowed as mutable more than once. Erroneous code example:

```compile_fail,E0499
let mut i = 0;
let mut x = &mut i;
let mut a = &mut i;
// error: cannot borrow `i` as mutable more than once at a time
```

Please note that in rust, you can either have many immutable references, or one
mutable reference. Take a look at
https://doc.rust-lang.org/stable/book/references-and-borrowing.html for more
information. Example:


```
let mut i = 0;
let mut x = &mut i; // ok!

// or:
let mut i = 0;
let a = &i; // ok!
let b = &i; // still ok!
let c = &i; // still ok!
```
"##,

E0500: r##"
A borrowed variable was used in another closure. Example of erroneous code:

```compile_fail
fn you_know_nothing(jon_snow: &mut i32) {
    let nights_watch = || {
        *jon_snow = 2;
    };
    let starks = || {
        *jon_snow = 3; // error: closure requires unique access to `jon_snow`
                       //        but it is already borrowed
    };
}
```

In here, `jon_snow` is already borrowed by the `nights_watch` closure, so it
cannot be borrowed by the `starks` closure at the same time. To fix this issue,
you can put the closure in its own scope:

```
fn you_know_nothing(jon_snow: &mut i32) {
    {
        let nights_watch = || {
            *jon_snow = 2;
        };
    } // At this point, `jon_snow` is free.
    let starks = || {
        *jon_snow = 3;
    };
}
```

Or, if the type implements the `Clone` trait, you can clone it between
closures:

```
fn you_know_nothing(jon_snow: &mut i32) {
    let mut jon_copy = jon_snow.clone();
    let nights_watch = || {
        jon_copy = 2;
    };
    let starks = || {
        *jon_snow = 3;
    };
}
```
"##,

E0501: r##"
This error indicates that a mutable variable is being used while it is still
captured by a closure. Because the closure has borrowed the variable, it is not
available for use until the closure goes out of scope.

Note that a capture will either move or borrow a variable, but in this
situation, the closure is borrowing the variable. Take a look at
http://rustbyexample.com/fn/closures/capture.html for more information about
capturing.

Example of erroneous code:

```compile_fail,E0501
fn inside_closure(x: &mut i32) {
    // Actions which require unique access
}

fn outside_closure(x: &mut i32) {
    // Actions which require unique access
}

fn foo(a: &mut i32) {
    let bar = || {
        inside_closure(a)
    };
    outside_closure(a); // error: cannot borrow `*a` as mutable because previous
                        //        closure requires unique access.
}
```

To fix this error, you can place the closure in its own scope:

```
fn inside_closure(x: &mut i32) {}
fn outside_closure(x: &mut i32) {}

fn foo(a: &mut i32) {
    {
        let bar = || {
            inside_closure(a)
        };
    } // borrow on `a` ends.
    outside_closure(a); // ok!
}
```

Or you can pass the variable as a parameter to the closure:

```
fn inside_closure(x: &mut i32) {}
fn outside_closure(x: &mut i32) {}

fn foo(a: &mut i32) {
    let bar = |s: &mut i32| {
        inside_closure(s)
    };
    outside_closure(a);
    bar(a);
}
```

It may be possible to define the closure later:

```
fn inside_closure(x: &mut i32) {}
fn outside_closure(x: &mut i32) {}

fn foo(a: &mut i32) {
    outside_closure(a);
    let bar = || {
        inside_closure(a)
    };
}
```
"##,

E0502: r##"
This error indicates that you are trying to borrow a variable as mutable when it
has already been borrowed as immutable.

Example of erroneous code:

```compile_fail,E0502
fn bar(x: &mut i32) {}
fn foo(a: &mut i32) {
    let ref y = a; // a is borrowed as immutable.
    bar(a); // error: cannot borrow `*a` as mutable because `a` is also borrowed
            //        as immutable
}
```

To fix this error, ensure that you don't have any other references to the
variable before trying to access it mutably:

```
fn bar(x: &mut i32) {}
fn foo(a: &mut i32) {
    bar(a);
    let ref y = a; // ok!
}
```

For more information on the rust ownership system, take a look at
https://doc.rust-lang.org/stable/book/references-and-borrowing.html.
"##,

E0503: r##"
A value was used after it was mutably borrowed.

Example of erroneous code:

```compile_fail,E0503
fn main() {
    let mut value = 3;
    // Create a mutable borrow of `value`. This borrow
    // lives until the end of this function.
    let _borrow = &mut value;
    let _sum = value + 1; // error: cannot use `value` because
                          //        it was mutably borrowed
}
```

In this example, `value` is mutably borrowed by `borrow` and cannot be
used to calculate `sum`. This is not possible because this would violate
Rust's mutability rules.

You can fix this error by limiting the scope of the borrow:

```
fn main() {
    let mut value = 3;
    // By creating a new block, you can limit the scope
    // of the reference.
    {
        let _borrow = &mut value; // Use `_borrow` inside this block.
    }
    // The block has ended and with it the borrow.
    // You can now use `value` again.
    let _sum = value + 1;
}
```

Or by cloning `value` before borrowing it:

```
fn main() {
    let mut value = 3;
    // We clone `value`, creating a copy.
    let value_cloned = value.clone();
    // The mutable borrow is a reference to `value` and
    // not to `value_cloned`...
    let _borrow = &mut value;
    // ... which means we can still use `value_cloned`,
    let _sum = value_cloned + 1;
    // even though the borrow only ends here.
}
```

You can find more information about borrowing in the rust-book:
http://doc.rust-lang.org/stable/book/references-and-borrowing.html
"##,

E0504: r##"
This error occurs when an attempt is made to move a borrowed variable into a
closure.

Example of erroneous code:

```compile_fail,E0504
struct FancyNum {
    num: u8,
}

fn main() {
    let fancy_num = FancyNum { num: 5 };
    let fancy_ref = &fancy_num;

    let x = move || {
        println!("child function: {}", fancy_num.num);
        // error: cannot move `fancy_num` into closure because it is borrowed
    };

    x();
    println!("main function: {}", fancy_ref.num);
}
```

Here, `fancy_num` is borrowed by `fancy_ref` and so cannot be moved into
the closure `x`. There is no way to move a value into a closure while it is
borrowed, as that would invalidate the borrow.

If the closure can't outlive the value being moved, try using a reference
rather than moving:

```
struct FancyNum {
    num: u8,
}

fn main() {
    let fancy_num = FancyNum { num: 5 };
    let fancy_ref = &fancy_num;

    let x = move || {
        // fancy_ref is usable here because it doesn't move `fancy_num`
        println!("child function: {}", fancy_ref.num);
    };

    x();

    println!("main function: {}", fancy_num.num);
}
```

If the value has to be borrowed and then moved, try limiting the lifetime of
the borrow using a scoped block:

```
struct FancyNum {
    num: u8,
}

fn main() {
    let fancy_num = FancyNum { num: 5 };

    {
        let fancy_ref = &fancy_num;
        println!("main function: {}", fancy_ref.num);
        // `fancy_ref` goes out of scope here
    }

    let x = move || {
        // `fancy_num` can be moved now (no more references exist)
        println!("child function: {}", fancy_num.num);
    };

    x();
}
```

If the lifetime of a reference isn't enough, such as in the case of threading,
consider using an `Arc` to create a reference-counted value:

```
use std::sync::Arc;
use std::thread;

struct FancyNum {
    num: u8,
}

fn main() {
    let fancy_ref1 = Arc::new(FancyNum { num: 5 });
    let fancy_ref2 = fancy_ref1.clone();

    let x = thread::spawn(move || {
        // `fancy_ref1` can be moved and has a `'static` lifetime
        println!("child thread: {}", fancy_ref1.num);
    });

    x.join().expect("child thread should finish");
    println!("main thread: {}", fancy_ref2.num);
}
```
"##,

E0505: r##"
A value was moved out while it was still borrowed.

Erroneous code example:

```compile_fail,E0505
struct Value {}

fn eat(val: Value) {}

fn main() {
    let x = Value{};
    {
        let _ref_to_val: &Value = &x;
        eat(x);
    }
}
```

Here, the function `eat` takes the ownership of `x`. However,
`x` cannot be moved because it was borrowed to `_ref_to_val`.
To fix that you can do few different things:

* Try to avoid moving the variable.
* Release borrow before move.
* Implement the `Copy` trait on the type.

Examples:

```
struct Value {}

fn eat(val: &Value) {}

fn main() {
    let x = Value{};
    {
        let _ref_to_val: &Value = &x;
        eat(&x); // pass by reference, if it's possible
    }
}
```

Or:

```
struct Value {}

fn eat(val: Value) {}

fn main() {
    let x = Value{};
    {
        let _ref_to_val: &Value = &x;
    }
    eat(x); // release borrow and then move it.
}
```

Or:

```
#[derive(Clone, Copy)] // implement Copy trait
struct Value {}

fn eat(val: Value) {}

fn main() {
    let x = Value{};
    {
        let _ref_to_val: &Value = &x;
        eat(x); // it will be copied here.
    }
}
```

You can find more information about borrowing in the rust-book:
http://doc.rust-lang.org/stable/book/references-and-borrowing.html
"##,

E0506: r##"
This error occurs when an attempt is made to assign to a borrowed value.

Example of erroneous code:

```compile_fail,E0506
struct FancyNum {
    num: u8,
}

fn main() {
    let mut fancy_num = FancyNum { num: 5 };
    let fancy_ref = &fancy_num;
    fancy_num = FancyNum { num: 6 };
    // error: cannot assign to `fancy_num` because it is borrowed

    println!("Num: {}, Ref: {}", fancy_num.num, fancy_ref.num);
}
```

Because `fancy_ref` still holds a reference to `fancy_num`, `fancy_num` can't
be assigned to a new value as it would invalidate the reference.

Alternatively, we can move out of `fancy_num` into a second `fancy_num`:

```
struct FancyNum {
    num: u8,
}

fn main() {
    let mut fancy_num = FancyNum { num: 5 };
    let moved_num = fancy_num;
    fancy_num = FancyNum { num: 6 };

    println!("Num: {}, Moved num: {}", fancy_num.num, moved_num.num);
}
```

If the value has to be borrowed, try limiting the lifetime of the borrow using
a scoped block:

```
struct FancyNum {
    num: u8,
}

fn main() {
    let mut fancy_num = FancyNum { num: 5 };

    {
        let fancy_ref = &fancy_num;
        println!("Ref: {}", fancy_ref.num);
    }

    // Works because `fancy_ref` is no longer in scope
    fancy_num = FancyNum { num: 6 };
    println!("Num: {}", fancy_num.num);
}
```

Or by moving the reference into a function:

```
struct FancyNum {
    num: u8,
}

fn main() {
    let mut fancy_num = FancyNum { num: 5 };

    print_fancy_ref(&fancy_num);

    // Works because function borrow has ended
    fancy_num = FancyNum { num: 6 };
    println!("Num: {}", fancy_num.num);
}

fn print_fancy_ref(fancy_ref: &FancyNum){
    println!("Ref: {}", fancy_ref.num);
}
```
"##,

E0507: r##"
You tried to move out of a value which was borrowed. Erroneous code example:

```compile_fail,E0507
use std::cell::RefCell;

struct TheDarkKnight;

impl TheDarkKnight {
    fn nothing_is_true(self) {}
}

fn main() {
    let x = RefCell::new(TheDarkKnight);

    x.borrow().nothing_is_true(); // error: cannot move out of borrowed content
}
```

Here, the `nothing_is_true` method takes the ownership of `self`. However,
`self` cannot be moved because `.borrow()` only provides an `&TheDarkKnight`,
which is a borrow of the content owned by the `RefCell`. To fix this error,
you have three choices:

* Try to avoid moving the variable.
* Somehow reclaim the ownership.
* Implement the `Copy` trait on the type.

Examples:

```
use std::cell::RefCell;

struct TheDarkKnight;

impl TheDarkKnight {
    fn nothing_is_true(&self) {} // First case, we don't take ownership
}

fn main() {
    let x = RefCell::new(TheDarkKnight);

    x.borrow().nothing_is_true(); // ok!
}
```

Or:

```
use std::cell::RefCell;

struct TheDarkKnight;

impl TheDarkKnight {
    fn nothing_is_true(self) {}
}

fn main() {
    let x = RefCell::new(TheDarkKnight);
    let x = x.into_inner(); // we get back ownership

    x.nothing_is_true(); // ok!
}
```

Or:

```
use std::cell::RefCell;

#[derive(Clone, Copy)] // we implement the Copy trait
struct TheDarkKnight;

impl TheDarkKnight {
    fn nothing_is_true(self) {}
}

fn main() {
    let x = RefCell::new(TheDarkKnight);

    x.borrow().nothing_is_true(); // ok!
}
```

Moving a member out of a mutably borrowed struct will also cause E0507 error:

```compile_fail,E0507
struct TheDarkKnight;

impl TheDarkKnight {
    fn nothing_is_true(self) {}
}

struct Batcave {
    knight: TheDarkKnight
}

fn main() {
    let mut cave = Batcave {
        knight: TheDarkKnight
    };
    let borrowed = &mut cave;

    borrowed.knight.nothing_is_true(); // E0507
}
```

It is fine only if you put something back. `mem::replace` can be used for that:

```
# struct TheDarkKnight;
# impl TheDarkKnight { fn nothing_is_true(self) {} }
# struct Batcave { knight: TheDarkKnight }
use std::mem;

let mut cave = Batcave {
    knight: TheDarkKnight
};
let borrowed = &mut cave;

mem::replace(&mut borrowed.knight, TheDarkKnight).nothing_is_true(); // ok!
```

You can find more information about borrowing in the rust-book:
http://doc.rust-lang.org/book/first-edition/references-and-borrowing.html
"##,

E0508: r##"
A value was moved out of a non-copy fixed-size array.

Example of erroneous code:

```compile_fail,E0508
struct NonCopy;

fn main() {
    let array = [NonCopy; 1];
    let _value = array[0]; // error: cannot move out of type `[NonCopy; 1]`,
                           //        a non-copy fixed-size array
}
```

The first element was moved out of the array, but this is not
possible because `NonCopy` does not implement the `Copy` trait.

Consider borrowing the element instead of moving it:

```
struct NonCopy;

fn main() {
    let array = [NonCopy; 1];
    let _value = &array[0]; // Borrowing is allowed, unlike moving.
}
```

Alternatively, if your type implements `Clone` and you need to own the value,
consider borrowing and then cloning:

```
#[derive(Clone)]
struct NonCopy;

fn main() {
    let array = [NonCopy; 1];
    // Now you can clone the array element.
    let _value = array[0].clone();
}
```
"##,

E0509: r##"
This error occurs when an attempt is made to move out of a value whose type
implements the `Drop` trait.

Example of erroneous code:

```compile_fail,E0509
struct FancyNum {
    num: usize
}

struct DropStruct {
    fancy: FancyNum
}

impl Drop for DropStruct {
    fn drop(&mut self) {
        // Destruct DropStruct, possibly using FancyNum
    }
}

fn main() {
    let drop_struct = DropStruct{fancy: FancyNum{num: 5}};
    let fancy_field = drop_struct.fancy; // Error E0509
    println!("Fancy: {}", fancy_field.num);
    // implicit call to `drop_struct.drop()` as drop_struct goes out of scope
}
```

Here, we tried to move a field out of a struct of type `DropStruct` which
implements the `Drop` trait. However, a struct cannot be dropped if one or
more of its fields have been moved.

Structs implementing the `Drop` trait have an implicit destructor that gets
called when they go out of scope. This destructor may use the fields of the
struct, so moving out of the struct could make it impossible to run the
destructor. Therefore, we must think of all values whose type implements the
`Drop` trait as single units whose fields cannot be moved.

This error can be fixed by creating a reference to the fields of a struct,
enum, or tuple using the `ref` keyword:

```
struct FancyNum {
    num: usize
}

struct DropStruct {
    fancy: FancyNum
}

impl Drop for DropStruct {
    fn drop(&mut self) {
        // Destruct DropStruct, possibly using FancyNum
    }
}

fn main() {
    let drop_struct = DropStruct{fancy: FancyNum{num: 5}};
    let ref fancy_field = drop_struct.fancy; // No more errors!
    println!("Fancy: {}", fancy_field.num);
    // implicit call to `drop_struct.drop()` as drop_struct goes out of scope
}
```

Note that this technique can also be used in the arms of a match expression:

```
struct FancyNum {
    num: usize
}

enum DropEnum {
    Fancy(FancyNum)
}

impl Drop for DropEnum {
    fn drop(&mut self) {
        // Destruct DropEnum, possibly using FancyNum
    }
}

fn main() {
    // Creates and enum of type `DropEnum`, which implements `Drop`
    let drop_enum = DropEnum::Fancy(FancyNum{num: 10});
    match drop_enum {
        // Creates a reference to the inside of `DropEnum::Fancy`
        DropEnum::Fancy(ref fancy_field) => // No error!
            println!("It was fancy-- {}!", fancy_field.num),
    }
    // implicit call to `drop_enum.drop()` as drop_enum goes out of scope
}
```
"##,

E0595: r##"
Closures cannot mutate immutable captured variables.

Erroneous code example:

```compile_fail,E0595
let x = 3; // error: closure cannot assign to immutable local variable `x`
let mut c = || { x += 1 };
```

Make the variable binding mutable:

```
let mut x = 3; // ok!
let mut c = || { x += 1 };
```
"##,

E0596: r##"
This error occurs because you tried to mutably borrow a non-mutable variable.

Example of erroneous code:

```compile_fail,E0596
let x = 1;
let y = &mut x; // error: cannot borrow mutably
```

In here, `x` isn't mutable, so when we try to mutably borrow it in `y`, it
fails. To fix this error, you need to make `x` mutable:

```
let mut x = 1;
let y = &mut x; // ok!
```
"##,

E0597: r##"
This error occurs because a borrow was made inside a variable which has a
greater lifetime than the borrowed one.

Example of erroneous code:

```compile_fail,E0597
struct Foo<'a> {
    x: Option<&'a u32>,
}

let mut x = Foo { x: None };
let y = 0;
x.x = Some(&y); // error: `y` does not live long enough
```

In here, `x` is created before `y` and therefore has a greater lifetime. Always
keep in mind that values in a scope are dropped in the opposite order they are
created. So to fix the previous example, just make the `y` lifetime greater than
the `x`'s one:

```
struct Foo<'a> {
    x: Option<&'a u32>,
}

let y = 0;
let mut x = Foo { x: None };
x.x = Some(&y);
```
"##,

E0626: r##"
This error occurs because a borrow in a generator persists across a
yield point.

```compile_fail,E0626
# #![feature(generators, generator_trait)]
# use std::ops::Generator;
let mut b = || {
    let a = &String::new(); // <-- This borrow...
    yield (); // ...is still in scope here, when the yield occurs.
    println!("{}", a);
};
b.resume();
```

At present, it is not permitted to have a yield that occurs while a
borrow is still in scope. To resolve this error, the borrow must
either be "contained" to a smaller scope that does not overlap the
yield or else eliminated in another way. So, for example, we might
resolve the previous example by removing the borrow and just storing
the integer by value:

```
# #![feature(generators, generator_trait)]
# use std::ops::Generator;
let mut b = || {
    let a = 3;
    yield ();
    println!("{}", a);
};
b.resume();
```

This is a very simple case, of course. In more complex cases, we may
wish to have more than one reference to the value that was borrowed --
in those cases, something like the `Rc` or `Arc` types may be useful.

This error also frequently arises with iteration:

```compile_fail,E0626
# #![feature(generators, generator_trait)]
# use std::ops::Generator;
let mut b = || {
  let v = vec![1,2,3];
  for &x in &v { // <-- borrow of `v` is still in scope...
    yield x; // ...when this yield occurs.
  }
};
b.resume();
```

Such cases can sometimes be resolved by iterating "by value" (or using
`into_iter()`) to avoid borrowing:

```
# #![feature(generators, generator_trait)]
# use std::ops::Generator;
let mut b = || {
  let v = vec![1,2,3];
  for x in v { // <-- Take ownership of the values instead!
    yield x; // <-- Now yield is OK.
  }
};
b.resume();
```

If taking ownership is not an option, using indices can work too:

```
# #![feature(generators, generator_trait)]
# use std::ops::Generator;
let mut b = || {
  let v = vec![1,2,3];
  let len = v.len(); // (*)
  for i in 0..len {
    let x = v[i]; // (*)
    yield x; // <-- Now yield is OK.
  }
};
b.resume();

// (*) -- Unfortunately, these temporaries are currently required.
// See <https://github.com/rust-lang/rust/issues/43122>.
```
"##,

}

register_diagnostics! {
//    E0385, // {} in an aliasable location
    E0493, // destructors cannot be evaluated at compile-time
    E0524, // two closures require unique access to `..` at the same time
    E0526, // shuffle indices are not constant
    E0594, // cannot assign to {}
    E0598, // lifetime of {} is too short to guarantee its contents can be...
    E0625, // thread-local statics cannot be accessed at compile-time
}
