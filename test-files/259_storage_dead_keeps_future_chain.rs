// When the storage of a reference ends while its referent is reborrowed, the
// future node of the reference's lifetime projection stays a single node:
// what the reborrow gives back flows into it and on to the lender `x`. Without
// this, the end of `_7`'s storage made the node current where it is the
// source of the future edge into `x`'s future node, but not where it is the
// target of the future edge from `*_7`, so `x` was given back nothing.
struct S8<'a, T> {
    x: &'a mut T,
}

struct X8<'a> {
    x: &'a mut i32,
}

fn reborrow_outlives_reference() {
    let mut n = 4;
    let mut x = X8 { x: &mut n };
    // PCG: bb0[20] post_main: (*_7) before bb0[20]:PreMain↓'?18 FUTURE -> _7 before bb0[20]:PreMain↓'?18 FUTURE
    // PCG: bb0[20] post_main: _7 before bb0[20]:PreMain↓'?18 FUTURE -> x↓'?10 FUTURE
    // ~PCG: bb0[20] post_main: _7 before bb0[20]:PreMain↓'?18 -> x↓'?10 FUTURE
    let mut s1 = S8 { x: &mut x };
    let mut s2 = &mut s1;
}

fn main() {}
