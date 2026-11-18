struct Pair<'b> {
    f: &'b mut i32,
    g: &'b mut i32,
}

fn set<'a, 'b>(x: &'a mut Pair<'b>) {
    // Removing the deref edge `{x} -> {*x}` labels `*x`, which renames the
    // expansion of `*x`'s lifetime projection. The leaves are identified again
    // after each removal, so the expansion is removed once, under one name.
    // PCG: bb0[1] pre_operands: Remove Edge {*x↓'?6 before bb0[0]:PreMain} -> {(*x).f↓'?6, (*x).g↓'?6}
    // ~PCG: bb0[1] pre_operands: Remove Edge {*x before bb0[1]:PreOperands↓'?6 before bb0[0]:PreMain} -> {(*x).f↓'?6 before bb0[1]:PreOperands, (*x).g↓'?6 before bb0[1]:PreOperands}
    *x.f = 1;
}

fn main() {}
