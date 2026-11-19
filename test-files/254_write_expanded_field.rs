struct Pair<'b> {
    f: &'b mut i32,
    g: &'b mut i32,
}

fn write_g<'b>(mut p: Pair<'b>, r: &'b mut i32) -> Pair<'b> {
    // Writing `p.g` first expands `p`. The expansion's `p.g↓'b` holds the
    // contents the write replaces, so it is labelled, and the assigned borrow
    // flows into a new, current `p.g↓'b`.
    // PCG: bb0[2] post_main: {p↓'?6 before bb0[2]:PreMain} -> {p.f↓'?6, p.g before bb0[2]:PreMain↓'?6}
    // ~PCG: bb0[2] post_main: {p↓'?6 before bb0[2]:PreMain} -> {p.f↓'?6, p.g↓'?6}
    // PCG: bb0[2] post_main: _3 before bb0[2]:PostOperands↓'?8 -> p.g↓'?6
    p.g = r;
    p
}

fn main() {}
