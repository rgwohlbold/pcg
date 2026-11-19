struct W<T> {
    f: T,
}

fn loop1(w: W<&mut i32>, n: u32) {
    let mut i = 0;
    // The loop head expands `w`. The entry edge reports the expansion of its
    // lifetime projection and the label of the expanded projection; the back
    // edge, where the expansion already exists, does not report it again.
    // PCG: bb0 -> bb1: Label lifetime projection w↓'?4 with label loop bb1
    // PCG: bb0 -> bb1: Add Edge {w↓'?4 loop bb1} -> {w.f↓'?4}
    // ~PCG: bb4 -> bb1: Label lifetime projection w↓'?4 with label loop bb1
    // ~PCG: bb4 -> bb1: Add Edge {w↓'?4 loop bb1} -> {w.f↓'?4}
    while i < n {
        *w.f = 1;
        i += 1;
    }
}

fn main() {}
