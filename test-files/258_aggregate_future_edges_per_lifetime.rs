// When an aggregate is built from a reborrow, the future edge of each of the
// reborrow's lifetime projections moves to the aggregate's lifetime projection
// of the same region. `s3`'s first lifetime projection takes only the future
// edge of the reborrow's `'a`, not that of its `'b`, which goes to `s3`'s
// second lifetime projection. In `generic`, the future edge of the reborrow's
// `'b` goes to `s1`'s projection of the region in `T`, not to that of `'a`,
// which the region in `T` outlives too and which comes first in `S8`.
struct S1<'a> {
    x: &'a mut u32,
}

struct S2<'a, 'b> {
    x: &'b mut S1<'a>,
}

struct S3<'a, 'b, 'c> {
    x: &'c mut S2<'a, 'b>,
}

fn nested() {
    let mut n = 4;
    let mut s1 = S1 { x: &mut n };
    let mut s2 = S2 { x: &mut s1 };
    // PCG: bb0[26] post_main: s3↓'?23 -> (*_10)↓'?30 FUTURE
    // PCG: bb0[26] post_main: s3↓'?24 -> (*_10)↓'?31 FUTURE
    // ~PCG: bb0[26] post_main: s3↓'?23 -> (*_10)↓'?31 FUTURE
    let s3 = S3 { x: &mut s2 };
}

struct S8<'a, T> {
    x: &'a mut T,
}

struct X8<'a> {
    x: &'a mut i32,
}

fn generic() {
    let mut n = 4;
    let mut x = X8 { x: &mut n };
    // PCG: bb0[17] post_main: s1↓'?14 -> (*_7)↓'?18 FUTURE
    // ~PCG: bb0[17] post_main: s1↓'?13 -> (*_7)↓'?18 FUTURE
    let mut s1 = S8 { x: &mut x };
    let mut s2 = &mut s1;
}

fn main() {}
