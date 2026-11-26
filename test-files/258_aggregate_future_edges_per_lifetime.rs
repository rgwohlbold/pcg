// When an aggregate is built from a reborrow, the future edges of the
// reborrow's lifetime projections move to the aggregate's lifetime projections
// they flow into. `s3`'s first lifetime projection takes only the future edge
// of the reborrow's `'a`, not that of its `'b`, which goes to `s3`'s second
// lifetime projection.
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

fn main() {}
