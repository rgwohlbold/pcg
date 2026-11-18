// The caller still holds the loans of an argument's referent, so a place
// expanded below it is packed back once its lifetime projections are dead,
// not weakened: its fields keep their capability until the collapse.
struct Number<A, B, C> {
    a: A,
    b: B,
    c: C,
}

fn write_nested<A, B, C, D>(arg: &mut Number<A, Number<B, i32, C>, D>) {
    // ~PCG: bb0[1] pre_operands: Weaken (*arg).b.a from E to W
    // ~PCG: bb0[1] pre_operands: Weaken (*arg).b.b from E to W
    // ~PCG: bb0[1] pre_operands: Weaken (*arg).b.c from E to W
    arg.b.b = 5;
}

fn main() {}
