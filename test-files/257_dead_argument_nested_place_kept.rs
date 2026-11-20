// A place below the referent of an argument is packed back into the
// reference when the dereference is removed, so it is not weakened while
// the graph still dereferences the argument, although the argument and its
// lifetime projections are dead.
struct Inner<'b, 'c> {
    a: &'b mut i32,
    b: i32,
    c: &'c mut i32,
}

struct Outer<'a, 'b, 'c, 'd> {
    a: &'a mut i32,
    b: Inner<'b, 'c>,
    c: &'d mut i32,
}

fn write_nested(arg: &mut Outer) {
    // ~PCG: bb0[1] pre_operands: Weaken (*arg).b from E to W
    arg.b.b = 5;
}

fn main() {}
