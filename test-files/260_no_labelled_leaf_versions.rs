// An earlier version of a lifetime projection (one with a location label) is
// never a leaf: once the edges out of it are gone, what it passed on has come
// back to its place, and the PCG removes its label.

struct Foo<T> {
    f: T,
}

// Writing through `foo.f` expands `foo`. The aggregate edge from `_3` is
// removed only after `foo` is collapsed, which makes the future version of
// `foo`'s projection current, and after the earlier version it leads into has
// become the latest version of `foo`'s value, which is dead by then.
fn aggregate_into_expanded_place() {
    let mut a = 1;
    let foo = Foo { f: &mut a };
    *foo.f = 2;
    // PCG: bb0[10] pre_operands: Unlabel lifetime projection foo↓'?5 FUTURE
    // PCG: bb0[10] pre_operands: Unlabel lifetime projection foo before bb0[10]:PreOperands↓'?5 before bb0[9]:PreMain
    // PCG: bb0[10] pre_operands: Remove Edge aggregate {_3 before bb0[6]:PostOperands↓'?6} -> foo before bb0[10]:PreOperands↓'?5
    // ~PCG: bb0[10] pre_operands: Remove Edge aggregate {_3 before bb0[6]:PostOperands↓'?6} -> foo↓'?5
}

// Dereferencing `y` labels its own lifetime projection, which `*y` has no
// projection of; collapsing `*y` removes the label, although `*y` contains
// other lifetimes.
fn own_lifetime_of_dereferenced_reference<'b, 'c>(y: &'b mut &'c mut i32, z: &'c mut i32) {
    *y = z;
    // PCG: bb0[3] pre_operands: Unlabel lifetime projection y↓'?5 before bb0[2]:PreMain
}

// `Option::take` returns nothing of the reference's own lifetime, so no edge
// of the call leads out of its version before the call.
fn argument_without_call_edge(o: &mut Option<i32>) -> Option<i32> {
    // PCG: bb0[2] post_main: Unlabel lifetime projection _2 before bb0[2]:PostOperands↓'?5 before bb0[2]:PostMain
    o.take()
}

fn main() {}
