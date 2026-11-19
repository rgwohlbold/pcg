fn write_elem<'a>(mut y: [&'a mut i32; 2], r: &'a mut i32) -> [&'a mut i32; 2] {
    // Writing `y[1]` expands `y↓'a` into a single element. The base of the
    // expansion holds the other elements, so the collapse after the write
    // joins it into the new `y↓'a` together with the written element.
    // PCG: bb1[1] pre_operands: aggregate {y↓'?5 before bb1[0]:PreMain, y[_4] before bb1[1]:PreOperands↓'?5} -> y↓'?5
    // ~PCG: bb1[1] pre_operands: aggregate {y[_4] before bb1[1]:PreOperands↓'?5} -> y↓'?5
    y[1] = r;
    y
}

fn main() {}
