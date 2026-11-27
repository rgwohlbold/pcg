// A loop head holds `*self` at exclusive capability while `*self` stays
// expanded for the shared borrow of `self.dfa.classes` that the iterator
// keeps. The reborrow of `*self` for the call in the body must give `*self`
// back when it ends, although `*self` is still expanded: no part of it is
// lent mutably.
struct Cache;
pub struct ByteClasses([u8; 256]);
pub struct Unit;

pub struct ByteClassRepresentatives<'a> {
    classes: &'a ByteClasses,
}

impl<'a> Iterator for ByteClassRepresentatives<'a> {
    type Item = Unit;

    fn next(&mut self) -> Option<Unit> {
        unimplemented!()
    }
}

impl ByteClasses {
    pub fn representatives(&self) -> ByteClassRepresentatives<'_> {
        unimplemented!()
    }
}

struct Dfa {
    classes: ByteClasses,
}

struct Lazy<'i, 'c> {
    dfa: &'i Dfa,
    cache: &'c mut Cache,
}

impl<'i, 'c> Lazy<'i, 'c> {
    fn set_transition(&mut self, unit: Unit) {
        unimplemented!()
    }

    fn set_all_transitions(&mut self) {
        for unit in self.dfa.classes.representatives() {
            self.set_transition(unit);
            // PCG: bb10[0] pre_operands: Restore *self to E
        }
    }
}

fn main() {}
