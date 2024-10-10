


/// An iterator to visit each byte in a byte mask, as you might get from [child_mask](crate::zipper::Zipper::child_mask)
pub struct ByteMaskIter {
    i: u8,
    mask: [u64; 4],
}

pub trait IntoByteMaskIter {
    fn byte_mask_iter(self) -> ByteMaskIter;
}

impl IntoByteMaskIter for [u64; 4] {
    fn byte_mask_iter(self) -> ByteMaskIter {
        ByteMaskIter::from(self)
    }
}

impl IntoByteMaskIter for &[u64; 4] {
    fn byte_mask_iter(self) -> ByteMaskIter {
        ByteMaskIter::from(*self)
    }
}

impl From<[u64; 4]> for ByteMaskIter {
    fn from(mask: [u64; 4]) -> Self {
        Self::new(mask)
    }
}

impl ByteMaskIter {
    /// Make a new `ByteMaskIter` from a mask, as you might get from [child_mask](crate::zipper::Zipper::child_mask)
    fn new(mask: [u64; 4]) -> Self {
        Self {
            i: 0,
            mask,
        }
    }
}

impl Iterator for ByteMaskIter {
    type Item = u8;

    fn next(&mut self) -> Option<u8> {
        loop {
            let w = &mut self.mask[self.i as usize];
            if *w != 0 {
                let wi = w.trailing_zeros() as u8;
                *w ^= 1u64 << wi;
                let index = self.i*64 + wi;
                return Some(index)
            } else if self.i < 3 {
                self.i += 1;
            } else {
                return None
            }
        }
    }
}