
/// Some useful bit-twiddling methods for working with the mask you might get from [child_mask](crate::zipper::Zipper::child_mask)
pub trait BitMask {
    /// Returns the number of set bits in `mask`
    fn count_bits(&self) -> usize;

    /// Returns `true` if all bits in `mask` are clear, otherwise returns `false`
    fn is_empty_mask(&self) -> bool;

    /// Returns `true` if the `k`th bit in `mask` is set, otherwise returns `false`
    fn test_bit(&self, k: u8) -> bool;

    /// Sets the `k`th bit in `mask`
    fn set_bit(&mut self, k: u8);

    /// Clears the `k`th bit in `mask`
    fn clear_bit(&mut self, k: u8);
}

impl BitMask for [u64; 4] {
    #[inline]
    fn count_bits(&self) -> usize {
        return (self[0].count_ones() + self[1].count_ones() + self[2].count_ones() + self[3].count_ones()) as usize;
    }
    #[inline]
    fn is_empty_mask(&self) -> bool {
        self[0] == 0 && self[1] == 0 && self[2] == 0 && self[3] == 0
    }
    #[inline]
    fn test_bit(&self, k: u8) -> bool {
        let idx = ((k & 0b11000000) >> 6) as usize;
        let bit_i = k & 0b00111111;
        debug_assert!(idx < 4);
        self[idx] & (1 << bit_i) > 0
    }
    #[inline]
    fn set_bit(&mut self, k: u8) {
        let idx = (k / 64) as usize;
        self[idx] |= 1 << (k % 64);
    }

    /// Clears the `k`th bit in `mask`
    #[inline]
    fn clear_bit(&mut self, k: u8) {
        let idx = (k / 64) as usize;
        self[idx] ^= 1 << (k % 64);
    }
}

/// An iterator to visit each byte in a byte mask in ascending order.  Useful for working with the mask
/// as you might get from [child_mask](crate::zipper::Zipper::child_mask)
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

/// Returns a new empty mask
#[inline]
pub const fn mask_empty() -> [u64; 4] {
    [0; 4]
}

#[test]
fn bit_utils_test() {
    let mut mask = mask_empty();
    assert_eq!(mask.count_bits(), 0);
    assert_eq!(mask.is_empty_mask(), true);

    mask.set_bit(b'C');
    mask.set_bit(b'a');
    mask.set_bit(b't');
    assert_eq!(mask.is_empty_mask(), false);
    assert_eq!(mask.count_bits(), 3);

    mask.set_bit(b'C');
    mask.set_bit(b'a');
    mask.set_bit(b'n');
    assert_eq!(mask.count_bits(), 4);

    mask.clear_bit(b't');
    assert_eq!(mask.test_bit(b'n'), true);
    assert_eq!(mask.test_bit(b't'), false);
}
