use core::mem::{ManuallyDrop, MaybeUninit};
use core::iter::Iterator;

use local_or_heap::LocalOrHeap;

use crate::bytetrie::*;
use crate::ring::*;
use crate::dense_byte_node::DenseByteNode;


/// A LineListNode stores up to 2 children in a single cache line
pub struct LineListNode<V> {
    /// bit 15 = slot_0_used
    /// bit 14 = slot_1_used
    /// bit 13 = slot_0_is_child (child ptr vs value)
    /// bit 12 = slot_1_is_child (child ptr vs value).  If bit 14 is 0, but bit 12 is 1, it means slot_0 consumed all the key space, so nothing can go in slot_1
    /// bits 11 to bit 6 = slot_0_key_len
    /// bit 5 to bit 0 = slot_1_key_len
    header: u16,
    key_bytes: [MaybeUninit<u8>; KEY_BYTES_CNT],
    val_or_child0: ValOrChild<V>,
    val_or_child1: ValOrChild<V>,
}
//DISCUSSION: Choosing a KEY_BYTES_CNT size
// The rest of the ListNode is 34 bytes.  So setting KEY_BYTES_CNT=30 means the ListNode is 64 bytes or
// one chache line.  But if we put in into an RcBox, (which adds a 16 byte header) we either need 14 bytes
// to stay within 1 cache line, or 78 to pack into two.
//WARNING the length bits mean I will overflow if I go above 63
const KEY_BYTES_CNT: usize = 14;

union ValOrChild<V> {
    child: ManuallyDrop<TrieNodeODRc<V>>,
    val: ManuallyDrop<LocalOrHeap<V>>,
    _unused: ()
}

impl<V> Drop for LineListNode<V> {
    fn drop(&mut self) {
        if self.is_used_0() {
            if self.is_child_ptr::<0>() {
                unsafe{ ManuallyDrop::drop(&mut self.val_or_child0.child) }
            } else {
                unsafe{ ManuallyDrop::drop(&mut self.val_or_child0.val) }
            }
        }
        if self.is_used_1() {
            if self.is_child_ptr::<1>() {
                unsafe{ ManuallyDrop::drop(&mut self.val_or_child1.child) }
            } else {
                unsafe{ ManuallyDrop::drop(&mut self.val_or_child1.val) }
            }
        }
    }
}

impl<V: Clone> Clone for LineListNode<V> {
    fn clone(&self) -> Self {
        let val_or_child0 = if self.is_used_0() {
            if self.is_child_ptr::<0>() {
                let child = unsafe{ &self.val_or_child0.child }.clone();
                ValOrChild{ child }
            } else {
                let val = unsafe{ &self.val_or_child0.val }.clone();
                ValOrChild{ val }
            }
        } else {
            ValOrChild{ _unused: () }
        };
        let val_or_child1 = if self.is_used_1() {
            if self.is_child_ptr::<1>() {
                let child = unsafe{ &self.val_or_child1.child }.clone();
                ValOrChild{ child }
            } else {
                let val = unsafe{ &self.val_or_child1.val }.clone();
                ValOrChild{ val }
            }
        } else {
            ValOrChild{ _unused: () }
        };
        Self {
            header: self.header,
            key_bytes: self.key_bytes,
            val_or_child0,
            val_or_child1,
        }
    }
}

impl<V> Default for LineListNode<V> {
    fn default() -> Self {
        Self::new()
    }
}

impl <V : core::fmt::Debug> core::fmt::Debug for LineListNode<V> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> std::fmt::Result {
        //Recursively printing a whole tree will get pretty unwieldy.  Should do something
        // like serialization for inspection using standard tools.
        let key_0 = if self.is_used_0() {
            std::str::from_utf8(unsafe{ self.key_unchecked_0() }).unwrap_or("")
        } else {
            ""
        };
        let key_1 = if self.is_used_1() {
            std::str::from_utf8(unsafe{ self.key_unchecked_1() }).unwrap_or("")
        } else {
            ""
        };
        write!(f,
               "LineListNode (\nslot0: occupied={} is_child={} key=\"{}\"\nslot1: occupied={} is_child={} key=\"{}\")",
               self.is_used_0(), self.is_child_ptr::<0>(), key_0,
               self.is_used_1(), self.is_child_ptr::<1>(), key_1)
    }
}

impl<V> LineListNode<V> {

    #[inline]
    pub fn new() -> Self {
        Self {
            header: 0,
            key_bytes: [MaybeUninit::uninit(); KEY_BYTES_CNT],
            val_or_child0: ValOrChild{ _unused: () },
            val_or_child1: ValOrChild{ _unused: () },
        }
    }
    #[inline]
    pub fn is_used_0(&self) -> bool {
        self.header & (1 << 15) > 0
    }
    #[inline]
    pub fn is_used_1(&self) -> bool {
        self.header & (1 << 14) > 0
    }
    /// Extracts the flag and length bits assocated with slot_0
    #[inline]
    fn flags_and_len_0(&self) -> usize {
        const LEN_MASK: usize = 0xfc0; //bits 11 to 6, inclusive
        self.header as usize & ((1 << 15) | (1 << 13) | LEN_MASK)
    }
    /// Extracts the flag and length bits assocated with slot_1
    #[inline]
    fn flags_and_len_1(&self) -> usize {
        const LEN_MASK: usize = 0x3f; //bits 5 to 0, inclusive
        (self.header as usize) & ((1 << 14) | (1 << 12) | LEN_MASK)
    }
    /// Returns `true` if slot_1 is available to be filled with an entry, otherwise `false`.  The reason
    /// `!is_used_1()` is insufficient is because `slot_1` may be empty but the key storage may be fully
    /// consumed by slot_0's key
    #[inline]
    pub fn is_available_1(&self) -> bool {
        self.header & ((1 << 14) | (1 << 12)) == 0
    }
    #[inline]
    pub fn is_child_ptr<const SLOT: usize>(&self) -> bool {
        match SLOT {
            0 => self.header & (1 << 13) > 0,
            1 => self.header & (1 << 12) > 0,
            _ => unreachable!()
        }
    }
    /// Conceptually identical to is_used_0 && is_child_ptr_0, but with a compound operation
    #[inline]
    pub fn is_used_child_0(&self) -> bool {
        self.header & ((1 << 15) | (1 << 13)) == ((1 << 15) | (1 << 13))
    }
    #[inline]
    pub fn is_used_child_1(&self) -> bool {
        self.header & ((1 << 14) | (1 << 12)) == ((1 << 14) | (1 << 12))
    }
    /// Conceptually identical to is_used_0 && !is_child_ptr_0, but with a compound operation
    #[inline]
    pub fn is_used_value_0(&self) -> bool {
        self.header & ((1 << 15) | (1 << 13)) == (1 << 15)
    }
    #[inline]
    pub fn is_used_value_1(&self) -> bool {
        self.header & ((1 << 14) | (1 << 12)) == (1 << 14)
    }
    #[inline]
    pub fn key_len_0(&self) -> usize {
        const MASK: u16 = 0xfc0; //bits 11 to 6, inclusive
        ((self.header & MASK) >> 6) as usize
    }
    #[inline]
    pub fn key_len_1(&self) -> usize {
        const MASK: u16 = 0x3f; //bits 5 to 0, inclusive
        (self.header & MASK) as usize
    }
    //NOTE: max_key_len_0 == KEY_BYTES_CNT, because LineListNodes are append-only
    // #[inline]
    // pub fn max_key_len_1(&self) -> usize {
    //     KEY_BYTES_CNT - self.key_len_0()
    // }
    //GOAT, Easier to construct the ranges as we need them
    // #[inline]
    // pub fn key_range_0(&self) -> core::ops::RangeTo<usize> {
    //     core::ops::RangeTo{ end: self.key_len_0() }
    // }
    // #[inline]
    // pub fn key_range_1(&self) -> core::ops::Range<usize> {
    //     core::ops::Range{ start: self.key_len_0(), end: self.key_len_1() }
    // }
    #[inline]
    unsafe fn key_unchecked_0(&self) -> &[u8] {
        core::slice::from_raw_parts(self.key_bytes.as_ptr().cast(), self.key_len_0())
    }
    #[inline]
    unsafe fn key_unchecked_1(&self) -> &[u8] {
        let base_ptr = self.key_bytes.get_unchecked(self.key_len_0());
        core::slice::from_raw_parts(base_ptr.as_ptr().cast(), self.key_len_1())
    }
    #[inline]
    unsafe fn child_in_slot<const SLOT: usize>(&self) -> &TrieNodeODRc<V> {
        match SLOT {
            0 => &*self.val_or_child0.child,
            1 => &*self.val_or_child1.child,
            _ => unreachable!()
        }
    }
    #[inline]
    unsafe fn child_in_slot_mut<const SLOT: usize>(&mut self) -> &mut TrieNodeODRc<V> {
        match SLOT {
            0 => &mut *self.val_or_child0.child,
            1 => &mut *self.val_or_child1.child,
            _ => unreachable!()
        }
    }
    #[inline]
    unsafe fn val_in_slot<const SLOT: usize>(&self) -> &V {
        match SLOT {
            0 => &**self.val_or_child0.val,
            1 => &**self.val_or_child1.val,
            _ => unreachable!()
        }
    }
    #[inline]
    unsafe fn val_in_slot_mut<const SLOT: usize>(&mut self) -> &mut V {
        match SLOT {
            0 => &mut **self.val_or_child0.val,
            1 => &mut **self.val_or_child1.val,
            _ => unreachable!()
        }
    }
    #[inline]
    unsafe fn set_val_0(&mut self, key: &[u8], val: LocalOrHeap<V>) {
        self.set_payload_0(key, false, ValOrChild{ val: ManuallyDrop::new(val) });
    }
    #[inline]
    unsafe fn set_val_1(&mut self, key: &[u8], val: LocalOrHeap<V>) {
        self.set_payload_1(key, false, ValOrChild{ val: ManuallyDrop::new(val) });
    }
    /// Sets the payload and key for slot_0
    #[inline]
    unsafe fn set_payload_0(&mut self, key: &[u8], is_child_ptr: bool, payload: ValOrChild<V>) {
        debug_assert!(key.len() <= KEY_BYTES_CNT);
        core::ptr::copy_nonoverlapping(key.as_ptr(), self.key_bytes.as_mut_ptr().cast(), key.len());
        self.val_or_child0 = payload;
        let mask = if is_child_ptr {
            0xa000 | (key.len() << 6)
        } else {
            0x8000 | (key.len() << 6)
        };
        self.header |= mask as u16;
        if key.len() == KEY_BYTES_CNT {
            self.header |= 1 << 12; //Set the flag state so slot_1 is unavailable
        }
    }
    #[inline]
    unsafe fn set_payload_1(&mut self, key: &[u8], is_child_ptr: bool, payload: ValOrChild<V>) {
        let key_0_used_cnt = self.key_len_0();
        debug_assert!(key.len() <= KEY_BYTES_CNT - key_0_used_cnt);
        let base_ptr = self.key_bytes.get_unchecked_mut(key_0_used_cnt);
        core::ptr::copy_nonoverlapping(key.as_ptr(), base_ptr.as_mut_ptr().cast(), key.len());
        self.val_or_child1 = payload;
        let mask = if is_child_ptr {
            0x5000 | key.len()
        } else {
            0x4000 | key.len()
        };
        self.header |= mask as u16;
    }
    //goat, might be easier to just inline this
    // /// Takes the ValOrChild<V> from slot_0.  WARNING! This method leaves the node in a corrupt state,
    // /// so it must be followed by something else to repair the node.
    // /// Also this method will corrput the node if there is a payload in slot_1
    // #[inline]
    // unsafe fn take_payload_0(&mut self) -> ValOrChild<V> {
    //     let mut payload = ValOrChild{ _unused: () };
    //     core::mem::swap(&mut payload, &mut self.val_or_child0);
    //     payload
    // }
    #[inline]
    unsafe fn set_child_0(&mut self, key: &[u8], child: TrieNodeODRc<V>) {
        self.set_payload_0(key, true, ValOrChild{ child: ManuallyDrop::new(child) });
    }
    #[inline]
    unsafe fn set_child_1(&mut self, key: &[u8], child: TrieNodeODRc<V>) {
        self.set_payload_1(key, true, ValOrChild{ child: ManuallyDrop::new(child) });
    }
    /// Splits the key in slot_0 at `idx` (exclusive.  ie. the length of the key)
    #[inline]
    fn split_0(&mut self, idx: usize) where V: Clone {
        let mut self_payload = ValOrChild{ _unused: () };
        core::mem::swap(&mut self_payload, &mut self.val_or_child0);
        let node_key_0 = unsafe{ self.key_unchecked_0() };

        let mut child_node = Self::new();
        unsafe{ child_node.set_payload_0(&node_key_0[idx..], self.is_child_ptr::<0>(), self_payload); }

        //Convert slot_0 from to a child ptr
        self.val_or_child0 = ValOrChild{ child: ManuallyDrop::new(TrieNodeODRc::new(child_node)) };

        //Shift the key for slot_1, if there is one
        let slot_mask_1 = if self.is_used_1() {
            let key_len_1 = self.key_len_1();
            unsafe {
                let src_ptr = self.key_bytes.get_unchecked(self.key_len_0()).as_ptr();
                let dst_ptr = self.key_bytes.get_unchecked_mut(idx).as_mut_ptr();
                core::ptr::copy(src_ptr, dst_ptr, key_len_1);
            }
            self.flags_and_len_1()
        } else {
            0
        };

        //Re-adjust the length and flags
        self.header = (0xa000 | (idx << 6) | slot_mask_1) as u16;
        if idx == KEY_BYTES_CNT {
            self.header |= 1 << 12; //Set the flag state so slot_1 is unavailable
        }
    }
    /// Splits the key in slot_0 at `idx` (exclusive.  ie. the length of the key)
    #[inline]
    fn split_1(&mut self, idx: usize) where V: Clone {
        let mut self_payload = ValOrChild{ _unused: () };
        core::mem::swap(&mut self_payload, &mut self.val_or_child1);
        let node_key_1 = unsafe{ self.key_unchecked_1() };

        let mut child_node = Self::new();
        unsafe{ child_node.set_payload_0(&node_key_1[idx..], self.is_child_ptr::<1>(), self_payload); }

        //Convert slot_0 from to a child ptr
        self.val_or_child1 = ValOrChild{ child: ManuallyDrop::new(TrieNodeODRc::new(child_node)) };

        //Re-adjust the length and flags
        let slot_mask_0 = self.flags_and_len_0();
        self.header = (slot_mask_0 | 0x5000 | idx) as u16;
    }
    #[inline]
    fn contains_val(&self, key: &[u8]) -> bool {
        if self.is_used_value_0() {
            let node_key_0 = unsafe{ self.key_unchecked_0() };
            if node_key_0 == key {
                return true;
            }
        }
        if self.is_used_value_1() {
            let node_key_1 = unsafe{ self.key_unchecked_1() };
            if node_key_1 == key {
                return true;
            }
        }
        false
    }
    #[inline]
    fn get_val(&self, key: &[u8]) -> Option<&V> {
        if self.is_used_value_0() {
            let node_key_0 = unsafe{ self.key_unchecked_0() };
            if node_key_0 == key {
                let val = unsafe{ self.val_in_slot::<0>() };
                return Some(val);
            }
        }
        if self.is_used_value_1() {
            let node_key_1 = unsafe{ self.key_unchecked_1() };
            if node_key_1 == key {
                let val = unsafe{ self.val_in_slot::<1>() };
                return Some(val);
            }
        }
        None
    }
    #[inline]
    fn get_val_mut(&mut self, key: &[u8]) -> Option<&mut V> {
        if self.is_used_value_0() {
            let node_key_0 = unsafe{ self.key_unchecked_0() };
            if node_key_0 == key {
                let val = unsafe{ self.val_in_slot_mut::<0>() };
                return Some(val);
            }
        }
        if self.is_used_value_1() {
            let node_key_1 = unsafe{ self.key_unchecked_1() };
            if node_key_1 == key {
                let val = unsafe{ self.val_in_slot_mut::<1>() };
                return Some(val);
            }
        }
        None
    }
    #[inline]
    fn get_child_mut(&mut self, key: &[u8]) -> Option<(usize, &mut TrieNodeODRc<V>)> {
        if self.is_used_child_0() {
            let node_key_0 = unsafe{ self.key_unchecked_0() };
            let key_len = self.key_len_0();
            if key.len() >= key_len {
                if node_key_0 == &key[..key_len] {
                    let child = unsafe{ self.child_in_slot_mut::<0>() };
                    return Some((key_len, child))
                }
            }
        }
        if self.is_used_child_1() {
            let node_key_1 = unsafe{ self.key_unchecked_1() };
            let key_len = self.key_len_1();
            if key.len() >= key_len {
                if node_key_1 == &key[..key_len] {
                    let child = unsafe{ self.child_in_slot_mut::<1>() };
                    return Some((key_len, child))
                }
            }
        }
        None
    }
    #[inline]
    fn get_both_keys(&self) -> (&[u8], &[u8]) {
        let mut key0: &[u8] = &[];
        let mut key1: &[u8] = &[];
        if self.is_used_0() {
            key0 = unsafe{ self.key_unchecked_0() };
        }
        if self.is_used_1() {
            key1 = unsafe{ self.key_unchecked_1() };
        }
        (key0, key1)
    }
    #[inline]
    fn count(&self) -> usize {
        match (self.is_used_0(), self.is_used_1()) {
            (true, false) => 1,
            (false, false) => 0,
            (true, true) => 2,
            (false, true) => unreachable!(),
        }
    }
}

/// Returns the number of characters shared between two slices
#[inline]
fn find_prefix_overlap(a: &[u8], b: &[u8]) -> usize {
    let mut cnt = 0;
    loop {
        if cnt == a.len() {break}
        if cnt == b.len() {break}
        if a[cnt] != b[cnt] {break}
        cnt += 1;
    }
    cnt
}

impl<V: Clone> TrieNode<V> for LineListNode<V> {
    fn node_get_child(&self, key: &[u8]) -> Option<(usize, &dyn TrieNode<V>)> {
        if self.is_used_child_0() {
            let node_key_0 = unsafe{ self.key_unchecked_0() };
            let key_len = self.key_len_0();
            if key.len() >= key_len {
                if node_key_0 == &key[..key_len] {
                    let child = unsafe{ self.child_in_slot::<0>().borrow() };
                    return Some((key_len, child))
                }
            }
        }
        if self.is_used_child_1() {
            let node_key_1 = unsafe{ self.key_unchecked_1() };
            let key_len = self.key_len_1();
            if key.len() >= key_len {
                if node_key_1 == &key[..key_len] {
                    let child = unsafe{ self.child_in_slot::<1>().borrow() };
                    return Some((key_len, child))
                }
            }
        }
        None
    }
    fn node_get_child_mut(&mut self, key: &[u8]) -> Option<(usize, &mut dyn TrieNode<V>)> {
        self.get_child_mut(key).map(|(consumed_bytes, child)| (consumed_bytes, child.make_mut()))
    }
    fn node_replace_child(&mut self, key: &[u8], new_node: TrieNodeODRc<V>) -> &mut dyn TrieNode<V> {
        let (consumed_bytes, child_node) = self.get_child_mut(key).unwrap();
        debug_assert!(consumed_bytes == key.len());
        *child_node = new_node;
        child_node.make_mut()
    }
    fn node_contains_val(&self, key: &[u8]) -> bool {
        self.contains_val(key)
    }
    fn node_get_val(&self, key: &[u8]) -> Option<&V> {
        self.get_val(key)
    }
    fn node_get_val_mut(&mut self, key: &[u8]) -> Option<&mut V> {
        self.get_val_mut(key)
    }
    fn node_set_val(&mut self, key: &[u8], mut val: V) -> Result<Option<V>, TrieNodeODRc<V>> {

        //If we already have a value at the key, then replace it
        if self.contains_val(key) {
            let node_val = self.get_val_mut(key).unwrap();
            core::mem::swap(&mut val, node_val);
            return Ok(Some(val));
        }

        //If this node is empty, insert the new key-value into slot_0
        if !self.is_used_0() {
            if key.len() <= KEY_BYTES_CNT {
                //The entire key fits within the node
                unsafe{ self.set_val_0(key, LocalOrHeap::new(val)); }
                return Ok(None)
            } else {
                //We need to recursively create a new node to hold the remaining part of the key
                let mut child_node = Self::new();
                child_node.node_set_val(&key[KEY_BYTES_CNT..], val).unwrap_or_else(|_| panic!()); //If a newly created node can't accept the value then it's a bug
                unsafe{ self.set_child_0(&key[..KEY_BYTES_CNT], TrieNodeODRc::new(child_node)); }
                return Ok(None)
            }
        }

        //If the key has overlap with slot_0, split the key, and add the value to the child
        let node_key_0 = unsafe{ self.key_unchecked_0() };
        let mut overlap = find_prefix_overlap(key, node_key_0);
        if overlap > 0 {
            if overlap == node_key_0.len() || overlap == key.len() {
                overlap -= 1;
            }
            if overlap > 0 {
                self.split_0(overlap);
                let child = unsafe{ self.child_in_slot_mut::<0>() }.make_mut();
                return child.node_set_val(&key[overlap..], val);
            }
        }

        //See if we are able to insert the node into slot_1
        if self.is_available_1() {
            let remaining_key_bytes = KEY_BYTES_CNT - self.key_len_0();
            if key.len() <= remaining_key_bytes {
                //The entire key fits within the node
                unsafe{ self.set_val_1(key, LocalOrHeap::new(val)); }
                return Ok(None)
            } else {
                //We need to recursively create a new node to hold the remaining part of the key
                let mut child_node = Self::new();
                child_node.node_set_val(&key[remaining_key_bytes..], val).unwrap_or_else(|_| panic!()); //If a newly created node can't accept the value then it's a bug
                unsafe{ self.set_child_1(&key[..remaining_key_bytes], TrieNodeODRc::new(child_node)); }
                return Ok(None)
            }
        }

        //If there is a single slot that is occupied but the key consumes the full node, then arbitrarily
        // chop the existing key in half to make room
        if !self.is_used_1() {
            self.split_0(KEY_BYTES_CNT / 2);

            //Try again to add the new value to self, now that we've cleared some space
            return self.node_set_val(key, val);
        }

        //If the key has overlap with slot_1, split that key
        let node_key_1 = unsafe{ self.key_unchecked_1() };
        let mut overlap = find_prefix_overlap(key, node_key_1);
        if overlap > 0 {
            if overlap == node_key_1.len() || overlap == key.len() {
                overlap -= 1;
            }
            if overlap > 0 {
                self.split_1(overlap);
                let child = unsafe{ self.child_in_slot_mut::<1>() }.make_mut();
                return child.node_set_val(&key[overlap..], val);
            }
        }

        //We couldn't store the value in either of the slots, so upgrade the node
        //=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
        let mut replacement_node = DenseByteNode::<V>::with_capacity(3);

        //1. Transplant the key / value from slot_1 to the new node
        let mut slot_0_payload = ValOrChild{ _unused: () };
        core::mem::swap(&mut slot_0_payload, &mut self.val_or_child0);
        let key_0 = unsafe{ self.key_unchecked_0() };
        //DenseByteNodes hold one byte keys, so if the key is more than 1 byte we need to
        // make an intermediate node to hold the rest of the key
        if key_0.len() > 1 {
            let mut child_node = Self::new();
            unsafe{ child_node.set_payload_0(&key_0[1..], self.is_child_ptr::<0>(), slot_0_payload); }
            replacement_node.add_child(key_0[0], TrieNodeODRc::new(child_node));
        } else {
            if self.is_child_ptr::<0>() {
                let child_node = unsafe{ ManuallyDrop::into_inner(slot_0_payload.child) };
                replacement_node.add_child(key_0[0], child_node);
            } else {
                let val_0 = unsafe{ ManuallyDrop::into_inner(slot_0_payload.val) };
                replacement_node.set_val(key_0[0], LocalOrHeap::into_inner(val_0));
            }
        }

        //2. Transplant the key / value from slot_1 to the new node
        let mut slot_1_payload = ValOrChild{ _unused: () };
        core::mem::swap(&mut slot_1_payload, &mut self.val_or_child1);
        let key_1 = unsafe{ self.key_unchecked_1() };
        if key_1.len() > 1 {
            let mut child_node = Self::new();
            unsafe{ child_node.set_payload_0(&key_1[1..], self.is_child_ptr::<1>(), slot_1_payload); }
            replacement_node.add_child(key_1[0], TrieNodeODRc::new(child_node));
        } else {
            if self.is_child_ptr::<1>() {
                let child_node = unsafe{ ManuallyDrop::into_inner(slot_1_payload.child) };
                replacement_node.add_child(key_1[0], child_node);
            } else {
                let val_1 = unsafe{ ManuallyDrop::into_inner(slot_1_payload.val) };
                replacement_node.set_val(key_1[0], LocalOrHeap::into_inner(val_1));
            }
        }

        //3. Add the new key-value pair to the new DenseByteNode
        if key.len() > 1 {
            let mut child_node = Self::new();
            child_node.node_set_val(&key[1..], val).unwrap_or_else(|_| panic!());
            replacement_node.add_child(key[0], TrieNodeODRc::new(child_node));
        } else {
            replacement_node.set_val(key[0], val);
        }

        //4. Clear self.header, so we don't double-free when this old node gets dropped
        self.header = 0;

        Err(TrieNodeODRc::new(replacement_node))
    }

    fn node_update_val(&mut self, key: &[u8], default_f: Box<dyn FnOnce()->V + '_>) -> Result<&mut V, TrieNodeODRc<V>> {
        panic!()
    }

    fn node_is_empty(&self) -> bool {
        !self.is_used_0()
    }

    fn boxed_node_iter<'a>(&'a self) -> Box<dyn Iterator<Item=(&'a[u8], ValOrChildRef<'a, V>)> + 'a> {
        Box::new(ListNodeIter::new(self))
    }

    fn node_subtree_len(&self) -> usize {
        panic!()
    }

    fn item_count(&self) -> usize {
        self.count()
    }

    fn nth_child(&self, n: usize, forward: bool) -> Option<(&[u8], &dyn TrieNode<V>)> {
        panic!()
    }

    fn get_sibling_of_child(&self, key: &[u8], next: bool) -> Option<(&[u8], &dyn TrieNode<V>)> {
        panic!()
    }

    fn join_dyn(&self, other: &dyn TrieNode<V>) -> TrieNodeODRc<V> where V: Lattice {
        if let Some(other_list_node) = other.as_list() {
            let (self_key0, self_key1) = self.get_both_keys();
            let (other_key0, other_key1) = other_list_node.get_both_keys();

            //Are there are any common paths between the nodes?
            let overlap_0_0 = find_prefix_overlap(self_key0, other_key0);
            if overlap_0_0 > 0 {
                //3 cases
                //1. a common prefix followed by two unique sub-strings, each with their own termination
                //2. One key is a subset of the other, in which case we need to back up to avoid zero-length keys
                //3. The keys are identical, in which case we need to join the child node or value

                //check case 3
                if overlap_0_0 == self_key0.len() && overlap_0_0 == other_key1.len() {

                    let onward = match (self.is_child_ptr::<0>(), other_list_node.is_child_ptr::<0>()) {
                        (true, true) => { //both are child nodes
                            let self_child = unsafe{ self.child_in_slot::<0>() };
                            let other_child = unsafe{ other_list_node.child_in_slot::<0>() };

                        },
                        (false, false) => { //both are values

                        },
                        (true, false) => { //one of each

                        },
                        (false, true) => {

                        }
                    };
                }

                //check case 1
                if overlap_0_0 < self_key0.len() && overlap_0_0 < other_key1.len() {

                }
            }

panic!()

            //Do we have two or fewer paths, that can be fit into a new ListNode? 

            //Otherwise, create a DenseByteNode
           // TrieNodeODRc::new(new_node)
        } else {
            //GOAT, need to iterate other, grow self, and merge each item in other into self
            panic!();
        }
    }

    fn join_into_dyn(&mut self, other: TrieNodeODRc<V>) where V: Lattice {
        panic!()
    }

    fn meet_dyn(&self, other: &dyn TrieNode<V>) -> TrieNodeODRc<V> where V: Lattice {
        panic!()
    }

    fn psubtract_dyn(&self, other: &dyn TrieNode<V>) -> Option<TrieNodeODRc<V>> where V: PartialDistributiveLattice {
        panic!();
    }

    fn as_dense(&self) -> Option<&DenseByteNode<V>> {
        None
    }
    fn as_dense_mut(&mut self) -> Option<&mut DenseByteNode<V>> {
        None
    }
    fn as_list(&self) -> Option<&Self> {
        Some(self)
    }
}

pub(crate) struct ListNodeIter<'a, V> {
    node: &'a LineListNode<V>,
    n: usize,
}

impl<'a, V> ListNodeIter<'a, V> {
    fn new(node: &'a LineListNode<V>) -> Self {
        Self {
            node,
            n: 0
        }
    }
}

impl<'a, V : Clone> Iterator for ListNodeIter<'a, V> {
    type Item = (&'a[u8], ValOrChildRef<'a, V>);

    fn next(&mut self) -> Option<(&'a[u8], ValOrChildRef<'a, V>)> {
        match self.n {
            0 => {
                self.n += 1;
                if self.node.is_used_0() {
                    let key = unsafe{ self.node.key_unchecked_0() };
                    if self.node.is_used_child_0() {
                        let child = unsafe{ self.node.child_in_slot::<0>() };
                        Some((key, ValOrChildRef::Child(child.borrow())))
                    } else {
                        let val = unsafe{ self.node.val_in_slot::<0>() };
                        Some((key, ValOrChildRef::Val(val)))
                    }
                } else {
                    None
                }
            },
            1 => {
                self.n += 1;
                if self.node.is_used_1() {
                    let key = unsafe{ self.node.key_unchecked_1() };
                    if self.node.is_used_child_1() {
                        let child = unsafe{ self.node.child_in_slot::<1>() };
                        Some((key, ValOrChildRef::Child(child.borrow())))
                    } else {
                        let val = unsafe{ self.node.val_in_slot::<1>() };
                        Some((key, ValOrChildRef::Val(val)))
                    }
                } else {
                    None
                }
            },
            _ => None
        }
    }
}

/// Common operations for a ListNode
#[test]
fn test_line_list_node() {
    // assert_eq!(core::mem::size_of::<LineListNode<[u8; 1024]>>(), 64);
    assert_eq!(core::mem::size_of::<LineListNode<[u8; 1024]>>(), 48); //Shrunk to account for DynBox header

    //A simple test with a V that fits inside 16 bytes, only testing slot_0
    let mut new_node = LineListNode::<usize>::new();
    assert_eq!(new_node.node_set_val("hello".as_bytes(), 42).map_err(|_| 0), Ok(None));
    assert_eq!(new_node.node_get_val("hello".as_bytes()), Some(&42));
    *new_node.node_get_val_mut("hello".as_bytes()).unwrap() = 123;
    assert_eq!(new_node.node_get_val("hello".as_bytes()), Some(&123));
    assert_eq!(new_node.node_set_val("hello".as_bytes(), 42).map_err(|_| 0), Ok(Some(123)));
    assert_eq!(new_node.node_contains_val("test".as_bytes()), false);

    //A simple test with a V that exceeds 16 bytes, only testing slot_0
    let mut new_node = LineListNode::<[u128; 4]>::new();
    assert_eq!(new_node.node_set_val("hello".as_bytes(), [0, 1, 2, 3]).map_err(|_| 0), Ok(None));
    assert_eq!(new_node.node_get_val("hello".as_bytes()), Some(&[0, 1, 2, 3]));
    *new_node.node_get_val_mut("hello".as_bytes()).unwrap() = [3, 2, 1, 0];
    assert_eq!(new_node.node_get_val("hello".as_bytes()), Some(&[3, 2, 1, 0]));
    assert_eq!(new_node.node_contains_val("test".as_bytes()), false);

    //A test using both slots for values, where the keys are different, but both fit inside the key space
    let mut new_node = LineListNode::<usize>::new();
    assert_eq!(new_node.node_set_val("hello".as_bytes(), 42).map_err(|_| 0), Ok(None));
    assert_eq!(new_node.node_set_val("goodbye".as_bytes(), 24).map_err(|_| 0), Ok(None));
    assert_eq!(new_node.node_get_val("hello".as_bytes()), Some(&42));
    assert_eq!(new_node.node_get_val("goodbye".as_bytes()), Some(&24));
}

#[test]
fn test_line_list_node_key_and_value_collision() {

    let mut new_node = LineListNode::<usize>::new();
    assert_eq!(new_node.node_set_val("a".as_bytes(), 42).map_err(|_| 0), Ok(None));
    assert_eq!(new_node.node_get_val("a".as_bytes()), Some(&42));

    let mut child_node = LineListNode::<usize>::new();
    assert_eq!(child_node.node_set_val("hello".as_bytes(), 24).map_err(|_| 0), Ok(None));
    //We are manufacturing this case.  Otherwise it would be a lot more indirect to achieve the
    // conditions for this test using the APIs available outside this module
    unsafe{ new_node.set_child_1("a".as_bytes(), TrieNodeODRc::new(child_node)); }

    assert_eq!(new_node.node_get_val("a".as_bytes()), Some(&42));
    let (bytes_used, child_node) = new_node.node_get_child("a".as_bytes()).unwrap();
    assert_eq!(bytes_used, 1);
    assert_eq!(child_node.node_get_val("hello".as_bytes()), Some(&24));
}

/// This tests that a common prefix will be found and the if the node only has an entry in slot_0
#[test]
fn test_line_list_node_shared_prefixes_empty() {

    let mut new_node = LineListNode::<usize>::new();
    assert_eq!(new_node.node_set_val("my name is".as_bytes(), 42).map_err(|_| 0), Ok(None));
    assert_eq!(new_node.node_set_val("my name is billy".as_bytes(), 24).map_err(|_| 0), Ok(None));
    let (bytes_used, child_node) = new_node.node_get_child("my name is".as_bytes()).unwrap();
    assert_eq!(bytes_used, 9);
    assert_eq!(child_node.node_get_val("s".as_bytes()), Some(&42));
    assert_eq!(child_node.node_get_val("s billy".as_bytes()), Some(&24));
}

/// This tests that a long key gets chopped up into multiple nodes
#[test]
fn test_line_list_node_overflow_keys() {

    //A test using both slots, where the second key exceeds the available space.  Make sure recursive nodes
    // are created
    const LONG_KEY: &[u8] = "Pack my box with five dozen liquor jugs".as_bytes();
    let mut new_node = LineListNode::<usize>::new();
    assert_eq!(new_node.node_set_val("hello".as_bytes(), 42).map_err(|_| 0), Ok(None));
    assert_eq!(new_node.node_set_val(LONG_KEY, 24).map_err(|_| 0), Ok(None));
    assert_eq!(new_node.node_get_val("hello".as_bytes()), Some(&42));

    let mut remaining_key = LONG_KEY;
    let mut child_node = &new_node as &dyn TrieNode<usize>;
    while let Some((bytes_used, next_node)) = child_node.node_get_child(remaining_key) {
        remaining_key = &remaining_key[bytes_used..];
        child_node = next_node;
    }
    assert_eq!(child_node.node_get_val(remaining_key), Some(&24));
}

/// This tests the logic to split a single key that consumes a whole node into multiple nodes
#[test]
fn test_line_list_overflow_split_in_place() {
    const LONG_KEY: &[u8] = "Pack my box with five dozen liquor jugs".as_bytes();

    //A test using only one slot, where the key exceeds the available space, make sure recursive nodes
    // are created
    let mut new_node = LineListNode::<usize>::new();
    assert_eq!(new_node.node_set_val(LONG_KEY, 24).map_err(|_| 0), Ok(None));
    let mut next_node = &new_node as &dyn TrieNode<usize>;
    let mut remaining_key = LONG_KEY;
    let mut levels = 0;
    while let Some((bytes_used, child_node)) = next_node.node_get_child(remaining_key) {
        next_node = child_node;
        remaining_key = &remaining_key[bytes_used..];
        levels += 1;
    }
    assert_eq!(next_node.node_get_val(remaining_key), Some(&24));
    assert_eq!(levels, (LONG_KEY.len()-1) / KEY_BYTES_CNT);

    //Now make sure that adding a second key is still ok because of in-place splitting
    assert_eq!(new_node.node_set_val("hello".as_bytes(), 42).map_err(|_| 0), Ok(None));
    assert_eq!(new_node.node_get_val("hello".as_bytes()), Some(&42));
}

/// This tests that a common prefix is found with the entry in slot_0, when slot_1 is already full
#[test]
fn test_line_list_node_shared_prefixes_slot_0() {

    let mut new_node = LineListNode::<usize>::new();
    assert_eq!(new_node.node_set_val("I'm billy".as_bytes(), 42).map_err(|_| 0), Ok(None));
    assert_eq!(new_node.node_set_val("slot1".as_bytes(), 123).map_err(|_| 0), Ok(None));
    assert_eq!(new_node.node_set_val("I'm johnny".as_bytes(), 24).map_err(|_| 0), Ok(None));
    let (bytes_used, child_node) = new_node.node_get_child("I'm billy".as_bytes()).unwrap();
    assert_eq!(bytes_used, 4);
    assert_eq!(child_node.node_get_val("billy".as_bytes()), Some(&42));
    assert_eq!(child_node.node_get_val("johnny".as_bytes()), Some(&24));
    assert_eq!(new_node.node_get_val("slot1".as_bytes()), Some(&123));
}

/// This test consumes slot_0, and tests that a common prefix is found when adding an entry to slot_1 
#[test]
fn test_line_list_node_shared_prefixes_slot_1() {

    let mut new_node = LineListNode::<usize>::new();
    assert_eq!(new_node.node_set_val("slot0".as_bytes(), 123).map_err(|_| 0), Ok(None));
    assert_eq!(new_node.node_set_val("I'm billy".as_bytes(), 42).map_err(|_| 0), Ok(None));
    assert_eq!(new_node.node_set_val("I'm johnny".as_bytes(), 24).map_err(|_| 0), Ok(None));
    let (bytes_used, child_node) = new_node.node_get_child("I'm billy".as_bytes()).unwrap();
    assert_eq!(bytes_used, 4);
    assert_eq!(child_node.node_get_val("billy".as_bytes()), Some(&42));
    assert_eq!(child_node.node_get_val("johnny".as_bytes()), Some(&24));
    assert_eq!(new_node.node_get_val("slot0".as_bytes()), Some(&123));
}

#[test]
fn test_line_list_node_replacement() {

    let mut new_node = LineListNode::<usize>::new();
    assert_eq!(new_node.node_set_val("apple".as_bytes(), 1).map_err(|_| 0), Ok(None));
    assert_eq!(new_node.node_set_val("banana".as_bytes(), 2).map_err(|_| 0), Ok(None));
    let replacement_node = new_node.node_set_val("carrot".as_bytes(), 3).unwrap_err();
    assert!(replacement_node.borrow().as_dense().is_some());
    let (bytes_used, child_node) = replacement_node.borrow().node_get_child("apple".as_bytes()).unwrap();
    assert_eq!(bytes_used, 1);
    assert_eq!(child_node.node_get_val("pple".as_bytes()), Some(&1));
    let (bytes_used, child_node) = replacement_node.borrow().node_get_child("banana".as_bytes()).unwrap();
    assert_eq!(bytes_used, 1);
    assert_eq!(child_node.node_get_val("anana".as_bytes()), Some(&2));
    let (bytes_used, child_node) = replacement_node.borrow().node_get_child("carrot".as_bytes()).unwrap();
    assert_eq!(bytes_used, 1);
    assert_eq!(child_node.node_get_val("arrot".as_bytes()), Some(&3));
}

//GOAT unneeded
// const FIFTY_DIGITS: &[u8] = "01234567890123456789012345678901234567890123456789".as_bytes();
