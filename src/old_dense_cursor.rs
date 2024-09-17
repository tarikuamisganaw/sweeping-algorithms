//!
//! Temporary file, porting old cursor to new trie.  ONLY WORKS WITH `all_dense_nodes` feature
//!

use crate::trie_map::BytesTrieMap;
use crate::dense_byte_node::{DenseByteNode, CoFree};

/// An iterator-like object that traverses key-value pairs in a [BytesTrieMap], however only one
/// returned reference may exist at a given time
pub struct OldCursor<'a, V> where V : Clone {
    prefix: Vec<u8>,
    btnis: Vec<ByteTrieNodeIter<'a, V>>,
    nopush: bool
}

impl <'a, V : Clone> OldCursor<'a, V> {
    pub fn new(btm: &'a BytesTrieMap<V>) -> Self {
        Self {
            prefix: vec![],
            btnis: vec![ByteTrieNodeIter::new(btm.root().borrow().as_dense().unwrap())],
            nopush: false
        }
    }
}

impl <'a, V : Clone> OldCursor<'a, V> {
    pub fn next(&mut self) -> Option<(&[u8], &'a V)> {
        loop {
            match self.btnis.last_mut() {
                None => { return None }
                Some(last) => {
                    match last.next() {
                        None => {
                            // decrease view len with one
                            self.prefix.pop();
                            self.btnis.pop();
                        }
                        Some((b, cf)) => {
                            if self.nopush {
                                *self.prefix.last_mut().unwrap() = b;
                                self.nopush = false;
                            } else {
                                self.prefix.push(b);
                            }

                            match &cf.rec {
                                None => {
                                    self.nopush = true;
                                }
                                Some(rec) => {
                                    self.nopush = false;
                                    self.btnis.push(ByteTrieNodeIter::new(rec.borrow().as_dense().unwrap()));
                                }
                            }

                            match &cf.value {
                                None => {}
                                Some(v) => {
                                    return Some((&self.prefix, v))
                                }
                            }
                        }
                    }
                }
            }
        }
    }
}

pub struct ByteTrieNodeIter<'a, V> {
    i: u8,
    w: u64,
    btn: &'a DenseByteNode<V>
}

impl <'a, V> ByteTrieNodeIter<'a, V> {
    fn new(btn: &'a DenseByteNode<V>) -> Self {
        Self {
            i: 0,
            w: btn.mask[0],
            btn: btn
        }
    }
}

impl <'a, V : Clone> Iterator for ByteTrieNodeIter<'a, V> {
    type Item = (u8, &'a CoFree<V>);

    fn next(&mut self) -> Option<(u8, &'a CoFree<V>)> {
        loop {
            if self.w != 0 {
                let wi = self.w.trailing_zeros() as u8;
                self.w ^= 1u64 << wi;
                let index = self.i*64 + wi;
                return Some((index, unsafe{ self.btn.get_unchecked(index) } ))
            } else if self.i < 3 {
                self.i += 1;
                self.w = unsafe { *self.btn.mask.get_unchecked(self.i as usize) };
            } else {
                return None
            }
        }
    }
}
