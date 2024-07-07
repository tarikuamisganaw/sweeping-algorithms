use std::fmt::Debug;
use crate::bytetrie::{BytesTrieMap, TrieNode};

// CZ2 uses a stack machine
// Store({a: 1}) // push

// CZ3 (incomplete) uses register machine

// Store({a: 1}, yym0)

// Content addressed abstract machine

// Store({a: 1}) // "you know what to do with this"

// ZAM (Warren Abstract Machine for triemaps)

// Store({a: 1}, [b, c])


enum Instruction {
    // == DESCEND ==
    Exact(u8),  // jumps to specific child
    Tail(u8),  // jumps to specific child and don't include

    Set([u64; 4]),  // jump to all children in mask
    Tails([u64; 4]),  // jump to all children in mask and don't include

    All(),  // jump to all
    Ignore(),  // jump to all and don't include

    Max(),  // Any
    Min(),  // Any

    // == ASCEND ==
    Head(u8),  // prefixes all with const

    // == SET OPS ==
    Union(),
    Intersection(),
    Subtraction(),

    // == CZ 2 OPS ==
    Restrict()
}

const EXPECTED_DEPTH: usize = 16;
const EXPECTED_PATH_LEN: usize = 64;

pub struct ReadZipper<'a, V> where V : Clone {
    pub(crate) _root: &'a BytesTrieMap<V>,
    pub(crate) focus: &'a dyn TrieNode<V>,
    pub(crate) prefix_buf: Vec<u8>,
    pub(crate) prefix_idx: Vec<usize>,
    pub(crate) ancestors: Vec<&'a dyn TrieNode<V>>,
}

impl <'a, V : Clone + Debug> ReadZipper<'a, V> {
    pub fn new(btm: &'a BytesTrieMap<V>) -> Self {
        Self {
            _root: btm,
            focus: btm.root.borrow(),
            prefix_buf: Vec::with_capacity(EXPECTED_PATH_LEN),
            prefix_idx: Vec::with_capacity(EXPECTED_DEPTH),
            ancestors: vec![],
        }
    }

    /// Moves the zipper deeper into the tree, in the direction of the specified key.  Returns `false` if
    /// there is no node to move towards
    pub fn child_towards<K: AsRef<[u8]>>(&mut self, k: K) -> bool {
        let k = k.as_ref();
        match self.focus.node_get_child(k) {
            None => { false }
            Some((consumed, child_node)) => {
                let key_start = *self.prefix_idx.last().unwrap_or(&0);
                self.prefix_buf.extend(&k[..consumed]);
                self.prefix_idx.push(key_start + consumed);
                self.ancestors.push(self.focus);
                self.focus = child_node;
                true
            }
        }
    }

    pub fn nth_child(&mut self, n: usize, forward: bool) -> bool {
        match self.focus.nth_child(n, forward) {
            Some((prefix, child_node)) => {
                let key_start = *self.prefix_idx.last().unwrap_or(&0);
                self.prefix_buf.extend(prefix);
                self.prefix_idx.push(key_start + prefix.len());
                self.ancestors.push(self.focus);
                self.focus = child_node;
                true
            },
            None => false
        }
    }

    // stays on the same level
    pub fn sibling(&mut self, next: bool) -> bool {
        match self.ancestors.last() {
            None => { false }
            Some(parent) => {
                let key_start = if self.prefix_idx.len() > 1 {
                    *self.prefix_idx.get(self.prefix_idx.len()-2).unwrap_or(&0)
                } else {
                    0
                };

                match parent.get_sibling_of_child(&self.prefix_buf[key_start..], next) {
                    Some((prefix_key, child_node)) => {
                        self.prefix_buf.truncate(key_start);
                        self.prefix_buf.extend(prefix_key);
                        self.focus = child_node;
                        true
                    },
                    None => false
                }
            }
        }
    }

    // moves up
    pub fn parent(&mut self) -> bool {
        match self.ancestors.pop() {
            None => { false }
            Some(parent) => {
                self.focus = parent;
                let key_start = self.prefix_idx.pop().unwrap_or(0);
                self.prefix_buf.truncate(key_start);
                true
            }
        }
    }

    /// Returns the count of the nodes from the root node.  Returns 0 at the root
    pub fn depth(&self) -> usize {
        self.prefix_idx.len()
    }

    /// Returns the path from the root to the focus node
    pub fn path(&self) -> &[u8] {
        &self.prefix_buf[..]
    }
}

//GOAT Thoughts / TODO on ReadZipper
//1. I should merge the Curson structure with the ReadZipper, by eliminating the cursor and adding a "next" method
//    that returns the next item in a depth-first traversal
//2. I need a "child_count" method to compliment the "nth_child" method.  But I need to look at what n means.
//    ie. is it the number of cofrees, or is it the number of actual children?
//3. √ Should make an accessor method to get the current path, since we have it easily available
//4. √ Should make an accessor method to get the current depth, since we have that in the form of self.prefix_idx.len()
//5. Should implement the TrieMap Iterator using the Zipper



// pub struct WriteZipper<'a, V> {
//     pub root: *mut BytesTrieMap<V>,
//     pub focus: *mut ByteTrieNode<CoFree<V>>,
//     pub path: Vec<u8>,
//     pub ancestors: Vec<*mut ByteTrieNode<CoFree<V>>>,
// }
//
// impl <'a, V : Clone + Debug> WriteZipper<'a, V> {
//     pub fn remove_children(m: [u64; 4]) {}
//
//     pub fn remove_child(k: u8) {}
//     pub fn remove_nth_child(n: u8) {}
//
//     pub fn remove_value(k: u8) {}
//     pub fn remove_nth_value(n: u8) {}
//
//     pub fn add_child(k: u8) {}
//     pub fn add_nth_child(n: u8) {}
//
//     pub fn add_value(k: u8) {}
//     pub fn add_nth_value(n: u8) {}
// }

trait Engine {
    // fn execute<V>(inp: &BytesTrieMap<V>, k: &[Instruction]) -> BytesTrieMap<V> {
    //     let mut out = BytesTrieMap::new();
    //     let mut inp_loc = &inp.root;
    //     let mut out_loc = &out.root;
    //
    //     match k[0] {
    //         Instruction::Exact(k) => {
    //             node.get()
    //         }
    //         Instruction::Set(_) => {}
    //         Instruction::Ignore() => {}
    //         Instruction::Any() => {}
    //     }
    //     if k.len() > 1 {
    //         for i in 0..k.len() - 1 {
    //             match node.get(k[i]) {
    //                 Some(cf) => {
    //                     match unsafe { cf.rec.as_ref() } {
    //                         Some(r) => { node = r }
    //                         None => { return None }
    //                     }
    //                 }
    //                 None => { return None }
    //             }
    //         }
    //     }
    //
    //     out
    // }
}