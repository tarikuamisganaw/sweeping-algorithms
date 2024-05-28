use std::fmt::Debug;
use std::ptr;
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

pub struct ReadZipper<'a, V> where V : Clone {
    pub root: &'a BytesTrieMap<V>,
    pub focus: &'a dyn TrieNode<V>,
    pub path: Vec<u8>,
    pub ancestors: Vec<&'a dyn TrieNode<V>>,
}

impl <'a, V : Clone + Debug> ReadZipper<'a, V> {
    pub fn new(btm: &'a BytesTrieMap<V>) -> Self {
        Self {
            root: btm,
            focus: &btm.root,
            path: vec![],
            ancestors: vec![],
        }
    }

    // moves deeper
    pub fn child(&mut self, k: u8) -> bool {
        match self.focus.node_get_child(&[k]) { //GOAT, this is going to fail as soon as we have keys that are variable length
            None => { false }
            Some((consumed, child_node)) => {
                self.path.push(k);
                self.ancestors.push(self.focus);
                self.focus = child_node.as_dense();
                true
            }
        }
    }

    pub fn nth_child(&mut self, n: usize, forward: bool) -> bool {
        match self.focus.nth_child(n, forward) {
            Some((prefix, child_node)) => {
                self.ancestors.push(self.focus);
                self.path.extend(prefix);
                self.focus = child_node.as_dense();
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
                let k = self.path.last().unwrap(); //GOAT, this is going to fail as soon as we have keys that are variable length

                match parent.get_sibling_of_child(&[*k], next) {
                    Some((prefix_key, child_node)) => {
                        *self.path.last_mut().unwrap() = prefix_key[0];
                        self.focus = child_node.as_dense();
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
                self.path.pop();
                true
            }
        }
    }
}


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