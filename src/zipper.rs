use std::fmt::Debug;
use std::ptr;
use crate::bit_sibling;
use crate::bytetrie::{BytesTrieMap, ByteTrieNode, CoFree};

enum Instruction {
    Exact(u8),
    Set([u64; 4]),
    Ignore(),
    Any()
}

pub struct ReadZipper<'a, V> {
    pub root: &'a BytesTrieMap<V>,
    pub focus: &'a ByteTrieNode<CoFree<V>>,
    pub path: Vec<u8>,
    pub ancestors: Vec<&'a ByteTrieNode<CoFree<V>>>,
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

    pub fn child(&mut self, k: u8) -> bool {
        match self.focus.get(k) {
            None => { false }
            Some(cf) => unsafe {
                match cf.rec.as_ref() {
                    None => { false }
                    Some(r) => {
                        self.path.push(k);
                        self.ancestors.push(self.focus);
                        self.focus = r;
                        true
                    }
                }
            }
        }
    }

    pub fn next_sibling(&mut self) -> bool {
        match self.ancestors.last() {
            None => { false }
            Some(parent) => {
                let k = self.path.last().unwrap(); // should be in-sync ancestors and non-empty
                let mut mask_i = ((k & 0b11000000) >> 6) as usize;
                let mut bit_i = k & 0b00111111;
                // println!("k {k}");

                loop {
                    // println!("loop");
                    let mut n = bit_sibling(bit_i, parent.mask[mask_i], false);
                    // println!("{} {bit_i} {mask_i}", n == bit_i);
                    if n == bit_i { // outside of word
                        loop {
                            mask_i += 1;
                            if !(0 <= mask_i && mask_i < 4) { return false }
                            if parent.mask[mask_i] == 0 { continue }
                            n = parent.mask[mask_i].trailing_zeros() as u8; break;
                        }
                    }
                    bit_i = n;
                    // println!("{} {bit_i} {mask_i}", n == bit_i);
                    // println!("{:?}", parent.items().map(|(k, _)| k).collect::<Vec<_>>());
                    let sk = n | ((mask_i << 6) as u8);
                    // println!("candidate {}", sk);
                    debug_assert!(parent.contains(sk));
                    match unsafe { parent.get_unchecked(sk).rec.as_ref() } {
                        None => {
                            // println!("{} {}", k, sk);
                            continue
                        }
                        Some(cs) => {
                            *self.path.last_mut().unwrap() = sk;
                            self.focus = cs;
                            return true
                        }
                    }
                }
            }
        }
    }

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