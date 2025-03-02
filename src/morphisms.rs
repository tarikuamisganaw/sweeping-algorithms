//! Functionality for applying various morphisms to [PathMap] and [Zipper](crate::zipper::Zipper)s
//!
//! Morphisms are a generalization of the [fold](std::iter::Iterator::fold) pattern, but for a trie or
//! sub-trie, as opposed to a list / sequence.  Similarly they rely on results being aggregated into
//! intermediate structures that are themselves joined together to produce a result.
//!
//! ### Supported Morphisms:
//!
//! #### Catamorphism
//!
//! Process a trie from the leaves towards the root.  This algorithm proceeds in a depth-first order.
//!
//! - A `map` closure is called on each leaf value; e.g. a value at location where there is no other value
//! deeper in the trie accessible from that location.  As the algoritm ascends.
//! - A `collapse` closure is called to merge a value along the path with the intermediate structure being
//! carried up the trie.
//! - An `alg` closure integrates intermediate structures from downstream branches into a single structure
//! for that location.
//!
//! The word "catamorphism" comes from the Greek for "down", because the root is considered the bottom
//! of the trie.  This is confusing because elsewhere we use the convention that `descend_` "deeper"
//! into the trie means moving further from the root while `ascend` moves closer to the root.  The docs
//! will stick to this convention in-spite of the Greek meaning.
//!
//! **NOTE**: The traversal order, while depth-first, is subtly different from the order of
//! [ZipperIteration::to_next_val](crate::zipper::ZipperIteration::to_next_val) and
//! [ZipperIteration::to_next_step](crate::zipper::ZipperIteration::to_next_step).  The
//! [ZipperIteration](crate::zipper::ZipperIteration) methods visit values first before descending to the
//! branches below, while the `cata` methods call the `mapper` on the deepest values first, before
//! returning to higher levels where `collapse` is called.
//!
//! #### Anamorphism
//!
//! Generate a trie from the root.  Conceptually it is the inverse of catamorphism.  This algorithm proceeds
//! from a starting point corresponding to a root of a trie, and generates branches and leaves recursively.
//!
//! ### Jumping Morphisms and the `jump` closure
//!
//! Ordinary morphism methods conceptually operate on a trie of bytes.  Therefore they execute the `alg`
//! closure for all non-leaf path positions, regardless of the existence of values.
//!
//! By contrast, `_jumping` methods conceptually operate on a trie of values.  That means the `alg` closure
//! is only called at "forking" path positions from which multiple downstream branches descend, and also for
//! the root.  There is an additional `jump` closure passed to these methods that can process an entire
//! substring from the path.
//!
//! In general, `jumping` methods will perform substantially better, so you should use them if your `alg`
//! closure simply passes the intermediate structure upwards when there is only one child branch.
//!
//! ### Side-Effecting vs Factored Iteration
//!
//! Many methods come (or will come) with a `_side_effect` and an ordinary or `factored` flavor.  The
//! algorithm is identical in both variants but the one to use depends on your situation.
//!
//! The `_side_effect` flavor of the methods will exhaustively traverse the entire trie, irrespective of
//! structural sharing within the trie.  So a subtrie that is included `n` times will be visited `n` times.
//! They take [`FnMut`] closure arguments, meaning the closures can produce side-effects, and making these
//! methods useful for things like serialization, etc.
//!
//! The ordinary `factored` flavor takes sharing into account, and thus will only visit each shared subtrie
//! once.  The methods take [`Fn`] closure arguments and they may cache and re-use intermediate results.
//! This means the intermediate result type must implement [`Clone`].
//!
//! In general, the ordinary methods should be preferred unless sife-effects are necessary, because many
//! operations produce structural sharing so the ordinary `factored` methods will likely be more efficient.
//!

use reusing_vec::ReusingQueue;

use crate::utils::*;
use crate::trie_map::BytesTrieMap;
use crate::trie_node::TrieNodeODRc;
use crate::zipper::*;

pub trait Catamorphism<V> {
    /// Applies a catamorphism to the trie descending from the zipper's root, running the `alg_f` at every
    /// step (at every byte)
    ///
    /// ## Args
    /// - `map_f`: `mapper(v: &V, path: &[u8]) -> W`
    /// Maps value `v` at a leaf `path` into an intermediate result
    ///
    /// - `collapse_f`: `collapse(v: &V, w: W, path: &[u8]) -> W`
    /// Folds value `v` at a non-leaf `path` with the aggregated results from the trie below `path`
    ///
    /// - `alg_f`: `alg(mask: [u64; 4], cs: &mut [W], path: &[u8]) -> W`
    /// Aggregates the results from the child branches, `cs`, descending from `path` into a single result
    ///
    /// The focus position of the zipper will be ignored and it will be immediately reset to the root.
    ///
    /// In all cases, the `path` arg is the [origin_path](ZipperAbsolutePath::origin_path)
    fn into_cata_side_effect<W, AlgF>(self, alg_f: AlgF) -> W
        where AlgF: FnMut(&ByteMask, &mut [W], Option<&V>, &[u8]) -> W;

    /// Applies a "jumping" catamorphism to the trie
    ///
    /// ## Args
    /// - `jump_f`: `FnMut(sub_path: &[u8], w: W, path: &[u8]) -> W`
    /// Elevates a result `w` descending from the relative path, `sub_path` to the current position at `path`
    ///
    /// See [into_cata_side_effect](Catamorphism::into_cata_side_effect) for explanation of other behavior
    fn into_cata_jumping_side_effect<W, AlgF>(self, alg_f: AlgF) -> W
        where AlgF: FnMut(&ByteMask, &mut [W], &[u8], Option<&V>, &[u8]) -> W;
}

pub struct SplitCata;

impl SplitCata {
    pub fn new<'a, V, W, MapF, CollapseF, AlgF>(mut map_f: MapF, mut collapse_f: CollapseF, mut alg_f: AlgF) -> impl FnMut(&ByteMask, &mut [W], Option<&V>, &[u8]) -> W + 'a
        where
        MapF: FnMut(&V, &[u8]) -> W + 'a,
        CollapseF: FnMut(&V, W, &[u8]) -> W + 'a,
        AlgF: FnMut(&ByteMask, &mut [W], &[u8]) -> W + 'a,
    {
        move |mask, children, val, path| -> W {
            // println!("STEPPING path=\"{path:?}\", mask={mask:?}, children_cnt={}, val={}", children.len(), val.is_some());
            if children.len() == 0 {
                return match val {
                    Some(val) => map_f(val, path),
                    None => {
                        // This degenerate case can only occur at the root
                        debug_assert_eq!(path.len(), 0);
                        alg_f(mask, children, path)
                    }
                }
            }
            let w = alg_f(mask, children, path);
            match val {
                Some(val) => collapse_f(val, w, path),
                None => w
            }
        }
    }
}

pub struct SplitCataJumping;

impl SplitCataJumping {
    pub fn new<'a, V, W, MapF, CollapseF, AlgF, JumpF>(mut map_f: MapF, mut collapse_f: CollapseF, mut alg_f: AlgF, mut jump_f: JumpF) -> impl FnMut(&ByteMask, &mut [W], &[u8], Option<&V>, &[u8]) -> W + 'a
        where
        //TODO GOAT!!: It would be nice to get rid of this Default bound on all morphism Ws.  In this case, the plan
        // for doing that would be to create a new type called a TakableSlice.  It would be able to deref
        // into a regular mutable slice of `T` so it would work just like an ordinary slice.  Additionally
        // there would be special `take(idx: usize)` methods. it would have an additional bitmask to keep
        // track of which elements have already been taken.  So each element would be backed by a MaybeUninit,
        // and taking an element twice would be a panic.  There would be an additional `try_take` method to
        // avoid the panic.
        //Additionally, if `T: Default`, the `take` method would become the ordinary mem::take, and would always
        // succeed, therefore the abstraction would have minimal cost
        //Creating a new TakableSlice would be very cheap as it could be transmuted from an existing slice of T.
        // The tricky part is making sure Drop does the right thing, dropping the elements that were taken, and
        // not double-dropping the ones that weren't.  For this reason, I think the right solution would be to
        // require a `TakableSlice` be borrowed from a `TakableVec`, and then making sure the `TakableVec`
        // methods like `clear` do the right thing.
        //When all this work is done, this object probably deserves a stand-alone crate.
        W: Default,
        MapF: FnMut(&V, &[u8]) -> W + 'a,
        CollapseF: FnMut(&V, W, &[u8]) -> W + 'a,
        AlgF: FnMut(&ByteMask, &mut [W], &[u8]) -> W + 'a,
        JumpF: FnMut(&[u8], W, &[u8]) -> W + 'a,
    {
        move |mask, children, stem, val, path| -> W {
            // println!("JUMPING  path=\"{path:?}\", mask={mask:?}, stem={stem:?}, children_cnt={}, val={}", children.len(), val.is_some());
            let w = if children.len() == 0 {
                match val {
                    Some(val) => map_f(val, path),
                    None => {
                        // This degenerate case can only occur at the root
                        debug_assert_eq!(path.len(), 0);
                        alg_f(mask, children, path)
                    }
                }
            } else {
                let w = if children.len() > 1 {
                    alg_f(mask, children, path)
                } else {
                    core::mem::take(&mut children[0])
                };
                match val {
                    Some(val) => collapse_f(val, w, path),
                    None => w
                }
            };
            debug_assert!(stem.len() <= path.len());
            let jump_dst_path = &path[..(path.len() - stem.len())];
            let w = if stem.len() > 0 && jump_dst_path.len() > 0 || stem.len() > 1 {
                jump_f(&stem[0..], w, jump_dst_path)
            } else {
                w
            };
            //If we jumped all the way to the root, run the alg one last time on the root to match the old behavior
            if jump_dst_path.len() == 0 && stem.len() > 0 {
                let mut temp_mask = ByteMask::EMPTY;
                temp_mask.set_bit(stem[0]);
                let mut temp_children = [w];
                alg_f(&temp_mask, &mut temp_children[..], &[])
            } else {
                w
            }
        }
    }
}

impl<'a, Z, V: 'a> Catamorphism<V> for Z where Z: Zipper<V> + ZipperReadOnly<'a, V> + ZipperAbsolutePath {
    fn into_cata_side_effect<W, AlgF>(self, mut alg_f: AlgF) -> W
        where AlgF: FnMut(&ByteMask, &mut [W], Option<&V>, &[u8]) -> W
    {
        cata_side_effect_body::<Self, V, W, _, false>(self, |mask, children, prefix_path, val, path| {
            debug_assert!(prefix_path.len() == 0);
            alg_f(mask, children, val, path)
        })
    }
    fn into_cata_jumping_side_effect<W, AlgF>(self, alg_f: AlgF) -> W
        where AlgF: FnMut(&ByteMask, &mut [W], &[u8], Option<&V>, &[u8]) -> W
    {
        cata_side_effect_body::<Self, V, W, AlgF, true>(self, alg_f)
    }
}

impl<V: 'static + Clone + Send + Sync + Unpin> Catamorphism<V> for BytesTrieMap<V> {
    fn into_cata_side_effect<W, AlgF>(self, mut alg_f: AlgF) -> W
        where AlgF: FnMut(&ByteMask, &mut [W], Option<&V>, &[u8]) -> W
    {
        let rz = self.into_read_zipper(&[]);
        cata_side_effect_body::<ReadZipperOwned<V>, V, W, _, false>(rz, |mask, children, prefix_path, val, path| {
            debug_assert!(prefix_path.len() == 0);
            alg_f(mask, children, val, path)
        })
    }
    fn into_cata_jumping_side_effect<W, AlgF>(self, alg_f: AlgF) -> W
        where AlgF: FnMut(&ByteMask, &mut [W], &[u8], Option<&V>, &[u8]) -> W
    {
        let rz = self.into_read_zipper(&[]);
        cata_side_effect_body::<ReadZipperOwned<V>, V, W, AlgF, true>(rz, alg_f)
    }
}

#[inline]
fn cata_side_effect_body<'a, Z, V: 'a, W, AlgF, const JUMPING: bool>(mut z: Z, mut alg_f: AlgF) -> W
    where
    Z: Zipper<V> + ZipperReadOnly<'a, V> + ZipperAbsolutePath,
    AlgF: FnMut(&ByteMask, &mut [W], &[u8], Option<&V>, &[u8]) -> W
{
    //`stack` holds a "frame" at each forking point above the zipper position.  No frames exist for values
    let mut stack = Vec::<StackFrame<W>>::with_capacity(12);
    let mut frame_idx = 0;

    z.reset();
    z.prepare_buffers();

    //Push a stack frame for the root, and start on the first branch off the root
    stack.push(StackFrame::new(z.child_count(), ByteMask::from(z.child_mask())));
    if !z.descend_first_byte() {
        //Empty trie is a special case
        return alg_f(&ByteMask::EMPTY, &mut [], &[], z.value(), z.origin_path().unwrap())
    }

    loop {
        //Descend to the next forking point, or leaf
        let mut is_leaf = false;
        while z.child_count() < 2 {
            if !z.descend_until() {
                is_leaf = true;
                break;
            }
        }

        if is_leaf {

            //Ascend back to the last fork point from this leaf
            let cur_w = ascend_to_fork::<Z, V, W, AlgF, JUMPING>(&mut z, &mut alg_f, None);
            stack[frame_idx].push_val(cur_w);

            //Keep ascending until we get to a branch that we haven't fully explored
            debug_assert!(stack[frame_idx].child_idx <= stack[frame_idx].child_cnt);
            while stack[frame_idx].child_idx == stack[frame_idx].child_cnt {

                if frame_idx == 0 {
                    //See if we need to run the aggregate function on the root before returning
                    let stack_frame = &mut stack[0];
                    let val = z.value();
                    let w = if stack_frame.child_cnt > 1 || val.is_some() || !JUMPING {
                        alg_f(&stack_frame.child_mask, &mut stack_frame.children, &[], val, z.origin_path().unwrap())
                    } else {
                        debug_assert_eq!(stack_frame.children.len(), 1);
                        stack_frame.children.pop().unwrap()
                    };
                    return w
                } else {

                    //Ascend the rest of the way back up to the branch
                    let cur_w = ascend_to_fork::<Z, V, W, AlgF, JUMPING>(&mut z, &mut alg_f, Some(&mut stack[frame_idx]));

                    frame_idx -= 1;

                    //Merge the result into the stack frame
                    stack[frame_idx].push_val(cur_w);
                }
            }

            //Position to descend the next child branch
            let descended = z.descend_indexed_branch(stack[frame_idx].child_idx);
            debug_assert!(descended);
        } else {
            //Push a new stack frame for this branch
            frame_idx += 1;
            let child_mask = ByteMask::from(z.child_mask());
            let child_cnt = z.child_count();
            if stack.len() <= frame_idx {
                stack.push(StackFrame::new(child_cnt, child_mask));
                debug_assert!(stack.len() > frame_idx);
            } else {
                stack[frame_idx].reset(child_cnt, child_mask);
            }

            //Descend the first child branch
            z.descend_first_byte();
        }
    }
}

#[inline(always)]
fn ascend_to_fork<'a, Z, V: 'a, W, AlgF, const JUMPING: bool>(z: &mut Z, 
        alg_f: &mut AlgF, mut prior_frame: Option<&mut StackFrame<W>>
) -> W
    where
    Z: Zipper<V> + ZipperReadOnly<'a, V> + ZipperAbsolutePath,
    AlgF: FnMut(&ByteMask, &mut [W], &[u8], Option<&V>, &[u8]) -> W,
{
    let mut w;
    let mut mask;
    let mut w_array: [W; 1];
    let (mut child_mask, mut children) = match &mut prior_frame {
        Some(prior_frame) => {
            (&prior_frame.child_mask, &mut prior_frame.children[..])
        },
        None => {
            (&ByteMask::EMPTY, &mut [][..])
        }
    };

    if JUMPING {
        //This loop runs until we got to a fork or the root.  We will take a spin through the loop
        // for each value we encounter along the way while ascending
        loop {
            let old_path_len = z.origin_path().unwrap().len();
            let old_val = z.get_value();
            let ascended = z.ascend_until();
            debug_assert!(ascended);

            //GOAT QUESTION: I'm on the fence about whether it makes more sense to include the stem in the
            // path.  I'm leaning to "yes" because having the contiguous buffer is more useful than not having
            // it because you can cheaply slice the buffer, but you can't re-compose it without needing to do a
            // copy.  It may make more conceptual sense to do "no" behavior like the old `jump_f`.

            let origin_path = unsafe{ z.origin_path_assert_len(old_path_len) };
            let stem_path = if z.child_count() != 1 || z.is_value() {
                &origin_path[z.origin_path().unwrap().len()+1..]
            } else {
                &origin_path[z.origin_path().unwrap().len()..]
            };

            w = alg_f(child_mask, children, stem_path, old_val, origin_path);

            if z.child_count() != 1 || z.at_root() {
                return w
            }

            w_array = [w];
            children = &mut w_array[..];

            //SAFETY: We know we won't over-read the buffer because we can only get here if we just ascended
            let byte = *unsafe{ z.origin_path_assert_len(origin_path.len()+1) }.last().unwrap();
            mask = ByteMask::EMPTY;
            mask.set_bit(byte);
            child_mask = &mask;
        }
    } else {
        //This loop runs at each byte step as we ascend
        loop {
            let origin_path = z.origin_path().unwrap();
            let byte = *origin_path.last().unwrap_or(&0);
            let val = z.value();
            w = alg_f(child_mask, children, &[], val, origin_path);

            let ascended = z.ascend_byte();
            debug_assert!(ascended);

            if z.child_count() != 1 || z.at_root() {
                return w
            }

            w_array = [w];
            children = &mut w_array[..];

            mask = ByteMask::EMPTY;
            mask.set_bit(byte);
            child_mask = &mask;
        }
    }
}

/// Internal structure to hold temporary info used inside morphism apply methods
struct StackFrame<W> {
    child_mask: ByteMask,
    mask_word_idx: usize,
    child_idx: usize,
    child_cnt: usize, //Could be derived from child_mask, but it's cheaper to store it
    remaining_children_mask: u64,
    children: Vec<W>,
}

impl<W> StackFrame<W> {
    /// Allocates a new StackFrame
    fn new(child_cnt: usize, child_mask: ByteMask) -> Self {
        debug_assert_eq!(child_cnt, child_mask.count_bits());
        let mut frame = Self {
            child_mask: <_>::default(),
            child_idx: 0,
            child_cnt,
            mask_word_idx: 0,
            remaining_children_mask: 0,
            children: Vec::with_capacity(child_cnt)
        };
        frame.reset(child_cnt, child_mask);
        frame
    }
    /// Resets a StackFrame to the state needed to iterate a new forking point
    fn reset(&mut self, child_cnt: usize, child_mask: ByteMask) {
        self.mask_word_idx = 0;
        self.child_idx = 0;
        while child_mask.0[self.mask_word_idx] == 0 && self.mask_word_idx < 3 {
            self.mask_word_idx += 1;
        }
        self.remaining_children_mask = child_mask.0[self.mask_word_idx];
        self.child_mask = child_mask;
        self.child_cnt = child_cnt;
        self.children.clear();
    }
    fn push_val(&mut self, w: W) {
        self.children.push(w);
        self.child_idx += 1;
        debug_assert!(self.remaining_children_mask > 0); //If this assert trips, then it means we're trying to push a value for a non-existent child
        let index = self.remaining_children_mask.trailing_zeros();
        self.remaining_children_mask ^= 1u64 << index;
        self.advance_word_idx();
    }
    //GOAT, unused for the time being.
    // fn push_none(&mut self) {
    //     self.child_idx += 1;
    //     debug_assert!(self.remaining_children_mask > 0); //If this assert trips, then it means we're trying to push a value for a non-existent child
    //     let index = self.remaining_children_mask.trailing_zeros();
    //     self.remaining_children_mask ^= 1u64 << index;
    //     self.child_mask.0[self.mask_word_idx] ^= 1u64 << index;
    //     self.advance_word_idx();
    // }
    fn advance_word_idx(&mut self) {
        if self.remaining_children_mask == 0 {
            if self.mask_word_idx < 3 {
                self.mask_word_idx += 1;
                while self.child_mask.0[self.mask_word_idx] == 0 && self.mask_word_idx < 3 {
                    self.mask_word_idx += 1;
                }
                self.remaining_children_mask = self.child_mask.0[self.mask_word_idx];
            }
        }
    }
}

/// Internal function to generate a new root trie node from an anamorphism
pub(crate) fn new_map_from_ana<V, W, AlgF>(w: W, mut alg_f: AlgF) -> BytesTrieMap<V>
    where
    V: 'static + Clone + Send + Sync + Unpin,
    W: Default,
    AlgF: FnMut(W, &mut Option<V>, &mut TrieBuilder<V, W>, &[u8])
{
    let mut stack = Vec::<(TrieBuilder<V, W>, usize)>::with_capacity(12);
    let mut frame_idx = 0;

    let mut new_map = BytesTrieMap::new();
    let mut z = new_map.write_zipper();
    let mut val = None;

    //The root is a special case
    stack.push((TrieBuilder::<V, W>::new(), 0));
    alg_f(w, &mut val, &mut stack[frame_idx].0, z.path());
    stack[frame_idx].0.finalize();
    if let Some(val) = core::mem::take(&mut val) {
        z.set_value(val);
    }
    loop {
        //Should we descend?
        if let Some(w_or_node) = stack[frame_idx].0.take_next() {
            //TODO Optimization Opportunity: There is likely a 2x speedup in here, that can be achieved by
            // setting all the children at the same time.  The reason is that the current behavior will create
            // a smaller node (ListNode), and then upgrade it if necessary.  But if we know in advance what
            // the node needs to hold, we could allocate the correct node right off the bat.
            //
            // I'm going to hold off on implementing this until the explicit path API is fully settled,
            // since ideally we'd call a WriteZipper method to set multiple downstream paths, but we'd want
            // some assurances those paths would actually be created, and not pruned because they're empty.
            //
            //I'm thinking this needs to take the form of a TrieNode trait method that looks something like:
            // `fn set_children_and_values(child_mask, val_mask, branches: &[??], vals: &[V])` or possibly
            // a node creation method.  Since this is designed to be used by anamorphism (trie construction)
            // perhaps we don't actually need the downstream nodes at all, and can fill them in later.
            //
            //BEWARE: This change needs to be accompanied by another change to allow an existing node's path
            // to be augmented, or the above change could be a performance step backwards.  Specifically,
            // consider a ListNode that is created with only one child, based on a mask.  Then, if the zipper
            // descends and tries to create the rest of a path, it would be a disaster if that took the form
            // of another node, as opposed to just putting the rest of the path into the existing node.

            let child_path_byte = stack[frame_idx].0.taken_child_byte();
            z.descend_to_byte(child_path_byte);
            let mut child_path_len = 1;

            if let Some(child_path_remains) = stack[frame_idx].0.taken_child_remaining_path(child_path_byte) {
                z.descend_to(child_path_remains);
                child_path_len += child_path_remains.len();
            }

            match w_or_node {
                // Recursive path with more Ws
                WOrNode::W(w) => {
                    debug_assert!(frame_idx < stack.len());
                    frame_idx += 1;
                    if frame_idx == stack.len() {
                        stack.push((TrieBuilder::<V, W>::new(), child_path_len));
                    } else {
                        stack[frame_idx].0.reset();
                        stack[frame_idx].1 = child_path_len;
                    }

                    //Run the alg if we just descended
                    alg_f(w, &mut val, &mut stack[frame_idx].0, z.path());
                    stack[frame_idx].0.finalize();
                    if let Some(val) = core::mem::take(&mut val) {
                        z.set_value(val);
                    }
                },
                // Path from a graft, we shouldn't descend
                WOrNode::Node(node) => {
                    z.core().graft_internal(Some(node));
                    z.ascend(child_path_len);
                }
            }
        } else {
            //If not, we should ascend
            if frame_idx == 0 {
                break
            }
            z.ascend(stack[frame_idx].1);
            stack[frame_idx].0.reset();
            frame_idx -= 1;
        }
    }
    drop(z);
    new_map
}

/// A [Vec]-like struct for assembling all the downstream branches from a path in the trie
//GOAT, Ideally I would skip the `val` argument to the anamorphism closure, and add a `set_val` method
// to TrieBuilder.  I'm a little on the fence about it, however, because it increases the size of the
// TrieBuilder by an `Option<V>`, which is stored for every stack frame, as opposed to just the one place
// it's needed.  However, this change opens up the possibility to embed the WriteZipper into the TrieBuilder,
// which can make some operations a bit more efficient.
//
//GOAT, If we exposed an interface that allowed values to be set in bulk, (e.g. with a mask), we could
// plumb it straight through to a node interface
pub struct TrieBuilder<V, W> {
    child_mask: [u64; 4],
    cur_mask_word: usize,
    child_paths: ReusingQueue<Vec<u8>>,
    child_structs: ReusingQueue<WOrNode<V, W>>,
}

/// Internal structure 
enum WOrNode<V, W> {
    W(W),
    Node(TrieNodeODRc<V>)
}

impl<V, W: Default> Default for WOrNode<V, W> {
    fn default() -> Self {
        //GOAT, the default impl here is mainly to facilitate core::mem::take, therefore, the default
        // should be the cheapest thing to create.  At some point that will be a TrieNodeODRc pointing
        // at a static empty node, but that's currently not implemented yet.
        // Alternatively we could use a MaybeUninit.
        Self::W(W::default())
    }
}

impl<V: Clone + Send + Sync, W: Default> TrieBuilder<V, W> {
    /// Internal method to make a new empty `TrieBuilder`
    fn new() -> Self {
        Self {
            child_mask: [0u64; 4],
            cur_mask_word: 0,
            child_paths: ReusingQueue::new(),
            child_structs: ReusingQueue::new() }
    }
    /// Internal method.  Clears a builder without freeing its memory
    fn reset(&mut self) {
        self.child_mask = [0u64; 4];
        self.cur_mask_word = 0;
        self.child_structs.clear();
        self.child_paths.clear();
    }
    /// Internal method.  Called after the user code has run to fill the builder, but before we start to empty it
    fn finalize(&mut self) {
        self.cur_mask_word = 0;
        while self.cur_mask_word < 4 && self.child_mask[self.cur_mask_word] == 0 {
            self.cur_mask_word += 1;
        }
    }
    /// Internal method to get the next child from the builder in the push order.  Used by the anamorphism
    fn take_next(&mut self) -> Option<WOrNode<V, W>> {
        self.child_structs.pop_front().map(|element| core::mem::take(element))
    }
    /// Internal method.  After [Self::take_next] returns `Some`, this method will return the first byte of the
    /// associated path.
    fn taken_child_byte(&mut self) -> u8 {
        let least_component = self.child_mask[self.cur_mask_word].trailing_zeros() as u8;
        debug_assert!(least_component < 64);
        let byte = (self.cur_mask_word * 64) as u8 + least_component;
        self.child_mask[self.cur_mask_word] ^= 1u64 << least_component;
        while self.cur_mask_word < 4 && self.child_mask[self.cur_mask_word] == 0 {
            self.cur_mask_word += 1;
        }
        byte
    }
    /// Internal method.  After [Self::take_next] returns `Some`, this method will return the associated path
    /// beyond the first byte, or `None` if the path is only 1-byte long
    fn taken_child_remaining_path(&mut self, byte: u8) -> Option<&[u8]> {
        if self.child_paths.get(0).map(|path| path[0]) != Some(byte) {
            None
        } else {
            self.child_paths.pop_front().map(|v| &v.as_slice()[1..])
        }
    }
    /// Returns the number of children that have been pushed to the `TrieBuilder`, so far
    pub fn len(&self) -> usize {
        self.child_structs.len()
    }
    /// Simultaneously sets all child branches with single-byte path continuations
    ///
    /// Panics if existing children have already been set / pushed, or if the number of bits set in `mask`
    /// doesn't match `children.len()`.
    pub fn set_child_mask<C: AsMut<[W]>>(&mut self, mask: [u64; 4], mut children: C) {
        if self.child_structs.len() != 0 {
            panic!("set_mask called over existing children")
        }
        let children = children.as_mut();
        debug_assert_eq!(mask.iter().fold(0, |sum, word| sum + word.count_ones() as usize), children.len());
        if children.len() == 0 {
            return
        }
        self.child_structs.clear();
        for child in children {
            self.child_structs.push_val(WOrNode::W(core::mem::take(child)));
        }
        debug_assert_eq!(self.cur_mask_word, 0);
        while mask[self.cur_mask_word] == 0 {
            self.cur_mask_word += 1;
        }
        self.child_mask = mask;
    }
    /// Pushes a new child branch into the `TrieBuilder` with the specified `byte`
    ///
    /// Panics if `byte <=` the first byte of any previosuly pushed paths.
    pub fn push_byte(&mut self, byte: u8, w: W) {
        let mask_word = (byte / 64) as usize;
        if mask_word < self.cur_mask_word {
            panic!("children must be pushed in sorted order")
        }
        self.cur_mask_word = mask_word;
        let mask_delta = 1u64 << (byte % 64);
        if self.child_mask[mask_word] >= mask_delta {
            panic!("children must be pushed in sorted order and each initial byte must be unique")
        }
        self.child_mask[mask_word] |= mask_delta;

        //Push the `W`
        self.child_structs.push_val(WOrNode::W(w));
    }
    /// Pushes a new child branch into the `TrieBuilder` with the specified `sub_path`
    ///
    /// Panics if `sub_path` fails to meet any of the following conditions:
    /// - `sub_path.len() > 0`.
    /// - `sub_path` must not begin with the same byte as any previously-pushed path.
    /// - `sub_path` must alphabetically sort after all previously pushed paths.
    ///
    /// For example, pushing `b"horse"` and then `b"hour"` is wrong.  Instead you should push `b"ho"`, and
    /// push the remaining parts of the path from the triggered closures downstream.
    //
    //TODO, could make a `push_unchecked` method to turn these these checks from `assert!` to `debug_assert`.
    // Not sure if it would make any difference.  Feels unlikely, but might be worth a try after we've implemented
    // the other speedup ideas
    pub fn push(&mut self, sub_path: &[u8], w: W) {
        assert!(sub_path.len() > 0);

        //Push the remaining path
        if sub_path.len() > 1 {
            let child_path = self.child_paths.push_mut();
            child_path.clear();
            child_path.extend(sub_path);
        }

        self.push_byte(sub_path[0], w);
    }
    /// Behaves like [push](Self::push), but will tolerate inputs in any order, and inputs and with
    /// overlapping initial bytes
    ///
    /// DISCUSSION: This method is handy when you are generating paths composed of data types that can't be
    /// cleanly separated at byte boundaries; for example UTF-8 encoded `char`s.  This method saves you the
    /// extra work of handling the case where different structures encode with the same initial byte, and of
    /// concerning yourself with partial encoding generally.
    ///
    /// This method is much higher overhead than the ordinary `push` method, and also it introduces
    /// some ambiguity in the order in which the closure is run for the children.  Specifically it means that
    /// the same path location in the trie may be visited multiple times, and you cannot rely on closure
    /// execution proceeding in a strictly depth-first order.  Furthermore, the closure order may not match
    /// the traversal order of the completed trie.
    ///
    /// NOTE: Because a given location may be visited multiple times, values set by later-running closures
    /// will overwrite a value set by an earlier closure running at the same path.
    ///
    /// NOTE: If you push twice to an identical path within the same closure execution, the second push will
    /// overwrite the first.
    ///
    /// NOTE: use of this method will preclude any automatic multi-threading of the anamorphism on downstream
    /// paths.
    pub fn tolerant_push(&mut self, sub_path: &[u8], w: W) {
        let byte = match sub_path.get(0) {
            Some(byte) => byte,
            None => return
        };

        //Find the index in the `child_structs` vec based on the initial byte
        let mask_word = (byte / 64) as usize;
        let byte_remainder = byte % 64;
        let mut byte_index = 0;
        for i in 0..mask_word {
            byte_index += self.child_mask[i].count_ones();
        }
        if byte_remainder > 0 {
            byte_index += (self.child_mask[mask_word] & 0xFFFFFFFFFFFFFFFF >> (64-byte_remainder)).count_ones();
        }

        let mask_delta = 1u64 << (byte % 64);
        let collision = self.child_mask[mask_word] & mask_delta > 0;
        self.child_mask[mask_word] |= mask_delta;

//GOAT, my thinking on the data structure changes
//For the paths, we should go back to storing the whole path, and use the first byte for association.  No need
// to keep the index association
//For the W array, we ought to just push the Ws in, in the order we want.  Since we always iterate the W vec
//If we want to support direct-push of values, we ought to have a separate value mask
//There should be two value vecs.  One for direct values of the current node, and one for values associated
// with downstream children / paths.  (we could even piggy-back the downstream value on the path)

//GOAT, THE W vec should have the string pairs hanging off each element.  So the W vec is `Vec<(W, Vec<(Vec<u8>, W)>)>`
//GOAT, Actually the W needs to be an Option<W>, and at that point, we may as well split the 

//GOAT options:
// 1. Make one vec that holds length-1 children, and another that holds lenth > 1,
//     

//GOAT!!! Vec<(Option<W>, Vec<(Vec<u8>, W)>)>
//GOAT!!! ReusingQueue<SmallVec<(Vec<u8>, W)>>

        //GOAT, we need to reset self.cur_mask_word, scanning the whole child_mask, because any child byte may have been added
        // self.cur_mask_word = mask_word;
    }
    /// Returns the child mask from the `TrieBuilder`, representing paths that have been pushed so far
    pub fn child_mask(&self) -> [u64; 4] {
        self.child_mask
    }
    /// Grafts the subtrie below the focus of the `read_zipper` at the specified `byte`
    ///
    /// WARNING: This method is incompatible with [Self::set_child_mask] and must follow the same
    /// rules as [Self::push_byte]
    pub fn graft_at_byte<Z: Zipper<V>>(&mut self, byte: u8, read_zipper: &Z) {
        let mask_word = (byte / 64) as usize;
        if mask_word < self.cur_mask_word {
            panic!("children must be pushed in sorted order")
        }
        self.cur_mask_word = mask_word;
        let mask_delta = 1u64 << (byte % 64);
        if self.child_mask[mask_word] >= mask_delta {
            panic!("children must be pushed in sorted order and each initial byte must be unique")
        }
        self.child_mask[mask_word] |= mask_delta;

        //Clone the read_zipper's focus and push it
        let node = read_zipper.get_focus().into_option();
        self.child_structs.push_val(WOrNode::Node(node.unwrap())); //GOAT!! Currently we panic if the read_zipper is at an nonexistent path
    }
    //GOAT, feature removed.  See below
    // /// Returns an [`Iterator`] type to iterate over the `(sub_path, w)` pairs that have been pushed
    // pub fn iter(&self) -> TrieBuilderIter<'_, W> {
    //     self.into_iter()
    // }
}

//GOAT, the IntoIterator impl is obnoxious because I don't have a contiguous buffer that holds the path anymore
// It's unnecessary anyway, so I'm just going to chuck it
//
// impl<'a, W> IntoIterator for &'a TrieBuilder<W> {
//     type Item = (&'a[u8], &'a W);
//     type IntoIter = TrieBuilderIter<'a, W>;

//     fn into_iter(self) -> Self::IntoIter {
//         TrieBuilderIter {
//             cb: self,
//             cur_mask: self.child_mask[0],
//             mask_word: 0,
//             i: 0
//         }
//     }
// }

// /// An [`Iterator`] type for a [`TrieBuilder`]
// pub struct TrieBuilderIter<'a, W> {
//     cb: &'a TrieBuilder<W>,
//     cur_mask: u64,
//     mask_word: usize,
//     i: usize,
// }

// impl<'a, W> Iterator for TrieBuilderIter<'a, W> {
//     type Item = (&'a[u8], &'a W);
//     fn next(&mut self) -> Option<Self::Item> {
//         while self.mask_word < 4 {
//             let tz = self.cur_mask.trailing_zeros();
//             if tz < 64 {

//                 self.i += 1;
//             } else {
//                 self.mask_word += 1;
//             }
//         }
//         None
//     }
// }

#[cfg(test)]
mod tests {
    use std::ops::Range;
    use crate::trie_map::BytesTrieMap;
    use crate::utils::BitMask;
    use super::*;

    #[test]
    fn cata_test1() {
        let tests = [
            (vec![], 0), //Empty special case
            (vec!["1"], 1), //A branch at the root
            (vec!["1", "2"], 3),
            (vec!["1", "2", "3", "4", "5", "6"], 21),
            (vec!["a1", "a2"], 3), //A branch above the root
            (vec!["a1", "a2", "a3", "a4", "a5", "a6"], 21),
            (vec!["12345"], 5), //A deep leaf
            (vec!["1", "12", "123", "1234", "12345"], 15), //Values along the path
            (vec!["123", "123456", "123789"], 18), //A branch that also has a value
            (vec!["12", "123", "123456", "123789"], 20),
            (vec!["1", "2", "123", "123765", "1234", "12345", "12349"], 29) //A challenging mix of everything
        ];
        for (keys, expected_sum) in tests {
            let map: BytesTrieMap<()> = keys.into_iter().map(|v| (v, ())).collect();
            let zip = map.read_zipper();

            let alg = |_child_mask: &ByteMask, children: &mut [u32], val: Option<&()>, path: &[u8]| {
                let this_digit = if val.is_some() {
                    (*path.last().unwrap() as char).to_digit(10).unwrap()
                } else {
                    0
                };
                let sum_of_branches = children.into_iter().fold(0, |sum, child| sum + *child);
                sum_of_branches + this_digit
            };

            //Test both the jumping and non-jumping versions, since they ought to do the same thing
            let sum = zip.clone().into_cata_side_effect(|child_mask: &ByteMask, children: &mut [u32], val: Option<&()>, path: &[u8]| {
                // println!("STEPPING path=\"{}\", mask={child_mask:?}, children={children:?}, val={}", String::from_utf8_lossy(path), val.is_some(), );
                alg(child_mask, children, val, path)
            });
            assert_eq!(sum, expected_sum);

            let sum = zip.into_cata_jumping_side_effect(|child_mask: &ByteMask, children: &mut [u32], _stem: &[u8], val: Option<&()>, path: &[u8]| {
                // println!("JUMPING  path=\"{}\", mask={child_mask:?}, children={children:?}, stem={}, val={}", String::from_utf8_lossy(path), String::from_utf8_lossy(_stem), val.is_some(), );
                alg(child_mask, children, val, path)
            });
            assert_eq!(sum, expected_sum);
        }
    }

    #[test]
    fn cata_test2() {
        let mut btm = BytesTrieMap::new();
        let rs = ["arrow", "bow", "cannon", "roman", "romane", "romanus", "romulus", "rubens", "ruber", "rubicon", "rubicundus", "rom'i"];
        rs.iter().enumerate().for_each(|(i, r)| { btm.insert(r.as_bytes(), i); });

        //These algorithms should perform the same with both "jumping" and "non-jumping" versions

        // like val count, but without counting internal values
        fn leaf_cnt(children: &[usize], val: Option<&usize>) -> usize {
            if children.len() > 0 {
                children.iter().sum() //Internal node
            } else {
                assert!(val.is_some()); //Cata doesn't include dangling paths, but it might in the future
                1 //leaf node
            }
        }
        let cnt = btm.read_zipper().into_cata_side_effect(|_mask, children, val, _path| {
            // println!("STEPPING path=\"{}\", mask={_mask:?}, children={children:?}, val={val:?}", String::from_utf8_lossy(_path));
            leaf_cnt(children, val)
        });
        assert_eq!(cnt, 11);

        let cnt = btm.read_zipper().into_cata_jumping_side_effect(|_mask, children, _stem, val, _path| {
            // println!("JUMPING  path=\"{}\", mask={_mask:?}, children={children:?}, stem={}, val={val:?}", String::from_utf8_lossy(_path), String::from_utf8_lossy(_stem));
            leaf_cnt(children, val)
        });
        assert_eq!(cnt, 11);

        // Finds the longest path in the trie
        fn longest_path(children: &mut[Vec<u8>], path: &[u8]) -> Vec<u8> {
            if children.len() == 0 {
                path.to_vec()
            } else {
                children.iter_mut().max_by_key(|p| p.len()).map_or(vec![], std::mem::take)
            }
        }
        let longest = btm.read_zipper().into_cata_side_effect(|_mask, children: &mut[Vec<u8>], _val, path| {
            // println!("STEPPING path=\"{}\", mask={_mask:?}, children={children:?}, val={_val:?}", String::from_utf8_lossy(path));
            longest_path(children, path)
        });
        assert_eq!(std::str::from_utf8(longest.as_slice()).unwrap(), "rubicundus");

        let longest = btm.read_zipper().into_cata_jumping_side_effect(|_mask, children: &mut[Vec<u8>], _stem, _val, path| {
            // println!("JUMPING  path=\"{}\", mask={_mask:?}, children={children:?}, stem={}, val={_val:?}", String::from_utf8_lossy(path), String::from_utf8_lossy(_stem));
            longest_path(children, path)
        });
        assert_eq!(std::str::from_utf8(longest.as_slice()).unwrap(), "rubicundus");

        // Finds all values that are positioned at branch points (where children.len() > 0)
        fn vals_at_branches(children: &mut [Vec<usize>], val: Option<&usize>) -> Vec<usize> {
            if children.len() > 0 {
                match val {
                    Some(val) => vec![*val],
                    None => {
                        let mut r = children.first_mut().map_or(vec![], std::mem::take);
                        for w in children[1..].iter_mut() { r.extend(w.drain(..)); }
                        r
                    }
                }
            } else {
                vec![]
            }
        }
        let at_truncated = btm.read_zipper().into_cata_side_effect(|_mask, children: &mut[Vec<usize>], val, _path| {
            // println!("STEPPING path=\"{}\", mask={_mask:?}, children={children:?}, val={val:?}", String::from_utf8_lossy(_path));
            vals_at_branches(children, val)
        });
        assert_eq!(at_truncated, vec![3]);

        let at_truncated = btm.read_zipper().into_cata_jumping_side_effect(|_mask, children: &mut[Vec<usize>], _stem, val, _path| {
            // println!("JUMPING  path=\"{}\", mask={_mask:?}, children={children:?}, stem={}, val={val:?}", String::from_utf8_lossy(_path), String::from_utf8_lossy(_stem));
            vals_at_branches(children, val)
        });
        assert_eq!(at_truncated, vec![3]);
    }

    #[test]
    fn cata_test3() {
        let tests = [
            (vec![], 0, 0),
            (vec!["i"], 1, 1), //1 leaf, 1 node
            (vec!["i", "ii"], 2, 1), //1 leaf, 2 total "nodes"
            (vec!["ii", "iiiii"], 5, 1), //1 leaf, 5 total "nodes"
            (vec!["ii", "iii", "iiiii", "iiiiiii"], 7, 1), //1 leaf, 7 total "nodes"
            (vec!["ii", "iiii", "iij", "iijjj"], 7, 3), //2 leaves, 1 fork, 7 total "nodes"
        ];
        for (keys, expected_sum_ordinary, expected_sum_jumping) in tests {
            let map: BytesTrieMap<()> = keys.into_iter().map(|v| (v, ())).collect();
            let zip = map.read_zipper();

            let map_f = |_v: &(), _path: &[u8]| {
                // println!("map path=\"{}\"", String::from_utf8_lossy(_path));
                1
            };
            let collapse_f = |_v: &(), upstream: u32, _path: &[u8]| {
                // println!("collapse path=\"{}\", upstream={upstream}", String::from_utf8_lossy(_path));
                upstream
            };
            let alg_f = |_child_mask: &ByteMask, children: &mut [u32], path: &[u8]| {
                // println!("aggregate path=\"{}\", children={children:?}", String::from_utf8_lossy(path));
                let sum = children.into_iter().fold(0, |sum, child| sum + *child);
                if path.len() > 0 {
                    sum + 1
                } else {
                    sum
                }
            };

            //Test both the jumping and non-jumping versions
            let sum = zip.clone().into_cata_side_effect(SplitCata::new(map_f, collapse_f, alg_f));
            assert_eq!(sum, expected_sum_ordinary);

            let sum = zip.into_cata_jumping_side_effect(SplitCataJumping::new(map_f, collapse_f, alg_f, |_subpath, w, _path| w));
            assert_eq!(sum, expected_sum_jumping);
        }
    }

    #[test]
    fn cata_test4() {
        #[derive(Debug, PartialEq)]
        enum Trie<V> {
            Value(V),
            Collapse(V, Box<Trie<V>>),
            Alg(Vec<(char, Trie<V>)>),
            Jump(String, Box<Trie<V>>)
        }
        use Trie::*;

        let mut btm = BytesTrieMap::new();
        let rs = ["arr", "arrow", "bow", "cannon", "roman", "romane", "romanus", "romulus", "rubens", "ruber", "rubicon", "rubicundus", "rom'i"];
        rs.iter().enumerate().for_each(|(i, r)| { btm.insert(r.as_bytes(), i); });

        let s = btm.read_zipper().into_cata_jumping_side_effect(SplitCataJumping::new(
            |v, _path| { Some(Box::new(Value(*v))) },
            |v, w, _path| { Some(Box::new(Collapse(*v, w.unwrap()))) },
            |cm, ws, _path| {
                let mut it = cm.iter();
                Some(Box::new(Alg(ws.iter_mut().map(|w| (it.next().unwrap() as char, *std::mem::take(w).unwrap())).collect())))},
            |sp, w, _path| { Some(Box::new(Jump(std::str::from_utf8(sp).unwrap().to_string(), w.unwrap()))) }
        ));

        assert_eq!(s, Some(Alg([
            ('a', Jump("rr".into(), Collapse(0, Jump("w".into(), Value(1).into()).into()).into())),
            ('b', Jump("ow".into(), Value(2).into())),
            ('c', Jump("annon".into(), Value(3).into())),
            ('r', Alg([
                ('o', Jump("m".into(), Alg([
                    ('\'', Jump("i".into(), Value(12).into())),
                    ('a', Jump("n".into(), Collapse(4, Alg([
                        ('e', Value(5)),
                        ('u', Jump("s".into(), Value(6).into()))
                    ].into()).into()).into())),
                    ('u', Jump("lus".into(), Value(7).into()))].into()).into())),
                ('u', Jump("b".into(), Alg([
                    ('e', Alg([
                        ('n', Jump("s".into(), Value(8).into())),
                        ('r', Value(9))].into())),
                    ('i', Jump("c".into(), Alg([
                        ('o', Jump("n".into(), Value(10).into())),
                        ('u', Jump("ndus".into(), Value(11).into()))].into()).into()))].into()).into()))].into()))].into()).into()));
    }

    /// Tests going from a map directly to a catamorphism
    #[test]
    fn cata_test5() {
        let empty = BytesTrieMap::<u64>::new();
        let result = empty.into_cata_side_effect(SplitCata::new(|_, _| 1, |_, _, _| 2, |_, _, _| 3));
        assert_eq!(result, 3);

        let mut nonempty = BytesTrieMap::<u64>::new();
        nonempty.insert(&[1, 2, 3], !0);
        let result = nonempty.into_cata_side_effect(SplitCata::new(|_, _| 1, |_, _, _| 2, |_, _, _| 3));
        assert_eq!(result, 3);
    }

    #[test]
    fn cata_test6() {
        let mut btm = BytesTrieMap::new();
        let rs = ["Hello, my name is", "Helsinki", "Hell"];
        rs.iter().enumerate().for_each(|(i, r)| { btm.insert(r.as_bytes(), i); });

        let mut map_cnt = 0;
        let mut collapse_cnt = 0;
        let mut alg_cnt = 0;
        let mut jump_cnt = 0;

        btm.read_zipper().into_cata_jumping_side_effect(SplitCataJumping::new(
            |_, _path| {
                // println!("map: \"{}\"", String::from_utf8_lossy(_path));
                map_cnt += 1;
            },
            |_, _, _path| {
                // println!("collapse: \"{}\"", String::from_utf8_lossy(_path));
                collapse_cnt += 1;
            },
            |_, _, _path| {
                // println!("alg: \"{}\"", String::from_utf8_lossy(_path));
                alg_cnt += 1;
            },
            |_sub_path, _, _path| {
                // println!("jump: over \"{}\" to \"{}\"", String::from_utf8_lossy(_sub_path), String::from_utf8_lossy(_path));
                jump_cnt += 1;
            }
        ));
        // println!("map_cnt={map_cnt}, collapse_cnt={collapse_cnt}, alg_cnt={alg_cnt}, jump_cnt={jump_cnt}");

        assert_eq!(map_cnt, 2);
        assert_eq!(collapse_cnt, 1);
        assert_eq!(alg_cnt, 2);
        assert_eq!(jump_cnt, 3);
    }

    /// Covers the full spectrum of byte values
    #[test]
    fn cata_test7() {
        let mut btm = BytesTrieMap::new();
        let rs = [[0, 0, 0, 0], [0, 255, 170, 170], [0, 255, 255, 255], [0, 255, 88, 88]];
        rs.iter().enumerate().for_each(|(i, r)| { btm.insert(r, i); });

        let mut map_cnt = 0;
        let mut collapse_cnt = 0;
        let mut alg_cnt = 0;
        let mut jump_cnt = 0;

        btm.read_zipper().into_cata_jumping_side_effect(SplitCataJumping::new(
            |_, _path| {
                // println!("map: {_path:?}");
                map_cnt += 1;
            },
            |_, _, _path| {
                // println!("collapse: {_path:?}");
                collapse_cnt += 1;
            },
            |_mask, _, _path| {
                // println!("alg: {_path:?}, mask: {_mask:?}");
                alg_cnt += 1;
            },
            |_sub_path, _, _path| {
                // println!("jump: over {_sub_path:?} to {_path:?}");
                jump_cnt += 1;
            }
        ));
        // println!("map_cnt={map_cnt}, collapse_cnt={collapse_cnt}, alg_cnt={alg_cnt}, jump_cnt={jump_cnt}");

        assert_eq!(map_cnt, 4);
        assert_eq!(collapse_cnt, 0);
        assert_eq!(alg_cnt, 3);
        assert_eq!(jump_cnt, 4);
    }

    /// Tests that cata hits the root value
    #[test]
    fn cata_test8() {
        let keys = ["", "ab", "abc"];
        let btm: BytesTrieMap<usize> = keys.into_iter().enumerate().map(|(i, k)| (k, i)).collect();

        btm.into_cata_jumping_side_effect(SplitCataJumping::new(
            |v, path| {
                // println!("map: {path:?}");
                assert_eq!(path, &[97, 98, 99]);
                assert_eq!(*v, 2);
            },
            |v, _, path| {
                // println!("collapse: {path:?}");
                match *v {
                    1 => assert_eq!(path, &[97, 98]),
                    0 => assert_eq!(path, &[]),
                    _ => unreachable!(),
                }
            },
            |_mask, _, path| {
                // println!("alg: {path:?}");
                assert_eq!(path, &[]);
            },
            |sub_path, _, path| {
                // println!("jump: over {sub_path:?} to {path:?}");
                assert_eq!(sub_path, &[98]);
                assert_eq!(path, &[97]);
            }
        ))
    }

    /// Generate some basic tries using the [TrieBuilder::push_byte] API
    #[test]
    fn ana_test1() {
        // Generate 5 'i's
        let mut invocations = 0;
        let map: BytesTrieMap<()> = BytesTrieMap::<()>::new_from_ana(5, |idx, val, children, _path| {
            // println!("path=\"{}\"", String::from_utf8_lossy(_path));
            *val = Some(());
            if idx > 0 {
                children.push_byte(b'i', idx - 1)
            }
            invocations += 1;
        });
        assert_eq!(map.val_count(), 5);
        assert_eq!(invocations, 6);

        // Generate all 3-lenght 'L' | 'R' permutations
        let mut invocations = 0;
        let map: BytesTrieMap<()> = BytesTrieMap::<()>::new_from_ana(3, |idx, val, children, _path| {
            // println!("path=\"{}\"", String::from_utf8_lossy(_path));
            if idx > 0 {
                children.push_byte(b'L', idx - 1);
                children.push_byte(b'R', idx - 1);
            } else {
                *val = Some(());
            }
            invocations += 1;
        });
        assert_eq!(map.val_count(), 8);
        assert_eq!(invocations, 15);
    }

    /// Test the [`TrieBuilder::set_child_mask`] API to set multiple children at once
    #[test]
    fn ana_test2() {
        let map: BytesTrieMap<()> = BytesTrieMap::<()>::new_from_ana(([0u64; 4], 0), |(mut mask, idx), val, children, _path| {
            // println!("path=\"{}\"", String::from_utf8_lossy(_path));
            if idx < 5 {
                mask[1] |= 1u64 << 1+idx;
                let child_vec = vec![(mask, idx+1); idx+1];
                children.set_child_mask(mask , child_vec);
            } else {
                *val = Some(());
            }
        });
        assert_eq!(map.val_count(), 120); // 1 * 2 * 3 * 4 * 5
        // for (path, ()) in map.iter() {
        //     println!("{}", String::from_utf8_lossy(&path));
        // }
    }
    /// Test the [`TrieBuilder::push`] API to set whole string paths
    #[test]
    fn ana_test3() {
        let map: BytesTrieMap<()> = BytesTrieMap::<()>::new_from_ana(3, |idx, val, children, _path| {
            // println!("path=\"{}\"", String::from_utf8_lossy(_path));
            if idx > 0 {
                children.push(b"Left:", idx-1);
                children.push(b"Right:", idx-1);
            } else {
                *val = Some(());
            }
        });
        // for (path, ()) in map.iter() {
        //     println!("{}", String::from_utf8_lossy(&path));
        // }
        assert_eq!(map.val_count(), 8);
        assert_eq!(map.get(b"Left:Right:Left:"), Some(&()));
        assert_eq!(map.get(b"Right:Left:Right:"), Some(&()));

        //Try intermixing whole strings and bytes
        let map: BytesTrieMap<()> = BytesTrieMap::<()>::new_from_ana(7, |idx, val, children, _path| {
            // println!("path=\"{}\"", String::from_utf8_lossy(_path));
            if idx > 0 {
                if idx % 2 == 0 {
                    children.push_byte(b'+', idx-1);
                    children.push_byte(b'-', idx-1);
                } else {
                    children.push(b"Left", idx-1);
                    children.push(b"Right", idx-1);
                }
            } else {
                *val = Some(());
            }
        });
        // for (path, ()) in map.iter() {
        //     println!("{}", String::from_utf8_lossy(&path));
        // }
        assert_eq!(map.val_count(), 128);
        assert_eq!(map.get(b"Right-Right+Left-Left"), Some(&()));
        assert_eq!(map.get(b"Left-Right-Right+Left"), Some(&()));

        //Intermix them in the same child list
        let map: BytesTrieMap<()> = BytesTrieMap::<()>::new_from_ana(7, |idx, val, children, _path| {
            // println!("path=\"{}\"", String::from_utf8_lossy(_path));
            if idx > 0 {
                if idx % 2 == 0 {
                    children.push_byte(b'+', idx-1);
                    children.push(b"Left", idx-1);
                } else {
                    children.push_byte(b'-', idx-1);
                    children.push(b"Right", idx-1);
                }
            } else {
                *val = Some(());
            }
        });
        // for (path, ()) in map.iter() {
        //     println!("{}", String::from_utf8_lossy(&path));
        // }
        assert_eq!(map.val_count(), 128);
        assert_eq!(map.get(b"Right+-+-+-"), Some(&()));
        assert_eq!(map.get(b"-+-+-+-"), Some(&()));
        assert_eq!(map.get(b"RightLeftRightLeftRightLeftRight"), Some(&()));
    }

    const GREETINGS: &[&str] = &["Hallo,Afrikaans", "Përshëndetje,Albanian", "እው ሰላም ነው,Amharic", "مرحبًا,Arabic",
        "Barev,Armenian", "Kamisaki,Aymara", "Salam,Azerbaijani", "Kaixo,Basque", "Вітаю,Belarusian", "হ্যালো,Bengali",
        "Zdravo,Bosnian", "Здравейте,Bulgarian", "ဟယ်လို,Burmese", "你好,Cantonese", "Hola,Catalan", "Kamusta,Cebuano",
        "Kamusta,Cebuano", "Moni,Chichewa", "Bonghjornu,Corsican", "Zdravo,Croatian", "Ahoj,Czech", "Hej,Danish",
        "Hallo,Dutch", "Hello,English", "Tere,Estonian", "Hello,Ewe", "سلام,Farsi (Persian)", "Bula,Fijian",
        "Kumusta,Filipino", "Hei,Finnish", "Bonjour,French", "Dia dhuit,Gaelic (Irish)", "Ola,Galician", "გამარჯობა,Georgian",
        "Guten tag,German", "γεια,Greek", "Mba'éichapa,Guarani", "Bonjou,Haitian Creole", "Aloha,Hawaiian",
        "שלום,Hebrew", "नमस्ते,Hindi", "Nyob zoo,Hmong", "Szia,Hungarian", "Halló,Icelandic", "Ndewo,Igbo",
        "TRASH-NO-COMMA", //Trash here, to test error-cases
        "Hello,Ilocano", "Halo,Indonesian", "Ciao,Italian", "こんにちは,Japanese", "Сәлеметсіз бе,Kazakh",
        "TRASH-NOTHING-AFTER-COMMA,", //Trash here, to test error-cases
        "សួស្តី,Khmer", "Mwaramutse,Kinyarwanda", "안녕하세요,Korean", "Slav,Kurdish", "ສະບາຍດີ,Lao", "Salve,Latin",
        ",TRASH-NOTHING-BEFORE-COMMA", //Trash here, to test error-cases
        "Sveika,Latvian", "Sveiki,Lithuanian", "Moien,Luxembourgish", "Salama,Malagasy", "Selamat pagi,Malay",
        "", //Trash here, empty string
        "Bongu,Maltese", "你好,Mandarin", "Kia ora,Maori", "नमस्कार,Marathi", "сайн уу,Mongolian", "Niltze Tialli Pialli,Nahuatl",
        "Ya’at’eeh,Navajo", "नमस्कार,Nepali", "Hei,Norwegian", "سلام,Pashto", "Cześć,Polish", "Olá,Portuguese",
        "ਸਤ ਸ੍ਰੀ ਅਕਾਲ,Punjabi", "Akkam,Oromo", "Allianchu,Quechua", "Bunâ,Romanian", "Привет,Russian", "Talofa,Samoan",
        "Thobela,Sepedi", "Здраво,Serbian", "Dumela,Sesotho", "Ahoj,Slovak", "Zdravo,Slovenian", "Hello,Somali",
        "Hola,Spanish", "Jambo,Swahili", "Hallå,Swedish", "Kamusta,Tagalog", "Ia Orana,Tahitian", "Li-hó,Taiwanese",
        "வணக்கம்,Tamil", "สวัสดี,Thai", "Tashi delek,Tibetan", "Mālō e lelei,Tongan", "Avuxeni,Tsonga", "Merhaba,Turkish",
        "привіт,Ukrainian", "السلام عليكم,Urdu", "Salom,Uzbek", "Xin chào,Vietnamese", "Helo,Welsh", "Molo,Xhosa",
    ];

    /// Test pushing into the trie, one byte at a time
    #[test]
    fn ana_test4() {
        let mut greetings_vec = GREETINGS.to_vec();
        let btm = BytesTrieMap::<Range<usize>>::new_from_ana(0..greetings_vec.len(), |mut range, val, children, path| {
            let n = path.len();

            //Sort the keys in the range by the first byte of each substring
            let string_slice = &mut greetings_vec[range.clone()];
            string_slice.sort_by_key(|s| s.as_bytes().get(n));

            //Discard the strings that are too short (that have ended prematurely)
            while range.len() > 0 && greetings_vec[range.start].len() <= n { range.start += 1; }

            while range.len() > 0 {
                //Find the range of strings that start with the same byte as the first string
                let mut m = range.start + 1;
                let byte = greetings_vec[range.start].as_bytes()[n];
                while range.contains(&m) && greetings_vec[m].as_bytes()[n] == byte {
                    m += 1;
                }

                let (mut same_prefix_range, remaining) = (range.start..m, m..range.end);

                //If this is the end of a path, set the value
                if byte == b',' {

                    //Sort by the languages
                    //NOTE: there is some ambiguity in the desired behavior, since the validity test
                    // sorts the greetings but not the languages.  However, if we don't sort the languages,
                    // then non-contiguous and non-prefixing empty language strings can't be removed unless
                    // we attempt to represent the results of a node by a list instead of a range
                    let string_slice = &mut greetings_vec[same_prefix_range.clone()];
                    string_slice.sort_by_key(|s| &s[n+1..]);

                    //Discard the strings have nothing after the ','
                    while same_prefix_range.len() > 0 && greetings_vec[same_prefix_range.start].len() <= n+1 {
                        same_prefix_range.start += 1;
                    }
                    //If we didn't discard all the items
                    if same_prefix_range.len() > 0 {
                        *val = Some(same_prefix_range);
                    }
                } else {
                    //Recursive case
                    children.push_byte(byte, same_prefix_range);
                }
                range = remaining;
            }
        });

        let mut check: Vec<&str> = GREETINGS.into_iter().copied()
            .filter(|x| {
                let comma_idx = x.find(",").unwrap_or(0);
                comma_idx != 0 && comma_idx < x.len()-1
            })
            .collect();
        check.sort_by_key(|x| x.split_once(",").map(|s| s.0).unwrap_or(&""));
        let mut it = check.iter();

        let mut rz = btm.read_zipper();
        while let Some(range) = rz.to_next_val() {
            for language_idx in range.clone().into_iter() {
                let greeting = std::str::from_utf8(rz.path()).unwrap();
                let language = &greetings_vec[language_idx][rz.path().len()+1..];

                // println!("language: {}, greeting: {}", language, greeting);
                assert_eq!(*it.next().unwrap(), format!("{greeting},{language}"));
            }
        }
    }

    #[test]
    fn ana_test5() {
        let _btm = BytesTrieMap::<&str>::new_from_ana(GREETINGS, |string_slice, val, children, _path| {

            fn split_key(in_str: &str) -> (&str, &str) {
                let det = in_str.find(',').unwrap_or(usize::MAX);
                if det == 0 {
                    ("", &in_str[1..])
                } else if det == usize::MAX {
                    ("", in_str)
                } else {
                    (&in_str[0..det], &in_str[det+1..])
                }
            }

            if string_slice.len() == 1 {
                let (_, split_val) = split_key(string_slice[0]);
                *val = Some(split_val);
            } else {
                for i in 0..string_slice.len() {
                    let (key, _) = split_key(string_slice[0]);
                    children.tolerant_push(key.as_bytes(), &string_slice[i..i+1]);
                }
            }
        });

        let mut rz = _btm.read_zipper();
        while let Some(language) = rz.to_next_val() {
            //GOAT, this feature (and therefore this test) is WIP
            println!("language: {}, greeting: {}", language, std::str::from_utf8(rz.path()).unwrap());
        }
    }

    #[test]
    fn apo_test1() {
        let mut btm = BytesTrieMap::new();
        let rs = ["arro^w", "bow", "cann^on", "roman", "romane", "romanus^", "romulus", "rubens", "ruber", "rubicon", "rubicundus", "rom^i"];
        rs.iter().enumerate().for_each(|(i, r)| { btm.insert(r.as_bytes(), i); });

        let mut alphabetic = [0u64; 4];
        for c in "abcdefghijklmnopqrstuvwxyz".bytes() { alphabetic.set_bit(c) }

        let trie_ref = btm.trie_ref_at_path([]);
        let counted = BytesTrieMap::new_from_ana(trie_ref, |trie_ref, _v, builder, loc| {

            let iter = crate::utils::ByteMaskIter::new(trie_ref.child_mask());
            for b in iter {
                if alphabetic.test_bit(b) {
                    let new_trie_ref = trie_ref.trie_ref_at_path([b]);
                    builder.push_byte(b, new_trie_ref);
                }
                // todo I didn't find a histogram/groupby function, so couldn't aggregate letter counts yet, just returning one
                else {
                    let new_map = BytesTrieMap::from_iter(loc.into_iter().copied().map(|x| ([x], 1)));
                    let temp_zipper = new_map.read_zipper();
                    builder.graft_at_byte(b, &temp_zipper)
                }
            }
        });

        println!("test");
        let mut rz = counted.read_zipper();
        while let Some(v) = rz.to_next_val() {
            // todo write out useful print function, that shows the count submaps
            println!("v: {}, p: {}", v, std::str::from_utf8(rz.path()).unwrap());
        }
    }
}
