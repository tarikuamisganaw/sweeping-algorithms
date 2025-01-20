//! Functionality for applying various morphisms to [PathMap] and [Zipper]s
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
//! [ZipperIteration::to_next_val] and [ZipperIteration::to_next_step].  The [Zipper] methods visit values
//! first before descending to the branches below, while the `cata` methods call the `mapper` on the deepest
//! values first, before returning to higher levels where `collapse` is called.
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
//! ### Side Effects
//!
//! Most methods come (or will come) with a `_side_effect` and an ordinary flavor.  The side-effecting
//! flavors take `FnMut` closures, while the ordinary methods take `Fn` closures.  The side-effecting
//! methods must traverse the entire trie exhaustively, while the ordinary methods may cache and re-use
//! intermediate results in cases where there is structural sharing within the trie.
//!
//! In general, the ordinary methods should be preferred unless sife-effects are necessary
//!


//GOAT QUESTION: Why not combine map_f and collapse_F by passing `Option<W>` to the closure?

// GOAT!! Are these names (collapse, and alg) part of math canon?  They are not very descriptive and hopefully we can change them.
// "map" is good because it's a perfect equivalent to map in map->reduce.

use crate::zipper::*;

pub trait ZipperMorphisms<V> {
    /// Applies a catamorphism to the trie
    ///
    /// ## Args
    /// - `map_f`: `mapper(v: &V, path: &[u8]) -> W`
    /// Maps value `v` at a leaf `path` into an intermediate result
    ///
    /// - `collapse_f`: `collapse(v: &V, w: W, path: &[u8]) -> W`
    /// Folds value `v` at a non-leaf `path` with the aggregated results from the trie below `path`
    ///
    /// - `alg_f`: `alg(m: [u64; 4], cs: &mut [W], path: &[u8]) -> W`
    /// Aggregates the results from the child branches, `cs`, descending from `path` into a single result
    ///
    /// In all cases, the `path` arg is the [origin_path](ZipperAbsolutePath::origin_path)
    fn into_cata_side_effect<W, MapF, CollapseF, AlgF>(self, map_f: MapF, collapse_f: CollapseF, alg_f: AlgF) -> W
        where
        MapF: FnMut(&V, &[u8]) -> W,
        CollapseF: FnMut(&V, W, &[u8]) -> W,
        AlgF: FnMut(&[u64; 4], &mut [W], &[u8]) -> W;

    /// Applies a "jumping" catamorphism to the trie
    ///
    /// ## Args
    /// - `jump_f`: `FnMut(sub_path: &[u8], w: W, path: &[u8]) -> W`
    /// Elevates a result `w` descending from the relative path, `sub_path` to the current position at `path`
    ///
    /// See [into_cata_side_effect](ZipperMorphisms::into_cata_side_effect) for explanation of other behavior
    fn into_cata_jumping_side_effect<W, MapF, CollapseF, AlgF, JumpF>(self, map_f: MapF, collapse_f: CollapseF, alg_f: AlgF, jump_f: JumpF) -> W
        where
        MapF: FnMut(&V, &[u8]) -> W,
        CollapseF: FnMut(&V, W, &[u8]) -> W,
        AlgF: FnMut(&[u64; 4], &mut [W], &[u8]) -> W,
        JumpF: FnMut(&[u8], W, &[u8]) -> W;
}

impl<'a, Z, V: 'a> ZipperMorphisms<V> for Z where Z: ReadOnlyZipper<'a, V> + ZipperAbsolutePath {
    fn into_cata_side_effect<W, MapF, CollapseF, AlgF>(self, map_f: MapF, collapse_f: CollapseF, alg_f: AlgF) -> W
        where
        MapF: FnMut(&V, &[u8]) -> W,
        CollapseF: FnMut(&V, W, &[u8]) -> W,
        AlgF: FnMut(&[u64; 4], &mut [W], &[u8]) -> W,
    {
        cata_side_effect_body::<Self, V, W, MapF, CollapseF, AlgF, _, false>(self, map_f, collapse_f, alg_f, |_, _, _| unreachable!())
    }
    fn into_cata_jumping_side_effect<W, MapF, CollapseF, AlgF, JumpF>(self, map_f: MapF, collapse_f: CollapseF, alg_f: AlgF, jump_f: JumpF) -> W
        where
        MapF: FnMut(&V, &[u8]) -> W,
        CollapseF: FnMut(&V, W, &[u8]) -> W,
        AlgF: FnMut(&[u64; 4], &mut [W], &[u8]) -> W,
        JumpF: FnMut(&[u8], W, &[u8]) -> W
    {
        cata_side_effect_body::<Self, V, W, MapF, CollapseF, AlgF, JumpF, true>(self, map_f, collapse_f, alg_f, jump_f)
    }
}

#[inline(always)]
fn cata_side_effect_body<'a, Z, V: 'a, W, MapF, CollapseF, AlgF, JumpF, const JUMPING: bool>(mut z: Z, mut map_f: MapF, mut collapse_f: CollapseF, mut alg_f: AlgF, mut jump_f: JumpF) -> W
    where
    Z: ReadOnlyZipper<'a, V> + ZipperAbsolutePath,
    MapF: FnMut(&V, &[u8]) -> W,
    CollapseF: FnMut(&V, W, &[u8]) -> W,
    AlgF: FnMut(&[u64; 4], &mut [W], &[u8]) -> W,
    JumpF: FnMut(&[u8], W, &[u8]) -> W,
{
    //`stack` holds a "frame" at each forking point above the zipper position.  No frames exist for values
    let mut stack = Vec::<StackFrame<W>>::with_capacity(12);
    let mut frame_idx = 0;

    //A scratch space to hold prior paths after we've ascended
    let mut path_buf = Vec::with_capacity(64);

    z.reset();

    //Push a stack frame for the root, and start on the first branch off the root
    stack.push(StackFrame::new(z.child_count(), z.child_mask()));
    if !z.descend_first_byte() {
        //Empty trie is a special case
        return alg_f(&[0; 4], &mut [], z.origin_path().unwrap());
    }

    loop {
        //Descend to the next forking point if we're jumping
        let mut is_leaf = false;
        while z.child_count() < 2 {
            if !z.descend_until() {
                is_leaf = true;
                break;
            }
        }

        if is_leaf {
            //Map the value from this leaf
            let mut cur_w = z.get_value().map(|v| map_f(v, z.origin_path().unwrap()));

            //Ascend back to the last fork point
            cur_w = ascend_to_fork::<Z, V, W, MapF, CollapseF, AlgF, JumpF, JUMPING>(&mut z, &mut map_f, &mut collapse_f, &mut alg_f, &mut jump_f, &mut path_buf, cur_w);

            //Merge the result into the stack frame
            match cur_w {
                Some(w) => stack[frame_idx].push_val(w),
                None => stack[frame_idx].push_none(),
            }

            debug_assert!(stack[frame_idx].child_idx <= z.child_count());
            while stack[frame_idx].child_idx == z.child_count() {

                //We finished all the children from this branch, so run the aggregate function
                let stack_frame = &mut stack[frame_idx];
                let mut w = alg_f(&stack_frame.child_mask, &mut stack_frame.children, z.origin_path().unwrap());
                if frame_idx == 0 {
                    return w
                } else {
                    frame_idx -= 1;

                    //Check to see if we have a value here we need to collapse
                    if let Some(v) = z.get_value() {
                        w = collapse_f(v, w, z.origin_path().unwrap());
                    }

                    //Ascend the rest of the way back up to the branch
                    w = ascend_to_fork::<Z, V, W, MapF, CollapseF, AlgF, JumpF, JUMPING>(&mut z, &mut map_f, &mut collapse_f, &mut alg_f, &mut jump_f, &mut path_buf, Some(w)).unwrap();

                    //Merge the result into the stack frame
                    stack[frame_idx].push_val(w);
                    debug_assert!(stack[frame_idx].child_idx <= z.child_count());
                }
            }

            //Position to descend the next child branch
            let descended = z.descend_indexed_branch(stack[frame_idx].child_idx);
            debug_assert!(descended);
        } else {
            //Push a new stack frame for this branch
            frame_idx += 1;
            let child_mask = z.child_mask();
            let child_cnt = z.child_count();
            if stack.len() <= frame_idx {
                stack.push(StackFrame::new(child_cnt, child_mask));
                debug_assert!(stack.len() > frame_idx);
            } else {
                stack[frame_idx].reset(child_mask);
            }

            //Descend the first child branch
            z.descend_first_byte();
        }
    }
}

#[inline(always)]
fn ascend_to_fork<'a, Z, V: 'a, W, MapF, CollapseF, AlgF, JumpF, const JUMPING: bool>(z: &mut Z, 
        map_f: &mut MapF,
        collapse_f: &mut CollapseF,
        alg_f: &mut AlgF,
        jump_f: &mut JumpF,
        path_buf: &mut Vec<u8>,
        mut cur_w: Option<W>
) -> Option<W>
    where
    Z: ReadOnlyZipper<'a, V> + ZipperAbsolutePath,
    MapF: FnMut(&V, &[u8]) -> W,
    CollapseF: FnMut(&V, W, &[u8]) -> W,
    AlgF: FnMut(&[u64; 4], &mut [W], &[u8]) -> W,
    JumpF: FnMut(&[u8], W, &[u8]) -> W,
{
    loop {
        let path = z.path();
        debug_assert_eq!(&path[0..path_buf.len()], path_buf); //Since this function is the only place we ascend...
        path_buf.extend(&path[path_buf.len()..]);

        let ascended = z.ascend_until();
        debug_assert!(ascended);

        let at_fork = z.child_count() > 1;
        let at_root = z.at_root();

        let new_path_len = z.path().len();
        debug_assert!(new_path_len < path_buf.len());

        if JUMPING {
            if path_buf.len() > new_path_len+1 || (!at_fork && !at_root) {
                if let Some(w) = cur_w {
                    cur_w = Some(jump_f(&path_buf[new_path_len..], w, z.origin_path().unwrap()));
                }
            }
            path_buf.truncate(new_path_len);
        } else {
            //This is the default code to call the `alg_f` for each intermediate path step
            // NOTE: the reason this is a special case rather than just a default JumpF is because I want
            // to be able to re-use the `path_buf`, but that's not possible through the defined interface
            while path_buf.len() > new_path_len {
                let byte = path_buf.pop().unwrap();
                if path_buf.len() > new_path_len || (!at_fork && !at_root) {
                    if let Some(w) = cur_w {
                        let mut mask = [0u64; 4];
                        let word_idx = (byte / 64) as usize;
                        mask[word_idx] = 1 << (byte % 64);
                        cur_w = Some(alg_f(&mask, &mut[w], &path_buf));
                    }
                }
            }
        }

        if at_root {
            return cur_w
        }

        if !at_fork {
            //This unwrap shouldn't panic, because `ascend_until` should only stop at values and forks
            let v = z.get_value().unwrap();
            match cur_w {
                None => { cur_w = Some(map_f(v, z.origin_path().unwrap())); },
                Some(w) => { cur_w = Some(collapse_f(v, w, z.origin_path().unwrap())); }
            }
        } else {
            break;
        }
    }
    cur_w
}

/// Internal structure to hold temporary info used inside morphism apply methods
struct StackFrame<W> {
    child_mask: [u64; 4],
    mask_word_idx: usize,
    child_idx: usize,
    remaining_children_mask: u64,
    children: Vec<W>,
}

impl<W> StackFrame<W> {
    /// Allocates a new StackFrame
    fn new(child_count: usize, child_mask: [u64; 4]) -> Self {
        let mut frame = Self {
            child_mask: <_>::default(),
            child_idx: 0,
            mask_word_idx: 0,
            remaining_children_mask: 0,
            children: Vec::with_capacity(child_count)
        };
        frame.reset(child_mask);
        frame
    }
    /// Resets a StackFrame to the state needed to iterate a new forking point
    fn reset(&mut self, child_mask: [u64; 4]) {
        self.mask_word_idx = 0;
        self.child_idx = 0;
        while child_mask[self.mask_word_idx] == 0 && self.mask_word_idx < 3 {
            self.mask_word_idx += 1;
        }
        self.remaining_children_mask = child_mask[self.mask_word_idx];
        self.child_mask = child_mask;
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
    fn push_none(&mut self) {
        self.child_idx += 1;
        debug_assert!(self.remaining_children_mask > 0); //If this assert trips, then it means we're trying to push a value for a non-existent child
        let index = self.remaining_children_mask.trailing_zeros();
        self.remaining_children_mask ^= 1u64 << index;
        self.child_mask[self.mask_word_idx] ^= 1u64 << index;
        self.advance_word_idx();
    }
    fn advance_word_idx(&mut self) {
        if self.remaining_children_mask == 0 {
            if self.remaining_children_mask < 3 {
                self.mask_word_idx += 1;
                while self.child_mask[self.mask_word_idx] == 0 && self.mask_word_idx < 3 {
                    self.mask_word_idx += 1;
                }
                self.remaining_children_mask = self.child_mask[self.mask_word_idx];
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::trie_map::BytesTrieMap;
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

            let map_f = |_v: &(), path: &[u8]| {
                let val = (*path.last().unwrap() as char).to_digit(10).unwrap();
                // println!("map path=\"{}\" val={val}", String::from_utf8_lossy(path));
                val
            };
            let collapse_f = |_v: &(), upstream: u32, path: &[u8]| {
                let this_digit = (*path.last().unwrap() as char).to_digit(10).unwrap();
                // println!("collapse path=\"{}\", upstream={upstream}, this_digit={this_digit}, sum={}", String::from_utf8_lossy(path), upstream + this_digit);
                upstream + this_digit
            };
            let alg_f = |_child_mask: &[u64; 4], children: &mut [u32], _path: &[u8]| {
                // println!("aggregate path=\"{}\", children={children:?}", String::from_utf8_lossy(_path));
                children.into_iter().fold(0, |sum, child| sum + *child)
            };
            let jump_f = |_subpath: &[u8], w: u32, _path: &[u8]| {
                // println!("jump sub-path=\"{}\", upstream={w} path=\"{}\",", String::from_utf8_lossy(_subpath), String::from_utf8_lossy(_path));
                w
            };

            //Test both the jumping and non-jumping versions, since they ought to do the same thing
            let sum = zip.clone().into_cata_side_effect(map_f, collapse_f, alg_f);
            assert_eq!(sum, expected_sum);

            let sum = zip.into_cata_jumping_side_effect(map_f, collapse_f, alg_f, jump_f);
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
        let cnt = btm.read_zipper().into_cata_side_effect(
            |_v, _p| { 1usize },
            |_v, w, _p| { w },
            |_m, ws, _p| { ws.iter().sum() });
        assert_eq!(cnt, 11);

        let cnt = btm.read_zipper().into_cata_jumping_side_effect(
            |_v, _p| { 1usize },
            |_v, w, _p| { w },
            |_m, ws, _p| { ws.iter().sum() },
            |_subpath, w, _path| w
        );
        assert_eq!(cnt, 11);

        let longest = btm.read_zipper().into_cata_side_effect(
            |_v, p| { p.to_vec() },
            |_v, w, _p| { w },
            |_m, ws: &mut [Vec<u8>], _p| { ws.iter_mut().max_by_key(|p| p.len()).map_or(vec![], std::mem::take) });
        assert_eq!(std::str::from_utf8(longest.as_slice()).unwrap(), "rubicundus");

        let longest = btm.read_zipper().into_cata_jumping_side_effect(
            |_v, p| { p.to_vec() },
            |_v, w, _p| { w },
            |_m, ws: &mut [Vec<u8>], _p| { ws.iter_mut().max_by_key(|p| p.len()).map_or(vec![], std::mem::take) },
            |_subpath, w, _path| w
        );
        assert_eq!(std::str::from_utf8(longest.as_slice()).unwrap(), "rubicundus");

        let at_truncated = btm.read_zipper().into_cata_side_effect(
            |_v, _p| { vec![] },
            |v, _w, _p| { vec![v.clone()] },
            |_m, ws: &mut [_], _p| {
                let mut r = ws.first_mut().map_or(vec![], std::mem::take);
                for w in ws[1..].iter_mut() { r.extend(w.drain(..)); }
                r
            });
        assert_eq!(at_truncated, vec![3]);

        let at_truncated = btm.read_zipper().into_cata_jumping_side_effect(
            |_v, _p| { vec![] },
            |v, _w, _p| { vec![v.clone()] },
            |_m, ws: &mut [_], _p| {
                let mut r = ws.first_mut().map_or(vec![], std::mem::take);
                for w in ws[1..].iter_mut() { r.extend(w.drain(..)); }
                r
            },
            |_subpath, w, _path| w
        );
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
            let alg_f = |_child_mask: &[u64; 4], children: &mut [u32], path: &[u8]| {
                // println!("aggregate path=\"{}\", children={children:?}", String::from_utf8_lossy(path));
                let sum = children.into_iter().fold(0, |sum, child| sum + *child);
                if path.len() > 0 {
                    sum + 1
                } else {
                    sum
                }
            };

            //Test both the jumping and non-jumping versions
            let sum = zip.clone().into_cata_side_effect(map_f, collapse_f, alg_f);
            assert_eq!(sum, expected_sum_ordinary);

            let sum = zip.into_cata_jumping_side_effect(map_f, collapse_f, alg_f, |_subpath, w, _path| w);
            assert_eq!(sum, expected_sum_jumping);
        }
    }

}
