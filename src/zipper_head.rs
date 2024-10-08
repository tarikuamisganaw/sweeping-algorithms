
use core::ptr::NonNull;
use core::cell::Cell;
use std::marker::PhantomData;
use crate::trie_node::*;
use crate::zipper::*;
use crate::zipper_tracking::*;

/// Used to make multiple simultaneous zippers in the same map
pub struct ZipperHead<'a, V> {
    root: Cell<NonNull<TrieNodeODRc<V>>>,
    zipper_tracker: ZipperTracker,
    _variance: PhantomData<&'a mut TrieNodeODRc<V>>
}

impl<'a, V: Clone + Send + Sync> ZipperHead<'a, V> {

    pub(crate) fn new(root: &'a mut TrieNodeODRc<V>) -> Self {
        Self {
            root: Cell::new(NonNull::from(root)),
            zipper_tracker: ZipperTracker::default(),
            _variance: PhantomData
        }
    }

    /// Creates a new [ReadZipper] with the specified path from the `ZipperHead`
    pub fn read_zipper_at_path<'k>(&self, path: &'k[u8]) -> ReadZipper<'a, 'k, V> {
        let zipper_tracker = self.zipper_tracker.new_read_path(path);
        let root = unsafe{ self.root.get().as_ref() };
        ReadZipper::new_with_node_and_path(root.borrow(), path.as_ref(), Some(path.len()), Some(zipper_tracker))
    }

    /// Creates a new [ReadZipper] with the specified path from the `ZipperHead`, where the caller
    /// guarantees that there will be no conflicts with any WriteZippers at any time in the future
    pub unsafe fn read_zipper_at_path_unchecked<'k>(&self, path: &'k[u8]) -> ReadZipper<'a, 'k, V> {
        let zipper_tracker = self.zipper_tracker.new_read_path_release_only(path);
        let root = unsafe{ self.root.get().as_ref() };
        ReadZipper::new_with_node_and_path(root.borrow(), path.as_ref(), Some(path.len()), zipper_tracker)
    }

    //GOAT, there may be no point to this API method
    // /// Creates a new [WriteZipper] starting at the root of the `ZipperHead``
    // pub fn root_write_zipper(&mut self) -> WriteZipper<V> {
    //     let zipper_tracker = self.zipper_tracker.new_write_path(&[]);
    //     let root = unsafe{ self.root.get().as_mut() };
    //     WriteZipper::new_with_node_and_path_internal(root, &[], true, Some(zipper_tracker))
    // }

    /// Creates a new [WriteZipper] with the specified path from the `ZipperHead`
    pub fn write_zipper_at_exclusive_path<'k, K: AsRef<[u8]>>(&self, path: K) -> WriteZipper<'a, 'k, V> {
        let path = path.as_ref();
        let zipper_tracker = self.zipper_tracker.new_write_path(path);
        let root = unsafe{ self.root.get().as_mut() };
        let (_created_node, zipper_root_node) = prepare_exclusive_write_path(root, &path);
        //GOAT QUESTION: Do we want to pay for pruning the parent of a zipper when the zipper get's dropped?
        // If we do, we can store (_created_node || _created_cf) in the zipper, so we can opt out of trying
        // to prune the zipper's path.

        let zipper = WriteZipper::new_with_node_and_path_internal(zipper_root_node, &[], false, Some(zipper_tracker));
        zipper
    }

    /// Creates a new [WriteZipper] with the specified path from the `ZipperHead`, where the caller guarantees
    /// that no existing zippers may access the specified path at any time before the `WriteZipper` is dropped
    pub unsafe fn write_zipper_at_exclusive_path_unchecked<'k, K: AsRef<[u8]>>(&self, path: K) -> WriteZipper<'a, 'k, V> {
        let path = path.as_ref();
        //GOAT, there may be no point to this
        // let path_len = path.len();
        // if path_len == 0 {
        //     panic!("Illegal Operation: WriteZipper can't be created at the root of a ZipperHead without mutable access.  Use ZipperHead::root_write_zipper instead.");
        // }
        let zipper_tracker = self.zipper_tracker.new_write_path_release_only(path);
        let root = unsafe{ self.root.get().as_mut() };
        let (_created_node, zipper_root_node) = prepare_exclusive_write_path(root, &path);
        //GOAT QUESTION: Do we want to pay for pruning the parent of a zipper when the zipper get's dropped?
        // If we do, we can store (_created_node || _created_cf) in the zipper, so we can opt out of trying
        // to prune the zipper's path.

        let zipper = WriteZipper::new_with_node_and_path_internal(zipper_root_node, &[], false, zipper_tracker);
        zipper
    }
}

#[cfg(test)]
mod tests {
    use std::{thread, thread::ScopedJoinHandle};
    use crate::tests::prefix_key;
    use crate::trie_map::BytesTrieMap;
    use crate::zipper::{Zipper, WriteZipper};

    #[test]
    fn parallel_insert_test() {
        let thread_cnt = 8;
        let elements = 1024;
        let elements_per_thread = elements / thread_cnt;

        let mut map = BytesTrieMap::<usize>::new();

        thread::scope(|scope| {
            let elements_per_thread = elements / thread_cnt;

            //Preallocate all zippers
            let zipper_head = map.zipper_head();
            let mut zippers: Vec<WriteZipper<usize>> = Vec::with_capacity(thread_cnt);
            for n in (0..thread_cnt).into_iter().rev() {
                let path = &[n as u8];
                let zipper = unsafe{ zipper_head.write_zipper_at_exclusive_path_unchecked(path) };
                zippers.push(zipper);
            };

            let mut threads: Vec<ScopedJoinHandle<()>> = Vec::with_capacity(thread_cnt);

            //Spawn all the threads
            for n in 0..thread_cnt {
                let mut zipper = zippers.pop().unwrap();
                let thread = scope.spawn(move || {
                    for i in (n * elements_per_thread)..((n+1) * elements_per_thread) {
                        zipper.descend_to(prefix_key(&(i as u64)));
                        assert!(zipper.set_value(i).is_none());
                        zipper.reset();
                    }
                });
                threads.push(thread);
            }

            //Wait for the threads to finish
            for thread in threads {
                thread.join().unwrap();
            }
        });

        //Test that the values set by the threads are correct
        for n in 0..thread_cnt {
            for i in (n * elements_per_thread)..((n+1) * elements_per_thread) {
                let mut path = vec![n as u8];
                path.extend(prefix_key(&(i as u64)));
                assert_eq!(map.get(path), Some(&i));
            }
        }
    }
}

//GOAT, TODO, make a test for hierarchical ZipperHeads