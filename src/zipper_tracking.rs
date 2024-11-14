use std::sync::Arc;
use std::sync::RwLock;

/// Tracks the root path of each zipper, to check for violations against all other outstanding zipper paths.
/// See [ZipperHead::write_zipper_at_exclusive_path_unchecked].
pub(crate) struct ZipperTracker {
    all_paths: SharedTrackerPaths,
    this_path: Vec<u8>,
    is_tracking: IsTracking,
}

impl Clone for ZipperTracker {
    fn clone(&self) -> Self {
        match self.is_tracking {
            IsTracking::ReadZipper => {
                Self::new_read_tracker_no_check(self.all_paths.clone(), &self.this_path[..])
            },
            IsTracking::None => { Self{
                all_paths: self.all_paths.clone(),
                this_path: vec![],
                is_tracking: IsTracking::None,
            } },
            IsTracking::WriteZipper => { unreachable!() }, //Write Zipper should *never* be cloned
        }
    }
}

#[derive(Clone, Default)]
pub(crate) struct SharedTrackerPaths(Arc<RwLock<ZipperPaths>>);

/// A shared registry of every outstanding zipper
#[derive(Default)]
pub(crate) struct ZipperPaths {
    read_zippers: Vec<Vec<u8>>,
    write_zippers: Vec<Vec<u8>>
}

#[derive(Debug, Default)]
enum IsTracking {
    #[default]
    None,
    WriteZipper,
    ReadZipper,
}

impl core::fmt::Debug for ZipperTracker {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        let all_paths = self.all_paths.0.read().unwrap();
        let _ = writeln!(f, "ZipperTracker {{ type = {:?}, path = {:?}", self.is_tracking, self.this_path);
        let _ = writeln!(f, "\tRead Zippers:");
        for rz in all_paths.read_zippers.iter() {
            let _ = writeln!(f, "\t\t{rz:?}");
        }
        let _ = writeln!(f, "\tWrite Zippers:");
        for wz in all_paths.write_zippers.iter() {
            let _ = writeln!(f, "\t\t{wz:?}");
        }
        write!(f, "}}")
    }
}

impl ZipperTracker {
    pub fn new_write_tracker(shared_paths: SharedTrackerPaths, path: &[u8]) -> Self {
        let mut shared_paths_guard = shared_paths.0.write().unwrap();
        for existing_path in shared_paths_guard.read_zippers.iter().chain(shared_paths_guard.write_zippers.iter()) {
            if existing_path.starts_with(path) || existing_path.len() == 0 {
                panic!("Illegal WriteZipper at {path:?} conflicts with existing zipper at {existing_path:?}");
            }
        }
        shared_paths_guard.write_zippers.push(path.to_vec());
        drop(shared_paths_guard);
        Self{
            all_paths: shared_paths,
            this_path: path.to_vec(),
            is_tracking: IsTracking::WriteZipper,
        }
    }
    pub fn new_read_tracker(shared_paths: SharedTrackerPaths, path: &[u8]) -> Self {
        let mut shared_paths_guard = shared_paths.0.write().unwrap();
        for existing_path in shared_paths_guard.write_zippers.iter() {
            if existing_path.starts_with(path) || existing_path.len() == 0 {
                panic!("Illegal ReadZipper at {path:?} conflicts with existing WriteZipper at {existing_path:?}");
            }
        }
        shared_paths_guard.read_zippers.push(path.to_vec());
        drop(shared_paths_guard);
        Self{
            all_paths: shared_paths,
            this_path: path.to_vec(),
            is_tracking: IsTracking::ReadZipper,
        }
    }
    pub fn new_read_tracker_no_check(shared_paths: SharedTrackerPaths, path: &[u8]) -> Self {
        let mut shared_paths_guard = shared_paths.0.write().unwrap();
        shared_paths_guard.read_zippers.push(path.to_vec());
        drop(shared_paths_guard);
        Self{
            all_paths: shared_paths,
            this_path: path.to_vec(),
            is_tracking: IsTracking::ReadZipper,
        }
    }
    /// Takes the contents of `self`, replacing it with an empty tracker, and returning the original tracker.
    /// Used to transplant the tracker from one zipper to another.
    pub fn take(&mut self) -> Self {
        let mut taken_tracker = Self {
            all_paths: self.all_paths.clone(),
            this_path: vec![],
            is_tracking: IsTracking::None,
        };
        core::mem::swap(&mut taken_tracker, self);
        taken_tracker
    }
    //GOAT, it seems we may not need this method after all, because forked ReadZippers never need to be
    // tracked, because they always exist within the footprint of their parent's permissions
    // /// Makes a ReadTracker from an existing tracker.  The source can be a WriteTracker or a ReadTracker
    // pub fn clone_read_tracker(&self, path: &[u8]) -> Self {
    //     debug_assert!(path.starts_with(&self.this_path));
    //     Self::new_read_tracker_no_check(self.all_paths.clone(), path)
    // }
}

impl Drop for ZipperTracker {
    fn drop(&mut self) {
        match self.is_tracking {
            IsTracking::WriteZipper => {
                let mut guard = self.all_paths.0.write().unwrap();
                let idx = guard.write_zippers.iter().position(|path| *path == self.this_path).unwrap();
                guard.write_zippers.remove(idx);
            },
            IsTracking::ReadZipper => {
                let mut guard = self.all_paths.0.write().unwrap();
                let idx = guard.read_zippers.iter().position(|path| *path == self.this_path).unwrap();
                guard.read_zippers.remove(idx);
            }
            IsTracking::None => { }
        }
    }
}
