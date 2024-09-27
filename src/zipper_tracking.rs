
/// Tracks the root path of each zipper, to check for violations against all other outstanding zipper paths.
/// See [ByteTrieMap::write_zipper_at_exclusive_path_unchecked].
#[cfg(debug_assertions)]
#[derive(Default)]
pub(crate) struct ZipperTracker {
    all_paths: std::sync::Arc<ZipperPaths>,
    this_path: Vec<u8>,
    is_tracking: IsTracking,
}

/// A shared registry of every outstanding zipper
#[cfg(debug_assertions)]
#[derive(Default)]
struct ZipperPaths {
    read_zippers: std::sync::RwLock<Vec<Vec<u8>>>,
    write_zippers: std::sync::RwLock<Vec<Vec<u8>>>
}

#[cfg(debug_assertions)]
#[derive(Debug, Default)]
enum IsTracking {
    #[default]
    Map,
    WriteZipper,
    ReadZipper,
}

#[cfg(debug_assertions)]
impl core::fmt::Debug for ZipperTracker {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        let _ = writeln!(f, "ZipperTracker {{ type = {:?}, path = {:?}", self.is_tracking, self.this_path);
        let _ = writeln!(f, "\tRead Zippers:");
        for rz in self.all_paths.read_zippers.read().unwrap().iter() {
            let _ = writeln!(f, "\t\t{rz:?}");
        }
        let _ = writeln!(f, "\tWrite Zippers:");
        for wz in self.all_paths.write_zippers.read().unwrap().iter() {
            let _ = writeln!(f, "\t\t{wz:?}");
        }
        write!(f, "}}")
    }
}

#[cfg(debug_assertions)]
impl ZipperTracker {
    pub fn new_write_path(&self, path: &[u8]) -> Self {
        let read_paths_lock = self.all_paths.read_zippers.read().unwrap();
        let mut write_paths_lock = self.all_paths.write_zippers.write().unwrap();
        for existing_path in read_paths_lock.iter().chain(write_paths_lock.iter()) {
            if existing_path.starts_with(path) || existing_path.len() == 0 {
                panic!("Illegal WriteZipper at {path:?} conflicts with existing zipper at {existing_path:?}");
            }
        }
        write_paths_lock.push(path.to_vec());
        Self{
            all_paths: self.all_paths.clone(),
            this_path: path.to_vec(),
            is_tracking: IsTracking::WriteZipper,
        }
    }
    pub fn new_read_path(&self, path: &[u8]) -> Self {
        let mut read_paths_lock = self.all_paths.write_zippers.write().unwrap();
        for existing_path in read_paths_lock.iter() {
            if existing_path.starts_with(path) || existing_path.len() == 0 {
                panic!("Illegal ReadZipper at {path:?} conflicts with existing WriteZipper at {existing_path:?}");
            }
        }
        read_paths_lock.push(path.to_vec());
        Self{
            all_paths: self.all_paths.clone(),
            this_path: path.to_vec(),
            is_tracking: IsTracking::ReadZipper,
        }
    }
    pub fn new_read_path_no_check(&self, path: &[u8]) -> Self {
        self.all_paths.read_zippers.write().unwrap().push(path.to_vec());
        Self{
            all_paths: self.all_paths.clone(),
            this_path: path.to_vec(),
            is_tracking: IsTracking::ReadZipper,
        }
    }
}

#[cfg(debug_assertions)]
impl Drop for ZipperTracker {
    fn drop(&mut self) {
        match self.is_tracking {
            IsTracking::Map => {},
            IsTracking::WriteZipper => {
                self.all_paths.write_zippers.write().unwrap().retain(|path| *path != self.this_path);
            },
            IsTracking::ReadZipper => {
                self.all_paths.read_zippers.write().unwrap().retain(|path| *path != self.this_path);
            }
        }
    }
}

//===---***---===---***---===---***---===---***---===---***---===---***---===---***---===---***---===
// Release Build no-op
//===---***---===---***---===---***---===---***---===---***---===---***---===---***---===---***---===

#[cfg(not(debug_assertions))]
#[derive(Default)]
pub(crate) struct ZipperTracker(());

#[cfg(not(debug_assertions))]
impl ZipperTracker {
    #[inline]
    pub fn new_write_path(&self, _path: &[u8]) -> Self { Self(()) }
    #[inline]
    pub fn new_read_path(&self, _path: &[u8]) -> Self { Self(()) }
    #[inline]
    pub fn new_read_path_no_check(&self, _path: &[u8]) -> Self { Self(()) }
}
