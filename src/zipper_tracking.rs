
use core::cell::RefCell;

/// Tracks the root paths of every outstanding zipper, to check for violations with the
/// [ByteTrieMap::write_zipper_at_exclusive_path_unchecked] API.
#[derive(Default)]
struct ZipperPaths {
    read_zippers: RefCell<Vec<Vec<u8>>>,
    write_zippers: RefCell<Vec<Vec<u8>>>
}

#[cfg(debug_assertions)]
#[derive(Default)]
pub(crate) struct ZipperTracker {
    all_paths: std::rc::Rc<ZipperPaths>,
    this_path: Vec<u8>,
    is_tracking: IsTracking,
}

#[derive(Default)]
enum IsTracking {
    #[default]
    Map,
    WriteZipper,
    ReadZipper,
}

#[cfg(debug_assertions)]
impl ZipperTracker {
    pub fn new_write_path(&self, path: &[u8]) -> Self {
        for existing_path in self.all_paths.read_zippers.borrow().iter().chain(self.all_paths.write_zippers.borrow().iter()) {
            if existing_path.starts_with(path) || existing_path.len() == 0 {
                panic!("Illegal WriteZipper at {path:?} conflicts with existing zipper at {existing_path:?}");
            }
        }
        self.all_paths.write_zippers.borrow_mut().push(path.to_vec());
        Self{
            all_paths: self.all_paths.clone(),
            this_path: path.to_vec(),
            is_tracking: IsTracking::WriteZipper,
        }
    }
    pub fn new_read_path(&self, path: &[u8]) -> Self {
        for existing_path in self.all_paths.write_zippers.borrow().iter() {
            if existing_path.starts_with(path) || existing_path.len() == 0 {
                panic!("Illegal ReadZipper at {path:?} conflicts with existing WriteZipper at {existing_path:?}");
            }
        }
        self.new_read_path_no_check(path)
    }
    pub fn new_read_path_no_check(&self, path: &[u8]) -> Self {
        self.all_paths.read_zippers.borrow_mut().push(path.to_vec());
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
                let idx = self.all_paths.write_zippers.borrow().iter().position(|path| *path == self.this_path).unwrap();
                self.all_paths.write_zippers.borrow_mut().remove(idx);
            },
            IsTracking::ReadZipper => {
                let idx = self.all_paths.read_zippers.borrow().iter().position(|path| *path == self.this_path).unwrap();
                self.all_paths.read_zippers.borrow_mut().remove(idx);
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
    pub fn new_write_path(&self, path: &[u8]) -> Self { Self(()) }
    #[inline]
    pub fn new_read_path(&self, path: &[u8]) -> Self { Self(()) }
    #[inline]
    pub fn new_read_path_no_check(&self, path: &[u8]) -> Self { Self(()) }
}
