
use crate::trie_node::*;
use crate::zipper::*;

/// A borrowed read-only reference to a location in a trie
///
/// `TrieRef`s are like read-only [Zipper]s that can't move, but are very cheap to create.
#[derive(Clone, Copy)]
pub struct TrieRef<'a, V> {
    node_ref: &'a TrieNodeODRc<V>,
    val_ref: Option<&'a V>
}

impl<'a, V> TrieRef<'a, V> {
    /// Internal constructor
    pub(crate) fn new(node_ref: &'a TrieNodeODRc<V>, val_ref: Option<&'a V>) -> Self {
        Self {node_ref, val_ref}
    }
}

