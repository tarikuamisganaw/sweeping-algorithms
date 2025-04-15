
# Discussion on Inter-Node References & Internal Resource Management

The [TrieNodeODRc](pathmap::trie_node::TrieNodeODRc) type is used for all inter-node links.  However it currently is just a `Arc<dyn TrieNode<V> + 'static>` and has a number of undesireable properties.

* It is a 128-bit fat pointer.  Links comprise a substantial amount of the in-memory footprint of the database, so shrinking this to 64 bits will be worth a lot.
* The `Arc` header in the node structure eats a further 16 bytes.  8 bytes for the weak count which is totally unused, and 8 bytes for the strong count, which probably has a lot more range than we need.
* Having each refcount separate on each node means we need to load the cache line for the node's header (which is often the whole node) into memory in order to check the refcount prior to freeing the node.  Sometimes this means freeing a trie is nearly as expensive as initializing it.
* There is no concept of availability that is separate from the refcount

Ideally we can solve all of these issues at the same time and lay the ground work for **persistence** (writable on-disk tries) at the same time.

## Desiderata

* Support for multiple (polymorphic) node data structures.
* Refcounts on each (inter-node) link, and maintain the "clone the pointer to increment the refcount" paradigm.
* Support for the `make_mut` copy-on-write pattern.  I.e. if a referenced node's refcount is 1, then allow mutation, otherwise clone the node to a new location for mutation.
* Support for multiple "node regions" in which nodes may be referenced and created. (More on node regions in its own section)
* Refcounts stored centrally so reading or modifying them doesn't thrash the cache.

### Nice to Have, but Ok if it's not possible

* Clean separation between node format code and resource management code.

## Proposal: Node Regions

Structures to own nodes and track dependencies.  A node region is a *logical* object responsible for node lifetimes.

### Features Enabled by Node Regions

* It should be possible to mmap a file containing nodes, and work with those nodes directly, and create new nodes in the same file if the file is writable.

* It should also be possible to create new nodes in memory (not backed by a file) that reference nodes from a file. (For example a map that stores intermediate results)

* It should be possible to copy nodes from memory to a file, and from a file to memory.

* It should be possible to work with multiple files at the same time, and potentially create in-memory structures that reference nodes in multiple files.

### Design Ideas for Node Regions

* Each node region is an object that handles its own resource management.  (Tracks all refcounts, Owns memory that stores all nodes).

* Some portion of a `TrieNodeODRc` smart pointer would point to a node region, and some other part of the pointer would identify the node within the region.

* A node region can have dependencies on other node regions, which are created when a graft or similar operation makes a cross-region node reference.  There is something like an `Arc` that keeps a region from deallocating / closing if one if its dependennt regions is still active.

* Node regions have properties that determine the behavior of operations that create references (graft-like operations).  For example, a file-backed region could not reference a node in a volatile memory region, so a graft-like operation would force a copy.  On the other hand a volatile in-memory region could reference a node in a file region.

## Proposal: Node Blocks

Structure that lays out multiple nodes in a contiguous block of memory.  A node block is a physical object.   A node region could use a single node block, or be composed of multiple node blocks.

A node block would have:
* Partial paths and node information for multiple nodes
* A table of owned values
* A table of external (links outside the node block) links

Internal links, linking nodes within the node block to other nodes within the same block, could take the form of internal links that don't need to bump the refcount, and can be heavily compressed (perhaps 8 bits would be enough to describe any value, external link, or internal node within a 4K block.

### Open Questions

* Do refcounts live with node blocks, or somewhere else?  If they live with node blocks, how do we make sure that circular references between blocks don't prevent deallocation?