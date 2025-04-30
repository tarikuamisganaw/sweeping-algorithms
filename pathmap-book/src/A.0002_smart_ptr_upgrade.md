
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

**NOTE(igorm)**: Storing refcounts separately from the node itself requires storing an additional
pointer (or an index at minimum) for each child.
My prediction is that any savings from storing it separately will be offset by increasing node or child size by including this pointer. Additionally, it might be difficult to store a freelist of refcounts.
We can experiment on this, not sure how it goes.
**LP**: That's certainly not the design I intended to suggest.  A design where a node could point at any arbitrary refcount-storage object, and thus required a pointer, would indeed be very silly.  The design I had in mind would infer the location of the refcount from the node location or pointer.  For example, one idea is to store all refcounts in a section at the head of each NodeBlock.

### Nice to Have, but Ok if it's not possible

* Clean separation between node format code and resource management code.

## Proposal: Node Regions

Structures to own nodes and track dependencies.  A node region is a *logical* object responsible for node lifetimes.

### Features Enabled by Node Regions

* It should be possible to mmap a file containing nodes, and work with those nodes directly, and create new nodes in the same file if the file is writable.

* It should also be possible to create new nodes in memory (not backed by a file) that reference nodes from a file. (For example a map that stores intermediate results)

* It should be possible to copy nodes from memory to a file, and from a file to memory.

**NOTE(igorm)**: what happens if we try to copy in-memory nodes that reference nodes on file?
**LP**: It depends on where we are copying them to (The destination region).  Before going through all the cases, I want to be clear on the distinction between copy (deep copy) and graft (create shallow reference).  I also want to establish that I see node region dependencies as being transitive.  i.e. if A depends on B, and B depends on C, then A also inherits a dependency on C.

The algorithm must proceed recursively from the source node.  Each time a node that resides in a region that is part of the destination region's dependencies is encountered, a simple reference is enough.  However if the node resiges in a foreign region (not in the dest region's dependencies) then a deep copy is needed, to copy the node to the destination region.

In the shallow graft-by-reference case, no recursive descent is needed.  When a deep copy occurs, each child node is visited and, depending on where it resides, it is either referenced or copied.

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

Internal links, linking nodes within the node block to other nodes within the same block, could take the form of simple indices, as there may be no need to bump the refcount, and can be heavily compressed; perhaps 8 bits would be enough to describe any value, external link, or internal node within a 4K block.

**NOTE(igorm)**: there's an alternative that we can we pursue: use a custom allocator in each node region, which would be transparent over the API. i.e. allocate a specific node type.
As for having pointers within blocks, I don't know a good strategy (and I don't know if it exists) to separate nodes into blocks, such that they're densely linked to each other.
I'd have to find/make an algorithm to see if this is even possible.
Intuitively, it seems the *optimal* distribution of nodes is NP-hard,
greedy solutions are potentially many times worse, and maintaining the distribution of nodes while editing the tree/graph (specifically adding+removing nodes) is an unsolved problem.

> ...use a custom allocator in each node region.
**LP**: I did several days worth of work on an ultimately abandoned a custom allocator at the beginning of this year.  I had 2 reasons for leaving it.  A. the rust allocator API isn't stable, and it's actually churning pretty rapidly.  For example the [allocator-api2](https://crates.io/crates/allocator-api2) crate is kinda bit rotten already.  But the bigger reason was B. I felt like the custom allocator approach only solved some of the problems / features outlined in this document, and avoiding the memory allocator paradigm altogether is probably where we want to get to to ultimately achieve all of the features.

> I don't know a good strategy...
**LP**: I'll diagram up what I have in mind and we can discuss where it might fail.  We don't need *optimal*, just good enough, and we have an existence proof in the system allocator (or jemalloc) that something workable is possible.  The other point is that usage patterns will play a big role in efficiency.  It will certainly be possible to fragment the node blocks badly.  Especially when we layer in the requirement for atomic updating and robustness against write failure.

> maintaining the distribution of nodes while editing the tree/graph (specifically adding+removing nodes) is an unsolved problem
**LP**: This will be partially ameliorated by in-memory regions.  This lets the implementation skip the writing of a lot of the intermediate work.  It is certainly still a problem that requires careful consideration.  I think there are a lot of good ideas in the design of [LMDB](https://en.wikipedia.org/wiki/Lightning_Memory-Mapped_Database)

### Open Questions

* Do refcounts live with node blocks, or somewhere else?  If they live with node blocks, how do we make sure that circular references between blocks don't prevent deallocation?

**NOTE(igorm)**: I think this is not possible to do (1) using purely reference counting (2) FAST (3) in generic case.
The alternative is to have a garbage collector of some sort.

Let's look at the following tree:

```
a - b - c
  \ d - e
```

if you have references to `c,d`, `b,e`, and graft `d` onto `c`, then `b` onto `e`,
this will create the following graph:

```
a - b - c
 \    X
  \ d - e
```

which has a circular path `abedc(b)`. It seems to me that detecting this loop is not possible without visiting all subtrees of `b` and `d` when they get grafted.

**LP**: Circular references at the node level are illegal, so this is not a problem.  Without that behavior we could get infinite paths, and break our isolation guarantees, and a bunch of other horrible things.  So, if you performed those operations described above, here is what would happen...

> graft `d` onto `c`
This leads to:
```
a - b - c
 \    /
  \ d - e
```
> then `b` onto `e`
Will cause a copy-on-write of `d` and `e`, leading to"
```
a - b - c - d - e
 \   ^------<.
  \ d' - e' -^
```
My fear of circular references was referring to circularity at the node-block level.  Although I think there is a credit scheme that can fix this too.  Although I haven't fully thought it through yet.

**LP**: For resource management, we may well want something that looks more like a GC than straight reference counts.  However, we will still need the refcounts on the nodes (or at least an atomic `is_shared` field) because that is a critical part of the copy-on-write semantic used to maintain structural sharing in the trie.  Before writing off refcounts entirely, 

### Proposal for action

1) We need a set of benchmarks *and* metrics to optimize for.
   Mork has a few benchmarks, and it would be nice to include some which measure deallocation.
2) As for additional metrics, we could measure the memory per node/path.
3) We can implement a set of cheap experiments:
  - replace global allocator with never-freeing allocator
    * What will we learn from this experiment?  Are you thinking you want to separate how much of the time spent in cleanup is time spent with refcount check-and-decrement, vs. how much is simply freeing the allocations?

    Many of the more complex tests and benchmarks will `forget` the maps.  And it does result in instant "cleanup".  However if we implement a NodeBlock approach, we get both centralized refcounts and big contiguous allocations, so it will cut both costs.
  - replace `Arc` with `Asc`
    * `Asc` is probably worth a test.  I did a prototype last year based on [triomphe](https://crates.io/crates/triomphe), and it actually got slower in spite of losing the weak counts, likely because of some of the pointer metadata not being available without the unstable APIs.

    My main hesitation here was just that I felt like addressing all the issues holistically is going to ultimately be less work and lead to a simpler and better-factored system.  For example the `ODRc` is an `&dyn` ptr, but I think there are probably only 8 or 16 different node types we actually need to support, so I think we can probably find 3 or 4 bits out of the 64 to use as a tag.  What we definitely don't want to do is a double-indirection (i.e. `&TaggedNodeRef`), so moving away from `&dyn` should happen at the same time as moving to a different smart-pointer type.
  - track allocated memory and created nodes, see the distribution
    * Right.  I'm imagining different `NodeBlock` formats will exist for different purposes.  We could even support native `NodeBlock` formats for some data file formats (not JSON because it doesn't contain lengths and offsets, but maybe [beve](https://github.com/beve-org/beve))
  - record profiling information during benchmarks and see differences
    * 100% agreed.  The `counters` feature provides a bit of that.  It's pretty ad-hoc and gets dusted off for each experiment when we want to run it.  But I'm definitely open to creating more tools and a better framework for the tools we want.
4) instead of having refcounting, we could have a GC of some sort.
  * Yes.  This is an option we shouldn't discount.
