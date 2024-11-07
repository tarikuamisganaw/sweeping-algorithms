
# pathmap

This crate provides a key-value store with prefix compression, structural sharing, and powerful algebraic operations.

PathMap is optimized for large data sets and can be used efficiently in a multi-threaded environment.

## Getting Started

GOAT TODO!

For more details, check out the [book](GOAT! need to host somewhere)

## Optional Cargo features

- `jemalloc`: **Recommended** Enables [jemalloc](https://jemalloc.net/) as the default allocator.  This dramatically improves scaling for write-heavy workloads and is generally recommended.  The only reason it is not the default is to avoid interference with the host's application allocator.

Other cargo features in this crate are intended for use by the developers of `pathmap` itself.
