
# Discussion on Map Root Values, get_value, set_value, and Zippers

Quite a lot of complexity (and a not-insignificant cost) comes from the outgrowth of the [`set_value`] / [`get_value`] API on [`PathMap`] and the zipper types.  This is because it is possible to call them with a zero-length path or with the zipper focus positioned at the root.

Conceptually the PathMap abstracts a `[CoFree; 256]` at each byte in the map.  Which means there is no conceptual location for a root value.  In the implementation it means each PathMap structure also needs to hold and `Option<V>` in addition to a root node, and each [`Zipper`] type needs to have a pointer to the root value in addition to the root node.

This means `PathMap` structures are bigger in memory and zippers are more expenseive to create, not to mention all the special case code paths dealing with root values.

Older versions of the code had the concept of rooted and un-rooted zippers, but this was a perennial foot gun and only partially addressed the problem.  It became unworkable with the introduction of the ZipperHead API, and was ultimately removed.

## Alternative

As with many tradeoffs in software, making something simpler in one place often pushes the complexity elsewhere, and this situation is no exception.

So, let's explore what would be involved getting rid of the `root_value` (which I am taking as an assumption a priori has very little actual utility beyond making the API behave in a consistent and useable way)

Beginning with the API, firstly we would need to change the `get_value` / `set_value` zipper methods to require a path (or at least a byte), as opposed to simply operating on the focus.  A zero-length path would need to be disallowed and become a usage error leading to an immediate panic.

But we still need to be able to access a value at every location in the trie (save the absolute map root).  So we would do this by positioning the zipper's focus one level above the location the user needs to access.

But what how does the user access a value at the root of a zipper (not the map root, but a zipper rooted from a path within the map)?  The zipper would need to be lifted up one byte, but the same problem exists at that level too.

This becomes tricky when the the [`ZipperHead`] assigns exclusive paths to zippers.  The only way this can work is if multiple zippers are allowed to be positioned at the same focus path, but able to access exclusive (disjoint) sub-paths below that focus.

A simplification of that idea is that a given zipper is allowed to access one and only one specific byte below its root position.  This solves the problem, but leads to questions around the correct behavior of the `child_mask` API, and what should happen if the client attemps to modify an invalid path relative to the zipper's root.

This still may be preferable to the currently-implemented design however, as it's a more faithful abstraction of the underlying structure and leads to a tighter fast-path
