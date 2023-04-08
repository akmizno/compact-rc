# compact-rc
Low-memory reference-counting pointers.

The types in this crate have almost the same as `std::rc::Rc`.
The differences from the standard `Rc` are as follows:

- Smaller counters like `u8` can be used.
- Weak references are not provided.

Due to the differences, some methods such as `new_cyclic` are not provided.
