# compact-rc
Low-memory reference-counting pointers.

The types in this crate have almost the same methods as standard `Rc`.
The differences from the standard type is as follows:

- Weak reference functionalities are not provided.
- Small integers can be used as reference counter.

Due to the differences, some methods such as `weak_count` are not provided.

# Sample code
```rust
use compact_rc::Rc8;

fn main() {
    // rc1 is a pointer containing i8 value with u8 refcount.
    let rc1: Rc8<i8> = Rc8::new(100);

    assert_eq!(Rc8::strong_count(&rc1), 1);
    assert_eq!(*rc1, 100);

    // Increment the refcount.
    // The value is shared by rc1 and rc2.
    let rc2 = rc1.clone();

    assert_eq!(Rc8::strong_count(&rc1), 2);
    assert_eq!(Rc8::strong_count(&rc2), 2);
    assert_eq!(*rc1, 100);
    assert_eq!(*rc2, 100);
}
```
