use std::cell::Cell;

/// Trait for refcount
pub trait RefCount {
    /// Type of count
    type Value;

    /// Creates a new counter object.
    ///
    /// The object is initialized as "one".
    fn one() -> Self;

    /// Gets current refcount.
    fn count(&self) -> Self::Value;

    /// Returns true if current count is one.
    fn is_one(&self) -> bool;

    /// Increments refcount.
    fn inc(&self);

    /// Decrements refcount.
    ///
    /// Returns true if count after decrementation is zero, otherwise false.
    fn dec(&self) -> bool;
}

/// Implement Counter for Cell<$type>.
/// Its implementors are used as single-threaded refcount.
macro_rules! impl_cell_counter {
    ($type:ty) => {
        impl RefCount for Cell<$type> {
            type Value = $type;

            fn one() -> Self {
                Self::new(1)
            }

            fn count(&self) -> Self::Value {
                self.get()
            }

            fn is_one(&self) -> bool {
                self.count() == 1
            }

            fn inc(&self) {
                let count = self.count();
                assume!(count != 0);
                match count.checked_add(1) {
                    Some(c) => self.set(c),
                    None => std::process::abort(),
                }
            }

            fn dec(&self) -> bool {
                let count = self.count();
                assume!(count != 0);
                let c = count - 1;
                self.set(c);
                c == 0
            }
        }
    };
}

impl_cell_counter!(u8);
impl_cell_counter!(u16);
impl_cell_counter!(u32);
impl_cell_counter!(u64);
impl_cell_counter!(usize);
