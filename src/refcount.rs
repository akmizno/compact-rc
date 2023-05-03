use std::cell::Cell;
use std::sync::atomic::{AtomicU16, AtomicU32, AtomicU64, AtomicU8, AtomicUsize, Ordering};

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

/// Implement Counter for atomic $types.
/// Its implementors are used as multi-threaded refcount.
macro_rules! impl_atomic_counter {
    ($type:ty, $raw:ty) => {
        impl RefCount for $type {
            type Value = $raw;

            fn one() -> Self {
                Self::new(1)
            }

            fn count(&self) -> Self::Value {
                self.load(Ordering::Acquire)
            }

            fn is_one(&self) -> bool {
                self.count() == 1
            }

            fn inc(&self) {
                self.fetch_add(1, Ordering::AcqRel);
            }

            fn dec(&self) -> bool {
                self.fetch_sub(1, Ordering::AcqRel) == 1
            }
        }
    };
}

impl_atomic_counter!(AtomicU8, u8);
impl_atomic_counter!(AtomicU16, u16);
impl_atomic_counter!(AtomicU32, u32);
impl_atomic_counter!(AtomicU64, u64);
impl_atomic_counter!(AtomicUsize, usize);
