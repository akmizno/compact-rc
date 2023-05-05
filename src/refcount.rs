use std::cell::Cell;
use std::sync::atomic::{AtomicU16, AtomicU32, AtomicU64, AtomicU8, AtomicUsize, Ordering};

/// Trait for refcount
pub trait RefCount {
    /// Type of count
    type Value;

    /// Creates a new RefCount object.
    ///
    /// The object is initialized as "one".
    fn one() -> Self;

    /// Checks whether a value equals to one.
    fn is_one(val: &Self::Value) -> bool;

    /// Gets a current value.
    fn load(&self) -> Self::Value;

    /// Increments its value and returns previous value.
    fn fetch_inc(&self) -> Self::Value;

    /// Decrements its value and returns previous value.
    fn fetch_dec(&self) -> Self::Value;
}

/// Implements RefCount for Cell<$type>.
/// Its implementors are used as single-threaded refcount.
macro_rules! impl_cell_refcount {
    ($type:ty) => {
        impl RefCount for Cell<$type> {
            type Value = $type;

            fn one() -> Self {
                let one = Self::new(1);
                debug_assert!(Self::is_one(&one.load()));
                one
            }

            fn is_one(val: &Self::Value) -> bool {
                *val == 1
            }

            fn load(&self) -> Self::Value {
                self.get()
            }

            fn fetch_inc(&self) -> Self::Value {
                let current = self.load();
                assume!(current != 0);
                match current.checked_add(1) {
                    Some(c) => {
                        self.set(c);
                        current
                    }
                    None => std::process::abort(),
                }
            }

            fn fetch_dec(&self) -> Self::Value {
                let current = self.load();
                assume!(0 < current);
                self.set(current - 1);
                current
            }
        }
    };
}

impl_cell_refcount!(u8);
impl_cell_refcount!(u16);
impl_cell_refcount!(u32);
impl_cell_refcount!(u64);
impl_cell_refcount!(usize);

/// Implements RefCount for atomic $types.
/// Its implementors are used as multi-threaded refcount.
macro_rules! impl_atomic_refcount {
    ($type:ty, $value_type:ty) => {
        impl RefCount for $type {
            type Value = $value_type;

            fn one() -> Self {
                let one = Self::new(1);
                debug_assert!(Self::is_one(&RefCount::load(&one)));
                one
            }

            fn is_one(val: &Self::Value) -> bool {
                *val == 1
            }

            fn load(&self) -> Self::Value {
                self.load(Ordering::Acquire)
            }

            fn fetch_inc(&self) -> Self::Value {
                self.fetch_add(1, Ordering::AcqRel)
            }

            fn fetch_dec(&self) -> Self::Value {
                self.fetch_sub(1, Ordering::AcqRel)
            }
        }
    };
}

impl_atomic_refcount!(AtomicU8, u8);
impl_atomic_refcount!(AtomicU16, u16);
impl_atomic_refcount!(AtomicU32, u32);
impl_atomic_refcount!(AtomicU64, u64);
impl_atomic_refcount!(AtomicUsize, usize);
