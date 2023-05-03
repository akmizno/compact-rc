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

    /// Checks a value equals to one.
    fn is_one(val: &Self::Value) -> bool;

    /// Gets a current value.
    fn load(&self) -> Self::Value;

    /// Increments its value and returns previous value.
    fn fetch_inc(&self) -> Self::Value;

    /// Decrements its value and returns previous value.
    fn fetch_dec(&self) -> Self::Value;
}

/// Implement RefCount for Cell<$type>.
/// Its implementors are used as single-threaded refcount.
macro_rules! impl_cell_counter {
    ($type:ty) => {
        impl RefCount for Cell<$type> {
            type Value = $type;

            fn one() -> Self {
                Self::new(1)
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
                let c = current - 1;
                self.set(c);
                current
            }
        }
    };
}

impl_cell_counter!(u8);
impl_cell_counter!(u16);
impl_cell_counter!(u32);
impl_cell_counter!(u64);
impl_cell_counter!(usize);

/// Implement RefCount for atomic $types.
/// Its implementors are used as multi-threaded refcount.
macro_rules! impl_atomic_counter {
    ($type:ty, $value_type:ty) => {
        impl RefCount for $type {
            type Value = $value_type;

            fn one() -> Self {
                Self::new(1)
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

impl_atomic_counter!(AtomicU8, u8);
impl_atomic_counter!(AtomicU16, u16);
impl_atomic_counter!(AtomicU32, u32);
impl_atomic_counter!(AtomicU64, u64);
impl_atomic_counter!(AtomicUsize, usize);
