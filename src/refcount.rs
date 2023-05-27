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

            #[inline]
            fn one() -> Self {
                Self::new(1)
            }

            #[inline]
            fn is_one(val: &Self::Value) -> bool {
                *val == 1
            }

            #[inline]
            fn load(&self) -> Self::Value {
                self.get()
            }

            #[inline]
            fn fetch_inc(&self) -> Self::Value {
                let count = self.load();
                assume!(count != 0);
                match count.checked_add(1) {
                    Some(c) => {
                        self.set(c);
                        count
                    }
                    None => std::process::abort(),
                }
            }

            #[inline]
            fn fetch_dec(&self) -> Self::Value {
                let count = self.load();
                assume!(0 < count);
                self.set(count - 1);
                count
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

            #[inline]
            fn one() -> Self {
                Self::new(1)
            }

            #[inline]
            fn is_one(val: &Self::Value) -> bool {
                *val == 1
            }

            #[inline]
            fn load(&self) -> Self::Value {
                self.load(Ordering::Acquire)
            }

            #[inline]
            fn fetch_inc(&self) -> Self::Value {
                let count = self.fetch_add(1, Ordering::AcqRel);
                if count == <$value_type>::MAX {
                    std::process::abort();
                }
                count
            }

            #[inline]
            fn fetch_dec(&self) -> Self::Value {
                let count = self.fetch_sub(1, Ordering::AcqRel);
                assume!(0 < count);
                count
            }
        }
    };
}

impl_atomic_refcount!(AtomicU8, u8);
impl_atomic_refcount!(AtomicU16, u16);
impl_atomic_refcount!(AtomicU32, u32);
impl_atomic_refcount!(AtomicU64, u64);
impl_atomic_refcount!(AtomicUsize, usize);
