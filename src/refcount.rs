use std::cell::Cell;
use std::sync::atomic::{AtomicU16, AtomicU32, AtomicU64, AtomicU8, AtomicUsize, Ordering};

/// Trait for refcount
///
/// Some method names explain required memory ordering in multi-threaded context.
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
    ///
    /// # Memory ordering
    /// [Acquire](std::sync::atomic::Ordering::Acquire) or stronger ordering is required if
    /// implementors are atomic types.
    fn load_acquire(&self) -> Self::Value;

    /// Memory fence.
    ///
    /// This method is needed only for multi-threaded refcount.
    /// In single-threaded implementors, this can be NO-OP.
    ///
    /// # Memory ordering
    /// [Acquire](std::sync::atomic::Ordering::Acquire) or stronger ordering is required if
    /// implementors are atomic types.
    fn fence_acquire(&self);

    /// Increments its value and returns previous value.
    ///
    /// # Memory ordering
    /// [Relaxed](std::sync::atomic::Ordering::Relaxed) ordering is allowed if implementors are
    /// atomic types.
    fn fetch_inc_relaxed(&self) -> Self::Value;

    /// Decrements its value and returns previous value.
    ///
    /// # Memory ordering
    /// [Release](std::sync::atomic::Ordering::Release) or stronger ordering is required if
    /// implementors are atomic types.
    fn fetch_dec_release(&self) -> Self::Value;
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
            fn load_acquire(&self) -> Self::Value {
                self.get()
            }

            #[inline(always)]
            fn fence_acquire(&self) {
                // noop
            }

            #[inline]
            fn fetch_inc_relaxed(&self) -> Self::Value {
                let count = self.load_acquire();
                assume!(count != 0);
                match count.checked_add(1) {
                    Some(c) => {
                        self.set(c);
                        count
                    }
                    None => std::process::abort(), // Overflow
                }
            }

            #[inline]
            fn fetch_dec_release(&self) -> Self::Value {
                let count = self.load_acquire();
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
            fn load_acquire(&self) -> Self::Value {
                self.load(Ordering::Acquire)
            }

            #[inline]
            fn fence_acquire(&self) {
                // Load-Acquire is used instead of a fence for performance[1].
                // [1] https://developer.arm.com/documentation/102336/0100/Load-Acquire-and-Store-Release-instructions
                let _count = self.load_acquire();
            }

            #[inline]
            fn fetch_inc_relaxed(&self) -> Self::Value {
                let count = self.fetch_add(1, Ordering::Relaxed);
                if count == <$value_type>::MAX {
                    // Overflow
                    std::process::abort();
                }
                count
            }

            #[inline]
            fn fetch_dec_release(&self) -> Self::Value {
                let count = self.fetch_sub(1, Ordering::Release);
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
