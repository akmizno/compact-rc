use std::any::Any;
use std::borrow;
use std::borrow::Cow;
use std::cell::Cell;
use std::cmp::Ordering;
use std::fmt;
use std::hash::{Hash, Hasher};
use std::iter;
use std::ops::Deref;
use std::ops::Sub;
use std::panic::{RefUnwindSafe, UnwindSafe};
use std::pin::Pin;
use std::ptr::NonNull;

use num::{one, CheckedAdd, Unsigned};

pub trait MarkerCounter: Copy + CheckedAdd + Sub + Unsigned {}

impl MarkerCounter for u8 {}
impl MarkerCounter for u16 {}
impl MarkerCounter for u32 {}
impl MarkerCounter for u64 {}
impl MarkerCounter for usize {}

pub type Rc8<T> = RcX<T, u8>;
pub type Rc16<T> = RcX<T, u16>;
pub type Rc32<T> = RcX<T, u32>;
pub type Rc64<T> = RcX<T, u64>;
pub type Rc<T> = RcX<T, usize>;

// NOTE
// `std::rc::RcBox` uses #[repr(C)], but this does not.
// Some methods such as `into_raw` and `from_raw` can not be implemented
// because of field-reordering.
struct RcBox<T: ?Sized, C> {
    strong: Cell<C>,
    value: T,
}

impl<T: ?Sized, C: MarkerCounter> RcBox<T, C> {
    fn strong(&self) -> C {
        self.strong.get()
    }

    fn inc_strong(&self) {
        let count = self.strong();
        assume!(!count.is_zero());
        match count.checked_add(&one()) {
            Some(c) => self.strong.set(c),
            None => std::process::abort(),
        }
    }

    fn dec_strong(&self) {
        let count = self.strong();
        assume!(!count.is_zero());
        let c = count.sub(one());
        self.strong.set(c);
    }
}

pub struct RcX<T: ?Sized, C: MarkerCounter> {
    ptr: NonNull<RcBox<T, C>>,
}

impl<T: RefUnwindSafe + ?Sized, C: MarkerCounter> UnwindSafe for RcX<T, C> {}
impl<T: RefUnwindSafe + ?Sized, C: MarkerCounter> RefUnwindSafe for RcX<T, C> {}

impl<T: ?Sized, C: MarkerCounter> RcX<T, C> {
    fn inner(&self) -> &RcBox<T, C> {
        unsafe { self.ptr.as_ref() }
    }

    unsafe fn from_inner(ptr: NonNull<RcBox<T, C>>) -> Self {
        Self { ptr }
    }
}

impl<T, C: MarkerCounter> RcX<T, C> {
    /// See [std::rc::Rc::new].
    pub fn new(value: T) -> RcX<T, C> {
        unsafe {
            Self::from_inner(NonNull::from(Box::leak(Box::new(RcBox {
                strong: Cell::new(C::one()),
                value,
            }))))
        }
    }

    /// See [std::rc::Rc::pin].
    pub fn pin(_value: T) -> Pin<RcX<T, C>> {
        todo!();
    }

    /// See [std::rc::Rc::try_unwrap].
    pub fn try_unwrap(_this: Self) -> Result<T, Self> {
        todo!();
    }
}

impl<T: ?Sized, C: MarkerCounter> RcX<T, C> {
    /// See [std::rc::Rc::as_ptr].
    pub fn as_ptr(this: &Self) -> *const T {
        &**this
    }

    /// See [std::rc::Rc::strong_count].
    pub fn strong_count(this: &Self) -> C {
        this.inner().strong()
    }

    /// See [std::rc::Rc::get_mut].
    pub fn get_mut(_this: &mut Self) -> Option<&mut T> {
        todo!();
    }

    /// See [std::rc::Rc::ptr_eq].
    pub fn ptr_eq(_this: &Self, _other: &Self) -> bool {
        todo!();
    }
}

impl<T: Clone, C: MarkerCounter> RcX<T, C> {
    /// See [std::rc::Rc::make_mut].
    pub fn make_mut(_this: &mut Self) -> &mut T {
        todo!();
    }
}

impl<C: MarkerCounter> RcX<dyn Any, C> {
    /// See [std::rc::Rc::downcast].
    pub fn downcast<T: Any>(self) -> Result<RcX<T, C>, RcX<dyn Any, C>> {
        todo!();
    }
}

impl<T: ?Sized, C: MarkerCounter> Deref for RcX<T, C> {
    type Target = T;

    fn deref(&self) -> &T {
        &self.inner().value
    }
}

impl<T: ?Sized, C: MarkerCounter> Drop for RcX<T, C> {
    fn drop(&mut self) {
        self.inner().dec_strong();
        if self.inner().strong().is_zero() {
            unsafe {
                drop(Box::from_raw(self.ptr.as_mut()));
            }
        }
    }
}

impl<T: ?Sized, C: MarkerCounter> Clone for RcX<T, C> {
    fn clone(&self) -> RcX<T, C> {
        self.inner().inc_strong();
        unsafe { Self::from_inner(self.ptr) }
    }
}

impl<T: Default, C: MarkerCounter> Default for RcX<T, C> {
    fn default() -> RcX<T, C> {
        RcX::new(Default::default())
    }
}

impl<T: ?Sized + PartialEq, C: MarkerCounter> PartialEq for RcX<T, C> {
    fn eq(&self, other: &RcX<T, C>) -> bool {
        // NOTE
        // Optimization by comparing their addresses can not be used for T: PartialEq.
        // For T: Eq, it is possible. But the specialization is unstable feature.
        PartialEq::eq(&**self, &**other)
    }
    fn ne(&self, other: &RcX<T, C>) -> bool {
        PartialEq::ne(&**self, &**other)
    }
}

impl<T: ?Sized + Eq, C: MarkerCounter> Eq for RcX<T, C> {}

impl<T: ?Sized + PartialOrd, C: MarkerCounter> PartialOrd for RcX<T, C> {
    fn partial_cmp(&self, other: &RcX<T, C>) -> Option<Ordering> {
        PartialOrd::partial_cmp(&**self, &**other)
    }
}

impl<T: ?Sized + Ord, C: MarkerCounter> Ord for RcX<T, C> {
    fn cmp(&self, other: &RcX<T, C>) -> Ordering {
        Ord::cmp(&**self, &**other)
    }
}

impl<T: ?Sized + Hash, C: MarkerCounter> Hash for RcX<T, C> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        Hash::hash(&**self, state)
    }
}

impl<T: ?Sized + fmt::Display, C: MarkerCounter> fmt::Display for RcX<T, C> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Display::fmt(&**self, f)
    }
}

impl<T: ?Sized + fmt::Debug, C: MarkerCounter> fmt::Debug for RcX<T, C> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Debug::fmt(&**self, f)
    }
}

impl<T: ?Sized, C: MarkerCounter> fmt::Pointer for RcX<T, C> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Pointer::fmt(&(RcX::as_ptr(self)), f)
    }
}

impl<T, C: MarkerCounter> From<T> for RcX<T, C> {
    fn from(_t: T) -> Self {
        todo!();
    }
}

impl<T: Clone, C: MarkerCounter> From<&[T]> for RcX<[T], C> {
    fn from(_v: &[T]) -> RcX<[T], C> {
        todo!();
    }
}

impl<C: MarkerCounter> From<&str> for RcX<str, C> {
    fn from(_v: &str) -> RcX<str, C> {
        todo!();
    }
}

impl<C: MarkerCounter> From<String> for RcX<str, C> {
    fn from(_v: String) -> RcX<str, C> {
        todo!();
    }
}

impl<T: ?Sized, C: MarkerCounter> From<Box<T>> for RcX<T, C> {
    fn from(_v: Box<T>) -> RcX<T, C> {
        todo!();
    }
}

impl<T, C: MarkerCounter> From<Vec<T>> for RcX<[T], C> {
    fn from(mut _v: Vec<T>) -> RcX<[T], C> {
        todo!();
    }
}

impl<'a, B, C: MarkerCounter> From<Cow<'a, B>> for RcX<B, C>
where
    B: ToOwned + ?Sized,
    RcX<B, C>: From<&'a B> + From<B::Owned>,
{
    fn from(_cow: Cow<'a, B>) -> RcX<B, C> {
        todo!();
    }
}

impl<C: MarkerCounter> From<RcX<str, C>> for RcX<[u8], C> {
    fn from(_rc: RcX<str, C>) -> Self {
        todo!();
    }
}

impl<T, C: MarkerCounter, const N: usize> TryFrom<RcX<[T], C>> for RcX<[T; N], C> {
    type Error = RcX<[T], C>;

    fn try_from(_boxed_slice: RcX<[T], C>) -> Result<Self, Self::Error> {
        todo!();
    }
}

impl<T, C: MarkerCounter> iter::FromIterator<T> for RcX<[T], C> {
    fn from_iter<I: iter::IntoIterator<Item = T>>(_iter: I) -> Self {
        todo!();
    }
}

impl<T: ?Sized, C: MarkerCounter> borrow::Borrow<T> for RcX<T, C> {
    fn borrow(&self) -> &T {
        todo!();
    }
}

impl<T: ?Sized, C: MarkerCounter> AsRef<T> for RcX<T, C> {
    fn as_ref(&self) -> &T {
        todo!();
    }
}

impl<T: ?Sized, C: MarkerCounter> Unpin for RcX<T, C> {}

#[cfg(test)]
mod tests {
    use super::*;
    type StdRc<T> = std::rc::Rc<T>;

    #[test]
    fn new_deref() {
        let rc = Rc8::new(1);
        assert_eq!(*rc, 1);
    }

    #[test]
    fn clone_drop_strong_count() {
        let rc1 = Rc8::new(1);
        assert_eq!(RcX::strong_count(&rc1), 1);

        let rc2 = rc1.clone();
        assert_eq!(RcX::strong_count(&rc1), 2);
        assert_eq!(RcX::strong_count(&rc2), 2);
        assert_eq!(*rc1, 1);
        assert_eq!(*rc2, 1);

        drop(rc1);
        assert_eq!(RcX::strong_count(&rc2), 1);
        assert_eq!(*rc2, 1);
    }

    #[test]
    fn default() {
        let rc = Rc8::<String>::default();
        let stdrc = StdRc::<String>::default();

        assert_eq!(*rc, *stdrc);
    }

    #[test]
    fn debug() {
        let rc = Rc8::new("debug".to_string());
        let stdrc = StdRc::new("debug".to_string());

        assert_eq!(format!("{:?}", rc), format!("{:?}", stdrc));
    }

    #[test]
    fn display() {
        let rc = Rc8::new("debug".to_string());
        let stdrc = StdRc::new("debug".to_string());

        assert_eq!(format!("{}", rc), format!("{}", stdrc));
    }

    #[test]
    fn pointer() {
        let rc = Rc8::new("debug".to_string());

        assert_eq!(format!("{:p}", rc), format!("{:p}", RcX::as_ptr(&rc)));
    }

    #[test]
    fn as_ptr() {
        let rc = Rc8::<u32>::new(1);

        unsafe {
            assert_eq!(*RcX::as_ptr(&rc), 1);
        }
    }

    #[test]
    fn eq_ne() {
        let rc = Rc8::<u32>::new(1);
        let rc1 = Rc8::<u32>::new(1);
        let rc2 = Rc8::<u32>::new(2);

        assert_eq!(rc, rc1);
        assert_ne!(rc, rc2);
    }

    #[test]
    fn partial_cmp() {
        let rc = Rc8::<u32>::new(2);
        let rc1 = Rc8::<u32>::new(1);
        let rc2 = Rc8::<u32>::new(2);
        let rc3 = Rc8::<u32>::new(3);

        assert_eq!(
            PartialOrd::partial_cmp(&rc, &rc1),
            PartialOrd::partial_cmp(&2, &1)
        );
        assert_eq!(
            PartialOrd::partial_cmp(&rc, &rc2),
            PartialOrd::partial_cmp(&2, &2)
        );
        assert_eq!(
            PartialOrd::partial_cmp(&rc, &rc3),
            PartialOrd::partial_cmp(&2, &3)
        );
    }

    #[test]
    fn cmp() {
        let rc = Rc8::<u32>::new(2);
        let rc1 = Rc8::<u32>::new(1);
        let rc2 = Rc8::<u32>::new(2);
        let rc3 = Rc8::<u32>::new(3);

        assert_eq!(Ord::cmp(&rc, &rc1), Ord::cmp(&2, &1));
        assert_eq!(Ord::cmp(&rc, &rc2), Ord::cmp(&2, &2));
        assert_eq!(Ord::cmp(&rc, &rc3), Ord::cmp(&2, &3));
    }

    #[test]
    fn hash() {
        let rc = Rc8::new("hello".to_string());

        let mut h = std::collections::hash_map::DefaultHasher::default();
        Hash::hash(&rc, &mut h);
        let hash_rc = h.finish();

        let mut h = std::collections::hash_map::DefaultHasher::default();
        Hash::hash("hello", &mut h);
        let hash_hello = h.finish();

        assert_eq!(hash_rc, hash_hello);
    }

    #[test]
    fn max_strong_count() {
        let rc = Rc8::new("hello".to_string());
        assert_eq!(Rc8::strong_count(&rc), 1);

        let mut v = Vec::new();
        for _ in 0..254 {
            v.push(rc.clone());
        }

        assert_eq!(Rc8::strong_count(&rc), 255);
        // rc.clone(); // overflow
    }
}
