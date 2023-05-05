use std::borrow;
use std::borrow::Cow;
use std::cell::Cell;
use std::ffi::{CStr, CString};
use std::fmt;
use std::hash::Hash;
use std::iter;
use std::ops::Deref;
use std::pin::Pin;

use crate::base::RcBase;
use crate::refcount::RefCount;

/// RcX with u8 counter
pub type Rc8<T> = RcX<T, u8>;
/// RcX with u16 counter
pub type Rc16<T> = RcX<T, u16>;
/// RcX with u32 counter
pub type Rc32<T> = RcX<T, u32>;
/// RcX with u64 counter
pub type Rc64<T> = RcX<T, u64>;
/// RcX with usize counter
pub type Rc<T> = RcX<T, usize>;

/// Low-memory version of [std::rc::Rc].
///
/// A type provides almost the same methods as standard `Rc`.
/// See [the top page](crate) for about differences from the standard `Rc`.
///
/// There are aliases for simplicity.
/// - [Rc]
/// - [Rc8]
/// - [Rc16]
/// - [Rc32]
/// - [Rc64]
#[derive(Clone, Default, Debug, Eq, PartialEq, PartialOrd, Ord, Hash)]
pub struct RcX<T: ?Sized, C>(RcBase<T, Cell<C>>)
where
    Cell<C>: RefCount;

impl<T, C> RcX<T, C>
where
    Cell<C>: RefCount,
{
    /// See [std::rc::Rc::new].
    pub fn new(value: T) -> RcX<T, C> {
        RcX(RcBase::new(value))
    }

    /// See [std::rc::Rc::pin].
    pub fn pin(value: T) -> Pin<RcX<T, C>> {
        unsafe { Pin::new_unchecked(Self::new(value)) }
    }

    /// See [std::rc::Rc::try_unwrap].
    pub fn try_unwrap(this: Self) -> Result<T, Self> {
        RcBase::try_unwrap(this.0).map_err(Self)
    }

    /// See [std::rc::Rc::from_raw].
    pub unsafe fn from_raw(ptr: *const T) -> Self {
        Self(RcBase::from_raw(ptr))
    }

    /// See [std::rc::Rc::increment_strong_count].
    pub unsafe fn increment_strong_count(ptr: *const T) {
        RcBase::<T, Cell<C>>::increment_strong_count(ptr)
    }

    /// See [std::rc::Rc::decrement_strong_count].
    pub unsafe fn decrement_strong_count(ptr: *const T) {
        RcBase::<T, Cell<C>>::decrement_strong_count(ptr)
    }
}

impl<T: ?Sized, C> RcX<T, C>
where
    Cell<C>: RefCount,
{
    /// See [std::rc::Rc::as_ptr].
    pub fn as_ptr(this: &Self) -> *const T {
        RcBase::as_ptr(&this.0)
    }

    /// See [std::rc::Rc::into_raw].
    pub fn into_raw(this: Self) -> *const T {
        RcBase::into_raw(this.0)
    }

    /// See [std::rc::Rc::strong_count].
    pub fn strong_count(this: &Self) -> <Cell<C> as RefCount>::Value {
        RcBase::strong_count(&this.0)
    }

    /// See [std::rc::Rc::get_mut].
    pub fn get_mut(this: &mut Self) -> Option<&mut T> {
        RcBase::get_mut(&mut this.0)
    }

    /// See [std::rc::Rc::ptr_eq].
    pub fn ptr_eq(this: &Self, other: &Self) -> bool {
        RcBase::ptr_eq(&this.0, &other.0)
    }
}

impl<T: Clone, C> RcX<T, C>
where
    Cell<C>: RefCount,
{
    /// See [std::rc::Rc::make_mut].
    pub fn make_mut(this: &mut Self) -> &mut T {
        RcBase::make_mut(&mut this.0)
    }
}

impl<T: ?Sized, C> Deref for RcX<T, C>
where
    Cell<C>: RefCount,
{
    type Target = T;

    fn deref(&self) -> &T {
        self.0.deref()
    }
}

impl<T: ?Sized + fmt::Display, C> fmt::Display for RcX<T, C>
where
    Cell<C>: RefCount,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Display::fmt(&self.0, f)
    }
}

impl<T: ?Sized, C> fmt::Pointer for RcX<T, C>
where
    Cell<C>: RefCount,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Pointer::fmt(&self.0, f)
    }
}

impl<T, C> From<T> for RcX<T, C>
where
    Cell<C>: RefCount,
{
    fn from(t: T) -> Self {
        Self(RcBase::from(t))
    }
}

impl<T: Clone, C> From<&[T]> for RcX<[T], C>
where
    Cell<C>: RefCount,
{
    fn from(v: &[T]) -> RcX<[T], C> {
        Self(RcBase::from(v))
    }
}

impl<C> From<&str> for RcX<str, C>
where
    Cell<C>: RefCount,
{
    fn from(s: &str) -> RcX<str, C> {
        Self(RcBase::from(s))
    }
}

impl<C> From<String> for RcX<str, C>
where
    Cell<C>: RefCount,
{
    fn from(s: String) -> RcX<str, C> {
        Self(RcBase::from(s))
    }
}

impl<C> From<&CStr> for RcX<CStr, C>
where
    Cell<C>: RefCount,
{
    fn from(s: &CStr) -> RcX<CStr, C> {
        Self(RcBase::from(s))
    }
}

impl<C> From<CString> for RcX<CStr, C>
where
    Cell<C>: RefCount,
{
    fn from(s: CString) -> RcX<CStr, C> {
        Self(RcBase::from(s))
    }
}

impl<T, C> From<Box<T>> for RcX<T, C>
where
    Cell<C>: RefCount,
{
    fn from(b: Box<T>) -> RcX<T, C> {
        Self(RcBase::from(b))
    }
}

impl<T, C> From<Vec<T>> for RcX<[T], C>
where
    Cell<C>: RefCount,
{
    fn from(v: Vec<T>) -> RcX<[T], C> {
        Self(RcBase::from(v))
    }
}

impl<'a, B, C> From<Cow<'a, B>> for RcX<B, C>
where
    Cell<C>: RefCount,
    B: ToOwned + ?Sized,
    RcX<B, C>: From<&'a B> + From<B::Owned>,
{
    fn from(cow: Cow<'a, B>) -> RcX<B, C> {
        match cow {
            Cow::Borrowed(s) => RcX::from(s),
            Cow::Owned(s) => RcX::from(s),
        }
    }
}

impl<C> From<RcX<str, C>> for RcX<[u8], C>
where
    Cell<C>: RefCount,
{
    fn from(rc: RcX<str, C>) -> Self {
        Self(RcBase::from(rc.0))
    }
}

impl<T, C, const N: usize> TryFrom<RcX<[T], C>> for RcX<[T; N], C>
where
    Cell<C>: RefCount,
{
    type Error = RcX<[T], C>;

    fn try_from(boxed_slice: RcX<[T], C>) -> Result<Self, Self::Error> {
        RcBase::try_from(boxed_slice.0)
            .map(Self)
            .map_err(RcX::<[T], C>)
    }
}

impl<T, C> iter::FromIterator<T> for RcX<[T], C>
where
    Cell<C>: RefCount,
{
    fn from_iter<I: iter::IntoIterator<Item = T>>(iter: I) -> Self {
        Self(RcBase::from_iter(iter))
    }
}

impl<T: ?Sized, C> borrow::Borrow<T> for RcX<T, C>
where
    Cell<C>: RefCount,
{
    fn borrow(&self) -> &T {
        self.0.borrow()
    }
}

impl<T: ?Sized, C> AsRef<T> for RcX<T, C>
where
    Cell<C>: RefCount,
{
    fn as_ref(&self) -> &T {
        self.0.as_ref()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn pin() {
        let rc = Rc8::pin(1i32);

        assert_eq!(*rc, 1);
    }

    #[test]
    fn from_cow() {
        // Owned
        {
            let v = "Hello".to_string();
            let owned: Cow<str> = Cow::Owned(v);
            assert!(matches!(owned, Cow::Owned(_)));
            let rc = Rc8::<str>::from(owned);
            assert_eq!(&*rc, "Hello");
        }

        // Borrowed
        {
            let v = "Hello";
            let borrowed: Cow<str> = Cow::Borrowed(v);
            assert!(matches!(borrowed, Cow::Borrowed(_)));
            let rc = Rc8::<str>::from(borrowed);
            assert_eq!(&*rc, "Hello");
        }
    }
}
