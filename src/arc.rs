use std::borrow;
use std::borrow::Cow;
use std::cmp::Ordering;
use std::ffi::{CStr, CString};
use std::fmt;
use std::hash::{Hash, Hasher};
use std::iter;
use std::ops::Deref;
use std::pin::Pin;
use std::sync::atomic::{AtomicU16, AtomicU32, AtomicU64, AtomicU8, AtomicUsize};

use crate::base::RcBase;
use crate::refcount::RefCount;

/// ArcX with u8 counter
pub type Arc8<T> = ArcX<T, AtomicU8>;
/// ArcX with u16 counter
pub type Arc16<T> = ArcX<T, AtomicU16>;
/// ArcX with u32 counter
pub type Arc32<T> = ArcX<T, AtomicU32>;
/// ArcX with u64 counter
pub type Arc64<T> = ArcX<T, AtomicU64>;
/// ArcX with usize counter
pub type Arc<T> = ArcX<T, AtomicUsize>;

/// Low-memory version of [std::sync::Arc].
///
/// This type provides almost the same methods as standard `Arc`.
/// See [the top page](crate) for about differences from the standard `Arc`.
///
/// There are aliases for simplicity.
/// - [Arc]
/// - [Arc8]
/// - [Arc16]
/// - [Arc32]
/// - [Arc64]
pub struct ArcX<T: ?Sized, C>(RcBase<T, C>)
where
    C: RefCount + Sync + Send;

impl<T, C> ArcX<T, C>
where
    C: RefCount + Sync + Send,
{
    /// See [std::sync::Arc::new].
    #[inline]
    pub fn new(value: T) -> ArcX<T, C> {
        ArcX(RcBase::new(value))
    }

    /// See [std::sync::Arc::pin].
    #[inline]
    pub fn pin(value: T) -> Pin<ArcX<T, C>> {
        unsafe { Pin::new_unchecked(Self::new(value)) }
    }

    /// See [std::sync::Arc::try_unwrap].
    #[inline]
    pub fn try_unwrap(this: Self) -> Result<T, Self> {
        RcBase::try_unwrap(this.0).map_err(Self)
    }

    /// See [std::sync::Arc::from_raw].
    #[inline]
    pub unsafe fn from_raw(ptr: *const T) -> Self {
        Self(RcBase::from_raw(ptr))
    }

    /// See [std::sync::Arc::increment_strong_count].
    #[inline]
    pub unsafe fn increment_strong_count(ptr: *const T) {
        RcBase::<T, C>::increment_strong_count(ptr)
    }

    /// See [std::sync::Arc::decrement_strong_count].
    #[inline]
    pub unsafe fn decrement_strong_count(ptr: *const T) {
        RcBase::<T, C>::decrement_strong_count(ptr)
    }
}

impl<T: ?Sized, C> ArcX<T, C>
where
    C: RefCount + Sync + Send,
{
    /// See [std::sync::Arc::as_ptr].
    #[inline]
    pub fn as_ptr(this: &Self) -> *const T {
        RcBase::as_ptr(&this.0)
    }

    /// See [std::sync::Arc::into_raw].
    #[inline]
    pub fn into_raw(this: Self) -> *const T {
        RcBase::into_raw(this.0)
    }

    /// See [std::sync::Arc::strong_count].
    #[inline]
    pub fn strong_count(this: &Self) -> <C as RefCount>::Value {
        RcBase::strong_count(&this.0)
    }

    /// See [std::sync::Arc::get_mut].
    #[inline]
    pub fn get_mut(this: &mut Self) -> Option<&mut T> {
        RcBase::get_mut(&mut this.0)
    }

    /// See [std::sync::Arc::ptr_eq].
    #[inline]
    pub fn ptr_eq(this: &Self, other: &Self) -> bool {
        RcBase::ptr_eq(&this.0, &other.0)
    }
}

impl<T: Clone, C> ArcX<T, C>
where
    C: RefCount + Sync + Send,
{
    /// See [std::sync::Arc::make_mut].
    #[inline]
    pub fn make_mut(this: &mut Self) -> &mut T {
        RcBase::make_mut(&mut this.0)
    }
}

impl<T: ?Sized, C> Deref for ArcX<T, C>
where
    C: RefCount + Sync + Send,
{
    type Target = T;

    #[inline]
    fn deref(&self) -> &T {
        self.0.deref()
    }
}

impl<T: ?Sized, C> Clone for ArcX<T, C>
where
    C: RefCount + Sync + Send,
{
    #[inline]
    fn clone(&self) -> ArcX<T, C> {
        Self(self.0.clone())
    }
}

impl<T: Default, C> Default for ArcX<T, C>
where
    C: RefCount + Sync + Send,
{
    #[inline]
    fn default() -> ArcX<T, C> {
        ArcX::new(Default::default())
    }
}

impl<T: ?Sized + PartialEq, C> PartialEq for ArcX<T, C>
where
    C: RefCount + Sync + Send,
{
    #[inline]
    fn eq(&self, other: &ArcX<T, C>) -> bool {
        PartialEq::eq(&self.0, &other.0)
    }
    #[inline]
    fn ne(&self, other: &ArcX<T, C>) -> bool {
        PartialEq::ne(&self.0, &other.0)
    }
}

impl<T: ?Sized + Eq, C> Eq for ArcX<T, C> where C: RefCount + Sync + Send {}

impl<T: ?Sized + PartialOrd, C> PartialOrd for ArcX<T, C>
where
    C: RefCount + Sync + Send,
{
    #[inline]
    fn partial_cmp(&self, other: &ArcX<T, C>) -> Option<Ordering> {
        PartialOrd::partial_cmp(&self.0, &other.0)
    }
}

impl<T: ?Sized + Ord, C> Ord for ArcX<T, C>
where
    C: RefCount + Sync + Send,
{
    #[inline]
    fn cmp(&self, other: &ArcX<T, C>) -> Ordering {
        Ord::cmp(&self.0, &other.0)
    }
}

impl<T: ?Sized + Hash, C> Hash for ArcX<T, C>
where
    C: RefCount + Sync + Send,
{
    #[inline]
    fn hash<H: Hasher>(&self, state: &mut H) {
        Hash::hash(&self.0, state)
    }
}

impl<T: ?Sized + fmt::Display, C> fmt::Display for ArcX<T, C>
where
    C: RefCount + Sync + Send,
{
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Display::fmt(&self.0, f)
    }
}

impl<T: ?Sized + fmt::Debug, C> fmt::Debug for ArcX<T, C>
where
    C: RefCount + Sync + Send,
{
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Debug::fmt(&self.0, f)
    }
}

impl<T: ?Sized, C> fmt::Pointer for ArcX<T, C>
where
    C: RefCount + Sync + Send,
{
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Pointer::fmt(&self.0, f)
    }
}

impl<T, C> From<T> for ArcX<T, C>
where
    C: RefCount + Sync + Send,
{
    #[inline]
    fn from(t: T) -> Self {
        Self(RcBase::from(t))
    }
}

impl<T: Clone, C> From<&[T]> for ArcX<[T], C>
where
    C: RefCount + Sync + Send,
{
    #[inline]
    fn from(v: &[T]) -> ArcX<[T], C> {
        Self(RcBase::from(v))
    }
}

impl<C> From<&str> for ArcX<str, C>
where
    C: RefCount + Sync + Send,
{
    #[inline]
    fn from(s: &str) -> ArcX<str, C> {
        Self(RcBase::from(s))
    }
}

impl<C> From<String> for ArcX<str, C>
where
    C: RefCount + Sync + Send,
{
    #[inline]
    fn from(s: String) -> ArcX<str, C> {
        Self(RcBase::from(s))
    }
}

impl<C> From<&CStr> for ArcX<CStr, C>
where
    C: RefCount + Sync + Send,
{
    #[inline]
    fn from(s: &CStr) -> ArcX<CStr, C> {
        Self(RcBase::from(s))
    }
}

impl<C> From<CString> for ArcX<CStr, C>
where
    C: RefCount + Sync + Send,
{
    #[inline]
    fn from(s: CString) -> ArcX<CStr, C> {
        Self(RcBase::from(s))
    }
}

impl<T, C> From<Box<T>> for ArcX<T, C>
where
    C: RefCount + Sync + Send,
{
    #[inline]
    fn from(b: Box<T>) -> ArcX<T, C> {
        Self(RcBase::from(b))
    }
}

impl<T, C> From<Vec<T>> for ArcX<[T], C>
where
    C: RefCount + Sync + Send,
{
    #[inline]
    fn from(v: Vec<T>) -> ArcX<[T], C> {
        Self(RcBase::from(v))
    }
}

impl<'a, B, C> From<Cow<'a, B>> for ArcX<B, C>
where
    C: RefCount + Sync + Send,
    B: ToOwned + ?Sized,
    ArcX<B, C>: From<&'a B> + From<B::Owned>,
{
    #[inline]
    fn from(cow: Cow<'a, B>) -> ArcX<B, C> {
        match cow {
            Cow::Borrowed(s) => ArcX::from(s),
            Cow::Owned(s) => ArcX::from(s),
        }
    }
}

impl<C> From<ArcX<str, C>> for ArcX<[u8], C>
where
    C: RefCount + Sync + Send,
{
    #[inline]
    fn from(rc: ArcX<str, C>) -> Self {
        Self(RcBase::from(rc.0))
    }
}

impl<T, C, const N: usize> TryFrom<ArcX<[T], C>> for ArcX<[T; N], C>
where
    C: RefCount + Sync + Send,
{
    type Error = ArcX<[T], C>;

    #[inline]
    fn try_from(boxed_slice: ArcX<[T], C>) -> Result<Self, Self::Error> {
        RcBase::try_from(boxed_slice.0)
            .map(Self)
            .map_err(ArcX::<[T], C>)
    }
}

impl<T, C> iter::FromIterator<T> for ArcX<[T], C>
where
    C: RefCount + Sync + Send,
{
    #[inline]
    fn from_iter<I: iter::IntoIterator<Item = T>>(iter: I) -> Self {
        Self(RcBase::from_iter(iter))
    }
}

impl<T: ?Sized, C> borrow::Borrow<T> for ArcX<T, C>
where
    C: RefCount + Sync + Send,
{
    #[inline]
    fn borrow(&self) -> &T {
        self.0.borrow()
    }
}

impl<T: ?Sized, C> AsRef<T> for ArcX<T, C>
where
    C: RefCount + Sync + Send,
{
    #[inline]
    fn as_ref(&self) -> &T {
        self.0.as_ref()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn pin() {
        let rc = Arc8::pin(1i32);

        assert_eq!(*rc, 1);
    }

    #[test]
    fn from_cow() {
        // Owned
        {
            let v = "Hello".to_string();
            let owned: Cow<str> = Cow::Owned(v);
            assert!(matches!(owned, Cow::Owned(_)));
            let rc = Arc8::<str>::from(owned);
            assert_eq!(&*rc, "Hello");
        }

        // Borrowed
        {
            let v = "Hello";
            let borrowed: Cow<str> = Cow::Borrowed(v);
            assert!(matches!(borrowed, Cow::Borrowed(_)));
            let rc = Arc8::<str>::from(borrowed);
            assert_eq!(&*rc, "Hello");
        }
    }
}
