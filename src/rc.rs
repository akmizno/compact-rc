use std::any::Any;
use std::borrow;
use std::borrow::Cow;
use std::cell::Cell;
use std::cmp::Ordering;
use std::fmt;
use std::hash::{Hash, Hasher};
use std::iter;
use std::ops::Deref;
use std::panic::{RefUnwindSafe, UnwindSafe};
use std::pin::Pin;
use std::ptr::NonNull;

struct RcBox<T: ?Sized> {
    _strong: Cell<usize>,
    _value: T,
}

pub struct Rc<T: ?Sized> {
    _ptr: NonNull<RcBox<T>>,
}

impl<T: RefUnwindSafe + ?Sized> UnwindSafe for Rc<T> {}
impl<T: RefUnwindSafe + ?Sized> RefUnwindSafe for Rc<T> {}

impl<T> Rc<T> {
    /// See [std::rc::Rc::new].
    pub fn new(_value: T) -> Rc<T> {
        todo!();
    }

    /// See [std::rc::Rc::new_cyclic].
    pub fn new_cyclic<F>(_data_fn: F) -> Rc<T>
    where
        F: FnOnce(&NonNull<T>) -> T,
    {
        todo!();
    }

    /// See [std::rc::Rc::pin].
    pub fn pin(_value: T) -> Pin<Rc<T>> {
        todo!();
    }

    /// See [std::rc::Rc::try_unwrap].
    pub fn try_unwrap(_this: Self) -> Result<T, Self> {
        todo!();
    }
}

impl<T: ?Sized> Rc<T> {
    /// See [std::rc::Rc::into_raw].
    pub fn into_raw(_this: Self) -> *const T {
        todo!();
    }

    /// See [std::rc::Rc::as_ptr].
    pub fn as_ptr(_this: &Self) -> *const T {
        todo!();
    }

    /// See [std::rc::Rc::from_raw].
    pub unsafe fn from_raw(_ptr: *const T) -> Self {
        todo!();
    }

    /// See [std::rc::Rc::downgrade].
    pub fn downgrade(_this: &Self) -> NonNull<T> {
        todo!();
    }

    /// See [std::rc::Rc::strong_count].
    pub fn strong_count(_this: &Self) -> usize {
        todo!();
    }

    /// See [std::rc::Rc::increment_strong_count].
    pub unsafe fn increment_strong_count(_ptr: *const T) {
        todo!();
    }

    /// See [std::rc::Rc::decrement_strong_count].
    pub unsafe fn decrement_strong_count(_ptr: *const T) {
        todo!();
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

impl<T: Clone> Rc<T> {
    /// See [std::rc::Rc::make_mut].
    pub fn make_mut(_this: &mut Self) -> &mut T {
        todo!();
    }
}

impl Rc<dyn Any> {
    /// See [std::rc::Rc::downcast].
    pub fn downcast<T: Any>(self) -> Result<Rc<T>, Rc<dyn Any>> {
        todo!();
    }
}

impl<T: ?Sized> Deref for Rc<T> {
    type Target = T;

    fn deref(&self) -> &T {
        todo!();
    }
}

impl<T: ?Sized> Drop for Rc<T> {
    fn drop(&mut self) {
        todo!();
    }
}

impl<T: ?Sized> Clone for Rc<T> {
    fn clone(&self) -> Rc<T> {
        todo!();
    }
}

impl<T: Default> Default for Rc<T> {
    fn default() -> Rc<T> {
        todo!();
    }
}

impl<T: ?Sized + PartialEq> PartialEq for Rc<T> {
    fn eq(&self, _other: &Rc<T>) -> bool {
        todo!();
    }
}

impl<T: ?Sized + Eq> Eq for Rc<T> {}

impl<T: ?Sized + PartialOrd> PartialOrd for Rc<T> {
    fn partial_cmp(&self, _other: &Rc<T>) -> Option<Ordering> {
        todo!();
    }
}

impl<T: ?Sized + Ord> Ord for Rc<T> {
    fn cmp(&self, _other: &Rc<T>) -> Ordering {
        todo!();
    }
}

impl<T: ?Sized + Hash> Hash for Rc<T> {
    fn hash<H: Hasher>(&self, _state: &mut H) {
        todo!();
    }
}

impl<T: ?Sized + fmt::Display> fmt::Display for Rc<T> {
    fn fmt(&self, _f: &mut fmt::Formatter<'_>) -> fmt::Result {
        todo!();
    }
}

impl<T: ?Sized + fmt::Debug> fmt::Debug for Rc<T> {
    fn fmt(&self, _f: &mut fmt::Formatter<'_>) -> fmt::Result {
        todo!();
    }
}

impl<T: ?Sized> fmt::Pointer for Rc<T> {
    fn fmt(&self, _f: &mut fmt::Formatter<'_>) -> fmt::Result {
        todo!();
    }
}

impl<T> From<T> for Rc<T> {
    fn from(_t: T) -> Self {
        todo!();
    }
}

impl<T: Clone> From<&[T]> for Rc<[T]> {
    fn from(_v: &[T]) -> Rc<[T]> {
        todo!();
    }
}

impl From<&str> for Rc<str> {
    fn from(_v: &str) -> Rc<str> {
        todo!();
    }
}

impl From<String> for Rc<str> {
    fn from(_v: String) -> Rc<str> {
        todo!();
    }
}

impl<T: ?Sized> From<Box<T>> for Rc<T> {
    fn from(_v: Box<T>) -> Rc<T> {
        todo!();
    }
}

impl<T> From<Vec<T>> for Rc<[T]> {
    fn from(mut _v: Vec<T>) -> Rc<[T]> {
        todo!();
    }
}

impl<'a, B> From<Cow<'a, B>> for Rc<B>
where
    B: ToOwned + ?Sized,
    Rc<B>: From<&'a B> + From<B::Owned>,
{
    fn from(_cow: Cow<'a, B>) -> Rc<B> {
        todo!();
    }
}

impl From<Rc<str>> for Rc<[u8]> {
    fn from(_rc: Rc<str>) -> Self {
        todo!();
    }
}

impl<T, const N: usize> TryFrom<Rc<[T]>> for Rc<[T; N]> {
    type Error = Rc<[T]>;

    fn try_from(_boxed_slice: Rc<[T]>) -> Result<Self, Self::Error> {
        todo!();
    }
}

impl<T> iter::FromIterator<T> for Rc<[T]> {
    fn from_iter<I: iter::IntoIterator<Item = T>>(_iter: I) -> Self {
        todo!();
    }
}

impl<T: ?Sized> borrow::Borrow<T> for Rc<T> {
    fn borrow(&self) -> &T {
        todo!();
    }
}

impl<T: ?Sized> AsRef<T> for Rc<T> {
    fn as_ref(&self) -> &T {
        todo!();
    }
}

impl<T: ?Sized> Unpin for Rc<T> {}

#[cfg(test)]
mod tests {
    // use super::*;
    // use std::rc::Rc;

    #[test]
    fn it_works() {}
}
