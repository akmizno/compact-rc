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
use std::ptr;
use std::ptr::NonNull;

#[repr(C)]
struct RcBox<T: ?Sized> {
    strong: Cell<usize>,
    value: T,
}

impl<T: ?Sized> RcBox<T> {
    fn strong(&self) -> usize {
        self.strong.get()
    }

    fn inc_strong(&self) {
        let count = self.strong();
        assume!(0 < count);
        let (count, overflow) = count.overflowing_add(1);
        self.strong.set(count);

        if unlikely!(overflow) {
            std::process::abort();
        }
    }

    fn dec_strong(&self) {
        let count = self.strong();
        assume!(0 < count);
        let count = count.wrapping_sub(1);
        self.strong.set(count);
    }
}

pub struct Rc<T: ?Sized> {
    ptr: NonNull<RcBox<T>>,
}

impl<T: RefUnwindSafe + ?Sized> UnwindSafe for Rc<T> {}
impl<T: RefUnwindSafe + ?Sized> RefUnwindSafe for Rc<T> {}

impl<T: ?Sized> Rc<T> {
    fn inner(&self) -> &RcBox<T> {
        unsafe { self.ptr.as_ref() }
    }

    unsafe fn from_inner(ptr: NonNull<RcBox<T>>) -> Self {
        Self { ptr }
    }
}

impl<T> Rc<T> {
    /// See [std::rc::Rc::new].
    pub fn new(value: T) -> Rc<T> {
        unsafe {
            Self::from_inner(NonNull::from(Box::leak(Box::new(RcBox {
                strong: Cell::new(1),
                value,
            }))))
        }
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
    pub fn as_ptr(this: &Self) -> *const T {
        let ptr: *mut RcBox<T> = NonNull::as_ptr(this.ptr);
        unsafe { ptr::addr_of_mut!((*ptr).value) }
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
    pub fn strong_count(this: &Self) -> usize {
        this.inner().strong()
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
        &self.inner().value
    }
}

impl<T: ?Sized> Drop for Rc<T> {
    fn drop(&mut self) {
        self.inner().dec_strong();
        if self.inner().strong() == 0 {
            unsafe {
                drop(Box::from_raw(self.ptr.as_mut()));
            }
        }
    }
}

impl<T: ?Sized> Clone for Rc<T> {
    fn clone(&self) -> Rc<T> {
        self.inner().inc_strong();
        unsafe { Self::from_inner(self.ptr) }
    }
}

impl<T: Default> Default for Rc<T> {
    fn default() -> Rc<T> {
        Rc::new(Default::default())
    }
}

impl<T: ?Sized + PartialEq> PartialEq for Rc<T> {
    fn eq(&self, other: &Rc<T>) -> bool {
        // NOTE
        // Optimization by comparing their addresses can not be used for T: PartialEq.
        // For T: Eq, it is possible. But the specialization is unstable feature.
        PartialEq::eq(&**self, &**other)
    }
    fn ne(&self, other: &Rc<T>) -> bool {
        PartialEq::ne(&**self, &**other)
    }
}

impl<T: ?Sized + Eq> Eq for Rc<T> {}

impl<T: ?Sized + PartialOrd> PartialOrd for Rc<T> {
    fn partial_cmp(&self, other: &Rc<T>) -> Option<Ordering> {
        PartialOrd::partial_cmp(&**self, &**other)
    }
}

impl<T: ?Sized + Ord> Ord for Rc<T> {
    fn cmp(&self, other: &Rc<T>) -> Ordering {
        Ord::cmp(&**self, &**other)
    }
}

impl<T: ?Sized + Hash> Hash for Rc<T> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        Hash::hash(&**self, state)
    }
}

impl<T: ?Sized + fmt::Display> fmt::Display for Rc<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Display::fmt(&**self, f)
    }
}

impl<T: ?Sized + fmt::Debug> fmt::Debug for Rc<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Debug::fmt(&**self, f)
    }
}

impl<T: ?Sized> fmt::Pointer for Rc<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Pointer::fmt(&(Rc::as_ptr(self)), f)
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
    use super::*;
    type StdRc<T> = std::rc::Rc<T>;

    #[test]
    fn new_deref() {
        let rc = Rc::new(1);
        assert_eq!(*rc, 1);
    }

    #[test]
    fn clone_drop_strong_count() {
        let rc1 = Rc::new(1);
        assert_eq!(Rc::strong_count(&rc1), 1);

        let rc2 = rc1.clone();
        assert_eq!(Rc::strong_count(&rc1), 2);
        assert_eq!(Rc::strong_count(&rc2), 2);
        assert_eq!(*rc1, 1);
        assert_eq!(*rc2, 1);

        drop(rc1);
        assert_eq!(Rc::strong_count(&rc2), 1);
        assert_eq!(*rc2, 1);
    }

    #[test]
    fn default() {
        let rc = Rc::<String>::default();
        let stdrc = StdRc::<String>::default();

        assert_eq!(*rc, *stdrc);
    }

    #[test]
    fn debug() {
        let rc = Rc::new("debug".to_string());
        let stdrc = StdRc::new("debug".to_string());

        assert_eq!(format!("{:?}", rc), format!("{:?}", stdrc));
    }

    #[test]
    fn display() {
        let rc = Rc::new("debug".to_string());
        let stdrc = StdRc::new("debug".to_string());

        assert_eq!(format!("{}", rc), format!("{}", stdrc));
    }

    #[test]
    fn pointer() {
        let rc = Rc::new("debug".to_string());

        assert_eq!(format!("{:p}", rc), format!("{:p}", Rc::as_ptr(&rc)));
    }

    #[test]
    fn as_ptr() {
        let rc = Rc::<u32>::new(1);

        unsafe {
            assert_eq!(*Rc::as_ptr(&rc), 1);
        }
    }

    #[test]
    fn eq_ne() {
        let rc = Rc::<u32>::new(1);
        let rc1 = Rc::<u32>::new(1);
        let rc2 = Rc::<u32>::new(2);

        assert_eq!(rc, rc1);
        assert_ne!(rc, rc2);
    }

    #[test]
    fn partial_cmp() {
        let rc = Rc::<u32>::new(2);
        let rc1 = Rc::<u32>::new(1);
        let rc2 = Rc::<u32>::new(2);
        let rc3 = Rc::<u32>::new(3);

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
        let rc = Rc::<u32>::new(2);
        let rc1 = Rc::<u32>::new(1);
        let rc2 = Rc::<u32>::new(2);
        let rc3 = Rc::<u32>::new(3);

        assert_eq!(Ord::cmp(&rc, &rc1), Ord::cmp(&2, &1));
        assert_eq!(Ord::cmp(&rc, &rc2), Ord::cmp(&2, &2));
        assert_eq!(Ord::cmp(&rc, &rc3), Ord::cmp(&2, &3));
    }

    #[test]
    fn hash() {
        let rc = Rc::new("hello".to_string());

        let mut h = std::collections::hash_map::DefaultHasher::default();
        Hash::hash(&rc, &mut h);
        let hash_rc = h.finish();

        let mut h = std::collections::hash_map::DefaultHasher::default();
        Hash::hash("hello", &mut h);
        let hash_hello = h.finish();

        assert_eq!(hash_rc, hash_hello);
    }
}
