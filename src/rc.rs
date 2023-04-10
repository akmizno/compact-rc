use std::borrow;
use std::borrow::Cow;
use std::cell::Cell;
use std::cmp::Ordering;
use std::fmt;
use std::hash::{Hash, Hasher};
use std::iter;
use std::marker::PhantomData;
use std::mem;
use std::mem::{ManuallyDrop, MaybeUninit};
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

impl<T, C: MarkerCounter> RcBox<T, C> {
    unsafe fn as_uninit(&mut self) -> &mut RcBox<MaybeUninit<T>, C> {
        mem::transmute(self)
    }
}

pub struct RcX<T: ?Sized, C: MarkerCounter> {
    ptr: NonNull<RcBox<T, C>>,

    // NOTE PhantomData for dropck.
    // This field indicates that this struct owns the data of type RcBox<T, C>.
    _phantom: PhantomData<RcBox<T, C>>,
}

impl<T: RefUnwindSafe + ?Sized, C: MarkerCounter> UnwindSafe for RcX<T, C> {}
impl<T: RefUnwindSafe + ?Sized, C: MarkerCounter> RefUnwindSafe for RcX<T, C> {}

impl<T: ?Sized, C: MarkerCounter> RcX<T, C> {
    fn inner(&self) -> &RcBox<T, C> {
        unsafe { self.ptr.as_ref() }
    }

    fn inner_mut(&mut self) -> &mut RcBox<T, C> {
        unsafe { self.ptr.as_mut() }
    }

    unsafe fn from_inner(ptr: NonNull<RcBox<T, C>>) -> Self {
        Self {
            ptr,
            _phantom: PhantomData,
        }
    }
}

impl<T, C: MarkerCounter> RcX<T, C> {
    unsafe fn unwrap_unchecked(self) -> T {
        assume!(RcX::is_unique(&self));

        // this forgets calling RcX's destructor.
        let mut this: ManuallyDrop<Self> = ManuallyDrop::new(self);

        // uninit_rcbox prevents calling T's destructor.
        let uninit_rcbox: &mut RcBox<MaybeUninit<T>, C> = this.ptr.as_mut().as_uninit();

        // this_box deallocates its memory at the end of this function, but does not call T's destructor.
        let _this_box: Box<RcBox<MaybeUninit<T>, C>> = Box::from_raw(uninit_rcbox);

        // move out the value
        uninit_rcbox.value.assume_init_read()
    }

    /// See [std::rc::Rc::new].
    pub fn new(value: T) -> RcX<T, C> {
        unsafe {
            Self::from_inner(
                Box::leak(Box::new(RcBox {
                    strong: Cell::new(C::one()),
                    value,
                }))
                .into(),
            )
        }
    }

    /// See [std::rc::Rc::pin].
    pub fn pin(value: T) -> Pin<RcX<T, C>> {
        unsafe { Pin::new_unchecked(Self::new(value)) }
    }

    /// See [std::rc::Rc::try_unwrap].
    pub fn try_unwrap(this: Self) -> Result<T, Self> {
        if Self::is_unique(&this) {
            unsafe { Ok(Self::unwrap_unchecked(this)) }
        } else {
            Err(this)
        }
    }
}

impl<T: ?Sized, C: MarkerCounter> RcX<T, C> {
    /// See [std::rc::Rc::as_ptr].
    fn as_ptr(this: &Self) -> *const T {
        &**this
    }

    /// See [std::rc::Rc::strong_count].
    pub fn strong_count(this: &Self) -> C {
        this.inner().strong()
    }

    fn is_unique(this: &Self) -> bool {
        Self::strong_count(&this) == C::one()
    }

    /// See [std::rc::Rc::get_mut].
    pub fn get_mut(this: &mut Self) -> Option<&mut T> {
        if Self::is_unique(this) {
            Some(&mut this.inner_mut().value)
        } else {
            None
        }
    }

    /// See [std::rc::Rc::ptr_eq].
    pub fn ptr_eq(this: &Self, other: &Self) -> bool {
        Self::as_ptr(this) == Self::as_ptr(other)
    }
}

impl<T: Clone, C: MarkerCounter> RcX<T, C> {
    /// See [std::rc::Rc::make_mut].
    pub fn make_mut(this: &mut Self) -> &mut T {
        if !Self::is_unique(this) {
            *this = Self::new((**this).clone());
        }
        unsafe { Self::get_mut(this).unwrap_unchecked() }
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
    fn from(t: T) -> Self {
        Self::new(t)
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
        &**self
    }
}

impl<T: ?Sized, C: MarkerCounter> AsRef<T> for RcX<T, C> {
    fn as_ref(&self) -> &T {
        &**self
    }
}

impl<T: ?Sized, C: MarkerCounter> Unpin for RcX<T, C> {}

#[cfg(test)]
mod tests {
    use super::*;
    use std::borrow::Borrow;
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

    #[test]
    fn get_mut() {
        let mut rc = Rc8::new(1i32);

        let rc2 = rc.clone();
        assert!(Rc8::get_mut(&mut rc).is_none());

        drop(rc2);
        assert!(Rc8::get_mut(&mut rc).is_some());

        *Rc8::get_mut(&mut rc).unwrap() = 2;
        assert_eq!(*rc, 2);
    }

    #[test]
    fn ptr_eq() {
        let rc = Rc8::new(1i32);
        let rc_eq = rc.clone();
        let rc_ne = Rc8::new(1i32);

        assert!(Rc8::ptr_eq(&rc, &rc_eq));
        assert!(!Rc8::ptr_eq(&rc, &rc_ne));
    }

    #[test]
    fn make_mut() {
        let mut rc = Rc8::new(1i32);
        assert_eq!(*rc, 1);

        *Rc8::make_mut(&mut rc) = 2;
        assert_eq!(*rc, 2);

        let rc2 = rc.clone();
        assert_eq!(*rc2, 2);

        *Rc8::make_mut(&mut rc) = 3;
        assert_eq!(*rc, 3);
        assert_eq!(*rc2, 2);
    }

    #[test]
    fn pin() {
        let rc = Rc8::pin(1i32);

        assert_eq!(*rc, 1);
    }

    #[test]
    fn try_unwrap() {
        {
            let rc = Rc8::new(1i32);
            let v = Rc8::try_unwrap(rc);
            assert_eq!(v.unwrap(), 1);
        }

        {
            let rc = Rc8::new(1i32);
            let _rc2 = rc.clone();
            let v = Rc8::try_unwrap(rc);
            assert_eq!(*v.unwrap_err(), 1);
        }

        {
            let rc = Rc8::new(1i32);
            let rc2 = rc.clone();
            drop(rc2);
            let v = Rc8::try_unwrap(rc);
            assert_eq!(v.unwrap(), 1);
        }
    }

    #[test]
    fn borrow() {
        let rc = Rc8::<i32>::new(1i32);

        assert_eq!(<Rc8<i32> as Borrow<i32>>::borrow(&rc), &1i32);
    }

    #[test]
    fn as_ref() {
        let rc = Rc8::<i32>::new(1i32);

        assert_eq!(rc.as_ref(), &1i32);
    }

    #[test]
    fn from_t() {
        let value: String = "hello".to_string();
        let rc = Rc8::<String>::from(value);

        assert_eq!(*rc, "hello");
    }
}

#[cfg(test)]
mod leak_ckeck {
    use super::*;

    struct DropCount<'a> {
        drop_count: &'a mut usize,
    }

    impl<'a> Drop for DropCount<'a> {
        fn drop(&mut self) {
            *self.drop_count += 1;
        }
    }

    #[test]
    fn single() {
        let mut drop_count = 0;
        let rc = Rc8::new(DropCount {
            drop_count: &mut drop_count,
        });
        drop(rc);
        assert_eq!(drop_count, 1);
    }

    #[test]
    fn clone() {
        let mut drop_count = 0;
        let rc = Rc8::new(DropCount {
            drop_count: &mut drop_count,
        });
        let rc2 = rc.clone();
        drop(rc);
        drop(rc2);
        assert_eq!(drop_count, 1);
    }

    #[test]
    fn try_unwrap() {
        {
            let mut drop_count = 0;
            {
                let rc = Rc8::new(DropCount {
                    drop_count: &mut drop_count,
                });

                let v = Rc8::try_unwrap(rc);
                assert!(v.is_ok());
            }
            assert_eq!(drop_count, 1);
        }

        {
            let mut drop_count = 0;
            {
                let rc = Rc8::new(DropCount {
                    drop_count: &mut drop_count,
                });
                let _rc2 = rc.clone();
                let v = Rc8::try_unwrap(rc);
                assert!(v.is_err());
            }
            assert_eq!(drop_count, 1);
        }

        {
            let mut drop_count = 0;
            {
                let rc = Rc8::new(DropCount {
                    drop_count: &mut drop_count,
                });
                let rc2 = rc.clone();
                drop(rc2);
                let v = Rc8::try_unwrap(rc);
                assert!(v.is_ok());
            }
            assert_eq!(drop_count, 1);
        }
    }
}
