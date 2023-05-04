use std::alloc::{Layout, LayoutError};
use std::borrow;
use std::cmp::Ordering;
use std::ffi::{CStr, CString};
use std::fmt;
use std::hash::{Hash, Hasher};
use std::iter;
use std::marker::PhantomData;
use std::mem;
use std::mem::{ManuallyDrop, MaybeUninit};
use std::ops::Deref;
use std::panic::{RefUnwindSafe, UnwindSafe};
use std::ptr::NonNull;

use crate::refcount::RefCount;

#[repr(C)]
struct RcBox<T: ?Sized, C> {
    strong: C,
    value: T,
}

impl<T: ?Sized, C: RefCount> RcBox<T, C> {
    fn strong(&self) -> &C {
        &self.strong
    }

    unsafe fn layout_nopad(layout_value: Layout) -> Result<(Layout, usize), LayoutError> {
        let layout_strong = Layout::new::<C>();
        layout_strong.extend(layout_value)
    }

    unsafe fn layout_nopad_for_value(value: &T) -> Result<(Layout, usize), LayoutError> {
        let layout_value = Layout::for_value(value);
        Self::layout_nopad(layout_value)
    }

    unsafe fn offset_of_value(value: &T) -> usize {
        Self::layout_nopad_for_value(value).unwrap().1
    }
}

impl<T, C: RefCount> RcBox<T, C> {
    /// Allocate an RcBox with the given length.
    ///
    /// Returns a pointer to the allocated RcBox.
    /// Its values are uninitialized, but counter initialized.
    unsafe fn allocate_for_slice(len: usize) -> NonNull<RcBox<[MaybeUninit<T>], C>> {
        let layout_value = Layout::array::<T>(len).unwrap();
        let (layout_nopad, _) = Self::layout_nopad(layout_value).unwrap();
        let tp = std::alloc::alloc(layout_nopad.pad_to_align());
        let mut tp = NonNull::new(tp).unwrap();
        // Convert thin pointer to fat pointer.
        let fp = std::ptr::slice_from_raw_parts_mut(tp.as_mut(), len);
        let pbox = fp as *mut RcBox<[MaybeUninit<T>], C>;
        let mut pbox = NonNull::new(pbox).unwrap_unchecked();
        std::ptr::write(&mut pbox.as_mut().strong, C::one());
        pbox
    }
    unsafe fn assume_init_slice(
        ptr: NonNull<RcBox<[MaybeUninit<T>], C>>,
    ) -> NonNull<RcBox<[T], C>> {
        NonNull::new(ptr.as_ptr() as *mut RcBox<[T], C>).unwrap_unchecked()
    }

    /// Allocate and initialize an RcBox from a raw pointer.
    ///
    /// Returns a pointer to the allocated RcBox;
    /// its contents are copied from the ptr, and counter initialized.
    unsafe fn alloc_copy_from_ptr(ptr: *const T) -> NonNull<RcBox<T, C>> {
        let (layout_nopad, offset) = Self::layout_nopad_for_value(&*ptr).unwrap();
        let nopad_size = layout_nopad.size();
        let pthin = std::alloc::alloc(layout_nopad.pad_to_align());
        let pthin = NonNull::new(pthin).unwrap();
        let pvalue = pthin.as_ptr().add(offset);

        // memcpy the contents.
        assume!(offset <= nopad_size);
        let copy_size = nopad_size - offset;
        std::ptr::copy_nonoverlapping(ptr as *const u8, pvalue, copy_size);

        let mut pbox = pthin.cast::<RcBox<T, C>>();

        // Initialize the counter
        std::ptr::write(&mut pbox.as_mut().strong, C::one());

        pbox
    }
}

impl<T, C: RefCount> RcBox<T, C> {
    unsafe fn as_uninit(&mut self) -> &mut RcBox<MaybeUninit<T>, C> {
        mem::transmute(self)
    }
}

/// Base type of [RcX] and [ArcX]
pub(crate) struct RcBase<T: ?Sized, C: RefCount> {
    ptr: NonNull<RcBox<T, C>>,

    // NOTE PhantomData for dropck.
    // This field indicates that this struct owns the data of type RcBox<T, C>.
    _phantom: PhantomData<RcBox<T, C>>,
}

unsafe impl<T, C> Send for RcBase<T, C>
where
    T: ?Sized + Sync + Send,
    C: RefCount + Sync + Send,
{
}
unsafe impl<T, C> Sync for RcBase<T, C>
where
    T: ?Sized + Sync + Send,
    C: RefCount + Sync + Send,
{
}

impl<T: RefUnwindSafe + ?Sized, C: RefCount> UnwindSafe for RcBase<T, C> {}
impl<T: RefUnwindSafe + ?Sized, C: RefCount> RefUnwindSafe for RcBase<T, C> {}

impl<T, C: RefCount> RcBase<T, C> {
    unsafe fn unwrap_unchecked(self) -> T {
        assume!(RcBase::is_unique(&self));

        // this forgets calling RcBase's destructor.
        let mut this: ManuallyDrop<Self> = ManuallyDrop::new(self);

        // uninit_rcbox prevents calling T's destructor.
        let uninit_rcbox: &mut RcBox<MaybeUninit<T>, C> = this.ptr.as_mut().as_uninit();

        // this_box deallocates its memory at the end of this function, but does not call T's destructor.
        let _this_box: Box<RcBox<MaybeUninit<T>, C>> = Box::from_raw(uninit_rcbox);

        // move the value
        uninit_rcbox.value.assume_init_read()
    }

    pub(crate) fn new(value: T) -> RcBase<T, C> {
        unsafe {
            Self::from_inner(
                Box::leak(Box::new(RcBox {
                    strong: C::one(),
                    value,
                }))
                .into(),
            )
        }
    }

    pub(crate) fn try_unwrap(this: Self) -> Result<T, Self> {
        if Self::is_unique(&this) {
            unsafe { Ok(Self::unwrap_unchecked(this)) }
        } else {
            Err(this)
        }
    }

    unsafe fn from_box(v: Box<T>) -> RcBase<T, C> {
        let ptr = v.as_ref() as *const T;
        let inner = RcBox::<T, C>::alloc_copy_from_ptr(ptr);

        deallocate_box(v);

        RcBase::from_inner(inner)
    }

    pub(crate) unsafe fn from_raw(ptr: *const T) -> Self {
        assume!(!ptr.is_null());

        let offset = RcBox::<T, C>::offset_of_value(&*ptr);

        // Fix address of the pointer.
        let address = ptr as usize;
        assume!(offset <= address);
        let pbox = address - offset;

        // Reinterpret the pptr as a pointer to RcBox.
        let pbox = pbox as *mut RcBox<T, C>;

        Self::from_inner(NonNull::new(pbox).unwrap_unchecked())
    }

    pub(crate) unsafe fn increment_strong_count(ptr: *const T) {
        let rc = Self::from_raw(ptr);
        // Increment the refcount, but do not drop it.
        mem::forget(rc.clone());
        mem::forget(rc);
    }

    pub(crate) unsafe fn decrement_strong_count(ptr: *const T) {
        let rc = Self::from_raw(ptr);
        // Decrement the refcount by dropping it.
        drop(rc);
    }
}

/// Deallocate the box without dropping its contents
unsafe fn deallocate_box<T: ?Sized>(v: Box<T>) {
    let _drop = Box::from_raw(Box::into_raw(v) as *mut ManuallyDrop<T>);
}

impl<T: ?Sized, C: RefCount> RcBase<T, C> {
    unsafe fn inner(&self) -> &RcBox<T, C> {
        self.ptr.as_ref()
    }

    unsafe fn inner_mut(&mut self) -> &mut RcBox<T, C> {
        self.ptr.as_mut()
    }

    unsafe fn from_inner(ptr: NonNull<RcBox<T, C>>) -> Self {
        Self {
            ptr,
            _phantom: PhantomData,
        }
    }

    pub(crate) fn as_ptr(this: &Self) -> *const T {
        // The value should be initialized.
        unsafe { &(*NonNull::as_ptr(this.ptr)).value }
    }

    pub(crate) fn into_raw(this: Self) -> *const T {
        let ptr = Self::as_ptr(&this);
        mem::forget(this);
        ptr
    }

    pub(crate) fn strong_count(this: &Self) -> C::Value {
        unsafe { this.inner().strong().load() }
    }

    fn is_unique(this: &Self) -> bool {
        C::is_one(&Self::strong_count(this))
    }

    unsafe fn get_mut_unchecked(this: &mut Self) -> &mut T {
        &mut this.inner_mut().value
    }

    pub(crate) fn get_mut(this: &mut Self) -> Option<&mut T> {
        if Self::is_unique(this) {
            Some(unsafe { Self::get_mut_unchecked(this) })
        } else {
            None
        }
    }

    pub(crate) fn ptr_eq(this: &Self, other: &Self) -> bool {
        Self::as_ptr(this) == Self::as_ptr(other)
    }
}

impl<T: Clone, C: RefCount> RcBase<T, C> {
    pub(crate) fn make_mut(this: &mut Self) -> &mut T {
        if !Self::is_unique(this) {
            *this = Self::new((**this).clone());
        }
        unsafe { Self::get_mut_unchecked(this) }
    }
}

impl<T: ?Sized, C: RefCount> Deref for RcBase<T, C> {
    type Target = T;

    fn deref(&self) -> &T {
        unsafe { &self.inner().value }
    }
}

impl<T: ?Sized, C: RefCount> Drop for RcBase<T, C> {
    fn drop(&mut self) {
        unsafe {
            if C::is_one(&self.inner().strong().fetch_dec()) {
                drop(Box::from_raw(self.ptr.as_mut()));
            }
        }
    }
}

impl<T: ?Sized, C: RefCount> Clone for RcBase<T, C> {
    fn clone(&self) -> RcBase<T, C> {
        unsafe {
            self.inner().strong().fetch_inc();
            Self::from_inner(self.ptr)
        }
    }
}

impl<T: Default, C: RefCount> Default for RcBase<T, C> {
    fn default() -> RcBase<T, C> {
        RcBase::new(Default::default())
    }
}

impl<T: ?Sized + PartialEq, C: RefCount> PartialEq for RcBase<T, C> {
    fn eq(&self, other: &RcBase<T, C>) -> bool {
        // NOTE
        // Optimization by comparing their addresses can not be used for T: PartialEq.
        // For T: Eq, it is possible. But the specialization is unstable feature.
        PartialEq::eq(&**self, &**other)
    }
    fn ne(&self, other: &RcBase<T, C>) -> bool {
        PartialEq::ne(&**self, &**other)
    }
}

impl<T: ?Sized + Eq, C: RefCount> Eq for RcBase<T, C> {}

impl<T: ?Sized + PartialOrd, C: RefCount> PartialOrd for RcBase<T, C> {
    fn partial_cmp(&self, other: &RcBase<T, C>) -> Option<Ordering> {
        PartialOrd::partial_cmp(&**self, &**other)
    }
}

impl<T: ?Sized + Ord, C: RefCount> Ord for RcBase<T, C> {
    fn cmp(&self, other: &RcBase<T, C>) -> Ordering {
        Ord::cmp(&**self, &**other)
    }
}

impl<T: ?Sized + Hash, C: RefCount> Hash for RcBase<T, C> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        Hash::hash(&**self, state)
    }
}

impl<T: ?Sized + fmt::Display, C: RefCount> fmt::Display for RcBase<T, C> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Display::fmt(&**self, f)
    }
}

impl<T: ?Sized + fmt::Debug, C: RefCount> fmt::Debug for RcBase<T, C> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Debug::fmt(&**self, f)
    }
}

impl<T: ?Sized, C: RefCount> fmt::Pointer for RcBase<T, C> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Pointer::fmt(&(RcBase::as_ptr(self)), f)
    }
}

impl<T, C: RefCount> From<T> for RcBase<T, C> {
    fn from(t: T) -> Self {
        Self::new(t)
    }
}

impl<T: Clone, C: RefCount> From<&[T]> for RcBase<[T], C> {
    fn from(v: &[T]) -> RcBase<[T], C> {
        unsafe {
            let mut pbox = RcBox::<T, C>::allocate_for_slice(v.len());
            let pvalue = &mut pbox.as_mut().value as *mut [MaybeUninit<T>];
            assume!((*pvalue).len() == v.len());
            for i in 0..v.len() {
                *(*pvalue).get_unchecked_mut(i) = MaybeUninit::new(v.get_unchecked(i).clone());
            }
            Self::from_inner(RcBox::assume_init_slice(pbox))
        }
    }
}

impl<C: RefCount> From<&str> for RcBase<str, C> {
    fn from(s: &str) -> RcBase<str, C> {
        let rc = RcBase::<[u8], C>::from(s.as_bytes());
        unsafe { mem::transmute(rc) }
    }
}

impl<C: RefCount> From<String> for RcBase<str, C> {
    fn from(s: String) -> RcBase<str, C> {
        RcBase::from(s.as_ref())
    }
}

impl<C: RefCount> From<&CStr> for RcBase<CStr, C> {
    fn from(s: &CStr) -> RcBase<CStr, C> {
        let rc = RcBase::<[u8], C>::from(s.to_bytes_with_nul());
        unsafe { mem::transmute(rc) }
    }
}

impl<C: RefCount> From<CString> for RcBase<CStr, C> {
    fn from(s: CString) -> RcBase<CStr, C> {
        RcBase::from(s.as_ref())
    }
}

impl<T, C: RefCount> From<Box<T>> for RcBase<T, C> {
    fn from(b: Box<T>) -> RcBase<T, C> {
        unsafe { RcBase::from_box(b) }
    }
}

impl<T, C: RefCount> From<Vec<T>> for RcBase<[T], C> {
    fn from(mut v: Vec<T>) -> RcBase<[T], C> {
        unsafe {
            let mut pbox = RcBox::<T, C>::allocate_for_slice(v.len());
            let pvalue = &mut pbox.as_mut().value as *mut [MaybeUninit<T>];
            std::ptr::copy_nonoverlapping(
                v.as_ptr() as *const MaybeUninit<T>,
                pvalue as *mut MaybeUninit<T>,
                v.len(),
            );

            // Deallocate the vec without dropping its contents.
            v.set_len(0);

            Self::from_inner(RcBox::assume_init_slice(pbox))
        }
    }
}

impl<C: RefCount> From<RcBase<str, C>> for RcBase<[u8], C> {
    fn from(rc: RcBase<str, C>) -> Self {
        unsafe { mem::transmute(rc) }
    }
}

impl<T, C: RefCount, const N: usize> TryFrom<RcBase<[T], C>> for RcBase<[T; N], C> {
    type Error = RcBase<[T], C>;

    fn try_from(boxed_slice: RcBase<[T], C>) -> Result<Self, Self::Error> {
        if boxed_slice.len() == N {
            Ok(unsafe { RcBase::from_raw(RcBase::into_raw(boxed_slice) as *mut [T; N]) })
        } else {
            Err(boxed_slice)
        }
    }
}

impl<T, C: RefCount> iter::FromIterator<T> for RcBase<[T], C> {
    fn from_iter<I: iter::IntoIterator<Item = T>>(iter: I) -> Self {
        Self::from(iter.into_iter().collect::<Vec<T>>())
    }
}

impl<T: ?Sized, C: RefCount> borrow::Borrow<T> for RcBase<T, C> {
    fn borrow(&self) -> &T {
        &**self
    }
}

impl<T: ?Sized, C: RefCount> AsRef<T> for RcBase<T, C> {
    fn as_ref(&self) -> &T {
        &**self
    }
}

impl<T: ?Sized, C: RefCount> Unpin for RcBase<T, C> {}

#[cfg(test)]
mod tests {
    use super::*;
    use std::borrow::Borrow;
    use std::cell::Cell;

    type Rc8<T> = RcBase<T, Cell<u8>>;
    type StdRc<T> = std::rc::Rc<T>;

    #[test]
    fn new_deref() {
        let rc = Rc8::new(1);
        assert_eq!(*rc, 1);
    }

    #[test]
    fn clone_drop_strong_count() {
        let rc1 = Rc8::new(1);
        assert_eq!(RcBase::strong_count(&rc1), 1);

        let rc2 = rc1.clone();
        assert_eq!(RcBase::strong_count(&rc1), 2);
        assert_eq!(RcBase::strong_count(&rc2), 2);
        assert_eq!(*rc1, 1);
        assert_eq!(*rc2, 1);

        drop(rc1);
        assert_eq!(RcBase::strong_count(&rc2), 1);
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

        assert_eq!(format!("{:p}", rc), format!("{:p}", RcBase::as_ptr(&rc)));
    }

    #[test]
    fn as_ptr() {
        let rc = Rc8::<u32>::new(1);

        unsafe {
            assert_eq!(*RcBase::as_ptr(&rc), 1);
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

    #[test]
    fn into_raw() {
        let rc = Rc8::<i32>::new(1i32);
        let ptr = Rc8::as_ptr(&rc);

        let raw = Rc8::into_raw(rc);
        assert_eq!(raw, ptr);

        unsafe { Rc8::from_raw(raw) };
    }

    #[test]
    fn from_raw() {
        let rc = Rc8::<i32>::new(1i32);
        let ptr = Rc8::as_ptr(&rc);

        let raw = Rc8::into_raw(rc);
        assert_eq!(raw, ptr);

        let rc2 = unsafe { Rc8::from_raw(raw) };
        let ptr2 = Rc8::as_ptr(&rc2);
        assert_eq!(ptr, ptr2);
        assert_eq!(*rc2, 1);
    }

    #[test]
    fn increment_decrement_strong_count() {
        let rc = Rc8::<i32>::new(1i32);
        let rc2 = rc.clone();
        let ptr = Rc8::into_raw(rc2);

        assert_eq!(Rc8::strong_count(&rc), 2);
        unsafe {
            Rc8::increment_strong_count(ptr);
        }
        assert_eq!(Rc8::strong_count(&rc), 3);

        unsafe {
            Rc8::decrement_strong_count(ptr);
        }
        assert_eq!(Rc8::strong_count(&rc), 2);

        unsafe {
            let _rc3 = Rc8::from_raw(ptr);
        }
    }

    #[test]
    fn from_vec() {
        let rc = Rc8::<[i64]>::from(vec![0, 1, 2, 3, 4]);
        assert_eq!(rc.len(), 5);
        assert_eq!(rc[0], 0);
        assert_eq!(rc[1], 1);
        assert_eq!(rc[2], 2);
        assert_eq!(rc[3], 3);
        assert_eq!(rc[4], 4);
    }

    #[test]
    fn from_large_vec() {
        let v = (0..1000).collect::<Vec<_>>();
        let rc = Rc8::<[i64]>::from(v);
        assert_eq!(rc.len(), 1000);
        for i in 0..1000 {
            assert_eq!(rc[i], i as i64);
        }
    }

    #[test]
    fn from_iter() {
        let rc = Rc8::<[i64]>::from_iter(0..5);
        assert_eq!(rc.len(), 5);
        assert_eq!(rc[0], 0);
        assert_eq!(rc[1], 1);
        assert_eq!(rc[2], 2);
        assert_eq!(rc[3], 3);
        assert_eq!(rc[4], 4);
    }

    #[test]
    fn from_slice() {
        let data = [0, 1, 2, 3, 4];
        let rc = Rc8::<[i64]>::from(&data[..]);
        assert_eq!(rc.len(), 5);
        assert_eq!(rc[0], 0);
        assert_eq!(rc[1], 1);
        assert_eq!(rc[2], 2);
        assert_eq!(rc[3], 3);
        assert_eq!(rc[4], 4);
    }

    #[test]
    fn from_str() {
        let s = "Hello";
        let rc = Rc8::<str>::from(s);
        assert_eq!(rc.len(), 5);
        assert_eq!(&*rc, "Hello");
    }

    #[test]
    fn from_string() {
        let s = "Hello".to_string();
        let rc = Rc8::<str>::from(s);
        assert_eq!(rc.len(), 5);
        assert_eq!(&*rc, "Hello");
    }

    #[test]
    fn from_cstr() {
        let s = CString::new("Hello").unwrap();
        let cs = s.as_c_str();
        let rc = Rc8::<CStr>::from(cs);
        let bytes = rc.to_bytes_with_nul();
        assert_eq!(bytes.len(), 6);
        assert_eq!(bytes, b"Hello\0");
    }

    #[test]
    fn from_cstring() {
        let s = CString::new("Hello").unwrap();
        let rc = Rc8::<CStr>::from(s);
        let bytes = rc.to_bytes_with_nul();
        assert_eq!(bytes.len(), 6);
        assert_eq!(bytes, b"Hello\0");
    }

    #[test]
    fn str_to_slice() {
        let s = "Hello";
        let rc_str = Rc8::<str>::from(s);
        let rc_slice = Rc8::<[u8]>::from(rc_str);

        assert_eq!(rc_slice.len(), 5);
        assert_eq!(rc_slice[0], b'H');
        assert_eq!(rc_slice[1], b'e');
        assert_eq!(rc_slice[2], b'l');
        assert_eq!(rc_slice[3], b'l');
        assert_eq!(rc_slice[4], b'o');
    }

    #[test]
    fn from_box() {
        let b = Box::<String>::from("Hello".to_string());
        let rc = Rc8::<String>::from(b);
        assert_eq!(&*rc, "Hello");
    }

    #[test]
    fn try_from() {
        let data = [0, 1, 2, 3, 4];
        {
            let rc_slice3 = Rc8::<[i64]>::from(&data[1..4]);
            let rc1 = Rc8::<[i64; 1]>::try_from(rc_slice3);
            assert!(rc1.is_err());
        }
        {
            let rc_slice3 = Rc8::<[i64]>::from(&data[1..4]);
            let rc = Rc8::<[i64; 2]>::try_from(rc_slice3);
            assert!(rc.is_err());
        }
        {
            let rc_slice3 = Rc8::<[i64]>::from(&data[1..4]);
            let rc = Rc8::<[i64; 3]>::try_from(rc_slice3);
            assert!(rc.is_ok());
            let rc = rc.unwrap();
            assert_eq!(rc[0], 1);
            assert_eq!(rc[1], 2);
            assert_eq!(rc[2], 3);
        }
        {
            let rc_slice3 = Rc8::<[i64]>::from(&data[1..4]);
            let rc = Rc8::<[i64; 4]>::try_from(rc_slice3);
            assert!(rc.is_err());
        }
        {
            let rc_slice3 = Rc8::<[i64]>::from(&data[1..4]);
            let rc = Rc8::<[i64; 5]>::try_from(rc_slice3);
            assert!(rc.is_err());
        }
    }
}

#[cfg(test)]
mod leak_ckeck {
    use super::*;
    use std::cell::Cell;
    use std::sync::atomic::{AtomicU8, AtomicUsize, Ordering};
    use std::thread;

    type Rc8<T> = RcBase<T, Cell<u8>>;
    type Arc8<T> = RcBase<T, AtomicU8>;

    struct DropCount<'a> {
        drop_count: &'a AtomicUsize,
    }
    impl<'a> DropCount<'a> {
        fn new(drop_count: &'a AtomicUsize) -> Self {
            DropCount { drop_count }
        }
    }

    impl<'a> Drop for DropCount<'a> {
        fn drop(&mut self) {
            self.drop_count.fetch_add(1, Ordering::SeqCst);
        }
    }

    #[test]
    fn send() {
        static DROP_COUNT: AtomicUsize = AtomicUsize::new(0);

        let rc = Arc8::new(DropCount::new(&DROP_COUNT));

        let rc2 = rc.clone();
        let th = thread::spawn(move || {
            drop(rc2);
        });

        drop(rc);

        th.join().unwrap();

        assert_eq!(DROP_COUNT.load(Ordering::SeqCst), 1);
    }

    #[test]
    fn sync() {
        static DROP_COUNT: AtomicUsize = AtomicUsize::new(0);

        let rc = Arc8::new(DropCount::new(&DROP_COUNT));

        thread::scope(|s| {
            s.spawn(|| {
                let rc2 = rc.clone();
                drop(rc2);
                assert_eq!(DROP_COUNT.load(Ordering::SeqCst), 0);
            });
        });

        drop(rc);
        assert_eq!(DROP_COUNT.load(Ordering::SeqCst), 1);
    }

    #[test]
    fn single() {
        let drop_count = AtomicUsize::new(0);
        let rc = Rc8::new(DropCount::new(&drop_count));
        drop(rc);
        assert_eq!(drop_count.into_inner(), 1);
    }

    #[test]
    fn clone() {
        let drop_count = AtomicUsize::new(0);
        let rc = Rc8::new(DropCount::new(&drop_count));
        let rc2 = rc.clone();
        drop(rc);
        drop(rc2);
        assert_eq!(drop_count.into_inner(), 1);
    }

    #[test]
    fn try_unwrap() {
        {
            let drop_count = AtomicUsize::new(0);
            {
                let rc = Rc8::new(DropCount::new(&drop_count));
                let v = Rc8::try_unwrap(rc);
                assert!(v.is_ok());
            }
            assert_eq!(drop_count.into_inner(), 1);
        }

        {
            let drop_count = AtomicUsize::new(0);
            {
                let rc = Rc8::new(DropCount::new(&drop_count));
                let _rc2 = rc.clone();
                let v = Rc8::try_unwrap(rc);
                assert!(v.is_err());
            }
            assert_eq!(drop_count.into_inner(), 1);
        }

        {
            let drop_count = AtomicUsize::new(0);
            {
                let rc = Rc8::new(DropCount::new(&drop_count));
                let rc2 = rc.clone();
                drop(rc2);
                let v = Rc8::try_unwrap(rc);
                assert!(v.is_ok());
            }
            assert_eq!(drop_count.into_inner(), 1);
        }
    }

    #[test]
    fn increment_decrement_strong_count() {
        let drop_count = AtomicUsize::new(0);
        let rc = Rc8::new(DropCount::new(&drop_count));
        let rc2 = rc.clone();
        let ptr = Rc8::into_raw(rc2);

        unsafe {
            Rc8::increment_strong_count(ptr);
            Rc8::decrement_strong_count(ptr);
        }

        unsafe {
            let _rc3 = Rc8::from_raw(ptr);
        }
        drop(rc);

        assert_eq!(drop_count.into_inner(), 1);
    }

    #[test]
    fn from_box() {
        let drop_count = AtomicUsize::new(0);
        let b = Box::new(DropCount::new(&drop_count));
        let rc = Rc8::<DropCount>::from(b);
        drop(rc);
        assert_eq!(drop_count.into_inner(), 1);
    }

    #[test]
    fn from_vec() {
        let drop_counts0 = AtomicUsize::new(0);
        let drop_counts1 = AtomicUsize::new(0);
        let drop_counts2 = AtomicUsize::new(0);
        let drop_counts3 = AtomicUsize::new(0);
        let drop_counts4 = AtomicUsize::new(0);

        {
            let v = vec![
                DropCount::new(&drop_counts0),
                DropCount::new(&drop_counts1),
                DropCount::new(&drop_counts2),
                DropCount::new(&drop_counts3),
                DropCount::new(&drop_counts4),
            ];
            let rc = Rc8::<[DropCount]>::from(v);
            assert_eq!(rc.len(), 5);
        }

        assert_eq!(drop_counts0.into_inner(), 1);
        assert_eq!(drop_counts1.into_inner(), 1);
        assert_eq!(drop_counts2.into_inner(), 1);
        assert_eq!(drop_counts3.into_inner(), 1);
        assert_eq!(drop_counts4.into_inner(), 1);
    }

    #[test]
    fn from_iter() {
        let drop_counts0 = AtomicUsize::new(0);
        let drop_counts1 = AtomicUsize::new(0);
        let drop_counts2 = AtomicUsize::new(0);
        let drop_counts3 = AtomicUsize::new(0);
        let drop_counts4 = AtomicUsize::new(0);

        {
            let v = vec![
                DropCount::new(&drop_counts0),
                DropCount::new(&drop_counts1),
                DropCount::new(&drop_counts2),
                DropCount::new(&drop_counts3),
                DropCount::new(&drop_counts4),
            ];

            let rc = Rc8::<[DropCount]>::from_iter(v.into_iter());
            assert_eq!(rc.len(), 5);
        }

        assert_eq!(drop_counts0.into_inner(), 1);
        assert_eq!(drop_counts1.into_inner(), 1);
        assert_eq!(drop_counts2.into_inner(), 1);
        assert_eq!(drop_counts3.into_inner(), 1);
        assert_eq!(drop_counts4.into_inner(), 1);
    }
}

#[cfg(test)]
mod rcbox {
    use super::*;
    use std::cell::Cell;

    type RcBox8<T> = RcBox<T, Cell<u8>>;
    type RcBox16<T> = RcBox<T, Cell<u16>>;
    type RcBox32<T> = RcBox<T, Cell<u32>>;
    type RcBox64<T> = RcBox<T, Cell<u64>>;
    type RcBoxU<T> = RcBox<T, Cell<usize>>;

    #[test]
    fn offset_of_value() {
        unsafe {
            assert_eq!(1, RcBox8::<u8>::offset_of_value(&0));
            assert_eq!(2, RcBox16::<u8>::offset_of_value(&0));
            assert_eq!(4, RcBox32::<u8>::offset_of_value(&0));
            assert_eq!(8, RcBox64::<u8>::offset_of_value(&0));
            assert_eq!(8, RcBoxU::<u8>::offset_of_value(&0));
        }

        unsafe {
            assert_eq!(2, RcBox8::<u16>::offset_of_value(&0));
            assert_eq!(2, RcBox16::<u16>::offset_of_value(&0));
            assert_eq!(4, RcBox32::<u16>::offset_of_value(&0));
            assert_eq!(8, RcBox64::<u16>::offset_of_value(&0));
            assert_eq!(8, RcBoxU::<u16>::offset_of_value(&0));
        }

        unsafe {
            assert_eq!(4, RcBox8::<u32>::offset_of_value(&0));
            assert_eq!(4, RcBox16::<u32>::offset_of_value(&0));
            assert_eq!(4, RcBox32::<u32>::offset_of_value(&0));
            assert_eq!(8, RcBox64::<u32>::offset_of_value(&0));
            assert_eq!(8, RcBoxU::<u32>::offset_of_value(&0));
        }

        unsafe {
            assert_eq!(8, RcBox8::<u64>::offset_of_value(&0));
            assert_eq!(8, RcBox16::<u64>::offset_of_value(&0));
            assert_eq!(8, RcBox32::<u64>::offset_of_value(&0));
            assert_eq!(8, RcBox64::<u64>::offset_of_value(&0));
            assert_eq!(8, RcBoxU::<u64>::offset_of_value(&0));
        }

        unsafe {
            assert_eq!(8, RcBox8::<usize>::offset_of_value(&0));
            assert_eq!(8, RcBox16::<usize>::offset_of_value(&0));
            assert_eq!(8, RcBox32::<usize>::offset_of_value(&0));
            assert_eq!(8, RcBox64::<usize>::offset_of_value(&0));
            assert_eq!(8, RcBoxU::<usize>::offset_of_value(&0));
        }

        unsafe {
            assert_eq!(2, RcBox8::<(u8, u16)>::offset_of_value(&(0, 0)));
            assert_eq!(2, RcBox16::<(u8, u16)>::offset_of_value(&(0, 0)));
            assert_eq!(4, RcBox32::<(u8, u16)>::offset_of_value(&(0, 0)));
            assert_eq!(8, RcBox64::<(u8, u16)>::offset_of_value(&(0, 0)));
            assert_eq!(8, RcBoxU::<(u8, u16)>::offset_of_value(&(0, 0)));
        }
    }

    #[test]
    fn offset_of_value_unsized() {
        // slice
        unsafe {
            let value = [0, 1, 2, 3];
            assert_eq!(1, RcBox8::<[u8]>::offset_of_value(&value));
            assert_eq!(2, RcBox16::<[u8]>::offset_of_value(&value));
            assert_eq!(4, RcBox32::<[u8]>::offset_of_value(&value));
            assert_eq!(8, RcBox64::<[u8]>::offset_of_value(&value));
            assert_eq!(8, RcBoxU::<[u8]>::offset_of_value(&value));
        }

        // slice
        unsafe {
            let value = [0, 1, 2, 3];
            assert_eq!(2, RcBox8::<[u16]>::offset_of_value(&value));
            assert_eq!(2, RcBox16::<[u16]>::offset_of_value(&value));
            assert_eq!(4, RcBox32::<[u16]>::offset_of_value(&value));
            assert_eq!(8, RcBox64::<[u16]>::offset_of_value(&value));
            assert_eq!(8, RcBoxU::<[u16]>::offset_of_value(&value));
        }

        // slice
        unsafe {
            let value = [0, 1, 2, 3];
            assert_eq!(4, RcBox8::<[u32]>::offset_of_value(&value));
            assert_eq!(4, RcBox16::<[u32]>::offset_of_value(&value));
            assert_eq!(4, RcBox32::<[u32]>::offset_of_value(&value));
            assert_eq!(8, RcBox64::<[u32]>::offset_of_value(&value));
            assert_eq!(8, RcBoxU::<[u32]>::offset_of_value(&value));
        }

        // slice
        unsafe {
            let value = [0, 1, 2, 3];
            assert_eq!(8, RcBox8::<[u64]>::offset_of_value(&value));
            assert_eq!(8, RcBox16::<[u64]>::offset_of_value(&value));
            assert_eq!(8, RcBox32::<[u64]>::offset_of_value(&value));
            assert_eq!(8, RcBox64::<[u64]>::offset_of_value(&value));
            assert_eq!(8, RcBoxU::<[u64]>::offset_of_value(&value));
        }

        // slice
        unsafe {
            let value = [0, 1, 2, 3];
            assert_eq!(8, RcBox8::<[usize]>::offset_of_value(&value));
            assert_eq!(8, RcBox16::<[usize]>::offset_of_value(&value));
            assert_eq!(8, RcBox32::<[usize]>::offset_of_value(&value));
            assert_eq!(8, RcBox64::<[usize]>::offset_of_value(&value));
            assert_eq!(8, RcBoxU::<[usize]>::offset_of_value(&value));
        }

        // str
        unsafe {
            let value = "Hello";
            assert_eq!(1, RcBox8::<str>::offset_of_value(value));
            assert_eq!(2, RcBox16::<str>::offset_of_value(value));
            assert_eq!(4, RcBox32::<str>::offset_of_value(value));
            assert_eq!(8, RcBox64::<str>::offset_of_value(value));
            assert_eq!(8, RcBoxU::<str>::offset_of_value(value));
        }

        // trait object
        unsafe {
            trait MyTrait {}
            struct MyStruct(u32);
            impl MyTrait for MyStruct {}
            let value = MyStruct(0);
            assert_eq!(4, RcBox8::<dyn MyTrait>::offset_of_value(&value));
            assert_eq!(4, RcBox16::<dyn MyTrait>::offset_of_value(&value));
            assert_eq!(4, RcBox32::<dyn MyTrait>::offset_of_value(&value));
            assert_eq!(8, RcBox64::<dyn MyTrait>::offset_of_value(&value));
            assert_eq!(8, RcBoxU::<dyn MyTrait>::offset_of_value(&value));
        }
    }
}
