/// FIXME A wrapper to deal with pointers to dynamically sized types in stable rust (version 1.68.2).
/// This code *assume* that the ptr is a fat pointer consists of two parts,
/// address and metadata, like (address: usize, metadata: usize).
/// Since the layout of fat pointer is not specified,
/// this should be rewritten in the future.
pub(crate) struct MaybeFatPtr<T: ?Sized> {
    ptr: *const T,
}

impl<T: ?Sized> MaybeFatPtr<T> {
    /// Initialize from raw pointer.
    /// The pointer may be a fat pointer or not.
    pub(crate) fn from_raw(maybe_fat_ptr: *const T) -> Self {
        Self { ptr: maybe_fat_ptr }
    }

    /// Consume self and get a raw pointer.
    pub(crate) fn into_raw(self) -> *const T {
        self.ptr
    }

    /// Obtain the reference to address part.
    pub(crate) unsafe fn address_part(&self) -> &usize {
        let pptr = (&self.ptr) as *const *const T;
        let ppfat = pptr as *const (usize, usize);
        &(*ppfat).0
    }

    /// Obtain the mutable reference to address part.
    pub(crate) unsafe fn address_part_mut(&mut self) -> &mut usize {
        let pptr = (&mut self.ptr) as *mut *const T;
        let ppfat = pptr as *mut (usize, usize);
        &mut (*ppfat).0
    }
}
