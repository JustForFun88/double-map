// This code partially use code from the [`Hashbrown`] crate
// [`Hashbrown`]: https://github.com/rust-lang/hashbrown

use super::offset_from;
use core::mem;
use core::ptr::NonNull;

/// A reference to a hash table bucket containing a `T`.
///
/// This is usually just a pointer to the element itself. However if the element
/// is a ZST, then we instead track the index of the element in the table so
/// that `erase` works properly.
pub struct DataBucket<T> {
    // Actually it is pointer to next element than element itself
    // this is needed to maintain pointer arithmetic invariants
    // keeping direct pointer to element introduces difficulty.
    // Using `NonNull` for variance and niche layout
    pub(super) ptr: NonNull<T>,
}

// This Send impl is needed for rayon support. This is safe since Bucket is
// never exposed in a public API.
unsafe impl<T> Send for DataBucket<T> {}

impl<T> Clone for DataBucket<T> {
    #[inline]
    fn clone(&self) -> Self {
        Self { ptr: self.ptr }
    }
}

impl<T> DataBucket<T> {
    /// Create [`DataBucket`] that contain pointer to the data.
    /// The pointer calculation is performed based on the given `index`
    /// and the `base point` (in the direction of decreasing address
    /// relative to the base point)
    #[inline]
    pub(super) unsafe fn from_base_index(base: NonNull<T>, index: usize) -> Self {
        let ptr = if mem::size_of::<T>() == 0 {
            // won't overflow because index must be less than length
            (index + 1) as *mut T
        } else {
            base.as_ptr().sub(index)
        };
        Self {
            ptr: NonNull::new_unchecked(ptr),
        }
    }

    /// Calculates the index of [`DataBucket`] as distance between two pointers.
    /// The returned value is in units of T: the distance in bytes divided by
    /// [`core::mem::size_of::<T>()`].
    #[inline]
    pub(super) unsafe fn to_base_index(&self, base: NonNull<T>) -> usize {
        if mem::size_of::<T>() == 0 {
            self.ptr.as_ptr() as usize - 1
        } else {
            offset_from(base.as_ptr(), self.ptr.as_ptr())
        }
    }

    /// Return raw unsafe pointer `*mut T` to `data`.
    #[inline]
    pub fn as_ptr(&self) -> *mut T {
        if mem::size_of::<T>() == 0 {
            // Just return an arbitrary ZST pointer which is properly aligned
            mem::align_of::<T>() as *mut T
        } else {
            unsafe { self.ptr.as_ptr().sub(1) }
        }
    }

    /// Сalculates a new [`DataBucket`] that adjacent to the given offset from the
    /// given [`DataBucket`] element. The returned pointer is used for iterators.
    #[inline]
    pub(super) unsafe fn next_n(&self, offset: usize) -> Self {
        let ptr = if mem::size_of::<T>() == 0 {
            (self.ptr.as_ptr() as usize + offset) as *mut T
        } else {
            self.ptr.as_ptr().sub(offset)
        };
        Self {
            ptr: NonNull::new_unchecked(ptr),
        }
    }

    /// Executes the destructor (if any) of the pointed-to `data value`.
    #[cfg_attr(feature = "inline-more", inline)]
    pub unsafe fn drop(&self) {
        self.as_ptr().drop_in_place();
    }

    /// Reads the `data value` from `self` without moving it. This leaves the
    /// memory in `self` unchanged.
    #[inline]
    pub unsafe fn read(&self) -> T {
        self.as_ptr().read()
    }

    /// Overwrites a memory location with the given `data value` without reading
    /// or dropping the old value.   
    #[inline]
    pub unsafe fn write(&self, val: T) {
        self.as_ptr().write(val);
    }

    /// Return immutable reference to `data`.
    #[inline]
    pub unsafe fn as_ref<'a>(&self) -> &'a T {
        &*self.as_ptr()
    }

    /// Return mutable reference to `data`.
    #[inline]
    pub unsafe fn as_mut<'a>(&self) -> &'a mut T {
        &mut *self.as_ptr()
    }

    /// Copies `count * size_of<T>` bytes from `other` to `self`. The source
    /// and destination may *not* overlap.
    ///
    /// Like [`read`], `copy_nonoverlapping` creates a bitwise copy of `T`, regardless of
    /// whether `T` is [`Copy`]. If `T` is not [`Copy`], using *both* the values
    /// in the region beginning at `*self` and the region beginning at `*other` can
    /// [violate memory safety].
    ///
    /// [`read`]: https://doc.rust-lang.org/core/ptr/fn.read.html
    /// [violate memory safety]: https://doc.rust-lang.org/std/ptr/fn.read.html#ownership-of-the-returned-value
    // #[cfg(feature = "raw")]
    #[inline]
    pub unsafe fn copy_from_nonoverlapping(&self, other: &Self) {
        self.as_ptr().copy_from_nonoverlapping(other.as_ptr(), 1);
    }
}

/// A reference to a hash table bucket containing a `T`.
///
/// This is usually just a pointer to the element itself.
/// Can not be ZST.
pub struct PointerBucket<T> {
    // Actually it is pointer to next element than element itself
    // this is needed to maintain pointer arithmetic invariants
    // keeping direct pointer to element introduces difficulty.
    // Using `NonNull` for variance and niche layout
    pub(super) ptr: NonNull<T>,
}

// This Send impl is needed for rayon support. This is safe since Bucket is
// never exposed in a public API.
unsafe impl<T> Send for PointerBucket<T> {}

impl<T> Clone for PointerBucket<T> {
    #[inline]
    fn clone(&self) -> Self {
        Self { ptr: self.ptr }
    }
}

impl<T> PointerBucket<DataBucket<T>> {
    /// Create correspondeng [`DataBucket`] from the given [`PointerBucket<DataBucket<T>>`].
    #[inline]
    pub unsafe fn to_data_bucket(self) -> DataBucket<T> {
        let ptr = NonNull::new_unchecked((*self.as_ptr()).as_ptr().add(1));
        DataBucket { ptr }
    }

    /// Return raw unsafe pointer `*mut T` to `data`.
    #[inline]
    pub unsafe fn as_data_ptr(&self) -> *mut T {
        (*self.as_ptr()).as_ptr()
    }

    /// Executes the destructor (if any) of the pointed-to `data value`.
    #[cfg_attr(feature = "inline-more", inline)]
    pub unsafe fn drop_data(&self) {
        (*self.as_ptr()).drop()
    }

    /// Reads the `data value` from `self` without moving it. This leaves the
    /// memory in `self` unchanged.
    #[inline]
    pub unsafe fn read_data(&self) -> T {
        (*self.as_ptr()).read()
    }

    /// Overwrites a memory location with the given `data value` without reading
    /// or dropping the old value.   
    #[inline]
    pub unsafe fn write_data(&self, val: T) {
        (*self.as_ptr()).write(val);
    }

    /// Return immutable reference to `data`.
    #[inline]
    pub unsafe fn as_data_ref<'a>(&self) -> &'a T {
        &*((*self.as_ptr()).as_ptr())
    }

    /// Return mutable reference to `data`.
    #[inline]
    pub unsafe fn as_data_mut<'a>(&self) -> &'a mut T {
        &mut *((*self.as_ptr()).as_ptr())
    }
}

impl<T> PointerBucket<T> {
    /// Create [`PointerBucket`] that will be contain pointer to the data,
    /// as [`DataBucket`].
    ///
    /// The pointer calculation is performed based on the given `index`
    /// and the `base point` (in the direction of decreasing address
    /// relative to the base point)
    #[inline]
    pub(super) unsafe fn from_base_index(base: NonNull<T>, index: usize) -> Self {
        // The fact that the size of our type is not equal to zero is guaranteed by
        // us, since only we can create this structure
        Self {
            ptr: NonNull::new_unchecked(base.as_ptr().sub(index)),
        }
    }

    /// Calculates the index of [`PointerBucket`] as distance between two pointers.
    /// The returned value is in units of `T`: the distance in bytes divided by
    /// [`core::mem::size_of::<T>()`]. `T` actually is [`DataBucket<T>`].
    #[inline]
    pub(super) unsafe fn to_base_index(&self, base: NonNull<T>) -> usize {
        // The fact that the size of our type is not equal to zero is guaranteed by
        // us, since only we can create this structure
        offset_from(base.as_ptr(), self.ptr.as_ptr())
    }

    /// Return raw unsafe pointer `*mut T`. In general `T` may be `*mut DataBucket<T>`.
    #[inline]
    pub(super) fn as_ptr(&self) -> *mut T {
        // The fact that the size of our type is not equal to zero is guaranteed by
        // us, since only we can create this structure
        unsafe { self.ptr.as_ptr().sub(1) }
    }

    /// Сalculates a [`PointerBucket`] that adjacent to the given offset from the
    /// given [`PointerBucket`] element. The returned pointer is used for iterators.
    #[inline]
    pub(super) unsafe fn next_n(&self, offset: usize) -> Self {
        // The fact that the size of our type is not equal to zero is guaranteed by
        // us, since only we can create this structure
        Self {
            ptr: NonNull::new_unchecked(self.ptr.as_ptr().sub(offset)),
        }
    }

    /// Reads the `pointer value` from `self` without moving it. This leaves the
    /// memory in `self` unchanged. `T` actually is [`DataBucket<T>`].
    #[allow(dead_code)]
    #[inline]
    pub(super) unsafe fn read(&self) -> T {
        self.as_ptr().read()
    }

    /// Overwrites a memory location with the given `pointer value` without reading
    /// or dropping the old value. `T` actually is [`DataBucket<T>`].
    #[inline]
    pub(super) unsafe fn write(&self, val: T) {
        self.as_ptr().write(val);
    }

    /// Return immutable reference to `pointer`.
    #[allow(dead_code)]
    #[inline]
    pub(super) unsafe fn as_ref<'a>(&self) -> &'a T {
        &*self.as_ptr()
    }

    /// Return mutable reference to `pointer`.
    #[allow(dead_code)]
    #[inline]
    pub(super) unsafe fn as_mut<'a>(&self) -> &'a mut T {
        &mut *self.as_ptr()
    }

    /// Copies `count * size_of<T>` bytes from `other` to `self`. The source
    /// and destination may *not* overlap. `T` actually is [`DataBucket<T>`].
    // #[cfg(feature = "raw")]
    #[allow(dead_code)]
    #[inline]
    pub(super) unsafe fn copy_from_nonoverlapping(&self, other: &Self) {
        self.as_ptr().copy_from_nonoverlapping(other.as_ptr(), 1);
    }
}
