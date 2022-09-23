// This code partially use code from the [`Hashbrown`] crate
// [`Hashbrown`]: https://github.com/rust-lang/hashbrown

#[cfg(test)]
mod test_raw_map;

use crate::alloc::alloc::{handle_alloc_error, Layout};
use crate::scopeguard::{guard, ScopeGuard};
use crate::TryReserveError;
use core::iter::FusedIterator;
use core::marker::PhantomData;
use core::mem;
use core::mem::{ManuallyDrop, MaybeUninit};
use core::ptr::NonNull;
use core::{hint, ptr};

cfg_if! {
    // Use the SSE2 implementation if possible: it allows us to scan 16 buckets
    // at once instead of 8. We don't bother with AVX since it would require
    // runtime dispatch and wouldn't gain us much anyways: the probability of
    // finding a match drops off drastically after the first few buckets.
    //
    // I attempted an implementation on ARM using NEON instructions, but it
    // turns out that most NEON instructions have multi-cycle latency, which in
    // the end outweighs any gains over the generic implementation.
    if #[cfg(all(
        target_feature = "sse2",
        any(target_arch = "x86", target_arch = "x86_64"),
        not(miri)
    ))] {
        mod sse2;
        use sse2 as imp;
    } else {
        #[path = "generic.rs"]
        mod generic;
        use generic as imp;
    }
}

mod alloc;
pub(crate) use self::alloc::{do_alloc, Allocator, Global};

mod bitmask;

use self::bitmask::{BitMask, BitMaskIter};
use self::imp::Group;

mod buckets;
pub use self::buckets::{DataBucket, PointerBucket};

// Branch prediction hint. This is currently only available on nightly but it
// consistently improves performance by 10-15%.
#[cfg(feature = "nightly")]
use core::intrinsics::{likely, unlikely};

// On stable we can use #[cold] to get a equivalent effect: this attributes
// suggests that the function is unlikely to be called
#[cfg(not(feature = "nightly"))]
#[inline]
#[cold]
fn cold() {}

#[cfg(not(feature = "nightly"))]
#[inline]
fn likely(b: bool) -> bool {
    if !b {
        cold();
    }
    b
}
#[cfg(not(feature = "nightly"))]
#[inline]
fn unlikely(b: bool) -> bool {
    if b {
        cold();
    }
    b
}

/// Calculates the distance between two pointers. The returned value is in
/// units of T: the distance in bytes divided by `mem::size_of::<T>()`.
#[inline]
unsafe fn offset_from<T>(to: *const T, from: *const T) -> usize {
    to.offset_from(from) as usize
}

/// Whether memory allocation errors should return an error or abort.
#[derive(Copy, Clone)]
enum Fallibility {
    Fallible,
    Infallible,
}

impl Fallibility {
    /// Error to return on capacity overflow.
    #[cfg_attr(feature = "inline-more", inline)]
    fn capacity_overflow(self) -> TryReserveError {
        match self {
            Fallibility::Fallible => TryReserveError::CapacityOverflow,
            Fallibility::Infallible => panic!("Hash table capacity overflow"),
        }
    }

    /// Error to return on allocation error.
    #[cfg_attr(feature = "inline-more", inline)]
    fn alloc_err(self, layout: Layout) -> TryReserveError {
        match self {
            Fallibility::Fallible => TryReserveError::AllocError { layout },
            Fallibility::Infallible => handle_alloc_error(layout),
        }
    }
}

/// Control byte value for an empty bucket.
const EMPTY: u8 = 0b1111_1111;

/// Control byte value for a deleted bucket.
const DELETED: u8 = 0b1000_0000;

/// Checks whether a control byte represents a full bucket (top bit is clear).
#[inline]
fn is_full(ctrl: u8) -> bool {
    ctrl & 0x80 == 0
}

/// Checks whether a control byte represents a special value (top bit is set).
#[inline]
fn is_special(ctrl: u8) -> bool {
    ctrl & 0x80 != 0
}

/// Checks whether a special control value is EMPTY (just check 1 bit).
#[inline]
fn special_is_empty(ctrl: u8) -> bool {
    debug_assert!(is_special(ctrl));
    ctrl & 0x01 != 0
}

/// Primary hash function, used to select the initial bucket to probe from.
#[inline]
#[allow(clippy::cast_possible_truncation)]
fn h1(hash: u64) -> usize {
    // On 32-bit platforms we simply ignore the higher hash bits.
    hash as usize
}

/// Secondary hash function, saved in the low 7 bits of the control byte.
#[inline]
#[allow(clippy::cast_possible_truncation)]
fn h2(hash: u64) -> u8 {
    // Grab the top 7 bits of the hash. While the hash is normally a full 64-bit
    // value, some hash functions (such as FxHash) produce a usize result
    // instead, which means that the top 32 bits are 0 on 32-bit platforms.
    let hash_len = usize::min(mem::size_of::<usize>(), mem::size_of::<u64>());
    let top7 = hash >> (hash_len * 8 - 7);
    (top7 & 0x7f) as u8 // truncation
}

/// Probe sequence based on triangular numbers, which is guaranteed (since our
/// table size is a power of two) to visit every group of elements exactly once.
///
/// A triangular probe has us jump by 1 more group every time. So first we
/// jump by 1 group (meaning we just continue our linear scan), then 2 groups
/// (skipping over 1 group), then 3 groups (skipping over 2 groups), and so on.
///
/// Proof that the probe will visit every group in the table:
/// <https://fgiesen.wordpress.com/2015/02/22/triangular-numbers-mod-2n/>
struct ProbeSeq {
    pos: usize,
    stride: usize,
}

impl ProbeSeq {
    #[inline]
    fn move_next(&mut self, bucket_mask: usize) {
        // We should have found an empty bucket by now and ended the probe.
        debug_assert!(
            self.stride <= bucket_mask,
            "Went past end of probe sequence"
        );

        self.stride += Group::WIDTH;
        self.pos += self.stride;
        self.pos &= bucket_mask;
    }
}

/// Returns the number of buckets needed to hold the given number of items,
/// taking the maximum load factor into account.
///
/// Returns `None` if an overflow occurs.
// Workaround for emscripten bug emscripten-core/emscripten-fastcomp#258
#[cfg_attr(target_os = "emscripten", inline(never))]
#[cfg_attr(not(target_os = "emscripten"), inline)]
fn capacity_to_buckets(cap: usize) -> Option<usize> {
    debug_assert_ne!(cap, 0);

    // For small tables we require at least 1 empty bucket so that lookups are
    // guaranteed to terminate if an element doesn't exist in the table.
    if cap < 8 {
        // We don't bother with a table size of 2 buckets since that can only
        // hold a single element. Instead we skip directly to a 4 bucket table
        // which can hold 3 elements.
        return Some(if cap < 4 { 4 } else { 8 });
    }

    // Otherwise require 1/8 buckets to be empty (87.5% load)
    //
    // Be careful when modifying this, calculate_layout relies on the
    // overflow check here.
    let adjusted_cap = cap.checked_mul(8)? / 7;

    // Any overflows will have been caught by the checked_mul. Also, any
    // rounding errors from the division above will be cleaned up by
    // next_power_of_two (which can't overflow because of the previous division).
    Some(adjusted_cap.next_power_of_two())
}

/// Returns the maximum effective capacity for the given bucket mask, taking
/// the maximum load factor into account.
#[inline]
fn bucket_mask_to_capacity(bucket_mask: usize) -> usize {
    if bucket_mask < 8 {
        // For tables with 1/2/4/8 buckets, we always reserve one empty slot.
        // Keep in mind that the bucket mask is one less than the bucket count.
        bucket_mask
    } else {
        // For larger tables we reserve 12.5% of the slots as empty.
        ((bucket_mask + 1) / 8) * 7
    }
}

/// Helper which allows memorize the `type_size` and the `pointer_size` of `T`,
/// the max calculation for `align` to be statically computed for each `T` while
/// keeping the rest of `calculate_layout_for` independent of `T`
#[derive(Copy, Clone)]
struct TableLayout {
    type_size: usize,
    pointer_size: usize,
    align: usize,
}

impl TableLayout {
    /// Create helper which allows memorize the `type_size` and the `pointer_size` of `T`,
    /// the max calculation for `align` to be statically computed for each `T` while
    /// keeping the rest of `calculate_layout_for` independent of `T`
    #[inline]
    pub fn new<T>() -> Self {
        let layout = Layout::new::<T>();
        let pointer_layout = Layout::new::<DataBucket<T>>();

        Self {
            type_size: layout.size(),
            pointer_size: pointer_layout.size(),
            align: usize::max(
                usize::max(layout.align(), pointer_layout.align()),
                Group::WIDTH,
            ),
        }
    }

    /// Function that return aligned necessary `Layout` for a table, as well as
    /// `ctrl_offset` and `pointers_ctrl_offset` necessary for calculation `data_ctrl: NonNull<u8>`,
    /// `pointers_ctrl: NonNull<u8>` that store pointers to the `data` and `pointers` control bits
    /// in the table respectively.
    #[inline]
    pub fn calculate_layout_for(self, buckets: usize) -> Option<(Layout, usize, usize)> {
        debug_assert!(buckets.is_power_of_two());

        let TableLayout {
            type_size,
            pointer_size,
            align,
        } = self;

        // Rough model of our memory looks like as shown below (we start counting from "0", so that
        // in the expression T[last], the "last" index actually one less than the given "buckets" number,
        // i.e. "last = buckets - 1"). It only reflects the amount of allocated memory, not the actual
        // arrangement of the elements:
        //
        //                                                            pointers_offset points here
        //                      ctrl_offset points here                     |                      pointers_ctrl_offset points here
        //                                ∨                                 ∨                              ∨
        // T0, T1, ..., Tlast, [Padding], CT0, CT1, ..., CTlast, [Padding], P0, P1, ..., Plast, [Padding], CP0, CP1, ..., CPlast, [Padding]
        // \____________  _____________/                                    \____________  _____________/
        //              \/                                                               \/
        //     type_size * buckets (with alignment)                               pointers_len (length of all pointers with alignment)
        // \____________________________________________________________  ________________________________________________________________/
        //                                                              \/
        //                                                    len (length of all allocation)
        //
        // where: Type of P = DataBucket<T>;
        //        T0...Tlast - our stored data;      CT0...CTlast - metadata for data;
        //        ^    ^
        //        |    |
        //        P0...Plast - our pointers to data; CP0...CPlast - metadata for pointers.
        //
        //
        // All pointers (ctrl_offset, pointers_offset, pointers_ctrl_offset) points at the start of the stored data
        //

        // Manual layout calculation since Layout methods are not yet stable.
        let ctrl_offset = type_size.checked_mul(buckets)?.checked_add(align - 1)? & !(align - 1);

        let pointers_offset = ctrl_offset
            .checked_add(buckets + Group::WIDTH)?
            .checked_add(align - 1)?
            & !(align - 1);

        let pointers_len =
            pointer_size.checked_mul(buckets)?.checked_add(align - 1)? & !(align - 1);

        let pointers_ctrl_offset = pointers_offset.checked_add(pointers_len)?;

        let len = pointers_ctrl_offset
            .checked_add(buckets + Group::WIDTH)?
            .checked_add(align - 1)?
            & !(align - 1);

        // We need an additional check to ensure that the allocation doesn't
        // exceed `isize::MAX` (https://github.com/rust-lang/rust/pull/95295).
        if len > isize::MAX as usize {
            // - (align - 1) {
            return None;
        }

        Some((
            unsafe { Layout::from_size_align_unchecked(len, align) },
            ctrl_offset,
            pointers_ctrl_offset,
        ))
    }
}

/// Returns a Layout which describes the allocation required for a hash table,
/// and the two offsets of the control bytes in the allocation. First offset of
/// the control bytes for the data itself, a second offset of the control bytes
/// for the pointers.
//
// This return the layout of memory of this type (see [`calculate_layout_for`] function):
//
// T0, T1, ..., Tlast, [Padding], CT0, CT1, ..., CTlast, [Padding], P0, P1, ..., Plast, [Padding], CP0, CP1, ..., CPlast, [Padding]
//                                ^ ctrl_offset                                                    ^ pointers_ctrl_offset
//                                  (first offset) points here                                     (second offset) points here
//                                  to the start of CT0                                            to the start of CP0
//
// where: Type of P = DataBucket<T>.
//
// But definitely we can assume that padding is at the beginning of the allocation, and actually
// use allocated memory as shown below. This usage makes it easier to calculate indexes when we
// start counting from the same point (ctrl_offset for data and pointers_ctrl_offset for pointers)
// but in opposite directions (to the right for control bytes, to the left for the data itself):
//
// [Padding], Tlast, ... T1, T0,  CT0, CT1, ..., CTlast, [Padding], Plast, ..., P1, P0, CP0, CP1, ..., CPlast, [Padding]
//                                ^ ctrl_offset                                         ^ pointers_ctrl_offset
//                                  (first offset) points here                            (second offset) points here
//                                  to the start of CT0                                   to the start of CP0
//
// where: Type of P = DataBucket<T>.
//
// So that the first offset is also one past last element of data buckets, and
// second offset is also one past last element of pointer type buckets. Second
// model is an actual model of how we store the data in the allocated memory
// (we start counting from "0", so that in the expression T[last], the "last"
// index actually one less than the given "buckets" number, i.e. "last = buckets - 1").
//
// Note: Pointers (P0...Plast) not actually point to the data elements (T0...Tlast)
// with the same index. First we use hasher_1 to store T[some index], then use hasher_2
// to store the pointer to it under P[some other index].
//
// Returns `None` if an overflow occurs.
#[cfg_attr(feature = "inline-more", inline)]
fn calculate_layout<T>(buckets: usize) -> Option<(Layout, usize, usize)> {
    TableLayout::new::<T>().calculate_layout_for(buckets)
}

/// A raw hash table with an unsafe API.
pub struct RawTable<T, A: Allocator + Clone = Global> {
    table: RawTableInner<A>,
    // Tell dropck that we own instances of T.
    marker: PhantomData<T>,
}

impl<T> RawTable<T, Global> {
    /// Creates a new empty hash table without allocating any memory.
    ///
    /// In effect this returns a table with exactly 1 bucket. However we can
    /// leave the data pointer dangling since that bucket is never written to
    /// due to our load factor forcing us to always have at least 1 free bucket.
    #[inline]
    pub const fn new() -> Self {
        Self {
            table: RawTableInner::new_in(Global),
            marker: PhantomData,
        }
    }

    /// Attempts to allocate a new hash table with at least enough capacity
    /// for inserting the given number of elements without reallocating.
    #[cfg(feature = "raw")]
    pub fn try_with_capacity(capacity: usize) -> Result<Self, TryReserveError> {
        Self::try_with_capacity_in(capacity, Global)
    }

    /// Allocates a new hash table with at least enough capacity for inserting
    /// the given number of elements without reallocating.
    pub fn with_capacity(capacity: usize) -> Self {
        Self::with_capacity_in(capacity, Global)
    }
}

impl<T, A: Allocator + Clone> RawTable<T, A> {
    /// Creates a new empty hash table without allocating any memory, using the
    /// given allocator.
    ///
    /// In effect this returns a table with exactly 1 bucket. However we can
    /// leave the data pointer dangling since that bucket is never written to
    /// due to our load factor forcing us to always have at least 1 free bucket.
    #[inline]
    pub fn new_in(alloc: A) -> Self {
        Self {
            table: RawTableInner::new_in(alloc),
            marker: PhantomData,
        }
    }

    /// Allocates a new hash table with the given number of `buckets`.
    /// Given number of `buckets` must be the power of 2, i.e.
    /// `buckets == 2^k` for some `k`.
    ///
    /// The control bytes for `data buckets` and `pointer buckets` are left
    /// uninitialized.
    #[cfg_attr(feature = "inline-more", inline)]
    unsafe fn new_uninitialized(
        alloc: A,
        buckets: usize,
        fallibility: Fallibility,
    ) -> Result<Self, TryReserveError> {
        debug_assert!(buckets.is_power_of_two());

        Ok(Self {
            table: RawTableInner::new_uninitialized(
                alloc,
                TableLayout::new::<T>(),
                buckets,
                fallibility,
            )?,
            marker: PhantomData,
        })
    }

    /// Attempts to allocate a new hash table with at least enough capacity
    /// for inserting the given number of elements without reallocating.
    ///
    /// All control bytes for `data buckets` and `pointer buckets` are
    /// initialized as `empty`.
    fn fallible_with_capacity(
        alloc: A,
        capacity: usize,
        fallibility: Fallibility,
    ) -> Result<Self, TryReserveError> {
        Ok(Self {
            table: RawTableInner::fallible_with_capacity(
                alloc,
                TableLayout::new::<T>(),
                capacity,
                fallibility,
            )?,
            marker: PhantomData,
        })
    }

    /// Attempts to allocate a new hash table using the given allocator, with at least enough
    /// capacity for inserting the given number of elements without reallocating.
    ///
    /// All control bytes for `data buckets` and `pointer buckets` are
    /// initialized as `empty`.
    #[cfg(feature = "raw")]
    pub fn try_with_capacity_in(capacity: usize, alloc: A) -> Result<Self, TryReserveError> {
        Self::fallible_with_capacity(alloc, capacity, Fallibility::Fallible)
    }

    /// Allocates a new hash table using the given allocator, with at least enough capacity for
    /// inserting the given number of elements without reallocating.
    ///
    /// All control bytes for `data buckets` and `pointer buckets` are
    /// initialized as `empty`.
    pub fn with_capacity_in(capacity: usize, alloc: A) -> Self {
        // Avoid `Result::unwrap_or_else` because it bloats LLVM IR.
        match Self::fallible_with_capacity(alloc, capacity, Fallibility::Infallible) {
            Ok(capacity) => capacity,
            Err(_) => unsafe { hint::unreachable_unchecked() },
        }
    }

    /// Returns a reference to the underlying allocator.
    #[inline]
    pub fn allocator(&self) -> &A {
        &self.table.alloc
    }

    /// Deallocates the table without dropping any entries.
    #[cfg_attr(feature = "inline-more", inline)]
    unsafe fn free_buckets(&mut self) {
        self.table.free_buckets(TableLayout::new::<T>());
    }

    /// Returns pointer to one past last `data element` `T` of the `data part` of the table
    /// as viewed from the start point of the allocation.
    ///
    /// Because actually we start counting from the beginning of the `data control bytes`,
    /// where we store our data under "0" index, when viewed from the base point
    /// (the beginning of the `data control bytes`), it returns a pointer to the end of the
    /// first `data element` from the `data part` of the table.
    //
    //                                data_end() return pointer
    //                                that points here in the data part of the table
    //                                (to the end of T0 or to the start of CT0,
    //                                which is the same)
    //                                ∨
    // [Padding], Tlast, ..., T1, T0, |CT0, CT1, ..., CTlast
    //
    // where: T0...Tlast - our stored data; CT0...CTlast - control bytes
    // or metadata for data.
    //
    // Note: We start counting from "0", so that in the expression CT[last] or T[last],
    // the "last" index actually one less than the given "buckets" number,
    // i.e. "last = buckets - 1".
    #[inline]
    pub unsafe fn data_end(&self) -> NonNull<T> {
        NonNull::new_unchecked(self.table.data_ctrl.as_ptr().cast())
    }

    /// Returns pointer to one past last `pointer element` of the `pointer part` of the table
    /// as viewed from the start point of the allocation.
    ///
    /// Because actually we start counting from the beginning of the `pointer control bytes`,
    /// where we store our pointer under "0" index, when viewed from the base point
    /// (the beginning of the `pointer control bytes`), it returns a pointer to the end of the
    /// first `pointer element` from the `pointer part` of the table.
    //
    //                                pointers_end() return pointer
    //                                that points here in the pointer part of the table
    //                                (to the end of P0 or to the start of CP0,
    //                                which is the same)
    //                                ∨
    // [Padding], Plast, ..., P1, P0, |CP0, CP1, ..., CPlast
    //
    // where: `P0...Plast` - our pointers to data; `CP0...CPlast` - control bytes
    // or metadata for pointers; type P = DataBucket<T>.
    //
    // Note: We start counting from "0", so that in the expression CP[last] or P[last],
    // the "last" index actually one less than the given "buckets" number,
    // i.e. "last = buckets - 1".
    #[inline]
    pub unsafe fn pointers_end(&self) -> NonNull<DataBucket<T>> {
        NonNull::new_unchecked(self.table.pointers_ctrl.as_ptr().cast())
    }

    /// Returns pointer to start of the `data part` of the table as viewed from the start
    /// point of the allocation.
    ///
    /// Because actually we start counting from the beginning of the `data control bytes`,
    /// where we store our data under "0" index, when viewed from the base point
    /// (the beginning of the `data control bytes`), it returns a pointer to the start of the
    /// last `data element` from the `data part` of the table.
    ///
    /// # Note
    ///
    /// Due to the table loading factor, the returned pointer always points to an
    /// uninitialized `T`.
    //
    //            data_start() return pointer
    //            that points here in the data part of the table
    //            (to the start of Tlast)
    //            ∨
    // [Padding], |Tlast, ..., T1, T0, CT0, CT1, ..., CTlast
    //
    // where: T0...Tlast - our stored data; CT0...CTlast - control bytes
    // or metadata for data.
    //
    // Note: We start counting from "0", so that in the expression CT[last] or T[last],
    // the "last" index actually one less than the given "buckets" number,
    // i.e. "last = buckets - 1".
    #[inline]
    #[cfg(feature = "nightly")]
    pub unsafe fn data_start(&self) -> *mut T {
        self.data_end().as_ptr().wrapping_sub(self.buckets())
    }

    /// Returns pointer to start of the `pointer part` of the table as viewed from the start
    /// point of the allocation.
    ///
    /// Because actually we start counting from the beginning of the `pointers control bytes`,
    /// where we store our pointer under "0" index, when viewed from the base point
    /// (the beginning of the `pointers control bytes`), it returns a pointer to the start of the
    /// last `pointer element` from the `pointers part` of the table.
    ///
    /// # Note
    ///
    /// Due to the table loading factor, the returned pointer always points to an
    /// uninitialized `DataBucket<T>`.
    //
    //            pointers_start() return pointer
    //            that points here in the pointers part of the table
    //            (to the start of Plast)
    //            ∨
    // [Padding], |Plast, ..., P1, P0, CP0, CP1, ..., CPlast
    //
    // where: `P0...Plast` - our pointers to data; `CP0...CPlast` - control bytes
    // or metadata for pointers; type P = DataBucket<T>.
    //
    // Note: We start counting from "0", so that in the expression CP[last] or P[last],
    // the "last" index actually one less than the given "buckets" number,
    // i.e. "last = buckets - 1".
    #[inline]
    #[cfg(feature = "nightly")]
    pub unsafe fn pointers_start(&self) -> *mut DataBucket<T> {
        self.pointers_end().as_ptr().wrapping_sub(self.buckets())
    }

    /// Returns the index of a `data bucket` in the `data part` of the table
    /// from a `DataBucket`.
    //
    //                        data_bucket(1).as_ptr() return pointer that
    //                        points here in tha data part of the table
    //                        (to the start of T1), so
    //                        data_index(data_bucket(1)) = 1
    //                        ∨
    // [Padding], Tlast, ..., |T1|, T0, CT0, CT1, ..., CTlast
    //                           ^
    //                           data_bucket(1) actually store the pointer
    //                           that points here in tha data part of the table
    //                           (to the end of T1)
    //
    // where: T0...Tlast - our stored data; CT0...CTlast - control bytes
    // or metadata for data.
    //
    // Note: We start counting from "0", so that in the expression CT[last] or T[last],
    // the "last" index actually one less than the given "buckets" number,
    // i.e. "last = buckets - 1".
    #[inline]
    pub unsafe fn data_index(&self, bucket: &DataBucket<T>) -> usize {
        bucket.to_base_index(self.data_end())
    }

    /// Returns the index of a `pointer bucket` in the `pointers part` of the table
    /// from a `PointerBucket`.
    //
    //                        pointer_bucket(1).as_ptr() return pointer
    //                        that points here in the pointer part of the table
    //                        (to the start of P1), so
    //                        pointer_index(pointer_bucket(1)) = 1
    //                        ∨
    // [Padding], Plast, ..., |P1|, P0, CP0, CP1, ..., CPlast
    //                           ^
    //                           pointer_bucket(1) actually store the
    //                           pointer that points here in the pointer part of the table
    //                           (to the end of P1)
    //
    // where: `P0...Plast` - our pointers to data; `CP0...CPlast` - control bytes
    // or metadata for pointers; type P = DataBucket<T>.
    //
    // Note: We start counting from "0", so that in the expression CP[last] or P[last],
    // the "last" index actually one less than the given "buckets" number,
    // i.e. "last = buckets - 1".
    #[inline]
    pub unsafe fn pointer_index(&self, bucket: &PointerBucket<DataBucket<T>>) -> usize {
        bucket.to_base_index(self.pointers_end())
    }

    /// Returns the two indexes from a `PointerBucket`. First one is a `data bucket` index in
    /// the `data part` of the table, second one is a `pointer bucket` index in the
    /// `pointers part` of the table.
    #[inline]
    pub unsafe fn data_pointer_indexes(
        &self,
        bucket: &PointerBucket<DataBucket<T>>,
    ) -> (usize, usize) {
        let index_2 = bucket.to_base_index(self.pointers_end());
        let index_1 = (*bucket.as_ptr()).to_base_index(self.data_end());
        (index_1, index_2)
    }

    /// Returns a pointer to a `data element` `T` in the data part of the table.
    //
    //                        data_bucket(1).as_ptr() return pointer that
    //                        points here in tha data part of the table
    //                        (to the start of T1)
    //                        ∨
    // [Padding], Tlast, ..., |T1|, T0, CT0, CT1, ..., CTlast
    //                           ^
    //                           data_bucket(1) actually store the pointer
    //                           that points here in tha data part of the table
    //                           (to the end of T1)
    //
    // where: T0...Tlast - our stored data; CT0...CTlast - control bytes
    // or metadata for data.
    #[inline]
    pub unsafe fn data_bucket(&self, index: usize) -> DataBucket<T> {
        debug_assert_ne!(self.table.bucket_mask, 0);
        debug_assert!(index < self.buckets());
        DataBucket::from_base_index(self.data_end(), index)
    }

    /// Returns a pointer to a `pointer element` in the pointer part of the table.
    //
    //                        pointer_bucket(1).as_ptr() return pointer
    //                        that points here in the pointer part of the table
    //                        (to the start of P1)
    //                        ∨
    // [Padding], Plast, ..., |P1|, P0, CP0, CP1, ..., CPlast
    //                           ^
    //                           pointer_bucket(1) actually store the
    //                           pointer that points here in the pointer part of the table
    //                           (to the end of P1)
    //
    // where: `P0...Plast` - our pointers to data; `CP0...CPlast` - control bytes
    // or metadata for pointers; type P = DataBucket<T>.
    #[inline]
    pub unsafe fn pointer_bucket(&self, index: usize) -> PointerBucket<DataBucket<T>> {
        debug_assert_ne!(self.table.bucket_mask, 0);
        debug_assert!(index < self.buckets());
        PointerBucket::from_base_index(self.pointers_end(), index)
    }

    /// Erases an element `T` from the table using both [`DataBucket<T>`] and
    /// [`PointerBucket<DataBucket<T>>`] to that element. Do not drop element `T`.
    ///
    /// Caller of this function must be ensure that [`DataBucket<T>`] and dereferenced
    /// [`PointerBucket<DataBucket<T>>`] arguments points to the same element `T`
    /// in the `data part` of the table. In other words this expression must be true:
    /// `core::ptr::eq(data.as_ptr(), ptr.as_data_ptr())`
    #[inline]
    unsafe fn erase_with_both_no_drop(
        &mut self,
        data: &DataBucket<T>,
        ptr: &PointerBucket<DataBucket<T>>,
    ) {
        let index_1 = self.data_index(data);
        let index_2 = self.pointer_index(ptr);
        self.table.erase(index_1, index_2);
    }

    /// Erases an element `T` from the table using both [`DataBucket<T>`] and
    /// [`PointerBucket<DataBucket<T>>`] to that element. Drop element `T` in place.
    ///
    /// Caller of this function must be ensure that [`DataBucket<T>`] and dereferenced
    /// [`PointerBucket<DataBucket<T>>`] arguments points to the same element `T`
    /// in the `data part` of the table. In other words this expression must be true:
    /// `core::ptr::eq(data.as_ptr(), ptr.as_data_ptr())`.
    ///
    /// Do not use copies of the [`DataBucket<T>`] and the [`PointerBucket<DataBucket<T>>`]
    /// to the same element `T` after calling this function.
    #[cfg(feature = "raw")]
    #[cfg_attr(feature = "inline-more", inline)]
    #[allow(clippy::needless_pass_by_value)]
    pub(crate) unsafe fn erase_with_both(
        &mut self,
        data: DataBucket<T>,
        ptr: PointerBucket<DataBucket<T>>,
    ) {
        debug_assert!(core::ptr::eq(data.as_ptr(), ptr.as_data_ptr()));
        // Erase the element from the table first since drop might panic.
        self.erase_with_both_no_drop(&data, &ptr);
        data.drop();
    }

    /// Erases an element `T` from the table using only [`PointerBucket<DataBucket<T>>`]
    /// to that element. Do not drop element `T`.
    #[inline]
    unsafe fn erase_no_drop(&mut self, ptr: &PointerBucket<DataBucket<T>>) {
        let (index_1, index_2) = self.data_pointer_indexes(ptr);
        debug_assert!(core::ptr::eq(
            self.data_bucket(index_1).as_ptr(),
            self.pointer_bucket(index_2).as_data_ptr()
        ));

        self.table.erase(index_1, index_2);
    }

    /// Erases an element `T` from the table using only [`PointerBucket<DataBucket<T>>`]
    /// to that element. Drop element `T` in place.
    ///
    /// Do not use copies of the [`DataBucket<T>`] and the [`PointerBucket<DataBucket<T>>`]
    /// to the same element `T` after calling this function.
    #[cfg_attr(feature = "inline-more", inline)]
    #[allow(clippy::needless_pass_by_value)]
    pub unsafe fn erase(&mut self, ptr: PointerBucket<DataBucket<T>>) {
        // Erase the element from the table first since drop might panic.
        self.erase_no_drop(&ptr);
        ptr.drop_data();
    }

    /// Finds and erases an element `T` from the table, dropping it in place.
    /// Returns true if an element `T` was found.
    ///
    /// Do not use copies of the [`DataBucket<T>`] and the [`PointerBucket<DataBucket<T>>`]
    /// to the same element `T` after calling this function.
    #[cfg(feature = "raw")]
    #[cfg_attr(feature = "inline-more", inline)]
    pub fn erase_entry<F1, F2>(&mut self, hash1: u64, eq1: F1, hash2: u64, eq2: F2) -> bool
    where
        F1: FnMut(&T) -> bool,
        F2: FnMut(&T) -> bool,
    {
        // Avoid `Option::map` because it bloats LLVM IR.
        match self.find(hash1, eq1, hash2, eq2) {
            Some((data, ptr)) => {
                unsafe { self.erase_with_both(data, ptr) };
                true
            }
            None => false,
        }
    }

    /// Finds and erases an element `T` from the table using second hash,
    /// for finding out [`PointerBucket<DataBucket<T>>`]. Drop element `T`
    /// in place. Returns true if an element `T` was found.
    ///
    /// Do not use copies of the [`DataBucket<T>`] and the [`PointerBucket<DataBucket<T>>`]
    /// to the same element `T` after calling this function.
    #[cfg(feature = "raw")]
    #[cfg_attr(feature = "inline-more", inline)]
    pub fn erase_entry_h2<F1, F2>(&mut self, hash2: u64, eq2: F2) -> bool
    where
        F2: FnMut(&T) -> bool,
    {
        // Avoid `Option::map` because it bloats LLVM IR.
        match self.find_h2(hash2, eq2) {
            Some(ptr) => {
                unsafe { self.erase(ptr) };
                true
            }
            None => false,
        }
    }

    /// Removes an element `T` from the table using both [`DataBucket<T>`] and
    /// [`PointerBucket<DataBucket<T>>`] to that element. Return the element `T`.
    ///
    /// Caller of this function must be ensure that [`DataBucket<T>`] and dereferenced
    /// [`PointerBucket<DataBucket<T>>`] arguments points to the same element `T`
    /// in the `data part` of the table. In other words this expression must be true:
    /// `core::ptr::eq(data.as_ptr(), ptr.as_data_ptr())`
    ///
    /// Do not use copies of the [`DataBucket<T>`] and the [`PointerBucket<DataBucket<T>>`]
    /// to the same element `T` after calling this function.
    #[cfg_attr(feature = "inline-more", inline)]
    #[allow(clippy::needless_pass_by_value)]
    pub(crate) unsafe fn remove_with_both(
        &mut self,
        data: DataBucket<T>,
        ptr: PointerBucket<DataBucket<T>>,
    ) -> T {
        debug_assert!(core::ptr::eq(data.as_ptr(), ptr.as_data_ptr()));
        self.erase_with_both_no_drop(&data, &ptr);
        data.read()
    }

    /// Removes an element `T` from the table using only [`PointerBucket<DataBucket<T>>`]
    /// to that element. Return the element `T`.
    ///
    /// Do not use copies of the [`DataBucket<T>`] and the [`PointerBucket<DataBucket<T>>`]
    /// to the same element `T` after calling this function.
    #[cfg_attr(feature = "inline-more", inline)]
    #[allow(clippy::needless_pass_by_value)]
    pub unsafe fn remove(&mut self, ptr: PointerBucket<DataBucket<T>>) -> T {
        self.erase_no_drop(&ptr);
        ptr.read_data()
    }

    /// Finds and removes an element `T` from the table, returning it.
    ///
    /// Do not use copies of the [`DataBucket<T>`] and the [`PointerBucket<DataBucket<T>>`]
    /// to the same element `T` after calling this function.
    #[cfg_attr(feature = "inline-more", inline)]
    pub fn remove_entry<F1, F2>(&mut self, hash1: u64, eq1: F1, hash2: u64, eq2: F2) -> Option<T>
    where
        F1: FnMut(&T) -> bool,
        F2: FnMut(&T) -> bool,
    {
        // Avoid `Option::map` because it bloats LLVM IR.
        match self.find(hash1, eq1, hash2, eq2) {
            Some((data, ptr)) => Some(unsafe { self.remove_with_both(data, ptr) }),
            None => None,
        }
    }

    /// Finds and removes an element `T` from the table using second hash,
    /// for finding out [`PointerBucket<DataBucket<T>>`]. Return the element `T`.
    ///
    /// Do not use copies of the [`DataBucket<T>`] and the [`PointerBucket<DataBucket<T>>`]
    /// to the same element `T` after calling this function.
    #[cfg_attr(feature = "inline-more", inline)]
    pub fn remove_entry_h2<F2>(&mut self, hash2: u64, eq2: F2) -> Option<T>
    where
        F2: FnMut(&T) -> bool,
    {
        // Avoid `Option::map` because it bloats LLVM IR.
        match self.find_h2(hash2, eq2) {
            Some(ptr) => Some(unsafe { self.remove(ptr) }),
            None => None,
        }
    }

    /// Marks all table buckets as empty without dropping data (`T`) contents.
    #[cfg_attr(feature = "inline-more", inline)]
    pub fn clear_no_drop(&mut self) {
        self.table.clear_no_drop();
    }

    /// Removes all elements from the table without freeing the backing memory.
    /// Drop all data (`T`) contents.
    #[cfg_attr(feature = "inline-more", inline)]
    pub fn clear(&mut self) {
        // Ensure that the table is reset even if one of the drops panic
        let mut self_ = guard(self, |self_| self_.clear_no_drop());
        unsafe {
            self_.drop_elements();
        }
    }

    unsafe fn drop_elements(&mut self) {
        if mem::needs_drop::<T>() && !self.is_empty() {
            for item in self.iter() {
                item.drop();
            }
        }
    }

    /// Shrinks the table to fit `max(self.len(), min_size)` elements.
    #[cfg_attr(feature = "inline-more", inline)]
    pub fn shrink_to<F1, F2>(&mut self, min_size: usize, hasher_1: F1, hasher_2: F2)
    where
        F1: Fn(&T) -> u64,
        F2: Fn(&T) -> u64,
    {
        // Calculate the minimal number of elements that we need to reserve
        // space for.
        let min_size = usize::max(self.table.items, min_size);
        if min_size == 0 {
            *self = Self::new_in(self.table.alloc.clone());
            return;
        }

        // Calculate the number of buckets that we need for this number of
        // elements. If the calculation overflows then the requested bucket
        // count must be larger than what we have right and nothing needs to be
        // done.
        let min_buckets = match capacity_to_buckets(min_size) {
            Some(buckets) => buckets,
            None => return,
        };

        // If we have more buckets than we need, shrink the table.
        if min_buckets < self.buckets() {
            // Fast path if the table is empty
            if self.table.items == 0 {
                *self = Self::with_capacity_in(min_size, self.table.alloc.clone());
            } else {
                // Avoid `Result::unwrap_or_else` because it bloats LLVM IR.
                if self
                    .resize(min_size, hasher_1, hasher_2, Fallibility::Infallible)
                    .is_err()
                {
                    unsafe { hint::unreachable_unchecked() }
                }
            }
        }
    }

    /// Ensures that at least `additional` items can be inserted into the table
    /// without reallocation.
    #[cfg_attr(feature = "inline-more", inline)]
    pub fn reserve<F1, F2>(&mut self, additional: usize, hasher_1: F1, hasher_2: F2)
    where
        F1: Fn(&T) -> u64,
        F2: Fn(&T) -> u64,
    {
        if additional > usize::min(self.table.data_growth_left, self.table.pointers_growth_left) {
            // Avoid `Result::unwrap_or_else` because it bloats LLVM IR.
            if self
                .reserve_rehash(additional, hasher_1, hasher_2, Fallibility::Infallible)
                .is_err()
            {
                unsafe { hint::unreachable_unchecked() }
            }
        }
    }

    /// Tries to ensure that at least `additional` items can be inserted into
    /// the table without reallocation.
    #[cfg_attr(feature = "inline-more", inline)]
    pub fn try_reserve<F1, F2>(
        &mut self,
        additional: usize,
        hasher_1: F1,
        hasher_2: F2,
    ) -> Result<(), TryReserveError>
    where
        F1: Fn(&T) -> u64,
        F2: Fn(&T) -> u64,
    {
        if additional > usize::min(self.table.data_growth_left, self.table.pointers_growth_left) {
            self.reserve_rehash(additional, hasher_1, hasher_2, Fallibility::Fallible)
        } else {
            Ok(())
        }
    }

    /// Out-of-line slow path for `reserve` and `try_reserve`.
    #[cold]
    #[inline(never)]
    fn reserve_rehash<F1, F2>(
        &mut self,
        additional: usize,
        hasher_1: F1,
        hasher_2: F2,
        fallibility: Fallibility,
    ) -> Result<(), TryReserveError>
    where
        F1: Fn(&T) -> u64,
        F2: Fn(&T) -> u64,
    {
        unsafe {
            self.table.reserve_rehash_inner::<T>(
                additional,
                &|table, index_1| hasher_1(table.data_bucket::<T>(index_1).as_ref()),
                &|table, index_2| hasher_2(table.data_bucket::<T>(index_2).as_ref()),
                // &|table, index_2| hasher_2(table.pointer_bucket::<T>(index_2).as_data_ref()),
                fallibility,
                TableLayout::new::<T>(),
                if mem::needs_drop::<T>() {
                    Some(mem::transmute(ptr::drop_in_place::<T> as unsafe fn(*mut T)))
                } else {
                    None
                },
            )
        }
    }

    /// Allocates a new table of a different size and moves the contents of the
    /// current table into it.
    fn resize<F1, F2>(
        &mut self,
        capacity: usize,
        hasher_1: F1,
        hasher_2: F2,
        fallibility: Fallibility,
    ) -> Result<(), TryReserveError>
    where
        F1: Fn(&T) -> u64,
        F2: Fn(&T) -> u64,
    {
        unsafe {
            self.table.resize_inner::<T>(
                capacity,
                &|table, index_1| hasher_1(table.data_bucket::<T>(index_1).as_ref()),
                &|table, index_2| hasher_2(table.data_bucket::<T>(index_2).as_ref()),
                // &|table, index_2| hasher_2(table.pointer_bucket::<T>(index_2).as_data_ref()),
                fallibility,
                TableLayout::new::<T>(),
            )
        }
    }

    /// Inserts a new element into the table, and returns its raw bucket.
    ///
    /// # Safety
    ///
    /// This does not check if the given element already exists in the table,
    /// i.e. function doesn't check existance of any `data` or `pointer`
    /// elements in the table, so the caller of this function must check
    /// that by themself.
    ///
    /// For example:
    /// - two tuples (100, 1000, "some value") and (100, 2000, "some value")
    ///   will have the same first hash and equivalence function;
    /// - two tuples (100, 1000, "some value") and (200, 1000, "some value")
    ///   will have the same second hash and equivalence function.
    ///
    /// Thus, you need to check:
    ///
    /// - that there is no element (`value`) in the table with the same first hash and an
    ///   equivalence function, i.e. when, for example, you try to put an element
    ///   (100, 2000, "some value") into the table, and there already is an element
    ///   (100, 1000, "some value "). It can be seen that the key `100` is present
    ///   in both tuples.
    ///
    /// - that there is no element (`value`) in the table with a matching second hash and an
    ///   equivalence function, i.e. when, for example, you try to put an element
    ///   (100, 1000, "some value") in the table, and there already is an element
    ///   (200, 1000, "some value"). It can be seen that the key `1000` is present
    ///   in both tuples.
    ///
    /// In case of failure of any of the above items, or failure of both at once, the
    /// behavior is unspecified: this operation may panic, loop forever, or any
    /// following operation with the map may panic, loop forever or return arbitrary
    /// result. That said, this operation (and following operations) are guaranteed
    /// to not violate memory safety.
    ///
    /// #Note
    ///
    /// If both elements are present in the table, you must additionally
    /// check that they point to the same element (`value`), and not to two different
    /// ones, i.e. if you, for example, are trying to place an element (100, 1000,
    /// "some value "), and there are already two elements (100, 2000, "some value")
    /// and (200, 1000, "some value") (in the example, you can see that the keys 100
    /// and 1000 are present in the table, but point to different values). Once this
    /// check has passed, the [`insert`](RawTable::insert) function cannot be used.
    /// Instead, you should get a mutable reference to an element and change the
    /// element through this reference.
    #[cfg_attr(feature = "inline-more", inline)]
    pub fn insert<F1, F2>(
        &mut self,
        hash_1: u64,
        hash_2: u64,
        value: T,
        hasher_1: F1,
        hasher_2: F2,
    ) -> (DataBucket<T>, PointerBucket<DataBucket<T>>)
    where
        F1: Fn(&T) -> u64,
        F2: Fn(&T) -> u64,
    {
        unsafe {
            let mut index_1 = self.table.find_data_insert_slot(hash_1);

            let mut index_2 = self.table.find_pointer_insert_slot(hash_2);

            // We can avoid growing the table once we have reached our load
            // factor if we are replacing a tombstone. This works since the
            // number of EMPTY slots does not change in this case.
            let old_ctrl_1 = *self.table.data_ctrl(index_1);
            let old_ctrl_2 = *self.table.pointers_ctrl(index_2);

            if unlikely(
                (self.table.data_growth_left == 0 && special_is_empty(old_ctrl_1))
                    || (self.table.pointers_growth_left == 0 && special_is_empty(old_ctrl_2)),
            ) {
                self.reserve(1, hasher_1, hasher_2);
                index_1 = self.table.find_data_insert_slot(hash_1);
                index_2 = self.table.find_pointer_insert_slot(hash_2);
            }

            self.table
                .record_item_insert_at(index_1, old_ctrl_1, hash_1, index_2, old_ctrl_2, hash_2);

            let data_bucket = self.data_bucket(index_1);
            data_bucket.write(value);

            let pointer_bucket = self.pointer_bucket(index_2);
            // pointer_bucket.write(data_bucket.clone());

            ptr::copy_nonoverlapping(
                &data_bucket as *const DataBucket<T>,
                pointer_bucket.as_ptr(),
                1,
            );

            (data_bucket, pointer_bucket)
        }
    }

    /// Attempts to insert a new element without growing the table and return its raw bucket.
    ///
    /// Returns an `Err` containing the given element if inserting it would require growing the
    /// table.
    ///
    /// # Safety
    ///
    /// This does not check if the given element already exists in the table,
    /// i.e. function doesn't check existance of any `data` or `pointer`
    /// elements in the table, so the caller of this function must check
    /// that by themself.
    ///
    /// For example:
    /// - two tuples (100, 1000, "some value") and (100, 2000, "some value")
    ///   will have the same first hash and equivalence function;
    /// - two tuples (100, 1000, "some value") and (200, 1000, "some value")
    ///   will have the same second hash and equivalence function.
    ///
    /// Thus, you need to check:
    ///
    /// - that there is no element (`value`) in the table with the same first hash and an
    ///   equivalence function, i.e. when, for example, you try to put an element
    ///   (100, 2000, "some value") into the table, and there already is an element
    ///   (100, 1000, "some value "). It can be seen that the key `100` is present
    ///   in both tuples.
    ///
    /// - that there is no element (`value`) in the table with a matching second hash and an
    ///   equivalence function, i.e. when, for example, you try to put an element
    ///   (100, 1000, "some value") in the table, and there already is an element
    ///   (200, 1000, "some value"). It can be seen that the key `1000` is present
    ///   in both tuples.
    ///
    /// In case of failure of any of the above items, or failure of both at once, the
    /// behavior is unspecified: this operation may panic, loop forever, or any
    /// following operation with the map may panic, loop forever or return arbitrary
    /// result. That said, this operation (and following operations) are guaranteed
    /// to not violate memory safety.
    ///
    /// #Note
    ///
    /// If both elements are present in the table, you must additionally
    /// check that they point to the same element (`value`), and not to two different
    /// ones, i.e. if you, for example, are trying to place an element (100, 1000,
    /// "some value "), and there are already two elements (100, 2000, "some value")
    /// and (200, 1000, "some value") (in the example, you can see that the keys 100
    /// and 1000 are present in the table, but point to different values). Once this
    /// check has passed, the [`try_insert_no_grow`](RawTable::try_insert_no_grow) function cannot be used.
    /// Instead, you should get a mutable reference to an element and change the
    /// element through this reference.
    #[cfg(feature = "raw")]
    #[cfg_attr(feature = "inline-more", inline)]
    pub fn try_insert_no_grow(
        &mut self,
        hash_1: u64,
        hash_2: u64,
        value: T,
    ) -> Result<(DataBucket<T>, PointerBucket<DataBucket<T>>), T> {
        unsafe {
            match self.table.prepare_insert_no_grow(hash_1, hash_2) {
                Ok((index_1, index_2)) => {
                    let data_bucket = self.data_bucket(index_1);
                    data_bucket.write(value);

                    let pointer_bucket = self.pointer_bucket(index_2);
                    // pointer_bucket.write(data_bucket.clone());

                    ptr::copy_nonoverlapping(
                        &data_bucket as *const DataBucket<T>,
                        pointer_bucket.as_ptr(),
                        1,
                    );

                    Ok((data_bucket, pointer_bucket))
                }
                Err(()) => Err(value),
            }
        }
    }

    /// Inserts a new element into the table, and returns a mutable reference to it.
    ///
    /// # Safety
    ///
    /// This does not check if the given element already exists in the table,
    /// i.e. function doesn't check existance of any `data` or `pointer`
    /// elements in the table, so the caller of this function must check
    /// that by themself.
    ///
    /// For example:
    /// - two tuples (100, 1000, "some value") and (100, 2000, "some value")
    ///   will have the same first hash and equivalence function;
    /// - two tuples (100, 1000, "some value") and (200, 1000, "some value")
    ///   will have the same second hash and equivalence function.
    ///
    /// Thus, you need to check:
    ///
    /// - that there is no element (`value`) in the table with the same first hash and an
    ///   equivalence function, i.e. when, for example, you try to put an element
    ///   (100, 2000, "some value") into the table, and there already is an element
    ///   (100, 1000, "some value "). It can be seen that the key `100` is present
    ///   in both tuples.
    ///
    /// - that there is no element (`value`) in the table with a matching second hash and an
    ///   equivalence function, i.e. when, for example, you try to put an element
    ///   (100, 1000, "some value") in the table, and there already is an element
    ///   (200, 1000, "some value"). It can be seen that the key `1000` is present
    ///   in both tuples.
    ///
    /// In case of failure of any of the above items, or failure of both at once, the
    /// behavior is unspecified: this operation may panic, loop forever, or any
    /// following operation with the map may panic, loop forever or return arbitrary
    /// result. That said, this operation (and following operations) are guaranteed
    /// to not violate memory safety.
    ///
    /// #Note
    ///
    /// If both elements are present in the table, you must additionally
    /// check that they point to the same element (`value`), and not to two different
    /// ones, i.e. if you, for example, are trying to place an element (100, 1000,
    /// "some value "), and there are already two elements (100, 2000, "some value")
    /// and (200, 1000, "some value") (in the example, you can see that the keys 100
    /// and 1000 are present in the table, but point to different values). Once this
    /// check has passed, the [`insert_entry`](RawTable::insert_entry) function cannot be used.
    /// Instead, you should get a mutable reference to an element and change the
    /// element through this reference.
    #[cfg_attr(feature = "inline-more", inline)]
    pub fn insert_entry<F1, F2>(
        &mut self,
        hash_1: u64,
        hash_2: u64,
        value: T,
        hasher_1: F1,
        hasher_2: F2,
    ) -> &mut T
    where
        F1: Fn(&T) -> u64,
        F2: Fn(&T) -> u64,
    {
        unsafe {
            self.insert(hash_1, hash_2, value, hasher_1, hasher_2)
                .0
                .as_mut()
        }
    }

    /// Inserts a new element into the table, without growing the table.
    ///
    /// There must be enough space in the table to insert the new element.
    ///
    /// # Safety
    ///
    /// Calling this method with full table is *[undefined behavior]*.
    ///
    /// This does not check if the given element already exists in the table,
    /// i.e. function doesn't check existance of any `data` or `pointer`
    /// elements in the table, so the caller of this function must check
    /// that by themself.
    ///
    /// For example:
    /// - two tuples (100, 1000, "some value") and (100, 2000, "some value")
    ///   will have the same first hash and equivalence function;
    /// - two tuples (100, 1000, "some value") and (200, 1000, "some value")
    ///   will have the same second hash and equivalence function.
    ///
    /// Thus, you need to check:
    ///
    /// - that there is no element (`value`) in the table with the same first hash and an
    ///   equivalence function, i.e. when, for example, you try to put an element
    ///   (100, 2000, "some value") into the table, and there already is an element
    ///   (100, 1000, "some value "). It can be seen that the key `100` is present
    ///   in both tuples.
    ///
    /// - that there is no element (`value`) in the table with a matching second hash and an
    ///   equivalence function, i.e. when, for example, you try to put an element
    ///   (100, 1000, "some value") in the table, and there already is an element
    ///   (200, 1000, "some value"). It can be seen that the key `1000` is present
    ///   in both tuples.
    ///
    /// In case of failure of any of the above items, or failure of both at once, the
    /// behavior is unspecified: this operation may panic, loop forever, or any
    /// following operation with the map may panic, loop forever or return arbitrary
    /// result. That said, this operation (and following operations) are guaranteed
    /// to not violate memory safety.
    ///
    /// [undefined behavior]: https://doc.rust-lang.org/reference/behavior-considered-undefined.html
    ///
    /// #Note
    ///
    /// If both elements are present in the table, you must additionally
    /// check that they point to the same element (`value`), and not to two different
    /// ones, i.e. if you, for example, are trying to place an element (100, 1000,
    /// "some value "), and there are already two elements (100, 2000, "some value")
    /// and (200, 1000, "some value") (in the example, you can see that the keys 100
    /// and 1000 are present in the table, but point to different values). Once this
    /// check has passed, the [`insert_no_grow`](RawTable::insert_no_grow) function cannot be used.
    /// Instead, you should get a mutable reference to an element and change the
    /// element through this reference.
    #[cfg_attr(feature = "inline-more", inline)]
    #[cfg(feature = "raw")]
    pub unsafe fn insert_no_grow(
        &mut self,
        hash_1: u64,
        hash_2: u64,
        value: T,
    ) -> (DataBucket<T>, PointerBucket<DataBucket<T>>) {
        let (index_1, old_ctrl_1) = self.table.prepare_data_insert_slot_return_old_byte(hash_1);
        let (index_2, old_ctrl_2) = self
            .table
            .prepare_pointer_insert_slot_return_old_byte(hash_2);

        // debug_assert_eq!(special_is_empty(old_ctrl_1), special_is_empty(old_ctrl_2));

        let data_bucket = self.table.data_bucket(index_1);

        // If we are replacing a DELETED entry then we don't need to update
        // the load counter.
        self.table.data_growth_left -= special_is_empty(old_ctrl_1) as usize;

        data_bucket.write(value);

        let pointer_bucket = self.table.pointer_bucket(index_2);

        self.table.pointers_growth_left -= special_is_empty(old_ctrl_2) as usize;

        // pointer_bucket.write(data_bucket.clone());
        ptr::copy_nonoverlapping(
            &data_bucket as *const DataBucket<T>,
            pointer_bucket.as_ptr(),
            1,
        );

        self.table.items += 1;

        (data_bucket, pointer_bucket)
    }

    /// Temporary removes a bucket, applying the given function to the removed
    /// element and optionally put back the returned value in the same bucket.
    ///
    /// Returns `true` if the bucket still contains an element
    ///
    /// This does not check if the given bucket is actually occupied.
    #[cfg_attr(feature = "inline-more", inline)]
    pub unsafe fn replace_data_with<F>(&mut self, ptr: PointerBucket<DataBucket<T>>, f: F) -> bool
    where
        F: FnOnce(T) -> Option<T>,
    {
        let (index_1, index_2) = self.data_pointer_indexes(&ptr);
        let old_ctrl_1 = *self.table.data_ctrl(index_1);
        let old_ctrl_2 = *self.table.pointers_ctrl(index_2);
        debug_assert!(is_full(old_ctrl_1));
        debug_assert!(is_full(old_ctrl_2));

        let old_data_growth_left = self.table.data_growth_left;
        let old_pointers_growth_left = self.table.pointers_growth_left;

        let item = self.remove(ptr);

        if let Some(new_item) = f(item) {
            self.table.data_growth_left = old_data_growth_left;
            self.table.pointers_growth_left = old_pointers_growth_left;
            self.table.set_data_ctrl(index_1, old_ctrl_1);
            self.table.set_pointers_ctrl(index_2, old_ctrl_2);

            let data_bucket = self.data_bucket(index_1);
            data_bucket.write(new_item);

            let pointer_bucket = self.pointer_bucket(index_2);
            pointer_bucket.write(data_bucket);

            self.table.items += 1;

            true
        } else {
            false
        }
    }

    /// Searches for an element in the table using hash 1
    #[inline]
    pub fn find_h1<F1>(&self, hash1: u64, mut eq1: F1) -> Option<DataBucket<T>>
    where
        F1: FnMut(&T) -> bool,
    {
        let index_1 = self.table.find_data_inner(hash1, &mut |index| unsafe {
            eq1(self.data_bucket(index).as_ref())
        });

        // Avoid `Option::map` because it bloats LLVM IR.
        match index_1 {
            Some(index_1) => Some(unsafe { self.data_bucket(index_1) }),
            None => None,
        }
    }

    /// Searches for an element in the table using hash 2
    #[inline]
    pub fn find_h2<F2>(&self, hash2: u64, mut eq2: F2) -> Option<PointerBucket<DataBucket<T>>>
    where
        F2: FnMut(&T) -> bool,
    {
        let index_2 = self.table.find_pointer_inner(hash2, &mut |index| unsafe {
            eq2(self.pointer_bucket(index).as_data_ref())
        });

        // Avoid `Option::map` because it bloats LLVM IR.
        match index_2 {
            Some(index_2) => Some(unsafe { self.pointer_bucket(index_2) }),
            None => None,
        }
    }

    /// Searches for an element in the table.
    #[inline]
    pub fn find<F1, F2>(
        &self,
        hash1: u64,
        mut eq1: F1,
        hash2: u64,
        mut eq2: F2,
    ) -> Option<(DataBucket<T>, PointerBucket<DataBucket<T>>)>
    where
        F1: FnMut(&T) -> bool,
        F2: FnMut(&T) -> bool,
    {
        let index_1 = self.table.find_data_inner(hash1, &mut |index| unsafe {
            eq1(self.data_bucket(index).as_ref())
        });

        // Avoid `Option::map` because it bloats LLVM IR.
        match index_1 {
            Some(index_1) => {
                let index_2 = self.table.find_pointer_inner(hash2, &mut |index| unsafe {
                    eq2(self.pointer_bucket(index).as_data_ref())
                });
                match index_2 {
                    Some(index_2) => unsafe {
                        let data = self.data_bucket(index_1);
                        let pointer = self.pointer_bucket(index_2);

                        if likely(ptr::eq(data.as_ptr(), pointer.as_data_ptr())) {
                            Some((data, pointer))
                        } else {
                            None
                        }
                    },
                    None => None,
                }
            }
            None => None,
        }
    }

    /// Gets an immutable reference to an element in the table using first hash
    /// (for [`DataBucket<T>`])
    #[inline]
    pub fn get_h1<F1>(&self, hash1: u64, eq1: F1) -> Option<&T>
    where
        F1: FnMut(&T) -> bool,
    {
        // Avoid `Option::map` because it bloats LLVM IR.
        match self.find_h1(hash1, eq1) {
            Some(bucket) => Some(unsafe { bucket.as_ref() }),
            None => None,
        }
    }

    /// Gets an immutable reference to an element in the table using second hash
    /// (for [`PointerBucket<DataBucket<T>>`])
    #[inline]
    pub fn get_h2<F2>(&self, hash2: u64, eq2: F2) -> Option<&T>
    where
        F2: FnMut(&T) -> bool,
    {
        // Avoid `Option::map` because it bloats LLVM IR.
        match self.find_h2(hash2, eq2) {
            Some(bucket) => Some(unsafe { bucket.as_data_ref() }),
            None => None,
        }
    }

    /// Gets an immutable reference to an element in the table using both hash
    /// (for [`DataBucket<T>`] and [`PointerBucket<DataBucket<T>>`])
    #[inline]
    pub fn get<F1, F2>(&self, hash1: u64, eq1: F1, hash2: u64, eq2: F2) -> Option<&T>
    where
        F1: FnMut(&T) -> bool,
        F2: FnMut(&T) -> bool,
    {
        // Avoid `Option::map` because it bloats LLVM IR.
        match self.find(hash1, eq1, hash2, eq2) {
            Some(buckets) => Some(unsafe { buckets.0.as_ref() }),
            None => None,
        }
    }

    /// Gets a mutable reference to an element in the table using first hash
    /// (for [`DataBucket<T>`])
    #[inline]
    pub fn get_mut_h1<F1>(&self, hash1: u64, eq1: F1) -> Option<&mut T>
    where
        F1: FnMut(&T) -> bool,
    {
        // Avoid `Option::map` because it bloats LLVM IR.
        match self.find_h1(hash1, eq1) {
            Some(bucket) => Some(unsafe { bucket.as_mut() }),
            None => None,
        }
    }

    /// Gets a mutable reference to an element in the table using second hash
    /// (for [`PointerBucket<DataBucket<T>>`])
    #[inline]
    pub fn get_mut_h2<F2>(&self, hash2: u64, eq2: F2) -> Option<&mut T>
    where
        F2: FnMut(&T) -> bool,
    {
        // Avoid `Option::map` because it bloats LLVM IR.
        match self.find_h2(hash2, eq2) {
            Some(bucket) => Some(unsafe { bucket.as_data_mut() }),
            None => None,
        }
    }

    /// Gets a mutable reference to an element in the table using both hash
    /// (for [`DataBucket<T>`] and [`PointerBucket<DataBucket<T>>`])
    #[inline]
    pub fn get_mut<F1, F2>(&self, hash1: u64, eq1: F1, hash2: u64, eq2: F2) -> Option<&mut T>
    where
        F1: FnMut(&T) -> bool,
        F2: FnMut(&T) -> bool,
    {
        // Avoid `Option::map` because it bloats LLVM IR.
        match self.find(hash1, eq1, hash2, eq2) {
            Some(buckets) => Some(unsafe { buckets.0.as_mut() }),
            None => None,
        }
    }

    /// Attempts to get mutable references to `N element` in the table at once
    /// using `hash 1`.
    ///
    /// The `hash1_iter` argument should be a iterator that return `hash 1` of
    /// the stored `element` and closure for checking the equivalence of that
    /// `element`.
    ///
    /// This function return `None`:
    /// - if any of the `elements` are duplicates;
    /// - if the `element` is not found for any items from iterator;
    /// - if given `const N` equal to zero (`0`).
    ///
    /// # Safety
    ///
    /// Calling this method is *[undefined behavior]* if given iterator length
    /// is not equal to the given `const N`.
    ///
    /// [undefined behavior]: https://doc.rust-lang.org/reference/behavior-considered-undefined.html
    #[allow(clippy::explicit_counter_loop)]
    pub unsafe fn get_many_mut_from_h1_iter<I, F1, const N: usize>(
        &mut self,
        hash1_iter: I,
    ) -> Option<[&'_ mut T; N]>
    where
        I: Iterator<Item = (u64, F1)>,
        F1: FnMut(&T) -> bool,
    {
        let ptrs = self.get_many_mut_pointers_from_h1_iter::<_, _, N>(hash1_iter)?;

        // Avoid using `Iterator::enumerate` because of double checking
        let mut index = 0_usize;
        for &cur in ptrs.iter() {
            if ptrs
                .get_unchecked(..index) // safety we now exactly that the `index` in `ptrs` index range
                .iter()
                .any(|&prev| ptr::eq::<T>(prev, cur))
            {
                return None;
            }
            index += 1;
        }
        // All bucket are distinct from all previous buckets so we're clear to return the result
        // of the lookup.

        // TODO use `MaybeUninit::array_assume_init` here instead once that's stable.
        Some(mem::transmute_copy(&ptrs))
    }

    /// Attempts to get mutable references to `N element` in the table at once
    /// using `hash 1`, without validating that the `elements` are unique.
    ///
    /// The `hash1_iter` argument should be a iterator that return `hash 1` of
    /// the stored `element` and closure for checking the equivalence of that
    /// `element`.
    ///
    /// This function return `None`:
    /// - if the `element` is not found for any items from iterator;
    /// - if given `const N` equal to zero (`0`).
    ///
    /// # Safety
    ///
    /// Calling this method is *[undefined behavior]*:
    /// - if given iterator length is not equal to the given `const N`;
    /// - if iterator contain overlapping items that refer to the same `elements`
    /// in the table even if the resulting references to `elements` in the table
    /// are not used.
    ///
    /// [undefined behavior]: https://doc.rust-lang.org/reference/behavior-considered-undefined.html
    pub unsafe fn get_many_unchecked_mut_from_h1_iter<I, F1, const N: usize>(
        &mut self,
        hash1_iter: I,
    ) -> Option<[&'_ mut T; N]>
    where
        I: Iterator<Item = (u64, F1)>,
        F1: FnMut(&T) -> bool,
    {
        let ptrs = self.get_many_mut_pointers_from_h1_iter::<_, _, N>(hash1_iter)?;
        Some(mem::transmute_copy(&ptrs))
    }

    /// Attempts to get mutable references to `N element` in the table at once
    /// using `hash 1`, without validating that the `elements` are unique.
    ///
    /// The `hash1_iter` argument should be a iterator that return `hash 1` of
    /// the stored `element` and closure for checking the equivalence of that
    /// `element`.
    ///
    /// This function return `None`:
    /// - if the `element` is not found for any items from iterator;
    /// - if given `const N` equal to zero (`0`).
    ///
    /// # Safety
    ///
    /// Calling this method is *[undefined behavior]* if given iterator length
    /// is not equal to the given `const N`.
    ///
    /// # Note
    ///
    /// Returning array may contain overlapping items that refer to the same `elements`
    /// in the table.
    ///
    /// [undefined behavior]: https://doc.rust-lang.org/reference/behavior-considered-undefined.html
    #[allow(clippy::explicit_counter_loop)]
    unsafe fn get_many_mut_pointers_from_h1_iter<I, F1, const N: usize>(
        &mut self,
        hash1_iter: I,
    ) -> Option<[*mut T; N]>
    where
        I: Iterator<Item = (u64, F1)>,
        F1: FnMut(&T) -> bool,
    {
        // Check trivial cases
        if N == 0 || N > self.len() {
            return None;
        }

        // If `iterator::size_hint` returns some upper bound, we check
        // that it is equal to `const N`, else return from the function,
        // since otherwise the following calculations do not make sense
        if let (_, Some(upper_bound)) = hash1_iter.size_hint() {
            if upper_bound != N {
                return None;
            }
        }

        // TODO use `MaybeUninit::uninit_array` here instead once that's stable.
        let mut outs: MaybeUninit<[*mut T; N]> = MaybeUninit::uninit();
        let outs_ptr = outs.as_mut_ptr();

        // Avoid using `Iterator::enumerate` because of double checking
        let mut index = 0_usize;
        for (hash1, eq1) in hash1_iter {
            let cur = self.find_h1(hash1, eq1)?;
            *(*outs_ptr).get_unchecked_mut(index) = cur.as_ptr();
            index += 1;
        }

        // TODO use `MaybeUninit::array_assume_init` here instead once that's stable.
        Some(outs.assume_init())
    }

    /// Attempts to get mutable references to `N element` in the table at once
    /// using `hash 2`, without validating that the `elements` are unique.
    ///
    /// The `hash2_iter` argument should be a iterator that return `hash 2` of
    /// the stored `element` and closure for checking the equivalence of that
    /// `element`.
    ///
    /// This function return `None`:
    /// - if any of the `elements` are duplicates;
    /// - if the `element` is not found for any items from iterator;
    /// - if given `const N` equal to zero (`0`).
    ///
    /// # Safety
    ///
    /// Calling this method is *[undefined behavior]* if given iterator length
    /// is not equal to the given `const N`.
    ///
    /// [undefined behavior]: https://doc.rust-lang.org/reference/behavior-considered-undefined.html
    #[allow(clippy::explicit_counter_loop)]
    pub unsafe fn get_many_mut_from_h2_iter<I, F2, const N: usize>(
        &mut self,
        hash2_iter: I,
    ) -> Option<[&'_ mut T; N]>
    where
        I: Iterator<Item = (u64, F2)>,
        F2: FnMut(&T) -> bool,
    {
        let ptrs = self.get_many_mut_pointers_from_h2_iter::<_, _, N>(hash2_iter)?;

        // Avoid using `Iterator::enumerate` because of double checking
        let mut index = 0_usize;
        for &cur in ptrs.iter() {
            if ptrs
                .get_unchecked(..index) // safety we now exactly that the `index` in `ptrs` index range
                .iter()
                .any(|&prev| ptr::eq::<T>(prev, cur))
            {
                return None;
            }
            index += 1;
        }
        // All bucket are distinct from all previous buckets so we're clear to return the result
        // of the lookup.

        // TODO use `MaybeUninit::array_assume_init` here instead once that's stable.
        Some(mem::transmute_copy(&ptrs))
    }

    /// Attempts to get mutable references to `N element` in the table at once
    /// using `hash 2`, without validating that the `elements` are unique.
    ///
    /// The `hash2_iter` argument should be a iterator that return `hash 2` of
    /// the stored `element` and closure for checking the equivalence of that
    /// `element`.
    ///
    /// This function return `None`:
    /// - if the `element` is not found for any items from iterator;
    /// - if given `const N` equal to zero (`0`).
    ///
    /// # Safety
    ///
    /// Calling this method is *[undefined behavior]*:
    /// - if given iterator length is not equal to the given `const N`;
    /// - if iterator contain overlapping items that refer to the same `elements`
    /// in the table even if the resulting references to `elements` in the table
    /// are not used.
    ///
    /// [undefined behavior]: https://doc.rust-lang.org/reference/behavior-considered-undefined.html
    pub unsafe fn get_many_unchecked_mut_from_h2_iter<I, F2, const N: usize>(
        &mut self,
        hash2_iter: I,
    ) -> Option<[&'_ mut T; N]>
    where
        I: Iterator<Item = (u64, F2)>,
        F2: FnMut(&T) -> bool,
    {
        let ptrs = self.get_many_mut_pointers_from_h2_iter::<_, _, N>(hash2_iter)?;
        Some(mem::transmute_copy(&ptrs))
    }

    /// Attempts to get mutable references to `N element` in the table at once
    /// using `hash 2`, without validating that the `elements` are unique.
    ///
    /// The `hash2_iter` argument should be a iterator that return `hash 2` of
    /// the stored `element` and closure for checking the equivalence of that
    /// `element`.
    ///
    /// This function return `None`:
    /// - if the `element` is not found for any items from iterator;
    /// - if given `const N` equal to zero (`0`).
    ///
    /// # Safety
    ///
    /// Calling this method is *[undefined behavior]* if given iterator length
    /// is not equal to the given `const N`.
    ///
    /// # Note
    ///
    /// Returning array may contain overlapping items that refer to the same `elements`
    /// in the table.
    ///
    /// [undefined behavior]: https://doc.rust-lang.org/reference/behavior-considered-undefined.html
    #[allow(clippy::explicit_counter_loop)]
    unsafe fn get_many_mut_pointers_from_h2_iter<I, F2, const N: usize>(
        &mut self,
        hash2_iter: I,
    ) -> Option<[*mut T; N]>
    where
        I: Iterator<Item = (u64, F2)>,
        F2: FnMut(&T) -> bool,
    {
        // Check trivial cases
        if N == 0 || N > self.len() {
            return None;
        }

        // If `iterator::size_hint` returns some upper bound, we check
        // that it is equal to `const N`, else return from the function,
        // since otherwise the following calculations do not make sense
        if let (_, Some(upper_bound)) = hash2_iter.size_hint() {
            if upper_bound != N {
                return None;
            }
        }

        // TODO use `MaybeUninit::uninit_array` here instead once that's stable.
        let mut outs: MaybeUninit<[*mut T; N]> = MaybeUninit::uninit();
        let outs_ptr = outs.as_mut_ptr();

        // Avoid using `Iterator::enumerate` because of double checking
        let mut index = 0_usize;
        for (hash2, eq2) in hash2_iter {
            let cur = self.find_h2(hash2, eq2)?;
            *(*outs_ptr).get_unchecked_mut(index) = cur.as_data_ptr();
            index += 1;
        }

        // TODO use `MaybeUninit::array_assume_init` here instead once that's stable.
        Some(outs.assume_init())
    }

    /// Attempts to get mutable references to `N element` in the table at once
    /// using `hash 1` and `hash 2`.
    ///
    /// The `hashes_iter` argument should be a iterator that return `hash 1` and
    /// `hash 2` of the stored `element` and closure for checking the equivalence
    /// of that `element`.
    ///
    /// This function return `None`:
    /// - if any of the `elements` are duplicates;
    /// - if the `element` is not found for any items from iterator;
    /// - if given `const N` equal to zero (`0`).
    ///
    /// # Safety
    ///
    /// Calling this method is *[undefined behavior]*:
    /// - if given iterator length is not equal to the given `const N`.
    ///
    /// [undefined behavior]: https://doc.rust-lang.org/reference/behavior-considered-undefined.html
    #[allow(clippy::explicit_counter_loop)]
    pub unsafe fn get_many_mut_from_iter<I, F1, F2, const N: usize>(
        &mut self,
        hashes_iter: I,
    ) -> Option<[&'_ mut T; N]>
    where
        I: Iterator<Item = (u64, F1, u64, F2)>,
        F1: FnMut(&T) -> bool,
        F2: FnMut(&T) -> bool,
    {
        let ptrs = self.get_many_mut_pointers_from_iter::<_, _, _, N>(hashes_iter)?;

        // Avoid using `Iterator::enumerate` because of double checking
        let mut index = 0_usize;
        for &cur in ptrs.iter() {
            if ptrs
                .get_unchecked(..index) // safety we now exactly that the `index` in `ptrs` index range
                .iter()
                .any(|&prev| ptr::eq::<T>(prev, cur))
            {
                return None;
            }
            index += 1;
        }
        // All bucket are distinct from all previous buckets so we're clear to return the result
        // of the lookup.

        // TODO use `MaybeUninit::array_assume_init` here instead once that's stable.
        Some(mem::transmute_copy(&ptrs))
    }

    /// Attempts to get mutable references to `N element` in the table at once
    /// using `hash 1` and `hash 2`, without validating that the `elements`
    /// are unique.
    ///
    /// The `hashes_iter` argument should be a iterator that return `hash 1` and
    /// `hash 2` of the stored `element` and closure for checking the equivalence
    /// of that `element`.
    ///
    /// This function return `None`:
    /// - if the `element` is not found for any items from iterator;
    /// - if given `const N` equal to zero (`0`).
    ///
    /// # Safety
    ///
    /// Calling this method is *[undefined behavior]*:
    /// - if given iterator length is not equal to the given `const N`;
    /// - if iterator contain overlapping items that refer to the same `elements`
    /// in the table even if the resulting references to `elements` in the table
    /// are not used.
    ///
    /// [undefined behavior]: https://doc.rust-lang.org/reference/behavior-considered-undefined.html
    pub unsafe fn get_many_unchecked_mut_from_iter<I, F1, F2, const N: usize>(
        &mut self,
        hashes_iter: I,
    ) -> Option<[&'_ mut T; N]>
    where
        I: Iterator<Item = (u64, F1, u64, F2)>,
        F1: FnMut(&T) -> bool,
        F2: FnMut(&T) -> bool,
    {
        let ptrs = self.get_many_mut_pointers_from_iter::<_, _, _, N>(hashes_iter)?;
        Some(mem::transmute_copy(&ptrs))
    }

    /// Attempts to get mutable references to `N element` in the table at once
    /// using `hash 1` and `hash 2`, without validating that the `elements`
    /// are unique.
    ///
    /// The `hashes_iter` argument should be a iterator that return `hash 1` and
    /// `hash 2` of the stored `element` and closure for checking the equivalence
    /// of that `element`.
    ///
    /// This function return `None`:
    /// - if the `element` is not found for any items from iterator;
    /// - if given `const N` equal to zero (`0`).
    ///
    /// # Safety
    ///
    /// Calling this method is *[undefined behavior]* if given iterator length
    /// is not equal to the given `const N`.
    ///
    /// # Note
    ///
    /// Returning array may contain overlapping items that refer to the same `elements`
    /// in the table.
    ///
    /// [undefined behavior]: https://doc.rust-lang.org/reference/behavior-considered-undefined.html
    #[allow(clippy::explicit_counter_loop)]
    unsafe fn get_many_mut_pointers_from_iter<I, F1, F2, const N: usize>(
        &mut self,
        hashes_iter: I,
    ) -> Option<[*mut T; N]>
    where
        I: Iterator<Item = (u64, F1, u64, F2)>,
        F1: FnMut(&T) -> bool,
        F2: FnMut(&T) -> bool,
    {
        // Check trivial cases
        if N == 0 || N > self.len() {
            return None;
        }

        // If `iterator::size_hint` returns some upper bound, we check
        // that it is equal to `const N`, else return from the function,
        // since otherwise the following calculations do not make sense
        if let (_, Some(upper_bound)) = hashes_iter.size_hint() {
            if upper_bound != N {
                return None;
            }
        }

        // TODO use `MaybeUninit::uninit_array` here instead once that's stable.
        let mut outs: MaybeUninit<[*mut T; N]> = MaybeUninit::uninit();
        let outs_ptr = outs.as_mut_ptr();

        // Avoid using `Iterator::enumerate` because of double checking
        let mut index = 0_usize;
        for (hash1, eq1, hash2, eq2) in hashes_iter {
            let cur = self.find(hash1, eq1, hash2, eq2)?;
            *(*outs_ptr).get_unchecked_mut(index) = cur.0.as_ptr();
            index += 1;
        }

        // TODO use `MaybeUninit::array_assume_init` here instead once that's stable.
        Some(outs.assume_init())
    }

    /// Returns the number of elements `T` the map can hold without reallocating.
    ///
    /// This number is a lower bound; the table might be able to hold
    /// more, but is guaranteed to be able to hold at least this many.
    #[inline]
    pub fn capacity(&self) -> usize {
        let table = &self.table;
        table.items + usize::min(table.data_growth_left, table.pointers_growth_left)
    }

    /// Returns the number of elements `T` in the table.
    #[inline]
    pub fn len(&self) -> usize {
        self.table.items
    }

    /// Returns `true` if the table contains no elements `T`.
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Returns the number of buckets in the table.
    #[inline]
    pub fn buckets(&self) -> usize {
        self.table.bucket_mask + 1
    }

    /// Checks whether the `data bucket` at `index` is full.
    ///
    /// # Safety
    ///
    /// The caller must ensure `index` is less than the number of buckets.
    #[inline]
    #[cfg(feature = "raw")]
    pub unsafe fn is_data_bucket_full(&self, index: usize) -> bool {
        self.table.is_data_bucket_full(index)
    }

    /// Checks whether the `pointer bucket` at `index` is full.
    ///
    /// # Safety
    ///
    /// The caller must ensure `index` is less than the number of buckets.
    #[inline]
    #[cfg(feature = "raw")]
    pub unsafe fn is_pointer_bucket_full(&self, index: usize) -> bool {
        self.table.is_pointer_bucket_full(index)
    }

    /// Returns an iterator over every element `T` in the table. It is up to
    /// the caller to ensure that the [`RawTable`] outlives the [`RawDataIter`].
    /// Because we cannot make the `next` method unsafe on the `RawDataIter`
    /// struct, we have to make the `iter` method unsafe.
    #[inline]
    pub unsafe fn iter(&self) -> RawDataIter<T> {
        let data = DataBucket::from_base_index(self.data_end(), 0);
        RawDataIter {
            iter: RawDataIterRange::new(self.table.data_ctrl.as_ptr(), data, self.table.buckets()),
            items: self.table.items,
        }
    }

    /// Returns an iterator over every [`PointerBucket`] element  in the table. It is up to
    /// the caller to ensure that the [`RawTable`] outlives the [`RawPointerIter`].
    /// Because we cannot make the `next` method unsafe on the `RawPointerIter`
    /// struct, we have to make the `pointers_iter` method unsafe.
    #[inline]
    pub unsafe fn pointers_iter(&self) -> RawPointerIter<T> {
        let ptr = PointerBucket::from_base_index(self.pointers_end(), 0);
        RawPointerIter {
            iter: RawPointerIterRange::new(
                self.table.pointers_ctrl.as_ptr(),
                ptr,
                self.table.buckets(),
            ),
            items: self.table.items,
        }
    }

    // /// Returns an iterator over occupied buckets that could match a given hash.
    // ///
    // /// `RawTable` only stores 7 bits of the hash value, so this iterator may
    // /// return items that have a hash value different than the one provided. You
    // /// should always validate the returned values before using them.
    // ///
    // /// It is up to the caller to ensure that the `RawTable` outlives the
    // /// `RawIterHash`. Because we cannot make the `next` method unsafe on the
    // /// `RawIterHash` struct, we have to make the `iter_hash` method unsafe.
    // #[cfg_attr(feature = "inline-more", inline)]
    // #[cfg(feature = "raw")]
    // pub unsafe fn iter_hash(&self, hash: u64) -> RawIterHash<'_, T, A> {
    //     RawIterHash::new(self, hash)
    // }

    /// Returns an iterator which removes all elements from the table without
    /// freeing the memory.
    #[cfg_attr(feature = "inline-more", inline)]
    pub fn drain(&mut self) -> RawDrain<'_, T, A> {
        unsafe {
            let iter = self.iter();
            self.drain_iter_from(iter)
        }
    }

    /// Returns an iterator which removes all elements from the table without
    /// freeing the memory.
    ///
    /// Iteration starts at the provided iterator's current location.
    ///
    /// It is up to the caller to ensure that the iterator is valid for this
    /// `RawTable` and covers all items that remain in the table.
    #[cfg_attr(feature = "inline-more", inline)]
    pub unsafe fn drain_iter_from(&mut self, iter: RawDataIter<T>) -> RawDrain<'_, T, A> {
        debug_assert_eq!(iter.len(), self.len());
        RawDrain {
            iter,
            table: ManuallyDrop::new(mem::replace(self, Self::new_in(self.table.alloc.clone()))),
            orig_table: NonNull::from(self),
            marker: PhantomData,
        }
    }

    /// Returns an iterator which consumes all elements from the table.
    ///
    /// Iteration starts at the provided iterator's current location.
    ///
    /// It is up to the caller to ensure that the iterator is valid for this
    /// `RawTable` and covers all items that remain in the table.
    pub unsafe fn into_iter_from(self, iter: RawDataIter<T>) -> RawIntoDataIter<T, A> {
        debug_assert_eq!(iter.len(), self.len());

        let alloc = self.table.alloc.clone();
        let allocation = self.into_allocation();
        RawIntoDataIter {
            iter,
            allocation,
            marker: PhantomData,
            alloc,
        }
    }

    /// Returns an iterator which consumes all elements from the table.
    ///
    /// Iteration starts at the provided iterator's current location.
    ///
    /// It is up to the caller to ensure that the iterator is valid for this
    /// `RawTable` and covers all items that remain in the table.
    #[cfg(feature = "raw")]
    pub unsafe fn into_pointer_iter_from(
        self,
        iter: RawPointerIter<T>,
    ) -> RawIntoPointerIter<T, A> {
        debug_assert_eq!(iter.len(), self.len());

        let alloc = self.table.alloc.clone();
        let allocation = self.into_allocation();
        RawIntoPointerIter {
            iter,
            allocation,
            marker: PhantomData,
            alloc,
        }
    }

    /// Returns an iterator which consumes all elements from the table.
    ///
    /// Iteration starts at the provided iterator's current location.
    ///
    /// It is up to the caller to ensure that the iterator is valid for this
    /// `RawTable` and covers all items that remain in the table.
    #[cfg(feature = "raw")]
    #[cfg_attr(feature = "inline-more", inline)]
    pub fn into_pointer_iter(self) -> RawIntoPointerIter<T, A> {
        unsafe {
            let iter = self.pointers_iter();
            self.into_pointer_iter_from(iter)
        }
    }

    /// Converts the table into a raw allocation. The contents of the table
    /// should be dropped using a `RawIter` before freeing the allocation.
    #[cfg_attr(feature = "inline-more", inline)]
    pub(crate) fn into_allocation(self) -> Option<(NonNull<u8>, Layout)> {
        let alloc = if self.table.is_empty_singleton() {
            None
        } else {
            // Avoid `Option::unwrap_or_else` because it bloats LLVM IR.
            let (layout, ctrl_offset, _) = match calculate_layout::<T>(self.table.buckets()) {
                Some(lco) => lco,
                None => unsafe { hint::unreachable_unchecked() },
            };
            Some((
                unsafe { NonNull::new_unchecked(self.table.data_ctrl.as_ptr().sub(ctrl_offset)) },
                layout,
            ))
        };
        mem::forget(self);
        alloc
    }
}

unsafe impl<T, A: Allocator + Clone> Send for RawTable<T, A>
where
    T: Send,
    A: Send,
{
}

unsafe impl<T, A: Allocator + Clone> Sync for RawTable<T, A>
where
    T: Sync,
    A: Sync,
{
}

impl<T: Clone, A: Allocator + Clone> Clone for RawTable<T, A> {
    fn clone(&self) -> Self {
        if self.table.is_empty_singleton() {
            Self::new_in(self.table.alloc.clone())
        } else {
            unsafe {
                // Avoid `Result::ok_or_else` because it bloats LLVM IR.
                let new_table = match Self::new_uninitialized(
                    self.table.alloc.clone(),
                    self.table.buckets(),
                    Fallibility::Infallible,
                ) {
                    Ok(table) => table,
                    Err(_) => hint::unreachable_unchecked(),
                };

                // If cloning fails then we need to free the allocation for the
                // new table. However we don't run its drop since its control
                // bytes are not initialized yet.
                let mut guard = guard(ManuallyDrop::new(new_table), |new_table| {
                    new_table.free_buckets();
                });

                guard.clone_from_spec(self);

                // Disarm the scope guard and return the newly created table.
                ManuallyDrop::into_inner(ScopeGuard::into_inner(guard))
            }
        }
    }

    fn clone_from(&mut self, source: &Self) {
        if source.table.is_empty_singleton() {
            *self = Self::new_in(self.table.alloc.clone());
        } else {
            unsafe {
                // Make sure that if any panics occurs, we clear the table and
                // leave it in an empty state.
                let mut self_ = guard(self, |self_| {
                    self_.clear_no_drop();
                });

                // First, drop all our elements without clearing the control
                // bytes. If this panics then the scope guard will clear the
                // table, leaking any elements that were not dropped yet.
                //
                // This leak is unavoidable: we can't try dropping more elements
                // since this could lead to another panic and abort the process.
                self_.drop_elements();

                // If necessary, resize our table to match the source.
                if self_.buckets() != source.buckets() {
                    // Skip our drop by using ptr::write.
                    if !self_.table.is_empty_singleton() {
                        self_.free_buckets();
                    }
                    (&mut **self_ as *mut Self).write(
                        // Avoid `Result::unwrap_or_else` because it bloats LLVM IR.
                        match Self::new_uninitialized(
                            self_.table.alloc.clone(),
                            source.buckets(),
                            Fallibility::Infallible,
                        ) {
                            Ok(table) => table,
                            Err(_) => hint::unreachable_unchecked(),
                        },
                    );
                }

                self_.clone_from_spec(source);

                // Disarm the scope guard if cloning was successful.
                ScopeGuard::into_inner(self_);
            }
        }
    }
}

/// Specialization of `clone_from` for `Copy` types
trait RawTableClone {
    unsafe fn clone_from_spec(&mut self, source: &Self);
}

impl<T: Clone, A: Allocator + Clone> RawTableClone for RawTable<T, A> {
    default_fn! {
        #[cfg_attr(feature = "inline-more", inline)]
        unsafe fn clone_from_spec(&mut self, source: &Self) {
            self.clone_from_impl(source);
        }
    }
}

#[cfg(feature = "nightly")]
impl<T: Copy, A: Allocator + Clone> RawTableClone for RawTable<T, A> {
    #[cfg_attr(feature = "inline-more", inline)]
    unsafe fn clone_from_spec(&mut self, source: &Self) {
        source
            .table
            .data_ctrl(0)
            .copy_to_nonoverlapping(self.table.data_ctrl(0), self.table.num_ctrl_bytes());

        source
            .table
            .pointers_ctrl(0)
            .copy_to_nonoverlapping(self.table.pointers_ctrl(0), self.table.num_ctrl_bytes());

        source
            .data_start()
            .copy_to_nonoverlapping(self.data_start(), self.table.buckets());

        for from in source.pointers_iter() {
            let (index_1, index_2) = source.data_pointer_indexes(&from);
            self.pointer_bucket(index_2)
                .write(self.data_bucket(index_1));
        }

        self.table.items = source.table.items;
        self.table.data_growth_left = source.table.data_growth_left;
        self.table.pointers_growth_left = source.table.pointers_growth_left;
    }
}

impl<T: Clone, A: Allocator + Clone> RawTable<T, A> {
    /// Common code for clone and clone_from. Assumes:
    /// - `self.buckets() == source.buckets()`.
    /// - Any existing elements have been dropped.
    /// - The control bytes are not initialized yet.
    #[cfg_attr(feature = "inline-more", inline)]
    unsafe fn clone_from_impl(&mut self, source: &Self) {
        // Copy the control bytes unchanged. We do this in a single pass
        source
            .table
            .data_ctrl(0)
            .copy_to_nonoverlapping(self.table.data_ctrl(0), self.table.num_ctrl_bytes());

        source
            .table
            .pointers_ctrl(0)
            .copy_to_nonoverlapping(self.table.pointers_ctrl(0), self.table.num_ctrl_bytes());

        // The cloning of elements may panic, in which case we need
        // to make sure we drop only the elements that have been
        // cloned so far.
        let mut guard = guard((0, &mut *self), |(index, self_)| {
            if mem::needs_drop::<T>() && !self_.is_empty() {
                for i in 0..=*index {
                    if is_full(*self_.table.data_ctrl(i)) {
                        self_.data_bucket(i).drop();
                    }
                }
            }
        });

        for from in source.pointers_iter() {
            let (index_1, index_2) = source.data_pointer_indexes(&from);
            let data_to = guard.1.data_bucket(index_1);
            data_to.write(from.as_data_ref().clone());

            guard.1.pointer_bucket(index_2).write(data_to);

            // Update the index in case we need to unwind.
            guard.0 = index_1;
        }

        // Successfully cloned all items, no need to clean up.
        mem::forget(guard);

        self.table.items = source.table.items;
        self.table.data_growth_left = source.table.data_growth_left;
        self.table.pointers_growth_left = source.table.pointers_growth_left;
    }

    /// Variant of `clone_from` to use when a hasher is available.
    #[cfg(feature = "raw")]
    pub fn clone_from_with_hasher<F1, F2>(&mut self, source: &Self, hasher_1: F1, hasher_2: F2)
    where
        F1: Fn(&T) -> u64,
        F2: Fn(&T) -> u64,
    {
        // If we have enough capacity in the table, just clear it and insert
        // elements one by one. We don't do this if we have the same number of
        // buckets as the source since we can just copy the contents directly
        // in that case.
        if self.table.buckets() != source.table.buckets()
            && bucket_mask_to_capacity(self.table.bucket_mask) >= source.len()
        {
            self.clear();

            let guard_self = guard(&mut *self, |self_| {
                // Clear the partially copied table if a panic occurs, otherwise
                // items and growth_left will be out of sync with the contents
                // of the table.
                self_.clear();
            });

            unsafe {
                for data_bucket in source.iter() {
                    // This may panic.
                    let data = data_bucket.as_ref().clone();
                    let hash_1 = hasher_1(&data);
                    let hash_2 = hasher_2(&data);

                    // We can use a simpler version of insert() here since:
                    // - there are no DELETED entries.
                    // - we know there is enough space in the table.
                    // - all elements are unique.
                    let index_1 = guard_self.table.prepare_data_insert_slot(hash_1);
                    let index_2 = guard_self.table.prepare_pointer_insert_slot(hash_2);

                    let data_bucket = guard_self.data_bucket(index_1);
                    data_bucket.write(data);
                    guard_self.pointer_bucket(index_2).write(data_bucket);
                }
            }

            // Successfully cloned all items, no need to clean up.
            mem::forget(guard_self);

            let source_table_items = source.table.items;
            self.table.items = source_table_items;
            self.table.data_growth_left -= source_table_items;
            self.table.pointers_growth_left -= source_table_items;
        } else {
            self.clone_from(source);
        }
    }
}

impl<T, A: Allocator + Clone + Default> Default for RawTable<T, A> {
    #[inline]
    fn default() -> Self {
        Self::new_in(Default::default())
    }
}

impl<T, A: Allocator + Clone> Drop for RawTable<T, A> {
    #[cfg_attr(feature = "inline-more", inline)]
    fn drop(&mut self) {
        if !self.table.is_empty_singleton() {
            unsafe {
                self.drop_elements();
                self.free_buckets();
            }
        }
    }
}

impl<T, A: Allocator + Clone> IntoIterator for RawTable<T, A> {
    type Item = T;
    type IntoIter = RawIntoDataIter<T, A>;

    #[cfg_attr(feature = "inline-more", inline)]
    fn into_iter(self) -> RawIntoDataIter<T, A> {
        unsafe {
            let iter = self.iter();
            self.into_iter_from(iter)
        }
    }
}

/// Non-generic part of `RawTable` which allows functions to be instantiated only once regardless
/// of how many different key-value types are used.
//
// Actual model of our table (90% true) looks like as shown below (we start counting from "0",
// so that in the expression T[last], the "last" index actually one less than the given
// "buckets" number, i.e. "last = bucket_mask = buckets - 1"). This usage makes it easier
// to calculate indexes when we start counting from the same point ("data_ctrl" for data and
// "pointers_ctrl" for pointers) but in opposite directions (to the right for control
// bytes, to the left for the data itself):
//
// [Padding], Tlast, ..., T1, T0, |CT0, CT1, ..., CTlast
//            ^           ^   ^   ^ data_ctrl points here (to the start of CT0
//            |           |   |     or to the end of T0, which is the same)
//            |           |   |
// [Padding], Plast, ..., P1, P0, |CP0, CP1, ..., CPlast, [Padding]
//                                ^ pointers_ctrl points here (to the start of CP0
//                                  or to the end of P0, which is the same)
//
// where: Type of P = DataBucket<T>;
//        T0...Tlast - our stored data;      CT0...CTlast - metadata for data;
//        ^    ^
//        |    |
//        P0...Plast - our pointers to data; CP0...CPlast - metadata for pointers.
//
// Pointers "data_ctrl" and "pointers_ctrl" points to the end of the first stored data
// (or to the start of the control bytes), and it is 100% true. The only inaccuracy is
// in the pointers part of our table:
//    1. We do not actually store there raw pointers, but the DataBucket<T> structures;
//    2. Pointers with some index not actually point to the Data with the same index, i.e.
//       a situation when P0 -> T0, P1 -> T1 and so on can be if we use the same hasher
//       and the same keys for all P0...Plast and T0...Tlast.
//       Actually firstly we use hasher_1 to store T[some index], then use hasher_2
//       to store the pointer to it under P[some other index].
//    3. Finally DataBucket<T> stored inside pointers part of our table actually point to
//       one past of our element, i.e. in other words it point to next element than the
//       element itself.
pub struct RawTableInner<A> {
    // Mask to get an index from a hash value. The value is one less than the
    // number of buckets in the table.
    bucket_mask: usize,

    // Actual model of our table (90% true) looks like this (we start counting from "0", so that in the
    // expression T[last], the "last" index actually one less than the given "buckets" number,
    // i.e. "last = bucket_mask = buckets - 1"):
    //
    // [Padding], Tlast, ..., T1, T0, |CT0, CT1, ..., CTlast
    //            ^           ^   ^   ^ data_ctrl points here (to the start of CT0
    //            |           |   |     or to the end of T0, which is the same)
    //            |           |   |
    // [Padding], Plast, ..., P1, P0, |CP0, CP1, ..., CPlast
    //                                ^ pointers_ctrl points here (to the start of CP0
    //                                  or to the end of P0, which is the same)
    //
    // where: Type of P = DataBucket<T>;
    //        T0...Tlast - our stored data;      CT0...CTlast - metadata for data;
    //        ^    ^
    //        |    |
    //        P0...Plast - our pointers to data; CP0...CPlast - metadata for pointers.
    //
    data_ctrl: NonNull<u8>,

    pointers_ctrl: NonNull<u8>,

    // Number of data elements that can be inserted before we need to grow the table
    data_growth_left: usize,

    // Number of pointer elements that can be inserted before we need to grow the table
    pointers_growth_left: usize,

    // Number of elements in the table, only really used by len()
    items: usize,

    // // Number of pointer elements in the table, only fodiagnostic purpose
    // pointer_items: usize,
    alloc: A,
}

impl<A> RawTableInner<A> {
    /// Creates a new empty table without allocating any memory, using the
    /// given allocator.
    ///
    /// In effect this returns a table with exactly 1 bucket. However we can
    /// leave the data pointer dangling since that bucket is never written to
    /// due to our load factor forcing us to always have at least 1 free bucket.
    #[inline]
    const fn new_in(alloc: A) -> Self {
        Self {
            // Be careful to cast the entire slice to a raw pointer.
            data_ctrl: unsafe {
                NonNull::new_unchecked(Group::static_empty() as *const _ as *mut u8)
            },
            pointers_ctrl: unsafe {
                NonNull::new_unchecked(Group::static_empty() as *const _ as *mut u8)
            },
            bucket_mask: 0,
            items: 0,
            data_growth_left: 0,
            pointers_growth_left: 0,
            alloc,
        }
    }
}

impl<A: Allocator + Clone> RawTableInner<A> {
    /// Allocates a new hash table with the given number of `buckets`.
    /// Given number of `buckets` must be the power of `2`, i.e.
    /// `buckets == 2^k` for some `k`.
    ///
    /// The control bytes for `data buckets` and `pointer buckets` are left
    /// uninitialized.
    #[cfg_attr(feature = "inline-more", inline)]
    unsafe fn new_uninitialized(
        alloc: A,
        table_layout: TableLayout,
        buckets: usize,
        fallibility: Fallibility,
    ) -> Result<Self, TryReserveError> {
        debug_assert!(buckets.is_power_of_two());

        // Avoid `Option::ok_or_else` because it bloats LLVM IR.
        let (layout, ctrl_offset, pointers_ctrl_offset) =
            match table_layout.calculate_layout_for(buckets) {
                Some(lco) => lco,
                None => return Err(fallibility.capacity_overflow()),
            };

        let ptr: NonNull<u8> = match do_alloc(&alloc, layout) {
            Ok(block) => block.cast(),
            Err(_) => return Err(fallibility.alloc_err(layout)),
        };

        let data_ctrl = NonNull::new_unchecked(ptr.as_ptr().add(ctrl_offset));
        let pointers_ctrl = NonNull::new_unchecked(ptr.as_ptr().add(pointers_ctrl_offset));

        let growth_left = bucket_mask_to_capacity(buckets - 1);
        Ok(Self {
            data_ctrl,
            pointers_ctrl,
            bucket_mask: buckets - 1,
            items: 0,
            data_growth_left: growth_left,
            pointers_growth_left: growth_left,
            alloc,
        })
    }

    /// Attempts to allocate a new hash table with at least enough capacity
    /// for inserting the given number of elements without reallocating.
    ///
    /// All control bytes for `data buckets` and `pointer buckets` are
    /// initialized as `empty`.
    #[inline]
    fn fallible_with_capacity(
        alloc: A,
        table_layout: TableLayout,
        capacity: usize,
        fallibility: Fallibility,
    ) -> Result<Self, TryReserveError> {
        if capacity == 0 {
            Ok(Self::new_in(alloc))
        } else {
            unsafe {
                match capacity_to_buckets(capacity) {
                    Some(buckets) => {
                        let result =
                            Self::new_uninitialized(alloc, table_layout, buckets, fallibility)?;

                        result
                            .data_ctrl(0)
                            .write_bytes(EMPTY, result.num_ctrl_bytes());
                        result
                            .pointers_ctrl(0)
                            .write_bytes(EMPTY, result.num_ctrl_bytes());

                        Ok(result)
                    }
                    None => Err(fallibility.capacity_overflow()),
                }
            }
        }
    }

    /// Searches for an empty or deleted `data bucket` which is suitable for inserting
    /// a new `data element` and sets the hash for that slot in the `data control bytes`.
    /// Return found `data bucket` index in the data part of the table, as well as an
    /// old control byte previously stored under that index.
    ///
    /// There must be at least 1 empty `data bucket` in the table.
    ///
    /// # Note
    ///
    /// This function must be used together with
    /// [`prepare_pointer_insert_slot`] function or combination of [`find_pointer_insert_slot`]
    /// and [`set_pointers_ctrl_h2`] functions, because firstly we store in the data
    /// part of the table a `data` using `hash_1`, and than we store in the pointer part of
    /// the table a `pointer` to the data using `hash_2`.
    ///
    /// [`prepare_pointer_insert_slot`]: RawTableInner::prepare_pointer_insert_slot
    /// [`find_pointer_insert_slot`]: RawTableInner::find_pointer_insert_slot
    /// [`set_pointers_ctrl_h2`]: RawTableInner::set_pointers_ctrl_h2
    ///
    #[cfg(feature = "raw")]
    #[inline]
    unsafe fn prepare_data_insert_slot_return_old_byte(&self, hash_1: u64) -> (usize, u8) {
        let index = self.find_data_insert_slot(hash_1);
        let old_ctrl = *self.data_ctrl(index);
        self.set_data_ctrl_h2(index, hash_1);
        (index, old_ctrl)
    }

    /// Searches for an empty or deleted `data bucket` which is suitable for inserting
    /// a new `data element` and sets the hash for that slot in the `data control bytes`.
    /// Return found `data bucket` index in the data part of the table. Difference
    /// from the [`prepare_data_insert_slot_return_old_byte`] finctuion is that this
    /// functon doesh't return old control byte previously stored under that index.
    ///
    /// There must be at least 1 empty `data bucket` in the table.
    ///
    /// # Note
    ///
    /// This function must be used together with
    /// [`prepare_pointer_insert_slot`] function or combination of [`find_pointer_insert_slot`]
    /// and [`set_pointers_ctrl_h2`] functions, because firstly we store in the data
    /// part of the table a `data` using `hash_1`, and than we store in the pointer part of
    /// the table a `pointer` to the data using `hash_2`.
    ///
    /// [`prepare_data_insert_slot_return_old_byte`]: RawTableInner::prepare_data_insert_slot_return_old_byte
    /// [`prepare_pointer_insert_slot`]: RawTableInner::prepare_pointer_insert_slot
    /// [`find_pointer_insert_slot`]: RawTableInner::find_pointer_insert_slot
    /// [`set_pointers_ctrl_h2`]: RawTableInner::set_pointers_ctrl_h2
    ///
    #[inline]
    unsafe fn prepare_data_insert_slot(&self, hash_1: u64) -> usize {
        let index = self.find_data_insert_slot(hash_1);
        self.set_data_ctrl_h2(index, hash_1);
        index
    }

    /// Searches for an empty or deleted `pointer bucket` which is suitable for inserting
    /// a new `pointer element` and sets the hash for that slot in the `pointer control bytes`.
    /// Return empty `pointer bucket` index in the pointers part of the table, as well as an old
    /// control byte stored under that index.
    ///
    /// There must be at least 1 empty `pointer bucket` in the table.
    ///
    /// # Note
    ///
    /// This function must be used together with
    /// [`prepare_data_insert_slot`] function or combination of [`find_data_insert_slot`]
    /// and [`set_ctrl_h2`] functions, because firstly we store in the data
    /// part of the table a `data` using `hash_1`, and than we store in the pointer part of
    /// the table a `pointer` to the data using `hash_2`.
    ///
    /// [`prepare_data_insert_slot`]: RawTableInner::prepare_data_insert_slot
    /// [`find_data_insert_slot`]: RawTableInner::find_data_insert_slot
    /// [`set_ctrl_h2`]: RawTableInner::set_ctrl_h2
    #[cfg(feature = "raw")]
    #[inline]
    unsafe fn prepare_pointer_insert_slot_return_old_byte(&self, hash_2: u64) -> (usize, u8) {
        let index = self.find_pointer_insert_slot(hash_2);
        let old_ctrl = *self.pointers_ctrl(index);
        self.set_pointers_ctrl_h2(index, hash_2);
        (index, old_ctrl)
    }

    /// Searches for an empty or deleted `pointer bucket` which is suitable for inserting
    /// a new `pointer element` and sets the hash for that slot in the `pointer control bytes`.
    /// Return found `pointer bucket` index in the pointers part of the table. Difference
    /// from the [`prepare_pointer_insert_slot_return_old_byte`] finctuion is that this
    /// functon doesh't return old control byte previously stored under that index.
    ///
    /// There must be at least 1 empty `pointer bucket` in the table.
    ///
    /// # Note
    ///
    /// This function must be used together with
    /// [`prepare_data_insert_slot`] function or combination of [`find_data_insert_slot`]
    /// and [`set_ctrl_h2`] functions, because firstly we store in the data
    /// part of the table a `data` using `hash_1`, and than we store in the pointer part of
    /// the table a `pointer` to the data using `hash_2`.
    ///
    /// [`prepare_pointer_insert_slot_return_old_byte`]: RawTableInner::prepare_pointer_insert_slot_return_old_byte
    /// [`prepare_data_insert_slot`]: RawTableInner::prepare_data_insert_slot
    /// [`find_data_insert_slot`]: RawTableInner::find_data_insert_slot
    /// [`set_ctrl_h2`]: RawTableInner::set_ctrl_h2
    #[inline]
    unsafe fn prepare_pointer_insert_slot(&self, hash_2: u64) -> usize {
        let index = self.find_pointer_insert_slot(hash_2);
        self.set_pointers_ctrl_h2(index, hash_2);
        index
    }

    /// Searches for an empty or deleted `data bucket` which is suitable for inserting
    /// a new `data element` and return it index in the data part of the table.
    /// The difference between this function and [`prepare_data_insert_slot`] function
    /// is that this function doesn't change `data control byte` under that index.
    ///
    /// There must be at least 1 empty `data bucket` in the table.
    ///
    /// # Note
    ///
    /// This function must be used together with [`find_pointer_insert_slot`]
    /// function, as well as with [`set_ctrl_h2`] and [`set_pointers_ctrl_h2`]
    /// functions, because firstly we store in the data part of the table
    /// a `data` using `hash_1`, and than we store in the pointer part of
    /// the table a `pointer` to the data using `hash_2`.
    ///
    /// [`prepare_data_insert_slot`]: RawTableInner::prepare_data_insert_slot
    /// [`find_pointer_insert_slot`]: RawTableInner::find_pointer_insert_slot
    /// [`set_ctrl_h2`]: RawTableInner::set_ctrl_h2
    /// [`set_pointers_ctrl_h2`]: RawTableInner::set_pointers_ctrl_h2
    #[inline]
    fn find_data_insert_slot(&self, hash_1: u64) -> usize {
        let mut probe_seq = self.probe_seq(hash_1);
        loop {
            unsafe {
                let group = Group::load(self.data_ctrl(probe_seq.pos));
                if let Some(bit) = group.match_empty_or_deleted().lowest_set_bit() {
                    let result = (probe_seq.pos + bit) & self.bucket_mask;

                    // In tables smaller than the group width, trailing control
                    // bytes outside the range of the table are filled with
                    // EMPTY entries. These will unfortunately trigger a
                    // match, but once masked may point to a full bucket that
                    // is already occupied. We detect this situation here and
                    // perform a second scan starting at the beginning of the
                    // table. This second scan is guaranteed to find an empty
                    // slot (due to the load factor) before hitting the trailing
                    // control bytes (containing EMPTY).
                    if unlikely(is_full(*self.data_ctrl(result))) {
                        debug_assert!(self.bucket_mask < Group::WIDTH);
                        debug_assert_ne!(probe_seq.pos, 0);
                        return Group::load_aligned(self.data_ctrl(0))
                            .match_empty_or_deleted()
                            .lowest_set_bit_nonzero();
                    }

                    return result;
                }
            }
            probe_seq.move_next(self.bucket_mask);
        }
    }

    /// Searches for an empty or deleted `pointer bucket` which is suitable for inserting
    /// a new `pointer element` and return it index in the pointer part of the table.
    /// The difference between this function and [`prepare_pointer_insert_slot`] function
    /// is that this function doesn't change `pointer control byte` under that index.
    ///
    /// There must be at least 1 empty `pointer bucket` in the table.
    ///
    /// # Note
    ///
    /// This function must be used together with [`find_data_insert_slot`]
    /// function, as well as with [`set_ctrl_h2`] and [`set_pointers_ctrl_h2`]
    /// functions, because firstly we store in the data part of the table
    /// a `data` using `hash_1`, and than we store in the pointer part of
    /// the table a `pointer` to the data using `hash_2`.
    ///
    /// [`prepare_pointer_insert_slot`]: RawTableInner::prepare_pointer_insert_slot
    /// [`find_data_insert_slot`]: RawTableInner::find_data_insert_slot
    /// [`set_ctrl_h2`]: RawTableInner::set_ctrl_h2
    /// [`set_pointers_ctrl_h2`]: RawTableInner::set_pointers_ctrl_h2
    #[inline]
    fn find_pointer_insert_slot(&self, hash_2: u64) -> usize {
        let mut probe_seq = self.probe_seq(hash_2);
        loop {
            unsafe {
                let group = Group::load(self.pointers_ctrl(probe_seq.pos));
                if let Some(bit) = group.match_empty_or_deleted().lowest_set_bit() {
                    let result = (probe_seq.pos + bit) & self.bucket_mask;

                    // In tables smaller than the group width, trailing control
                    // bytes outside the range of the table are filled with
                    // EMPTY entries. These will unfortunately trigger a
                    // match, but once masked may point to a full bucket that
                    // is already occupied. We detect this situation here and
                    // perform a second scan starting at the beginning of the
                    // table. This second scan is guaranteed to find an empty
                    // slot (due to the load factor) before hitting the trailing
                    // control bytes (containing EMPTY).
                    if unlikely(is_full(*self.pointers_ctrl(result))) {
                        debug_assert!(self.bucket_mask < Group::WIDTH);
                        debug_assert_ne!(probe_seq.pos, 0);
                        return Group::load_aligned(self.pointers_ctrl(0))
                            .match_empty_or_deleted()
                            .lowest_set_bit_nonzero();
                    }

                    return result;
                }
            }
            probe_seq.move_next(self.bucket_mask);
        }
    }

    /// Searches for an `data element` in the data part of the table.
    /// This uses dynamic dispatch to reduce the amount of
    /// code generated, but it is eliminated by LLVM optimizations.
    #[inline]
    fn find_data_inner(&self, hash_1: u64, eq_1: &mut dyn FnMut(usize) -> bool) -> Option<usize> {
        let h2_hash_1 = h2(hash_1);
        let mut probe_seq = self.probe_seq(hash_1);

        loop {
            let group = unsafe { Group::load(self.data_ctrl(probe_seq.pos)) };

            for bit in group.match_byte(h2_hash_1) {
                let index = (probe_seq.pos + bit) & self.bucket_mask;

                if likely(eq_1(index)) {
                    return Some(index);
                }
            }

            if likely(group.match_empty().any_bit_set()) {
                return None;
            }

            probe_seq.move_next(self.bucket_mask);
        }
    }

    /// Searches for an `pointer element` in the pointer part of the table.
    /// This uses dynamic dispatch to reduce the amount of
    /// code generated, but it is eliminated by LLVM optimizations.
    #[inline]
    fn find_pointer_inner(
        &self,
        hash_2: u64,
        eq_2: &mut dyn FnMut(usize) -> bool,
    ) -> Option<usize> {
        let h2_hash_2 = h2(hash_2);
        let mut probe_seq = self.probe_seq(hash_2);

        loop {
            let group = unsafe { Group::load(self.pointers_ctrl(probe_seq.pos)) };

            for bit in group.match_byte(h2_hash_2) {
                let index = (probe_seq.pos + bit) & self.bucket_mask;

                if likely(eq_2(index)) {
                    return Some(index);
                }
            }

            if likely(group.match_empty().any_bit_set()) {
                return None;
            }

            probe_seq.move_next(self.bucket_mask);
        }
    }

    /// Prepere to rehashing the contents of the table in place (i.e. without changing the
    /// allocation). Convert all full `data control bytes` to `DELETED`, and all `DELETED`
    /// control bytes to `EMPTY`, i.e. performs the following transformation in the
    /// data part of the table:
    /// - `EMPTY data control bytes   -> EMPTY`
    /// - `DELETED data control bytes -> EMPTY`
    /// - `FULL data control bytes    -> DELETED`
    ///
    /// # Note
    ///
    /// All `pointer control bytes` are converted to `EMPTY` in the pointer part of table.
    /// Therefore, all pointers part of the table must be updated (filled again) after
    /// rehashig `data buckets`.
    #[allow(clippy::mut_mut)]
    #[inline]
    unsafe fn prepare_rehash_in_place(&mut self) {
        // Bulk convert all full data control bytes to DELETED, and all DELETED
        // data control bytes to EMPTY. This effectively frees up all data buckets
        // containing a DELETED entry.
        for i in (0..self.buckets()).step_by(Group::WIDTH) {
            let data_group = Group::load_aligned(self.data_ctrl(i));
            let data_group = data_group.convert_special_to_empty_and_full_to_deleted();
            data_group.store_aligned(self.data_ctrl(i));
        }

        // Fix up the trailing control bytes. See the comments in set_ctrl
        // for the handling of tables smaller than the group width.
        if self.buckets() < Group::WIDTH {
            self.data_ctrl(0)
                .copy_to(self.data_ctrl(Group::WIDTH), self.buckets());
        } else {
            self.data_ctrl(0)
                .copy_to(self.data_ctrl(self.buckets()), Group::WIDTH);
        }

        // At this point all full `data control bytes` converted to DELETED, other `data
        // control bytes` are EMPTY. And because we rehash all data, we clean up our
        // pointers part of table. Unfortunately, it is impossible to reliably determine
        // which data remained in place after rehashing, and which moved to a new location.
        // In addition, the data could have a collision. Therefore, it is safer just to clear
        // the pointers information and fill them again after data rehashing.
        self.pointers_ctrl(0)
            .write_bytes(EMPTY, self.num_ctrl_bytes());
    }

    /// Returns a pointer to a `data element` in the data part of the table.
    //
    //                        data_bucket::<T>(1).as_ptr() return pointer that
    //                        points here in tha data part of the table
    //                        (to the start of T1)
    //                        ∨
    // [Padding], Tlast, ..., |T1|, T0, CT0, CT1, ..., CTlast
    //                           ^
    //                           data_bucket::<T>(1) actually store the pointer
    //                           that points here in tha data part of the table
    //                           (to the end of T1)
    //
    // where: T0...Tlast - our stored data; CT0...CTlast - control bytes
    // or metadata for data.
    #[inline]
    pub unsafe fn data_bucket<T>(&self, index: usize) -> DataBucket<T> {
        debug_assert_ne!(self.bucket_mask, 0);
        debug_assert!(index < self.buckets());
        DataBucket::from_base_index(self.data_end(), index)
    }

    /// Returns a pointer to a `pointer element` in the pointer part of the table.
    //
    //                        pointer_bucket::<T>(1).as_ptr() return pointer
    //                        that points here in the pointer part of the table
    //                        (to the start of P1)
    //                        ∨
    // [Padding], Plast, ..., |P1|, P0, CP0, CP1, ..., CPlast
    //                           ^
    //                           pointer_bucket::<T>(1) actually store the
    //                           pointer that points here in the pointer part of the table
    //                           (to the end of P1)
    //
    // where: `P0...Plast` - our pointers to data; `CP0...CPlast` - control bytes
    // or metadata for pointers; type P = DataBucket<T>.
    #[inline]
    pub unsafe fn pointer_bucket<T>(&self, index: usize) -> PointerBucket<DataBucket<T>> {
        //PointerBucket<NonNull<T>> {
        debug_assert_ne!(self.bucket_mask, 0);
        debug_assert!(index < self.buckets());
        PointerBucket::from_base_index(self.pointers_end(), index)
    }

    /// Returns a pointer to a start of `data element` in the data part of the table.
    //
    //                        data_bucket_ptr(1, mem::size_of::<T>()) return pointer
    //                        that points here in the data part of the table
    //                        (to the start of T1)
    //                        ∨
    // [Padding], Tlast, ..., |T1, T0, CT0, CT1, ..., CTlast
    //
    // where: T0...Tlast - our stored data; CT0...CTlast - control bytes
    // or metadata for data.
    #[inline]
    unsafe fn data_bucket_ptr(&self, index: usize, size_of: usize) -> *mut u8 {
        debug_assert_ne!(self.bucket_mask, 0);
        debug_assert!(index < self.buckets());
        let base: *mut u8 = self.data_end().as_ptr();
        base.sub((index + 1) * size_of)
    }

    /// Returns a pointer to a start of `pointer element` in the pointer part of the
    /// table. Given `size_of` parametr must be equal to mem::size_of::<DataBucket<T>>(),
    /// where T - data type stored inside the table.
    //
    //                        pointer_bucket_ptr(1, mem::size_of::<DataBucket<T>>())
    //                        return pointer that points here in the pointer part of
    //                        the table (to the start of P1)
    //                        ∨
    // [Padding], Plast, ..., |P1, P0, CP0, CP1, ..., CPlast
    //
    // where: `P0...Plast` - our pointers to data; `CP0...CPlast` - control bytes
    // or metadata for pointers; type P = DataBucket<T>.
    #[allow(dead_code)]
    #[inline]
    unsafe fn pointer_bucket_ptr(&self, index: usize, size_of: usize) -> *mut u8 {
        debug_assert_ne!(self.bucket_mask, 0);
        debug_assert!(index < self.buckets());
        let base: *mut u8 = self.pointers_end().as_ptr();
        base.sub((index + 1) * size_of)
    }

    /// Returns pointer to one past last `data element` of the `data part` of the table
    /// as viewed from the start point of the allocation.
    ///
    /// Because actually we start counting from the beginning of the `data control bytes`,
    /// where we store our data under "0" index, when viewed from the base point
    /// (the beginning of the `data control bytes`), it returns a pointer to the end of the
    /// first `data element` from the `data part` of the table.
    ///
    /// Because of the above, there are several more equivalents of this function that
    /// return a pointer to the same place, for example:
    /// - `self.data_end::<u8>().as_ptr() == self.data_bucket::<u8>(0).as_ptr().add(1)`;
    /// - `self.data_end::<u8>().as_ptr() == self.data_ctrl(0)`.
    //
    //                                data_end::<T>() return pointer
    //                                that points here in the data part of the table
    //                                (to the end of T0 or to the start of CT0,
    //                                which is the same)
    //                                ∨
    // [Padding], Tlast, ..., T1, T0, |CT0, CT1, ..., CTlast
    //
    // where: T0...Tlast - our stored data; CT0...CTlast - control bytes
    // or metadata for data.
    #[inline]
    unsafe fn data_end<T>(&self) -> NonNull<T> {
        NonNull::new_unchecked(self.data_ctrl.as_ptr().cast())
    }

    /// Returns pointer to one past last `pointer element` of the `pointer part` of the table
    /// as viewed from the start point of the allocation.
    ///
    /// Because actually we start counting from the beginning of the `pointer control bytes`,
    /// where we store our pointer under "0" index, when viewed from the base point
    /// (the beginning of the `pointer control bytes`), it returns a pointer to the end of the
    /// first `pointer element` from the `pointer part` of the table.
    ///
    /// Because of the above, there are several more equivalents of this function that
    /// return a pointer to the same place, for example:
    /// - `self.pointers_end::<u8>().as_ptr() == self.pointer_bucket::<u8>(0).as_ptr().add(1)`;
    /// - `self.pointers_end::<u8>().as_ptr() == self.data_ctrl(0)`.
    //
    //                                pointers_end::<T>() return pointer
    //                                that points here in the pointer part of the table
    //                                (to the end of P0 or to the start of CP0,
    //                                which is the same)
    //                                ∨
    // [Padding], Plast, ..., P1, P0, |CP0, CP1, ..., CPlast
    //
    // where: `P0...Plast` - our pointers to data; `CP0...CPlast` - control bytes
    // or metadata for pointers; type P = DataBucket<T>.
    #[inline]
    unsafe fn pointers_end<T>(&self) -> NonNull<T> {
        NonNull::new_unchecked(self.pointers_ctrl.as_ptr().cast())
    }

    /// Returns an iterator-like object for a probe sequence on the table.
    ///
    /// This iterator never terminates, but is guaranteed to visit each bucket
    /// group exactly once. The loop using `probe_seq` must terminate upon
    /// reaching a group containing an empty bucket.
    #[inline]
    fn probe_seq(&self, hash: u64) -> ProbeSeq {
        ProbeSeq {
            pos: h1(hash) & self.bucket_mask,
            stride: 0,
        }
    }

    /// Returns the indexes of a `data bucket` and a `pointer bucket` for
    /// which a `data value` and pointer to that `data` must be inserted
    /// if there is enough room in the table, otherwise returns error.
    ///
    /// # Safety
    ///
    /// This function doesn't check existance of any `data` or `pointer`
    /// elements in the table, so the caller of this function must check
    /// that by themself.
    #[cfg(feature = "raw")]
    #[inline]
    unsafe fn prepare_insert_no_grow(
        &mut self,
        hash_1: u64,
        hash_2: u64,
    ) -> Result<(usize, usize), ()> {
        let index_1 = self.find_data_insert_slot(hash_1);
        let old_ctrl_1 = *self.data_ctrl(index_1);

        if unlikely(self.data_growth_left == 0 && special_is_empty(old_ctrl_1)) {
            Err(())
        } else {
            let index_2 = self.find_pointer_insert_slot(hash_2);
            let old_ctrl_2 = *self.pointers_ctrl(index_2);

            if unlikely(self.pointers_growth_left == 0 && special_is_empty(old_ctrl_2)) {
                Err(())
            } else {
                self.record_item_insert_at(
                    index_1, old_ctrl_1, hash_1, index_2, old_ctrl_2, hash_2,
                );
                Ok((index_1, index_2))
            }
        }
    }

    /// Sets the `hash_1` for the slot under given `index_1` in the `data control bytes`
    /// in the data part of the table and sets the `hash_2` for the slot under given
    /// `index_2` in the `pointer control bytes` in the pointer part of the table.
    ///
    /// If `old_ctrl_1` marked as empty than we decrease by one the number of elements
    /// that can be inserted before we need to grow the table.
    #[inline]
    unsafe fn record_item_insert_at(
        &mut self,
        index_1: usize,
        old_ctrl_1: u8,
        hash_1: u64,
        index_2: usize,
        old_ctrl_2: u8,
        hash_2: u64,
    ) {
        // debug_assert_eq!(special_is_empty(old_ctrl_1), special_is_empty(old_ctrl_2));

        self.data_growth_left -= usize::from(special_is_empty(old_ctrl_1));
        self.pointers_growth_left -= usize::from(special_is_empty(old_ctrl_2));
        self.set_data_ctrl_h2(index_1, hash_1);
        self.set_pointers_ctrl_h2(index_2, hash_2);
        self.items += 1;
    }

    /// Scan through all of the control bytes in groups, which may not
    /// be aligned to the group size. Return true if both the `i` and `new_i`
    /// positions fall within the same unaligned group.
    #[inline]
    fn is_in_same_group(&self, i: usize, new_i: usize, hash: u64) -> bool {
        let probe_seq_pos = self.probe_seq(hash).pos;
        let probe_index =
            |pos: usize| (pos.wrapping_sub(probe_seq_pos) & self.bucket_mask) / Group::WIDTH;
        probe_index(i) == probe_index(new_i)
    }

    /// Sets a `data control byte` to the hash, and possibly also the replicated
    /// `data control byte` at the end of the `data array`.
    #[inline]
    unsafe fn set_data_ctrl_h2(&self, index: usize, hash: u64) {
        self.set_data_ctrl(index, h2(hash));
    }

    /// Sets a `pointer control byte` to the hash, and possibly also the replicated
    /// `pointer control byte` at the end of the `pointer array`.
    #[inline]
    unsafe fn set_pointers_ctrl_h2(&self, index: usize, hash: u64) {
        self.set_pointers_ctrl(index, h2(hash));
    }

    /// Replase a `data control byte` to the given hash under the given index
    /// in the data part of the table and return old one under that index.
    #[inline]
    unsafe fn replace_data_ctrl_h2(&self, index: usize, hash: u64) -> u8 {
        let prev_ctrl = *self.data_ctrl(index);
        self.set_data_ctrl_h2(index, hash);
        prev_ctrl
    }

    /// Replase a `pointer control byte` to the given hash under the given index
    /// in the pointer part of the table and return old one under that index.
    #[allow(dead_code)]
    #[inline]
    unsafe fn replace_pointers_ctrl_h2(&self, index: usize, hash: u64) -> u8 {
        let prev_ctrl = *self.pointers_ctrl(index);
        self.set_pointers_ctrl_h2(index, hash);
        prev_ctrl
    }

    /// Sets a `data control byte`, and possibly also the replicated control byte at
    /// the end of the `data array`.
    #[inline]
    unsafe fn set_data_ctrl(&self, index: usize, ctrl: u8) {
        // Replicate the first Group::WIDTH control bytes at the end of
        // the array without using a branch:
        // - If index >= Group::WIDTH then index == index2.
        // - Otherwise index2 == self.bucket_mask + 1 + index.
        //
        // The very last replicated control byte is never actually read because
        // we mask the initial index for unaligned loads, but we write it
        // anyways because it makes the set_ctrl implementation simpler.
        //
        // If there are fewer buckets than Group::WIDTH then this code will
        // replicate the buckets at the end of the trailing group. For example
        // with 2 buckets and a group size of 4, the control bytes will look
        // like this:
        //
        //     Real    |             Replicated
        // ---------------------------------------------
        // | [A] | [B] | [EMPTY] | [EMPTY] | [A] | [B] |
        // ---------------------------------------------
        let index2 = ((index.wrapping_sub(Group::WIDTH)) & self.bucket_mask) + Group::WIDTH;

        *self.data_ctrl(index) = ctrl;
        *self.data_ctrl(index2) = ctrl;
    }

    /// Sets a `pointer control byte`, and possibly also the replicated control byte at
    /// the end of the `pointer array`.
    #[inline]
    unsafe fn set_pointers_ctrl(&self, index: usize, ctrl: u8) {
        // Replicate the first Group::WIDTH control bytes at the end of
        // the array without using a branch:
        // - If index >= Group::WIDTH then index == index2.
        // - Otherwise index2 == self.bucket_mask + 1 + index.
        //
        // The very last replicated control byte is never actually read because
        // we mask the initial index for unaligned loads, but we write it
        // anyways because it makes the set_ctrl implementation simpler.
        //
        // If there are fewer buckets than Group::WIDTH then this code will
        // replicate the buckets at the end of the trailing group. For example
        // with 2 buckets and a group size of 4, the control bytes will look
        // like this:
        //
        //     Real    |             Replicated
        // ---------------------------------------------
        // | [A] | [B] | [EMPTY] | [EMPTY] | [A] | [B] |
        // ---------------------------------------------
        let index2 = ((index.wrapping_sub(Group::WIDTH)) & self.bucket_mask) + Group::WIDTH;

        *self.pointers_ctrl(index) = ctrl;
        *self.pointers_ctrl(index2) = ctrl;
    }

    /// Returns a pointer to a `data control byte` in the data
    /// part of the table.
    //
    //                                      data_ctrl(1) return pointer that points here
    //      data_ctrl(0) return pointer     in the data part of the table (to the
    //                 that points here     start of CT1)
    //                                ∨     ∨
    // [Padding], Tlast, ..., T1, T0, |CT0, |CT1, ..., CTlast
    //
    // where: T0...Tlast - our stored data; CT0...CTlast - control bytes
    // or metadata for data.
    #[inline]
    unsafe fn data_ctrl(&self, index: usize) -> *mut u8 {
        debug_assert!(index < self.num_ctrl_bytes());
        self.data_ctrl.as_ptr().add(index)
    }

    /// Returns a pointer to a `pointer control byte` in the pointers
    /// part of the table.
    //
    //                                      pointers_ctrl(1) return pointer that points
    //  pointers_ctrl(0) return pointer     here in the data part of the table (to the
    //                 that points here     start of CP1)
    //                                ∨     ∨
    // [Padding], Plast, ..., P1, P0, |CP0, |CP1, ..., CPlast
    //
    // where: `P0...Plast` - our pointers to data; `CP0...CPlast` - control bytes
    // or metadata for pointers; type P = DataBucket<T>.
    #[inline]
    unsafe fn pointers_ctrl(&self, index: usize) -> *mut u8 {
        debug_assert!(index < self.num_ctrl_bytes());
        self.pointers_ctrl.as_ptr().add(index)
    }

    /// Return the number of buckets in the table. It is the same
    /// value for both `data` and `pointers` parts of the table.
    #[inline]
    fn buckets(&self) -> usize {
        self.bucket_mask + 1
    }

    /// Checks whether the `data bucket` at `index` is full.
    ///
    /// # Safety
    ///
    /// The caller must ensure `index` is less than the number of buckets.
    #[inline]
    #[cfg(feature = "raw")]
    unsafe fn is_data_bucket_full(&self, index: usize) -> bool {
        debug_assert!(index < self.buckets());
        is_full(*self.data_ctrl(index))
    }

    /// Checks whether the `pointer bucket` at `index` is full.
    ///
    /// # Safety
    ///
    /// The caller must ensure `index` is less than the number of buckets.
    #[inline]
    #[cfg(feature = "raw")]
    unsafe fn is_pointer_bucket_full(&self, index: usize) -> bool {
        debug_assert!(index < self.buckets());
        is_full(*self.pointers_ctrl(index))
    }

    /// Return the number of contlol bytes in the table. It is the same
    /// value for both `data` and `pointers` parts of the table.
    #[inline]
    fn num_ctrl_bytes(&self) -> usize {
        self.bucket_mask + 1 + Group::WIDTH
    }

    /// Return if it is an empty table, without allocation.
    #[inline]
    fn is_empty_singleton(&self) -> bool {
        self.bucket_mask == 0
    }

    /// Attempts to allocate a new hash table with at least enough capacity
    /// for inserting the given number of elements without reallocating,
    /// and return it inside ScopeGuard to protect against panic in the hash
    /// function.
    #[allow(clippy::mut_mut)]
    #[inline]
    unsafe fn prepare_resize(
        &self,
        table_layout: TableLayout,
        capacity: usize,
        fallibility: Fallibility,
    ) -> Result<crate::scopeguard::ScopeGuard<Self, impl FnMut(&mut Self)>, TryReserveError> {
        let items = self.items;
        debug_assert!(items <= capacity);

        // Allocate and initialize the new table.
        let mut new_table = RawTableInner::fallible_with_capacity(
            self.alloc.clone(),
            table_layout,
            capacity,
            fallibility,
        )?;
        new_table.data_growth_left -= items;
        new_table.pointers_growth_left -= items;
        new_table.items = items;

        // The hash function may panic, in which case we simply free the new
        // table without dropping any elements that may have been copied into
        // it.
        //
        // This guard is also used to free the old table on success, see
        // the comment at the bottom of this function.
        Ok(guard(new_table, move |self_| {
            if !self_.is_empty_singleton() {
                self_.free_buckets(table_layout);
            }
        }))
    }

    /// Reserves or rehashes to make room for `additional` more elements.
    ///
    /// This uses dynamic dispatch to reduce the amount of
    /// code generated, but it is eliminated by LLVM optimizations when inlined.
    #[allow(clippy::inline_always)]
    #[inline(always)]
    unsafe fn reserve_rehash_inner<T>(
        &mut self,
        additional: usize,
        hasher_1: &dyn Fn(&mut Self, usize) -> u64,
        hasher_2: &dyn Fn(&mut Self, usize) -> u64,
        fallibility: Fallibility,
        layout: TableLayout,
        drop: Option<fn(*mut u8)>,
    ) -> Result<(), TryReserveError> {
        // Avoid `Option::ok_or_else` because it bloats LLVM IR.
        let new_items = match self.items.checked_add(additional) {
            Some(new_items) => new_items,
            None => return Err(fallibility.capacity_overflow()),
        };
        let full_capacity = bucket_mask_to_capacity(self.bucket_mask);
        if new_items <= full_capacity / 2 {
            // Rehash in-place without re-allocating if we have plenty of spare
            // capacity that is locked up due to DELETED entries.
            self.rehash_in_place::<T>(hasher_1, hasher_2, layout.type_size, drop);
            Ok(())
        } else {
            // Otherwise, conservatively resize to at least the next size up
            // to avoid churning deletes into frequent rehashes.
            self.resize_inner::<T>(
                usize::max(new_items, full_capacity + 1),
                hasher_1,
                hasher_2,
                fallibility,
                layout,
            )
        }
    }

    /// Allocates a new table of a different size and moves the contents of the
    /// current table into it.
    ///
    /// This uses dynamic dispatch to reduce the amount of
    /// code generated, but it is eliminated by LLVM optimizations when inlined.
    #[allow(clippy::inline_always)]
    #[inline(always)]
    unsafe fn resize_inner<T>(
        &mut self,
        capacity: usize,
        hasher_1: &dyn Fn(&mut Self, usize) -> u64,
        hasher_2: &dyn Fn(&mut Self, usize) -> u64,
        fallibility: Fallibility,
        layout: TableLayout,
    ) -> Result<(), TryReserveError> {
        let mut new_table = self.prepare_resize(layout, capacity, fallibility)?;

        // Copy all elements to the new table.
        for i in 0..self.buckets() {
            if !is_full(*self.data_ctrl(i)) {
                continue;
            }

            // This may panic.
            let hash_1 = hasher_1(self, i);
            let hash_2 = hasher_2(self, i);

            // We can use a simpler version of insert() here since:
            // - there are no DELETED entries.
            // - we know there is enough space in the table.
            // - all elements are unique.
            let index_1 = new_table.prepare_data_insert_slot(hash_1);
            let index_2 = new_table.prepare_pointer_insert_slot(hash_2);

            ptr::copy_nonoverlapping(
                self.data_bucket_ptr(i, layout.type_size),
                new_table.data_bucket_ptr(index_1, layout.type_size),
                layout.type_size,
            );

            ptr::write(
                new_table.pointer_bucket::<T>(index_2).as_ptr(),
                new_table.data_bucket::<T>(index_1),
            );
        }

        // We successfully copied all elements without panicking. Now replace
        // self with the new table. The old table will have its memory freed but
        // the items will not be dropped (since they have been moved into the
        // new table).
        mem::swap(self, &mut new_table);

        Ok(())
    }

    /// Rehashes the contents of the table in place (i.e. without changing the
    /// allocation).
    ///
    /// If `hasher` panics then all the table's contents will be lost.
    ///
    /// This uses dynamic dispatch to reduce the amount of
    /// code generated, but it is eliminated by LLVM optimizations when inlined.
    #[allow(clippy::inline_always)]
    #[cfg_attr(feature = "inline-more", inline(always))]
    #[cfg_attr(not(feature = "inline-more"), inline)]
    pub unsafe fn rehash_in_place<T>(
        &mut self,
        hasher_1: &dyn Fn(&mut Self, usize) -> u64,
        hasher_2: &dyn Fn(&mut Self, usize) -> u64,
        size_of: usize,
        drop: Option<fn(*mut u8)>,
    ) {
        // If the hash function panics then properly clean up all elements
        // that we have in the table. Unfortunately, there is no way to save the
        // elements, since we have to restore the index part of our table. But
        // there is no way to determine in which hashing function the panic occurred.
        // Therefore, calling the second hash function again for pointers is risky
        // because of the possible another panic.
        self.prepare_rehash_in_place();

        let mut guard = guard(self, move |self_| {
            if let Some(drop) = drop {
                for index in 0..self_.buckets() {
                    if *self_.data_ctrl(index) != EMPTY {
                        drop(self_.data_bucket_ptr(index, size_of));
                    }
                }
            }
            self_
                .data_ctrl(0)
                .write_bytes(EMPTY, self_.num_ctrl_bytes());
            self_
                .pointers_ctrl(0)
                .write_bytes(EMPTY, self_.num_ctrl_bytes());

            let growth_left = bucket_mask_to_capacity(self_.bucket_mask);
            // self_.data_growth_left = bucket_mask_to_capacity(self_.bucket_mask);
            self_.data_growth_left = growth_left;
            self_.pointers_growth_left = growth_left;

            self_.items = 0;
        });

        // At this point, DELETED data elements are elements that we haven't
        // rehashed yet. Find them and re-insert them at their ideal
        // position.
        'outer: for i in 0..guard.buckets() {
            if *guard.data_ctrl(i) != DELETED {
                continue;
            }

            let i_p = guard.data_bucket_ptr(i, size_of);

            'inner: loop {
                // Hash the current item
                let hash_1 = hasher_1(*guard, i);

                // Search for a suitable place to put it
                let new_i = guard.find_data_insert_slot(hash_1);

                // Probing works by scanning through all of the control
                // bytes in groups, which may not be aligned to the group
                // size. If both the new and old position fall within the
                // same unaligned group, then there is no benefit in moving
                // it and we can just continue to the next item.
                if likely(guard.is_in_same_group(i, new_i, hash_1)) {
                    guard.set_data_ctrl_h2(i, hash_1);
                    continue 'outer;
                }

                let new_i_p = guard.data_bucket_ptr(new_i, size_of);

                // We are moving the current item to a new position. Write
                // our H2 to the control byte of the new position.
                let prev_ctrl = guard.replace_data_ctrl_h2(new_i, hash_1);
                if prev_ctrl == EMPTY {
                    guard.set_data_ctrl(i, EMPTY);
                    // If the target slot is empty, simply move the current
                    // element into the new slot and clear the old control
                    // byte.
                    ptr::copy_nonoverlapping(i_p, new_i_p, size_of);
                    continue 'outer;
                } else {
                    // If the target slot is occupied, swap the two elements
                    // and then continue processing the element that we just
                    // swapped into the old slot.
                    debug_assert_eq!(prev_ctrl, DELETED);
                    ptr::swap_nonoverlapping(i_p, new_i_p, size_of);
                    continue 'inner;
                }
            }
        }

        // So we re-insert all data elements at their ideal position and can fill
        // the pointers part of the table (we can not do it in above loops
        // due to the non-obvious arrangement of elements)
        for index_1 in 0..guard.buckets() {
            if !is_full(*guard.data_ctrl(index_1)) {
                continue;
            }

            // Hash the current item. This may panic.
            let hash_2 = hasher_2(*guard, index_1);

            // We can use a simpler version of insert() here since:
            // - there are no DELETED entries.
            // - we know there is enough space in the table.
            // - all elements are unique.
            let index_2 = guard.prepare_pointer_insert_slot(hash_2);

            ptr::write(
                guard.pointer_bucket::<T>(index_2).as_ptr(),
                guard.data_bucket::<T>(index_1),
            );
        }

        let growth_left = bucket_mask_to_capacity(guard.bucket_mask) - guard.items;
        guard.data_growth_left = growth_left;
        guard.pointers_growth_left = growth_left;
        // guard.data_growth_left = bucket_mask_to_capacity(guard.bucket_mask) - guard.items;

        mem::forget(guard);
    }

    /// Deallocates the table without dropping any entries.
    #[inline]
    unsafe fn free_buckets(&mut self, table_layout: TableLayout) {
        // Avoid `Option::ok_or_else` because it bloats LLVM IR.
        let (layout, ctrl_offset, _) = match table_layout.calculate_layout_for(self.buckets()) {
            Some(lco) => lco,
            None => hint::unreachable_unchecked(),
        };

        self.alloc.deallocate(
            NonNull::new_unchecked(self.data_ctrl.as_ptr().sub(ctrl_offset)),
            layout,
        );
    }

    /// Marks all table `data` and `pointer` buckets as empty without dropping
    /// data contents.
    #[inline]
    fn clear_no_drop(&mut self) {
        if !self.is_empty_singleton() {
            unsafe {
                self.data_ctrl(0).write_bytes(EMPTY, self.num_ctrl_bytes());
                self.pointers_ctrl(0)
                    .write_bytes(EMPTY, self.num_ctrl_bytes());
            }
        }
        self.items = 0;
        let growth_left = bucket_mask_to_capacity(self.bucket_mask);
        self.data_growth_left = growth_left;
        self.pointers_growth_left = growth_left;
    }

    /// Erases an element from the table without dropping it.
    #[inline]
    unsafe fn erase(&mut self, index_1: usize, index_2: usize) {
        debug_assert!(is_full(*self.data_ctrl(index_1)));
        debug_assert!(is_full(*self.pointers_ctrl(index_2)));

        let d_index_before = index_1.wrapping_sub(Group::WIDTH) & self.bucket_mask;
        let d_empty_before = Group::load(self.data_ctrl(d_index_before)).match_empty();
        let d_empty_after = Group::load(self.data_ctrl(index_1)).match_empty();

        let p_index_before = index_2.wrapping_sub(Group::WIDTH) & self.bucket_mask;
        let p_empty_before = Group::load(self.pointers_ctrl(p_index_before)).match_empty();
        let p_empty_after = Group::load(self.pointers_ctrl(index_2)).match_empty();

        // If we are inside a continuous block of Group::WIDTH full or deleted
        // cells then a probe window may have seen a full block when trying to
        // insert. We therefore need to keep that block non-empty so that
        // lookups will continue searching to the next probe window.
        //
        // Note that in this context `leading_zeros` refers to the bytes at the
        // end of a group, while `trailing_zeros` refers to the bytes at the
        // beginning of a group.
        let d_ctrl =
            if d_empty_before.leading_zeros() + d_empty_after.trailing_zeros() >= Group::WIDTH {
                DELETED
            } else {
                self.data_growth_left += 1;
                EMPTY
            };
        let p_ctrl =
            if p_empty_before.leading_zeros() + p_empty_after.trailing_zeros() >= Group::WIDTH {
                DELETED
            } else {
                self.pointers_growth_left += 1;
                EMPTY
            };
        self.set_data_ctrl(index_1, d_ctrl);
        self.set_pointers_ctrl(index_2, p_ctrl);
        self.items -= 1;
    }
}

/// Iterator over a sub-range of a table. Unlike `RawIter` this iterator does
/// not track an item count.
pub(crate) struct RawDataIterRange<T> {
    // Mask of full buckets in the current group. Bits are cleared from this
    // mask as each element is processed.
    current_group: BitMask,

    // Pointer to the buckets for the current group.
    data: DataBucket<T>,

    // Pointer to the next group of control bytes,
    // Must be aligned to the group size.
    next_ctrl: *const u8,

    // Pointer one past the last control byte of this range.
    //
    //                                 "end" must points here
    //                          in the data part of the table
    //                                 (to the end of CTlast)
    //                                                      ∨
    // [Padding], Tlast, ..., T1, T0, CT0, CT1, ..., CTlast,| Group::WIDTH
    //
    // where: T0...Tlast - our stored data; CT0...CTlast - control bytes
    // or metadata for data.
    // Note: We start counting from "0", so that in the expression CT[last],
    // the "last" index actually one less than the given "buckets" number,
    // i.e. "last = buckets - 1".
    end: *const u8,
}

impl<T> RawDataIterRange<T> {
    /// Returns a `RawDataIterRange` covering a subset of a table.
    ///
    /// The control byte address must be aligned to the group size.
    //
    //                                "data_ctrl" must points here
    //                                in the data part of the table
    //                                (to the start of CT0)
    //                                ∨
    // [Padding], Tlast, ..., T1, T0, |CT0, CT1, ..., CTlast, Group::WIDTH
    //                                \_________  _________/
    //                                          \/
    //                                   len = buckets number, i.e. RawTableInner::buckets
    //
    // where: T0...Tlast - our stored data; CT0...CTlast - control bytes
    // or metadata for data.
    // Note: We start counting from "0", so that in the expression CT[last],
    // the "last" index actually one less than the given "buckets" number,
    // i.e. "last = buckets - 1".
    #[cfg_attr(feature = "inline-more", inline)]
    unsafe fn new(data_ctrl: *const u8, data: DataBucket<T>, len: usize) -> Self {
        debug_assert_ne!(len, 0);
        debug_assert_eq!(data_ctrl as usize % Group::WIDTH, 0);
        let end = data_ctrl.add(len);

        // Load the first group and advance ctrl to point to the next group
        let current_group = Group::load_aligned(data_ctrl).match_full();
        let next_ctrl = data_ctrl.add(Group::WIDTH);

        Self {
            current_group,
            data,
            next_ctrl,
            end,
        }
    }

    /// Splits a `RawIterRange` into two halves.
    ///
    /// Returns `None` if the remaining range is smaller than or equal to the
    /// group width.
    #[cfg_attr(feature = "inline-more", inline)]
    #[allow(dead_code)]
    #[cfg(feature = "rayon")]
    pub(crate) fn split(mut self) -> (Self, Option<RawDataIterRange<T>>) {
        unsafe {
            if self.end <= self.next_ctrl {
                // Nothing to split if the group that we are current processing
                // is the last one.
                (self, None)
            } else {
                // len is the remaining number of elements after the group that
                // we are currently processing. It must be a multiple of the
                // group size (small tables are caught by the check above).
                let len = offset_from(self.end, self.next_ctrl);
                debug_assert_eq!(len % Group::WIDTH, 0);

                // Split the remaining elements into two halves, but round the
                // midpoint down in case there is an odd number of groups
                // remaining. This ensures that:
                // - The tail is at least 1 group long.
                // - The split is roughly even considering we still have the
                //   current group to process.
                let mid = (len / 2) & !(Group::WIDTH - 1);

                let tail = Self::new(
                    self.next_ctrl.add(mid),
                    self.data.next_n(Group::WIDTH).next_n(mid),
                    len - mid,
                );
                debug_assert_eq!(
                    self.data.next_n(Group::WIDTH).next_n(mid).ptr,
                    tail.data.ptr
                );
                debug_assert_eq!(self.end, tail.end);
                self.end = self.next_ctrl.add(mid);
                debug_assert_eq!(self.end.add(Group::WIDTH), tail.next_ctrl);
                (self, Some(tail))
            }
        }
    }

    /// # Safety
    /// Caller must ensure that we never try to iterate after yielding all elements.
    #[cfg_attr(feature = "inline-more", inline)]
    unsafe fn next_impl_unchecked_ptr_range(&mut self) -> Option<DataBucket<T>> {
        loop {
            if let Some(index) = self.current_group.lowest_set_bit() {
                self.current_group = self.current_group.remove_lowest_bit();
                return Some(self.data.next_n(index));
            }

            // We might read past self.end up to the next group boundary,
            // but this is fine because it only occurs on tables smaller
            // than the group size where the trailing control bytes are all
            // EMPTY. On larger tables self.end is guaranteed to be aligned
            // to the group size (since tables are power-of-two sized).
            self.current_group = Group::load_aligned(self.next_ctrl).match_full();
            self.data = self.data.next_n(Group::WIDTH);
            self.next_ctrl = self.next_ctrl.add(Group::WIDTH);
        }
    }

    /// # Safety
    /// We check if we already yielding all elements.
    #[cfg_attr(feature = "inline-more", inline)]
    unsafe fn next_impl_check_ptr_range(&mut self) -> Option<DataBucket<T>> {
        loop {
            if let Some(index) = self.current_group.lowest_set_bit() {
                self.current_group = self.current_group.remove_lowest_bit();
                return Some(self.data.next_n(index));
            }

            if self.next_ctrl >= self.end {
                return None;
            }

            // We might read past self.end up to the next group boundary,
            // but this is fine because it only occurs on tables smaller
            // than the group size where the trailing control bytes are all
            // EMPTY. On larger tables self.end is guaranteed to be aligned
            // to the group size (since tables are power-of-two sized).
            self.current_group = Group::load_aligned(self.next_ctrl).match_full();
            self.data = self.data.next_n(Group::WIDTH);
            self.next_ctrl = self.next_ctrl.add(Group::WIDTH);
        }
    }
}

// We make raw iterators unconditionally Send and Sync, and let the PhantomData
// in the actual iterator implementations determine the real Send/Sync bounds.
unsafe impl<T> Send for RawDataIterRange<T> {}
unsafe impl<T> Sync for RawDataIterRange<T> {}

impl<T> Clone for RawDataIterRange<T> {
    #[cfg_attr(feature = "inline-more", inline)]
    fn clone(&self) -> Self {
        Self {
            data: self.data.clone(),
            next_ctrl: self.next_ctrl,
            current_group: self.current_group,
            end: self.end,
        }
    }
}

impl<T> Iterator for RawDataIterRange<T> {
    type Item = DataBucket<T>;

    #[cfg_attr(feature = "inline-more", inline)]
    fn next(&mut self) -> Option<DataBucket<T>> {
        unsafe {
            // SAFETY: We check if we already yielding all elements.
            self.next_impl_check_ptr_range()
        }
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        // We don't have an item count, so just guess based on the range size.
        let remaining_buckets = if self.end > self.next_ctrl {
            unsafe { offset_from(self.end, self.next_ctrl) }
        } else {
            0
        };

        // Add a group width to include the group we are currently processing.
        (0, Some(Group::WIDTH + remaining_buckets))
    }
}

impl<T> FusedIterator for RawDataIterRange<T> {}

/// Iterator which returns a raw pointer to every full bucket in the table.
///
/// For maximum flexibility this iterator is not bound by a lifetime, but you
/// must observe several rules when using it:
/// - You must not free the hash table while iterating (including via growing/shrinking).
/// - It is fine to erase a bucket that has been yielded by the iterator.
/// - Erasing a bucket that has not yet been yielded by the iterator may still
///   result in the iterator yielding that bucket (unless `reflect_remove` is called).
/// - It is unspecified whether an element inserted after the iterator was
///   created will be yielded by that iterator (unless `reflect_insert` is called).
/// - The order in which the iterator yields bucket is unspecified and may
///   change in the future.
pub struct RawDataIter<T> {
    pub(crate) iter: RawDataIterRange<T>,
    items: usize,
}

impl<T> RawDataIter<T> {
    /// Refresh the iterator so that it reflects a removal from the given bucket.
    ///
    /// For the iterator to remain valid, this method must be called once
    /// for each removed bucket before `next` is called again.
    ///
    /// This method should be called _before_ the removal is made. It is not necessary to call this
    /// method if you are removing an item that this iterator yielded in the past.
    #[cfg(feature = "raw")]
    pub fn reflect_remove(&mut self, b: &DataBucket<T>) {
        self.reflect_toggle_full(b, false);
    }

    /// Refresh the iterator so that it reflects an insertion into the given bucket.
    ///
    /// For the iterator to remain valid, this method must be called once
    /// for each insert before `next` is called again.
    ///
    /// This method does not guarantee that an insertion of a bucket with a greater
    /// index than the last one yielded will be reflected in the iterator.
    ///
    /// This method should be called _after_ the given insert is made.
    #[cfg(feature = "raw")]
    pub fn reflect_insert(&mut self, b: &DataBucket<T>) {
        self.reflect_toggle_full(b, true);
    }

    /// Refresh the iterator so that it reflects a change to the state of the given bucket.
    #[cfg(feature = "raw")]
    fn reflect_toggle_full(&mut self, b: &DataBucket<T>, is_insert: bool) {
        unsafe {
            if b.as_ptr() > self.iter.data.as_ptr() {
                // The iterator has already passed the bucket's group.
                // So the toggle isn't relevant to this iterator.
                return;
            }

            if self.iter.next_ctrl < self.iter.end
                && b.as_ptr() <= self.iter.data.next_n(Group::WIDTH).as_ptr()
            {
                // The iterator has not yet reached the bucket's group.
                // We don't need to reload anything, but we do need to adjust the item count.

                if cfg!(debug_assertions) {
                    // Double-check that the user isn't lying to us by checking the bucket state.
                    // To do that, we need to find its control byte. We know that self.iter.data is
                    // at self.iter.next_ctrl - Group::WIDTH, so we work from there:
                    let offset = offset_from(self.iter.data.as_ptr(), b.as_ptr());
                    let ctrl = self.iter.next_ctrl.sub(Group::WIDTH).add(offset);
                    // This method should be called _before_ a removal, or _after_ an insert,
                    // so in both cases the ctrl byte should indicate that the bucket is full.
                    assert!(is_full(*ctrl));
                }

                if is_insert {
                    self.items += 1;
                } else {
                    self.items -= 1;
                }

                return;
            }

            // The iterator is at the bucket group that the toggled bucket is in.
            // We need to do two things:
            //
            //  - Determine if the iterator already yielded the toggled bucket.
            //    If it did, we're done.
            //  - Otherwise, update the iterator cached group so that it won't
            //    yield a to-be-removed bucket, or _will_ yield a to-be-added bucket.
            //    We'll also need to update the item count accordingly.
            if let Some(index) = self.iter.current_group.lowest_set_bit() {
                let next_bucket = self.iter.data.next_n(index);
                if b.as_ptr() > next_bucket.as_ptr() {
                    // The toggled bucket is "before" the bucket the iterator would yield next. We
                    // therefore don't need to do anything --- the iterator has already passed the
                    // bucket in question.
                    //
                    // The item count must already be correct, since a removal or insert "prior" to
                    // the iterator's position wouldn't affect the item count.
                } else {
                    // The removed bucket is an upcoming bucket. We need to make sure it does _not_
                    // get yielded, and also that it's no longer included in the item count.
                    //
                    // NOTE: We can't just reload the group here, both since that might reflect
                    // inserts we've already passed, and because that might inadvertently unset the
                    // bits for _other_ removals. If we do that, we'd have to also decrement the
                    // item count for those other bits that we unset. But the presumably subsequent
                    // call to reflect for those buckets might _also_ decrement the item count.
                    // Instead, we _just_ flip the bit for the particular bucket the caller asked
                    // us to reflect.
                    let our_bit = offset_from(self.iter.data.as_ptr(), b.as_ptr());
                    let was_full = self.iter.current_group.flip(our_bit);
                    debug_assert_ne!(was_full, is_insert);

                    if is_insert {
                        self.items += 1;
                    } else {
                        self.items -= 1;
                    }

                    if cfg!(debug_assertions) {
                        if b.as_ptr() == next_bucket.as_ptr() {
                            // The removed bucket should no longer be next
                            debug_assert_ne!(self.iter.current_group.lowest_set_bit(), Some(index));
                        } else {
                            // We should not have changed what bucket comes next.
                            debug_assert_eq!(self.iter.current_group.lowest_set_bit(), Some(index));
                        }
                    }
                }
            } else {
                // We must have already iterated past the removed item.
            }
        }
    }

    unsafe fn drop_elements(&mut self) {
        if mem::needs_drop::<T>() && self.len() != 0 {
            for item in self {
                item.drop();
            }
        }
    }
}

impl<T> Clone for RawDataIter<T> {
    #[cfg_attr(feature = "inline-more", inline)]
    fn clone(&self) -> Self {
        Self {
            iter: self.iter.clone(),
            items: self.items,
        }
    }
}

impl<T> Iterator for RawDataIter<T> {
    type Item = DataBucket<T>;

    #[cfg_attr(feature = "inline-more", inline)]
    fn next(&mut self) -> Option<DataBucket<T>> {
        // Inner iterator iterates over buckets
        // so it can do unnecessary work if we already yielded all items.
        if self.items == 0 {
            return None;
        }

        let nxt = unsafe {
            // SAFETY: We check number of items to yield using `items` field.
            self.iter.next_impl_unchecked_ptr_range()
        };

        if nxt.is_some() {
            self.items -= 1;
        }

        nxt
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.items, Some(self.items))
    }
}

impl<T> ExactSizeIterator for RawDataIter<T> {}
impl<T> FusedIterator for RawDataIter<T> {}

/// Iterator over a sub-range of a table. Unlike `RawIter` this iterator does
/// not track an item count.
pub(crate) struct RawPointerIterRange<T> {
    // Mask of full buckets in the current group. Bits are cleared from this
    // mask as each element is processed.
    current_group: BitMask,

    // Pointer to the buckets for the current group.
    ptr_to_data: PointerBucket<DataBucket<T>>,

    // Pointer to the next group of control bytes,
    // Must be aligned to the group size.
    next_ctrl: *const u8,

    // Pointer one past the last control byte of this range.
    //
    //                                 "end" must points here
    //                       in the pointer part of the table
    //                                 (to the end of CPlast)
    //                                                      ∨
    // [Padding], Plast, ..., P1, P0, CP0, CP1, ..., CPlast,| Group::WIDTH
    //
    // where: `P0...Plast` - our pointers to data; `CP0...CPlast` - control bytes
    // or metadata for pointers; type P = DataBucket<T>.
    // Note: We start counting from "0", so that in the expression CP[last],
    // the "last" index actually one less than the given "buckets" number,
    // i.e. "last = buckets - 1".
    end: *const u8,
}

impl<T> RawPointerIterRange<T> {
    /// Returns a `RawPointerIterRange` covering a subset of a table.
    ///
    /// The control byte address must be aligned to the group size.
    //
    //                                "ptr_ctrl" must points here
    //                                in the pointer part of the table
    //                                (to the start of CP0)
    //                                ∨
    // [Padding], Plast, ..., P1, P0, |CP0, CP1, ..., CPlast, Group::WIDTH
    //                                \_________  _________/
    //                                          \/
    //                                   len = buckets number, i.e. RawTableInner::buckets
    //
    // where: `P0...Plast` - our pointers to data; `CP0...CPlast` - control bytes
    // or metadata for pointers; type P = DataBucket<T>.
    // Note: We start counting from "0", so that in the expression CT[last],
    // the "last" index actually one less than the given "buckets" number,
    // i.e. "last = buckets - 1".
    #[cfg_attr(feature = "inline-more", inline)]
    unsafe fn new(ptr_ctrl: *const u8, ptr: PointerBucket<DataBucket<T>>, len: usize) -> Self {
        debug_assert_ne!(len, 0);
        debug_assert_eq!(ptr_ctrl as usize % Group::WIDTH, 0);
        let end = ptr_ctrl.add(len);

        // Load the first group and advance ctrl to point to the next group
        let current_group = Group::load_aligned(ptr_ctrl).match_full();
        let next_ctrl = ptr_ctrl.add(Group::WIDTH);

        Self {
            current_group,
            ptr_to_data: ptr,
            next_ctrl,
            end,
        }
    }

    /// Splits a `RawIterRange` into two halves.
    ///
    /// Returns `None` if the remaining range is smaller than or equal to the
    /// group width.
    #[cfg_attr(feature = "inline-more", inline)]
    #[allow(dead_code)]
    #[cfg(feature = "rayon")]
    pub(crate) fn split(mut self) -> (Self, Option<RawPointerIterRange<T>>) {
        unsafe {
            if self.end <= self.next_ctrl {
                // Nothing to split if the group that we are current processing
                // is the last one.
                (self, None)
            } else {
                // len is the remaining number of elements after the group that
                // we are currently processing. It must be a multiple of the
                // group size (small tables are caught by the check above).
                let len = offset_from(self.end, self.next_ctrl);
                debug_assert_eq!(len % Group::WIDTH, 0);

                // Split the remaining elements into two halves, but round the
                // midpoint down in case there is an odd number of groups
                // remaining. This ensures that:
                // - The tail is at least 1 group long.
                // - The split is roughly even considering we still have the
                //   current group to process.
                let mid = (len / 2) & !(Group::WIDTH - 1);

                let tail = Self::new(
                    self.next_ctrl.add(mid),
                    self.ptr_to_data.next_n(Group::WIDTH).next_n(mid),
                    len - mid,
                );
                debug_assert_eq!(
                    self.ptr_to_data.next_n(Group::WIDTH).next_n(mid).ptr,
                    tail.ptr_to_data.ptr
                );
                debug_assert_eq!(self.end, tail.end);
                self.end = self.next_ctrl.add(mid);
                debug_assert_eq!(self.end.add(Group::WIDTH), tail.next_ctrl);
                (self, Some(tail))
            }
        }
    }

    /// # Safety
    /// Caller must ensure that we never try to iterate after yielding all elements.
    #[cfg_attr(feature = "inline-more", inline)]
    unsafe fn next_impl_unchecked_ptr_range(&mut self) -> Option<PointerBucket<DataBucket<T>>> {
        loop {
            if let Some(index) = self.current_group.lowest_set_bit() {
                self.current_group = self.current_group.remove_lowest_bit();
                return Some(self.ptr_to_data.next_n(index));
            }

            // We might read past self.end up to the next group boundary,
            // but this is fine because it only occurs on tables smaller
            // than the group size where the trailing control bytes are all
            // EMPTY. On larger tables self.end is guaranteed to be aligned
            // to the group size (since tables are power-of-two sized).
            self.current_group = Group::load_aligned(self.next_ctrl).match_full();
            self.ptr_to_data = self.ptr_to_data.next_n(Group::WIDTH);
            self.next_ctrl = self.next_ctrl.add(Group::WIDTH);
        }
    }

    /// # Safety
    /// We check if we already yielding all elements.
    #[cfg_attr(feature = "inline-more", inline)]
    unsafe fn next_impl_check_ptr_range(&mut self) -> Option<PointerBucket<DataBucket<T>>> {
        loop {
            if let Some(index) = self.current_group.lowest_set_bit() {
                self.current_group = self.current_group.remove_lowest_bit();
                return Some(self.ptr_to_data.next_n(index));
            }

            if self.next_ctrl >= self.end {
                return None;
            }

            // We might read past self.end up to the next group boundary,
            // but this is fine because it only occurs on tables smaller
            // than the group size where the trailing control bytes are all
            // EMPTY. On larger tables self.end is guaranteed to be aligned
            // to the group size (since tables are power-of-two sized).
            self.current_group = Group::load_aligned(self.next_ctrl).match_full();
            self.ptr_to_data = self.ptr_to_data.next_n(Group::WIDTH);
            self.next_ctrl = self.next_ctrl.add(Group::WIDTH);
        }
    }
}

// We make raw iterators unconditionally Send and Sync, and let the PhantomData
// in the actual iterator implementations determine the real Send/Sync bounds.
unsafe impl<T> Send for RawPointerIterRange<T> {}
unsafe impl<T> Sync for RawPointerIterRange<T> {}

impl<T> Clone for RawPointerIterRange<T> {
    #[cfg_attr(feature = "inline-more", inline)]
    fn clone(&self) -> Self {
        Self {
            ptr_to_data: self.ptr_to_data.clone(),
            next_ctrl: self.next_ctrl,
            current_group: self.current_group,
            end: self.end,
        }
    }
}

impl<T> Iterator for RawPointerIterRange<T> {
    type Item = PointerBucket<DataBucket<T>>;

    #[cfg_attr(feature = "inline-more", inline)]
    fn next(&mut self) -> Option<Self::Item> {
        unsafe {
            // SAFETY: We check if we already yielding all elements.
            self.next_impl_check_ptr_range()
        }
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        // We don't have an item count, so just guess based on the range size.
        let remaining_buckets = if self.end > self.next_ctrl {
            unsafe { offset_from(self.end, self.next_ctrl) }
        } else {
            0
        };

        // Add a group width to include the group we are currently processing.
        (0, Some(Group::WIDTH + remaining_buckets))
    }
}

impl<T> FusedIterator for RawPointerIterRange<T> {}

/// Iterator which returns a raw pointer to every full bucket in the table.
///
/// For maximum flexibility this iterator is not bound by a lifetime, but you
/// must observe several rules when using it:
/// - You must not free the hash table while iterating (including via growing/shrinking).
/// - It is fine to erase a bucket that has been yielded by the iterator.
/// - Erasing a bucket that has not yet been yielded by the iterator may still
///   result in the iterator yielding that bucket (unless `reflect_remove` is called).
/// - It is unspecified whether an element inserted after the iterator was
///   created will be yielded by that iterator (unless `reflect_insert` is called).
/// - The order in which the iterator yields bucket is unspecified and may
///   change in the future.
pub struct RawPointerIter<T> {
    pub(crate) iter: RawPointerIterRange<T>,
    items: usize,
}

impl<T> RawPointerIter<T> {
    /// Refresh the iterator so that it reflects a removal from the given bucket.
    ///
    /// For the iterator to remain valid, this method must be called once
    /// for each removed bucket before `next` is called again.
    ///
    /// This method should be called _before_ the removal is made. It is not necessary to call this
    /// method if you are removing an item that this iterator yielded in the past.
    #[cfg(feature = "raw")]
    pub fn reflect_remove(&mut self, b: &PointerBucket<DataBucket<T>>) {
        self.reflect_toggle_full(b, false);
    }

    /// Refresh the iterator so that it reflects an insertion into the given bucket.
    ///
    /// For the iterator to remain valid, this method must be called once
    /// for each insert before `next` is called again.
    ///
    /// This method does not guarantee that an insertion of a bucket with a greater
    /// index than the last one yielded will be reflected in the iterator.
    ///
    /// This method should be called _after_ the given insert is made.
    #[cfg(feature = "raw")]
    pub fn reflect_insert(&mut self, b: &PointerBucket<DataBucket<T>>) {
        self.reflect_toggle_full(b, true);
    }

    /// Refresh the iterator so that it reflects a change to the state of the given bucket.
    #[cfg(feature = "raw")]
    fn reflect_toggle_full(&mut self, b: &PointerBucket<DataBucket<T>>, is_insert: bool) {
        unsafe {
            if b.as_ptr() > self.iter.ptr_to_data.as_ptr() {
                // The iterator has already passed the bucket's group.
                // So the toggle isn't relevant to this iterator.
                return;
            }

            if self.iter.next_ctrl < self.iter.end
                && b.as_ptr() <= self.iter.ptr_to_data.next_n(Group::WIDTH).as_ptr()
            {
                // The iterator has not yet reached the bucket's group.
                // We don't need to reload anything, but we do need to adjust the item count.

                if cfg!(debug_assertions) {
                    // Double-check that the user isn't lying to us by checking the bucket state.
                    // To do that, we need to find its control byte. We know that self.iter.data is
                    // at self.iter.next_ctrl - Group::WIDTH, so we work from there:
                    let offset = offset_from(self.iter.ptr_to_data.as_ptr(), b.as_ptr());
                    let ctrl = self.iter.next_ctrl.sub(Group::WIDTH).add(offset);
                    // This method should be called _before_ a removal, or _after_ an insert,
                    // so in both cases the ctrl byte should indicate that the bucket is full.
                    assert!(is_full(*ctrl));
                }

                if is_insert {
                    self.items += 1;
                } else {
                    self.items -= 1;
                }

                return;
            }

            // The iterator is at the bucket group that the toggled bucket is in.
            // We need to do two things:
            //
            //  - Determine if the iterator already yielded the toggled bucket.
            //    If it did, we're done.
            //  - Otherwise, update the iterator cached group so that it won't
            //    yield a to-be-removed bucket, or _will_ yield a to-be-added bucket.
            //    We'll also need to update the item count accordingly.
            if let Some(index) = self.iter.current_group.lowest_set_bit() {
                let next_bucket = self.iter.ptr_to_data.next_n(index);
                if b.as_ptr() > next_bucket.as_ptr() {
                    // The toggled bucket is "before" the bucket the iterator would yield next. We
                    // therefore don't need to do anything --- the iterator has already passed the
                    // bucket in question.
                    //
                    // The item count must already be correct, since a removal or insert "prior" to
                    // the iterator's position wouldn't affect the item count.
                } else {
                    // The removed bucket is an upcoming bucket. We need to make sure it does _not_
                    // get yielded, and also that it's no longer included in the item count.
                    //
                    // NOTE: We can't just reload the group here, both since that might reflect
                    // inserts we've already passed, and because that might inadvertently unset the
                    // bits for _other_ removals. If we do that, we'd have to also decrement the
                    // item count for those other bits that we unset. But the presumably subsequent
                    // call to reflect for those buckets might _also_ decrement the item count.
                    // Instead, we _just_ flip the bit for the particular bucket the caller asked
                    // us to reflect.
                    let our_bit = offset_from(self.iter.ptr_to_data.as_ptr(), b.as_ptr());
                    let was_full = self.iter.current_group.flip(our_bit);
                    debug_assert_ne!(was_full, is_insert);

                    if is_insert {
                        self.items += 1;
                    } else {
                        self.items -= 1;
                    }

                    if cfg!(debug_assertions) {
                        if b.as_ptr() == next_bucket.as_ptr() {
                            // The removed bucket should no longer be next
                            debug_assert_ne!(self.iter.current_group.lowest_set_bit(), Some(index));
                        } else {
                            // We should not have changed what bucket comes next.
                            debug_assert_eq!(self.iter.current_group.lowest_set_bit(), Some(index));
                        }
                    }
                }
            } else {
                // We must have already iterated past the removed item.
            }
        }
    }

    unsafe fn drop_data_elements(&mut self) {
        if mem::needs_drop::<T>() && self.len() != 0 {
            for item in self {
                item.drop_data();
            }
        }
    }
}

impl<T> Clone for RawPointerIter<T> {
    #[cfg_attr(feature = "inline-more", inline)]
    fn clone(&self) -> Self {
        Self {
            iter: self.iter.clone(),
            items: self.items,
        }
    }
}

impl<T> Iterator for RawPointerIter<T> {
    type Item = PointerBucket<DataBucket<T>>;

    #[cfg_attr(feature = "inline-more", inline)]
    fn next(&mut self) -> Option<PointerBucket<DataBucket<T>>> {
        // Inner iterator iterates over buckets
        // so it can do unnecessary work if we already yielded all items.
        if self.items == 0 {
            return None;
        }

        let nxt = unsafe {
            // SAFETY: We check number of items to yield using `items` field.
            self.iter.next_impl_unchecked_ptr_range()
        };

        if nxt.is_some() {
            self.items -= 1;
        }

        nxt
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.items, Some(self.items))
    }
}

impl<T> ExactSizeIterator for RawPointerIter<T> {}
impl<T> FusedIterator for RawPointerIter<T> {}

/// Iterator which consumes a table and returns elements.
pub struct RawIntoDataIter<T, A: Allocator + Clone = Global> {
    iter: RawDataIter<T>,
    allocation: Option<(NonNull<u8>, Layout)>,
    marker: PhantomData<T>,
    alloc: A,
}

impl<T, A: Allocator + Clone> RawIntoDataIter<T, A> {
    /// Returns an iterator over every element `T` in the table / [`RawIntoDataIter`].
    /// It is up to the caller to ensure that the [`RawIntoDataIter`] outlives the [`RawDataIter`].
    #[cfg_attr(feature = "inline-more", inline)]
    pub fn iter(&self) -> RawDataIter<T> {
        self.iter.clone()
    }
}

unsafe impl<T, A: Allocator + Clone> Send for RawIntoDataIter<T, A>
where
    T: Send,
    A: Send,
{
}

unsafe impl<T, A: Allocator + Clone> Sync for RawIntoDataIter<T, A>
where
    T: Sync,
    A: Sync,
{
}

impl<T, A: Allocator + Clone> Drop for RawIntoDataIter<T, A> {
    #[cfg_attr(feature = "inline-more", inline)]
    fn drop(&mut self) {
        unsafe {
            // Drop all remaining elements
            self.iter.drop_elements();

            // Free the table
            if let Some((ptr, layout)) = self.allocation {
                self.alloc.deallocate(ptr, layout);
            }
        }
    }
}

impl<T, A: Allocator + Clone> Iterator for RawIntoDataIter<T, A> {
    type Item = T;

    #[cfg_attr(feature = "inline-more", inline)]
    fn next(&mut self) -> Option<T> {
        unsafe {
            match self.iter.next() {
                Some(elem) => Some(elem.read()),
                None => None,
            }
        }
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.iter.size_hint()
    }
}

impl<T, A: Allocator + Clone> ExactSizeIterator for RawIntoDataIter<T, A> {}
impl<T, A: Allocator + Clone> FusedIterator for RawIntoDataIter<T, A> {}

/// Iterator which consumes a table and returns elements.
pub struct RawIntoPointerIter<T, A: Allocator + Clone = Global> {
    iter: RawPointerIter<T>,
    allocation: Option<(NonNull<u8>, Layout)>,
    marker: PhantomData<T>,
    alloc: A,
}

#[cfg(feature = "raw")]
impl<T, A: Allocator + Clone> RawIntoPointerIter<T, A> {
    /// Returns an iterator over every element `T` in the table / [`RawIntoPointerIter`].
    /// It is up to the caller to ensure that the [`RawIntoPointerIter`] outlives the [`RawPointerIter`].
    #[cfg_attr(feature = "inline-more", inline)]
    pub fn iter(&self) -> RawPointerIter<T> {
        self.iter.clone()
    }
}

unsafe impl<T, A: Allocator + Clone> Send for RawIntoPointerIter<T, A>
where
    T: Send,
    A: Send,
{
}

unsafe impl<T, A: Allocator + Clone> Sync for RawIntoPointerIter<T, A>
where
    T: Sync,
    A: Sync,
{
}

impl<T, A: Allocator + Clone> Drop for RawIntoPointerIter<T, A> {
    #[cfg_attr(feature = "inline-more", inline)]
    fn drop(&mut self) {
        unsafe {
            // Drop all remaining elements
            self.iter.drop_data_elements();

            // Free the table
            if let Some((ptr, layout)) = self.allocation {
                self.alloc.deallocate(ptr, layout);
            }
        }
    }
}

impl<T, A: Allocator + Clone> Iterator for RawIntoPointerIter<T, A> {
    type Item = T;

    #[cfg_attr(feature = "inline-more", inline)]
    fn next(&mut self) -> Option<T> {
        unsafe {
            match self.iter.next() {
                Some(elem) => Some(elem.read_data()),
                None => None,
            }
        }
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.iter.size_hint()
    }
}

impl<T, A: Allocator + Clone> ExactSizeIterator for RawIntoPointerIter<T, A> {}
impl<T, A: Allocator + Clone> FusedIterator for RawIntoPointerIter<T, A> {}

/// Iterator which consumes elements without freeing the table storage.
pub struct RawDrain<'a, T, A: Allocator + Clone = Global> {
    iter: RawDataIter<T>,

    // The table is moved into the iterator for the duration of the drain. This
    // ensures that an empty table is left if the drain iterator is leaked
    // without dropping.
    table: ManuallyDrop<RawTable<T, A>>,
    orig_table: NonNull<RawTable<T, A>>,

    // We don't use a &'a mut RawTable<T> because we want RawDrain to be
    // covariant over T.
    marker: PhantomData<&'a RawTable<T, A>>,
}

impl<T, A: Allocator + Clone> RawDrain<'_, T, A> {
    #[cfg_attr(feature = "inline-more", inline)]
    pub fn iter(&self) -> RawDataIter<T> {
        self.iter.clone()
    }
}

unsafe impl<T, A: Allocator + Copy> Send for RawDrain<'_, T, A>
where
    T: Send,
    A: Send,
{
}

unsafe impl<T, A: Allocator + Copy> Sync for RawDrain<'_, T, A>
where
    T: Sync,
    A: Sync,
{
}

impl<T, A: Allocator + Clone> Drop for RawDrain<'_, T, A> {
    #[cfg_attr(feature = "inline-more", inline)]
    fn drop(&mut self) {
        unsafe {
            // Drop all remaining elements. Note that this may panic.
            self.iter.drop_elements();

            // Reset the contents of the table now that all elements have been
            // dropped.
            self.table.clear_no_drop();

            // Move the now empty table back to its original location.
            self.orig_table
                .as_ptr()
                .copy_from_nonoverlapping(&*self.table, 1);
        }
    }
}

impl<T, A: Allocator + Clone> Iterator for RawDrain<'_, T, A> {
    type Item = T;

    #[cfg_attr(feature = "inline-more", inline)]
    fn next(&mut self) -> Option<T> {
        unsafe {
            match self.iter.next() {
                Some(item) => Some(item.read()),
                None => None,
            }
        }
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.iter.size_hint()
    }
}

impl<T, A: Allocator + Clone> ExactSizeIterator for RawDrain<'_, T, A> {}
impl<T, A: Allocator + Clone> FusedIterator for RawDrain<'_, T, A> {}
