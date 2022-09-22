//! Double map
//!
//! **`This crate is an attempt to provide Rust hash map with double key to single
//! data/value.`**
//!
//! Sometimes during development, it may be necessary to have a data structure like
//! a [`HashMaps`] but with two different keys referring to the same data.
//! For example, if you have some data with a unique ID and a name, then you create
//! a structure that contains the name, and store it in a normal HashMap using the
//! unique ID as the key. However, finding the element throughout the name will be
//! performed with `O(n)` time. The same is true for the reverse case.
//!
//! This crate try to resolve this contradiction by providing a [`DHashMap`] structure -
//! a map where you can add, look up and remove elements using either the first
//! key of type `K1` or the second key of type `K2`.
//!
//! Internally, this crate uses adapted and significantly redesigned code of the
//! *[`RawTable`]* from the [`Hashbrown`] crate which in turn is a Rust port
//! of Google's high-performance [SwissTable] hash map.
//!
//! The original C++ version of [SwissTable] can be found [here], and this
//! [CppCon talk] gives an overview of how the algorithm works.
//!
//! [`HashMaps`]: https://doc.rust-lang.org/stable/std/collections/struct.HashMap.html
//! [`RawTable`]: https://docs.rs/hashbrown/latest/hashbrown/raw/struct.RawTable.html
//! [`Hashbrown`]: https://github.com/rust-lang/hashbrown
//! [SwissTable]: https://abseil.io/blog/20180927-swisstables
//! [here]: https://github.com/abseil/abseil-cpp/blob/master/absl/container/internal/raw_hash_set.h
//! [CppCon talk]: https://www.youtube.com/watch?v=ncHmEUmJZf4

#![no_std]
#![cfg_attr(
    feature = "nightly",
    feature(
        test,
        core_intrinsics,
        min_specialization,
        extend_one,
        allocator_api,
        slice_ptr_get,
        nonnull_slice_from_raw_parts,
        build_hasher_simple_hash_one
    )
)]
#![allow(clippy::missing_safety_doc)]
#![allow(clippy::manual_map)]
#![warn(missing_docs)]
#![warn(rust_2018_idioms)]
#![warn(rustdoc::broken_intra_doc_links)]

#[cfg(test)]
#[macro_use]
extern crate std;

#[cfg_attr(test, macro_use)]
extern crate alloc;

#[macro_use]
mod macros;

#[cfg(feature = "raw")]
/// Experimental and unsafe `RawTable` API. This module is only available if the
/// `raw` feature is enabled.
pub mod raw {
    // The RawTable API is still experimental and is not properly documented yet.
    #[allow(missing_docs)]
    #[allow(unused_imports)]
    #[allow(dead_code)]
    #[path = "mod.rs"]
    mod inner;
    pub use inner::*;
}
#[allow(unused_imports)]
#[cfg(not(feature = "raw"))]
mod raw;

mod scopeguard;

#[allow(missing_docs)]
mod map;

pub mod dhash_map {
    //! A hash map implemented with quadratic probing and SIMD lookup.
    #![allow(missing_docs)]
    pub use crate::map::*;
}

pub use crate::map::DHashMap;

/// Key equivalence trait.
///
/// This trait defines the function used to compare the input value with the
/// map keys (or set values) during a lookup operation such as [`DHashMap::get_key1`]
/// or [`DHashMap::contains_key1`].
/// It is provided with a blanket implementation based on the
/// [`Borrow`](core::borrow::Borrow) trait.
///
/// # Correctness
///
/// Equivalent values must hash to the same value.
///
// [`DHashMap`](crate::map::DHashMap)
// [`DHashMap::get_key1`](crate::map::DHashMap::get_key1)
// [`DHashMap::contains_key1`](crate::map::DHashMap::contains_key1)
pub trait Equivalent<K: ?Sized> {
    /// Checks if this value is equivalent to the given key.
    ///
    /// Returns `true` if both values are equivalent, and `false` otherwise.
    ///
    /// # Correctness
    ///
    /// When this function returns `true`, both `self` and `key` must hash to
    /// the same value.
    fn equivalent(&self, key: &K) -> bool;
}

impl<Q: ?Sized, K: ?Sized> Equivalent<K> for Q
where
    Q: Eq,
    K: core::borrow::Borrow<Q>,
{
    fn equivalent(&self, key: &K) -> bool {
        self == key.borrow()
    }
}

/// The error type for `try_reserve` methods.
#[derive(Clone, PartialEq, Eq, Debug)]
pub enum TryReserveError {
    /// Error due to the computed capacity exceeding the collection's maximum
    /// (usually `isize::MAX` bytes).
    CapacityOverflow,

    /// The memory allocator returned an error
    AllocError {
        /// The layout of the allocation request that failed.
        layout: alloc::alloc::Layout,
    },
}

/// Wrapper around `Bump` which allows it to be used as an allocator for
/// `DHashMap` and `RawTable`.
///
/// `Bump` can be used directly without this wrapper on nightly if you enable
/// the `allocator-api` feature of the `bumpalo` crate.
#[cfg(feature = "bumpalo")]
#[derive(Clone, Copy, Debug)]
pub struct BumpWrapper<'a>(pub &'a bumpalo::Bump);

#[cfg(feature = "bumpalo")]
#[test]
fn test_bumpalo() {
    use bumpalo::Bump;
    let bump = Bump::new();
    let mut map = DHashMap::new_in(BumpWrapper(&bump));
    map.insert(0, 1, 10);
}
