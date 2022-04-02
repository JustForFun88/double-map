//! Double map
//!
//! **`This crate is an attempt to provide Rust hash map with double key to single
//! data/value.`**
//!
//! Sometimes during development, it may be necessary to have a data structure like
//! a [`HashMaps`](`std::collections::HashMap`) but with two different keys referring
//! to the same data.
//! For example, if you have some data with a unique ID and a name, then you create
//! a structure that contains the name, and store it in a normal HashMap using the
//! unique ID as the key. However, finding the element throughout the name will be
//! performed with `O(n)` time. The same is true for the reverse case.
//!
//! This crate try to resolve this contradiction by providing a [`DHashMap`] structure -
//! a map where you can add, look up and remove elements using either the first
//! key of type `K1` or the second key of type `K2`.
//! Internally, it uses two [`HashMaps`](`std::collections::HashMap`): the first
//! is of type `HashMap<K1, (K2, V)>` and the second is of type `HashMap<K2, K1>`.
//! Using two `HashMap`'s insides instead one brings to the performance and
//! memory penalty.
//!
//! It is recommended to use the first key of type `K1` for quick access to the data,
//! because indexing by the second key of type `K2` requires two HashMap lookups.

#![warn(rustdoc::broken_intra_doc_links)]
#![warn(missing_docs)]

mod map;

pub mod dhash_map {
    //! A hash map with double keys implemented as wrapper above two
    //! [`HashMaps`](`std::collections::HashMap`).
    pub use crate::map::*;
}

pub use crate::map::DHashMap;