#[cfg(test)]
mod tests_dhash_map;

use crate::raw::{
    Allocator, DataBucket, Global, PointerBucket, RawDataIter, RawDrain, RawIntoDataIter,
    RawPointerIter, RawTable,
};
use crate::{Equivalent, TryReserveError};
use core::borrow::Borrow;
use core::fmt::{self, Debug};
use core::hash::{BuildHasher, Hash};
use core::iter::{FromIterator, FusedIterator};
use core::marker::PhantomData;
use core::mem;
use core::ops::Index;
use core::ptr;

mod drain;
mod drain_filter;
mod entry;
mod entry_ref;
mod error;
mod into_iter;
mod into_keys;
mod into_values;
mod iter;
mod iter_mut;
mod keys;
mod raw_entry;
mod raw_entry_mut;
mod values;
mod values_mut;

pub use self::drain::*;
pub use self::drain_filter::*;
pub use self::entry::*;
pub use self::entry_ref::*;
pub use self::error::*;
pub use self::into_iter::*;
pub use self::into_keys::*;
pub use self::into_values::*;
pub use self::iter::*;
pub use self::iter_mut::*;
pub use self::keys::*;
pub use self::raw_entry::*;
pub use self::raw_entry_mut::*;
pub use self::values::*;
pub use self::values_mut::*;

/// Default hasher for `HashMap`.
#[cfg(feature = "ahash")]
pub type DefaultHashBuilder = core::hash::BuildHasherDefault<ahash::AHasher>;

/// Dummy default hasher for `HashMap`.
#[cfg(not(feature = "ahash"))]
pub enum DefaultHashBuilder {}

/// A hash map with double keys implemented with quadratic probing and SIMD lookup.
///
/// The default hashing algorithm is currently [`AHash`], though this is
/// subject to change at any point in the future. This hash function is very
/// fast for all types of keys, but this algorithm will typically *not* protect
/// against attacks such as HashDoS.
///
/// The hashing algorithm can be replaced on a per-[`DHashMap`] basis using the
/// [`default`], [`with_hasher`], and [`with_capacity_and_hasher`] methods.
/// There are many alternative [hashing algorithms available on crates.io].
///
/// It is required that the keys implement the [`Eq`] and [`Hash`] traits, although
/// this can frequently be achieved by using `#[derive(PartialEq, Eq, Hash)]`.
/// If you implement these yourself, it is important that the following
/// property holds:
///
/// ```text
/// k1 == k2 -> hash(k1) == hash(k2)
/// ```
///
/// In other words, if two keys are equal, their hashes must be equal.
///
/// It is a logic error for a key to be modified in such a way that the key's
/// hash, as determined by the [`Hash`] trait, or its equality, as determined by
/// the [`Eq`] trait, changes while it is in the map. This is normally only
/// possible through [`Cell`], [`RefCell`], global state, I/O, or unsafe code.
/// The behavior resulting from such a logic error is not specified, but will
/// not result in undefined behavior. This could include panics, incorrect results,
/// aborts, memory leaks, and non-termination.
///
/// It is also a logic error for the [`Hash`] implementation of a key to panic.
/// This is generally only possible if the trait is implemented manually. If a
/// panic does occur then the contents of the `HashMap` become corrupted and
/// all items are dropped from the table.
///
/// [`Eq`]: https://doc.rust-lang.org/std/cmp/trait.Eq.html
/// [`Hash`]: https://doc.rust-lang.org/std/hash/trait.Hash.html
/// [`PartialEq`]: https://doc.rust-lang.org/std/cmp/trait.PartialEq.html
/// [`RefCell`]: https://doc.rust-lang.org/std/cell/struct.RefCell.html
/// [`Cell`]: https://doc.rust-lang.org/std/cell/struct.Cell.html
/// [`default`]: #method.default
/// [`with_hasher`]: #method.with_hasher
/// [`with_capacity_and_hasher`]: #method.with_capacity_and_hasher
/// [`fnv`]: https://crates.io/crates/fnv
/// [`AHash`]: https://crates.io/crates/ahash
/// [hashing algorithms available on crates.io]: https://crates.io/keywords/hasher
pub struct DHashMap<K1, K2, V, S = DefaultHashBuilder, A: Allocator + Clone = Global> {
    hash_builder: S,
    table: RawTable<(K1, K2, V), A>,
}

impl<K1: Clone, K2: Clone, V: Clone, S: Clone, A: Allocator + Clone> Clone
    for DHashMap<K1, K2, V, S, A>
{
    fn clone(&self) -> Self {
        DHashMap {
            hash_builder: self.hash_builder.clone(),
            table: self.table.clone(),
        }
    }

    fn clone_from(&mut self, source: &Self) {
        self.table.clone_from(&source.table);

        // Update hash_builder only if we successfully cloned all elements.
        self.hash_builder.clone_from(&source.hash_builder);
    }
}

/// Ensures that a single closure type across uses of this which, in turn prevents multiple
/// instances of any functions like RawTable::reserve from being generated
#[cfg_attr(feature = "inline-more", inline)]
pub(crate) fn make_hasher_key1<K1, K2, V, S>(hash_builder: &S) -> impl Fn(&(K1, K2, V)) -> u64 + '_
where
    K1: Hash,
    S: BuildHasher,
{
    move |val| make_hash::<K1, S>(hash_builder, &val.0)
}

/// Ensures that a single closure type across uses of this which, in turn prevents multiple
/// instances of any functions like RawTable::reserve from being generated
#[cfg_attr(feature = "inline-more", inline)]
pub(crate) fn make_hasher_key2<K1, K2, V, S>(hash_builder: &S) -> impl Fn(&(K1, K2, V)) -> u64 + '_
where
    K2: Hash,
    S: BuildHasher,
{
    move |val| make_hash::<K2, S>(hash_builder, &val.1)
}

#[cfg(not(feature = "nightly"))]
#[cfg_attr(feature = "inline-more", inline)]
pub(crate) fn make_hash<Q, S>(hash_builder: &S, val: &Q) -> u64
where
    Q: Hash + ?Sized,
    S: BuildHasher,
{
    use core::hash::Hasher;
    let mut state = hash_builder.build_hasher();
    val.hash(&mut state);
    state.finish()
}

#[cfg(feature = "nightly")]
#[cfg_attr(feature = "inline-more", inline)]
pub(crate) fn make_hash<Q, S>(hash_builder: &S, val: &Q) -> u64
where
    Q: Hash + ?Sized,
    S: BuildHasher,
{
    hash_builder.hash_one(val)
}

#[cfg(not(feature = "nightly"))]
#[cfg_attr(feature = "inline-more", inline)]
pub(crate) fn make_insert_hash<K, S>(hash_builder: &S, val: &K) -> u64
where
    K: Hash,
    S: BuildHasher,
{
    use core::hash::Hasher;
    let mut state = hash_builder.build_hasher();
    val.hash(&mut state);
    state.finish()
}

#[cfg(feature = "nightly")]
#[cfg_attr(feature = "inline-more", inline)]
pub(crate) fn make_insert_hash<K, S>(hash_builder: &S, val: &K) -> u64
where
    K: Hash,
    S: BuildHasher,
{
    hash_builder.hash_one(val)
}

/// Ensures that a single closure type across uses of this which, in turn prevents multiple
/// instances of any functions like RawTable::reserve from being generated
#[cfg_attr(feature = "inline-more", inline)]
fn equivalent_key1<Q1, K1, K2, V>(k: &Q1) -> impl Fn(&(K1, K2, V)) -> bool + '_
where
    Q1: ?Sized + Equivalent<K1>,
{
    move |x| k.equivalent(&x.0)
}

/// Ensures that a single closure type across uses of this which, in turn prevents multiple
/// instances of any functions like RawTable::reserve from being generated
#[cfg_attr(feature = "inline-more", inline)]
fn equivalent_key2<Q2, K1, K2, V>(k: &Q2) -> impl Fn(&(K1, K2, V)) -> bool + '_
where
    Q2: ?Sized + Equivalent<K2>,
{
    move |x| k.equivalent(&x.1)
}

/// Ensures that a single closure type across uses of this which, in turn prevents multiple
/// instances of any functions like RawTable::reserve from being generated
#[cfg_attr(feature = "inline-more", inline)]
fn equivalent<Q, K>(k: &Q) -> impl Fn(&K) -> bool + '_
where
    Q: ?Sized + Equivalent<K>,
{
    move |x| k.equivalent(x)
}

#[cfg(feature = "ahash")]
impl<K1, K2, V> DHashMap<K1, K2, V, DefaultHashBuilder> {
    /// Creates a new empty [`DHashMap`]s with [`DefaultHashBuilder`]
    /// type of hash builder to hash keys.
    ///
    /// The hash map is initially created with a capacity of 0, so it
    /// will not allocate until it is first inserted into.
    ///
    /// Warning: `hash_builder` normally use a fixed key by default and that does
    /// not allow the `DHashMaps` to be protected against attacks such as [`HashDoS`].
    /// Users who require HashDoS resistance should explicitly use
    /// [`ahash::RandomState`] or [`std::collections::hash_map::RandomState`]
    /// as the hasher when creating a [`DHashMap`], for example with
    /// [`with_hasher`](DHashMap::with_hasher) method.
    ///
    /// [`HashDoS`]: https://en.wikipedia.org/wiki/Collision_attack
    /// [`std::collections::hash_map::RandomState`]: https://doc.rust-lang.org/std/collections/hash_map/struct.RandomState.html
    ///
    /// # Examples
    ///
    /// ```
    /// use double_map::DHashMap;
    /// let mut map: DHashMap<u32, &str, i32> = DHashMap::new();
    ///
    /// // The created DHashMap holds none elements
    /// assert_eq!(map.len(), 0);
    ///
    /// // The created DHashMap also doesn't allocate memory
    /// assert_eq!(map.capacity(), 0);
    ///
    /// // Now we insert element inside created DHashMap
    /// map.insert(1, "One", 1);
    /// // We can see that the DHashMap holds 1 element
    /// assert_eq!(map.len(), 1);
    /// // And it also allocates some capacity
    /// assert!(map.capacity() > 1);
    /// ```
    #[cfg_attr(feature = "inline-more", inline)]
    pub fn new() -> Self {
        Self::default()
    }

    /// Creates an empty [`DHashMap`] with the specified capacity and
    /// [`DefaultHashBuilder`] type of hash builder to hash keys.
    ///
    /// The hash map will be able to hold at least `capacity` elements without
    /// reallocating. If `capacity` is 0, the hash map will not allocate.
    ///
    /// Warning: `hash_builder` normally use a fixed key by default and that does
    /// not allow the `DHashMaps` to be protected against attacks such as [`HashDoS`].
    /// Users who require HashDoS resistance should explicitly use
    /// [`ahash::RandomState`] or [`std::collections::hash_map::RandomState`]
    /// as the hasher when creating a [`DHashMap`], for example with
    /// [`with_capacity_and_hasher`](DHashMap::with_capacity_and_hasher) method.
    ///
    /// [`HashDoS`]: https://en.wikipedia.org/wiki/Collision_attack
    /// [`std::collections::hash_map::RandomState`]: https://doc.rust-lang.org/std/collections/hash_map/struct.RandomState.html
    ///
    /// # Examples
    ///
    /// ```
    /// use double_map::DHashMap;
    /// let mut map: DHashMap<&str, i32, &str> = DHashMap::with_capacity(5);
    ///
    /// // The created DHashMap holds none elements
    /// assert_eq!(map.len(), 0);
    /// // But it can hold at least 5 elements without reallocating
    /// let empty_map_capacity = map.capacity();
    /// assert!(empty_map_capacity >= 5);
    ///
    /// // Now we insert some 5 elements inside created DHashMap
    /// map.insert("One",   1, "a");
    /// map.insert("Two",   2, "b");
    /// map.insert("Three", 3, "c");
    /// map.insert("Four",  4, "d");
    /// map.insert("Five",  5, "e");
    ///
    /// // We can see that the DHashMap holds 5 elements
    /// assert_eq!(map.len(), 5);
    /// // But its capacity isn't changed
    /// assert_eq!(map.capacity(), empty_map_capacity)
    /// ```
    #[cfg_attr(feature = "inline-more", inline)]
    pub fn with_capacity(capacity: usize) -> Self {
        Self::with_capacity_and_hasher(capacity, DefaultHashBuilder::default())
    }
}

#[cfg(feature = "ahash")]
impl<K1, K2, V, A: Allocator + Clone> DHashMap<K1, K2, V, DefaultHashBuilder, A> {
    /// Creates an empty [`DHashMap`] using the given allocator. Uses
    /// [`DefaultHashBuilder`] type of hash builder to hash keys.
    ///
    /// The hash map is initially created with a capacity of 0, so it
    /// will not allocate until it is first inserted into.
    ///
    /// Warning: `hash_builder` normally use a fixed key by default and that does
    /// not allow the `DHashMaps` to be protected against attacks such as [`HashDoS`].
    /// Users who require HashDoS resistance should explicitly use
    /// [`ahash::RandomState`] or [`std::collections::hash_map::RandomState`]
    /// as the hasher when creating a [`DHashMap`], for example with
    /// [`with_hasher_in`](DHashMap::with_hasher_in) method.
    ///
    /// [`HashDoS`]: https://en.wikipedia.org/wiki/Collision_attack
    /// [`std::collections::hash_map::RandomState`]: https://doc.rust-lang.org/std/collections/hash_map/struct.RandomState.html
    ///
    /// # Examples
    ///
    /// ```
    /// # #[cfg(feature = "bumpalo")]
    /// # fn test() {
    /// use double_map::{DHashMap, BumpWrapper};
    /// use bumpalo::Bump;
    ///
    /// let bump = Bump::new();
    /// let mut map = DHashMap::new_in(BumpWrapper(&bump));
    ///
    /// // The created DHashMap holds none elements
    /// assert_eq!(map.len(), 0);
    ///
    /// // The created DHashMap also doesn't allocate memory
    /// assert_eq!(map.capacity(), 0);
    ///
    /// // Now we insert element inside created DHashMap
    /// map.insert("One", 1, "First");
    /// // We can see that the DHashMap holds 1 element
    /// assert_eq!(map.len(), 1);
    /// // And it also allocates some capacity
    /// assert!(map.capacity() > 1);
    /// # }
    /// # fn main() {
    /// #     #[cfg(feature = "bumpalo")]
    /// #     test()
    /// # }
    /// ```
    #[cfg_attr(feature = "inline-more", inline)]
    pub fn new_in(alloc: A) -> Self {
        Self::with_hasher_in(DefaultHashBuilder::default(), alloc)
    }

    /// Creates an empty [`DHashMap`] with the specified capacity and
    /// [`DefaultHashBuilder`] type of hash builder to hash keys.
    /// It will be allocated with the given allocator.
    ///
    /// The hash map will be able to hold at least `capacity` elements without
    /// reallocating. If `capacity` is 0, the hash map will not allocate.
    ///
    /// Warning: `hash_builder` normally use a fixed key by default and that does
    /// not allow the `DHashMaps` to be protected against attacks such as [`HashDoS`].
    /// Users who require HashDoS resistance should explicitly use
    /// [`ahash::RandomState`] or [`std::collections::hash_map::RandomState`]
    /// as the hasher when creating a [`DHashMap`], for example with
    /// [`with_capacity_and_hasher_in`](DHashMap::with_capacity_and_hasher_in) method.
    ///
    /// [`HashDoS`]: https://en.wikipedia.org/wiki/Collision_attack
    /// [`std::collections::hash_map::RandomState`]: https://doc.rust-lang.org/std/collections/hash_map/struct.RandomState.html
    ///
    /// # Examples
    ///
    /// ```
    /// # #[cfg(feature = "bumpalo")]
    /// # fn test() {
    /// use double_map::{DHashMap, BumpWrapper};
    /// use bumpalo::Bump;
    ///
    /// let bump = Bump::new();
    /// let mut map = DHashMap::with_capacity_in(5, BumpWrapper(&bump));
    ///
    /// // The created DHashMap holds none elements
    /// assert_eq!(map.len(), 0);
    /// // But it can hold at least 5 elements without reallocating
    /// let empty_map_capacity = map.capacity();
    /// assert!(empty_map_capacity >= 5);
    ///
    /// // Now we insert some 5 elements inside created DHashMap
    /// map.insert("One",   1, "a");
    /// map.insert("Two",   2, "b");
    /// map.insert("Three", 3, "c");
    /// map.insert("Four",  4, "d");
    /// map.insert("Five",  5, "e");
    ///
    /// // We can see that the DHashMap holds 5 elements
    /// assert_eq!(map.len(), 5);
    /// // But its capacity isn't changed
    /// assert_eq!(map.capacity(), empty_map_capacity)
    /// # }
    /// # fn main() {
    /// #     #[cfg(feature = "bumpalo")]
    /// #     test()
    /// # }
    /// ```
    #[cfg_attr(feature = "inline-more", inline)]
    pub fn with_capacity_in(capacity: usize, alloc: A) -> Self {
        Self::with_capacity_and_hasher_in(capacity, DefaultHashBuilder::default(), alloc)
    }
}

impl<K1, K2, V, S> DHashMap<K1, K2, V, S> {
    /// Creates an empty [`DHashMap`] which will use the given hash builder to hash
    /// keys.
    ///
    /// The created map has the default initial capacity, witch is equal to 0, so
    /// it will not allocate until it is first inserted into.
    ///
    /// Warning: `hash_builder` is normally use a fixed key by default and that is
    /// not allow `DHashMaps` to be protected against attacks such as [`HashDoS`].
    /// Users who require HashDoS resistance should explicitly use
    /// [`ahash::RandomState`] or [`std::collections::hash_map::RandomState`]
    /// as the hasher when creating a [`DHashMap`].
    ///
    /// The `hash_builder` passed should implement the [`BuildHasher`] trait for
    /// the [`DHashMap`] to be useful, see its documentation for details.
    ///
    /// [`HashDoS`]: https://en.wikipedia.org/wiki/Collision_attack
    /// [`std::collections::hash_map::RandomState`]: https://doc.rust-lang.org/std/collections/hash_map/struct.RandomState.html
    ///
    /// # Examples
    ///
    /// ```
    /// use double_map::DHashMap;
    /// use double_map::dhash_map::DefaultHashBuilder;
    ///
    /// let s = DefaultHashBuilder::default();
    /// let mut map = DHashMap::with_hasher(s);
    ///
    /// // The created DHashMap holds none elements
    /// assert_eq!(map.len(), 0);
    ///
    /// // The created DHashMap also doesn't allocate memory
    /// assert_eq!(map.capacity(), 0);
    ///
    /// // Now we insert elements inside created DHashMap
    /// map.insert("One", 1, 2);
    /// // We can see that the DHashMap holds 1 element
    /// assert_eq!(map.len(), 1);
    /// // And it also allocates some capacity
    /// assert!(map.capacity() > 1);
    /// ```
    #[cfg_attr(feature = "inline-more", inline)]
    pub const fn with_hasher(hash_builder: S) -> Self {
        Self {
            hash_builder,
            table: RawTable::new(),
        }
    }

    /// Creates an empty [`DHashMap`] with the specified capacity, using `hash_builder`
    /// to hash the keys.
    ///
    /// The hash map will be able to hold at least `capacity` elements without
    /// reallocating. If `capacity` is 0, the hash map will not allocate.
    ///
    /// Warning: `hash_builder` normally use a fixed key by default and that does
    /// not allow the `DHashMaps` to be protected against attacks such as [`HashDoS`].
    /// Users who require HashDoS resistance should explicitly use
    /// [`ahash::RandomState`] or [`std::collections::hash_map::RandomState`]
    /// as the hasher when creating a [`DHashMap`].
    ///
    /// The `hash_builder` passed should implement the [`BuildHasher`] trait for
    /// the [`DHashMap`] to be useful, see its documentation for details.
    ///
    /// [`HashDoS`]: https://en.wikipedia.org/wiki/Collision_attack
    /// [`std::collections::hash_map::RandomState`]: https://doc.rust-lang.org/std/collections/hash_map/struct.RandomState.html
    ///
    /// # Examples
    ///
    /// ```
    /// use double_map::DHashMap;
    /// use double_map::dhash_map::DefaultHashBuilder;
    ///
    /// let s = DefaultHashBuilder::default();
    /// let mut map = DHashMap::with_capacity_and_hasher(5, s);
    ///
    /// // The created DHashMap holds none elements
    /// assert_eq!(map.len(), 0);
    /// // But it can hold at least 5 elements without reallocating
    /// let empty_map_capacity = map.capacity();
    /// assert!(empty_map_capacity >= 5);
    ///
    /// // Now we insert some 5 elements inside the created DHashMap
    /// map.insert("One",   1, "a");
    /// map.insert("Two",   2, "b");
    /// map.insert("Three", 3, "c");
    /// map.insert("Four",  4, "d");
    /// map.insert("Five",  5, "e");
    ///
    /// // We can see that the DHashMap holds 5 elements
    /// assert_eq!(map.len(), 5);
    /// // But its capacity isn't changed
    /// assert_eq!(map.capacity(), empty_map_capacity)
    /// ```
    #[cfg_attr(feature = "inline-more", inline)]
    pub fn with_capacity_and_hasher(capacity: usize, hash_builder: S) -> Self {
        Self {
            hash_builder,
            table: RawTable::with_capacity(capacity),
        }
    }
}

impl<K1, K2, V, S, A: Allocator + Clone> DHashMap<K1, K2, V, S, A> {
    /// Returns a reference to the underlying allocator.
    ///
    /// # Examples
    ///
    /// ```
    /// # #[cfg(feature = "bumpalo")]
    /// # fn test() {
    /// use double_map::{DHashMap, BumpWrapper};
    /// use bumpalo::Bump;
    ///
    /// let bump = Bump::new();
    /// let mut map: DHashMap<i8, i8, i8, _, BumpWrapper> = DHashMap::new_in(BumpWrapper(&bump));
    ///
    /// let bumpwrap: &BumpWrapper = map.allocator();
    /// # }
    /// # fn main() {
    /// #     #[cfg(feature = "bumpalo")]
    /// #     test()
    /// # }
    /// ```
    #[inline]
    pub fn allocator(&self) -> &A {
        self.table.allocator()
    }

    /// Creates an empty [`DHashMap`] which will use the given hash builder
    /// to hash keys. It will be allocated with the given allocator.
    ///
    /// The created map has the default initial capacity, witch is equal to 0,
    /// so it will not allocate until it is first inserted into.
    ///
    /// Warning: `hash_builder` normally use a fixed key by default and that does
    /// not allow the `DHashMaps` to be protected against attacks such as [`HashDoS`].
    /// Users who require HashDoS resistance should explicitly use
    /// [`ahash::RandomState`] or [`std::collections::hash_map::RandomState`]
    /// as the hasher when creating a [`DHashMap`].
    ///
    /// [`HashDoS`]: https://en.wikipedia.org/wiki/Collision_attack
    /// [`std::collections::hash_map::RandomState`]: https://doc.rust-lang.org/std/collections/hash_map/struct.RandomState.html
    ///
    /// # Examples
    ///
    /// ```
    /// # #[cfg(feature = "bumpalo")]
    /// # fn test() {
    /// use double_map::{DHashMap, BumpWrapper};
    /// use double_map::dhash_map::DefaultHashBuilder;
    /// use bumpalo::Bump;
    ///
    /// let s = DefaultHashBuilder::default();
    /// let bump = Bump::new();
    /// let mut map = DHashMap::with_hasher_in(s, BumpWrapper(&bump));
    ///
    /// // The created DHashMap holds none elements
    /// assert_eq!(map.len(), 0);
    ///
    /// // The created DHashMap also doesn't allocate memory
    /// assert_eq!(map.capacity(), 0);
    ///
    /// // Now we insert elements inside created DHashMap
    /// map.insert("One", 1, 2);
    /// // We can see that the DHashMap holds 1 element
    /// assert_eq!(map.len(), 1);
    /// // And it also allocates some capacity
    /// assert!(map.capacity() > 1);
    /// # }
    /// # fn main() {
    /// #     #[cfg(feature = "bumpalo")]
    /// #     test()
    /// # }
    /// ```
    #[cfg_attr(feature = "inline-more", inline)]
    pub fn with_hasher_in(hash_builder: S, alloc: A) -> Self {
        Self {
            hash_builder,
            table: RawTable::new_in(alloc),
        }
    }

    /// Creates an empty [`DHashMap`] with the specified capacity, using `hash_builder`
    /// to hash the keys. It will be allocated with the given allocator.
    ///
    /// The hash map will be able to hold at least `capacity` elements without
    /// reallocating. If `capacity` is 0, the hash map will not allocate.
    ///
    /// Warning: `hash_builder` normally use a fixed key by default and that does
    /// not allow the `DHashMaps` to be protected against attacks such as [`HashDoS`].
    /// Users who require HashDoS resistance should explicitly use
    /// [`ahash::RandomState`] or [`std::collections::hash_map::RandomState`]
    /// as the hasher when creating a [`DHashMap`].
    ///
    /// [`HashDoS`]: https://en.wikipedia.org/wiki/Collision_attack
    /// [`std::collections::hash_map::RandomState`]: https://doc.rust-lang.org/std/collections/hash_map/struct.RandomState.html
    ///
    /// # Examples
    ///
    /// ```
    /// # #[cfg(feature = "bumpalo")]
    /// # fn test() {
    /// use double_map::{DHashMap, BumpWrapper};
    /// use double_map::dhash_map::DefaultHashBuilder;
    /// use bumpalo::Bump;
    ///
    /// let s = DefaultHashBuilder::default();
    /// let bump = Bump::new();
    /// let mut map = DHashMap::with_capacity_and_hasher_in(5, s, BumpWrapper(&bump));
    ///
    /// // The created DHashMap holds none elements
    /// assert_eq!(map.len(), 0);
    /// // But it can hold at least 5 elements without reallocating
    /// let empty_map_capacity = map.capacity();
    /// assert!(empty_map_capacity >= 5);
    ///
    /// // Now we insert some 5 elements inside the created DHashMap
    /// map.insert("One",   1, "a");
    /// map.insert("Two",   2, "b");
    /// map.insert("Three", 3, "c");
    /// map.insert("Four",  4, "d");
    /// map.insert("Five",  5, "e");
    ///
    /// // We can see that the DHashMap holds 5 elements
    /// assert_eq!(map.len(), 5);
    /// // But its capacity isn't changed
    /// assert_eq!(map.capacity(), empty_map_capacity)
    /// # }
    /// # fn main() {
    /// #     #[cfg(feature = "bumpalo")]
    /// #     test()
    /// # }
    /// ```
    #[cfg_attr(feature = "inline-more", inline)]
    pub fn with_capacity_and_hasher_in(capacity: usize, hash_builder: S, alloc: A) -> Self {
        Self {
            hash_builder,
            table: RawTable::with_capacity_in(capacity, alloc),
        }
    }

    /// Returns a reference to the map's [`BuildHasher`].
    ///
    /// [`BuildHasher`]: https://doc.rust-lang.org/std/hash/trait.BuildHasher.html
    ///
    /// # Examples
    ///
    /// ```
    /// use double_map::DHashMap;
    /// use double_map::dhash_map::DefaultHashBuilder;
    ///
    /// let hasher = DefaultHashBuilder::default();
    /// let map: DHashMap<i32, i32, i32> = DHashMap::with_hasher(hasher);
    /// let hasher: &DefaultHashBuilder = map.hasher();
    /// ```
    #[cfg_attr(feature = "inline-more", inline)]
    pub fn hasher(&self) -> &S {
        &self.hash_builder
    }

    /// Returns the number of elements the map can hold without reallocating.
    ///
    /// This number is a lower bound; the [`DHashMap<K1, K2, V>`] might
    /// be able to hold more, but is guaranteed to be able to hold at least
    /// this many.
    ///
    /// # Examples
    ///
    /// ```
    /// use double_map::DHashMap;
    /// let map = DHashMap::<i32, &str, &str>::with_capacity(16);
    ///
    /// // The created DHashMap can hold at least 16 elements
    /// assert!(map.capacity() >= 16);
    /// // But for now it doesn't hold any elements
    /// assert_eq!(map.len(), 0);
    /// ```
    #[cfg_attr(feature = "inline-more", inline)]
    pub fn capacity(&self) -> usize {
        self.table.capacity()
    }

    /// An iterator visiting all keys in arbitrary order.
    /// The iterator element is tuple of type `(&'a K1, &'a K2)`.
    ///
    /// # Examples
    ///
    /// ```
    /// use double_map::DHashMap;
    ///
    /// let mut map = DHashMap::new();
    /// map.insert("a", 1, "One");
    /// map.insert("b", 2, "Two");
    /// map.insert("c", 3, "Three");
    ///
    /// assert_eq!(map.len(), 3);
    ///
    /// let mut vec: Vec<(&str, i32)> = Vec::new();
    ///
    /// for (key1, key2)  in map.keys() {
    ///     println!("key1: {}, key2: {}", key1, key2);
    ///     vec.push((*key1, *key2));
    /// }
    ///
    /// // The `Keys` iterator produces keys in arbitrary order, so the
    /// // keys must be sorted to test them against a sorted array.
    /// vec.sort_unstable();
    /// assert_eq!(vec, [("a", 1), ("b", 2), ("c", 3)]);
    ///
    /// assert_eq!(map.len(), 3);
    /// ```
    #[cfg_attr(feature = "inline-more", inline)]
    pub fn keys(&self) -> Keys<'_, K1, K2, V> {
        Keys { inner: self.iter() }
    }

    /// An iterator visiting all values in arbitrary order.
    /// The iterator element type is `&'a V`.
    ///
    /// # Examples
    ///
    /// ```
    /// use double_map::DHashMap;
    ///
    /// let mut map = DHashMap::new();
    /// map.insert("a", "One", 1);
    /// map.insert("b", "Two", 2);
    /// map.insert("c", "Three", 3);
    ///
    /// assert_eq!(map.len(), 3);
    ///
    /// let mut vec: Vec<i32> = Vec::new();
    ///
    /// for value in map.values() {
    ///     println!("value = {}", value);
    ///     vec.push(*value);
    /// }
    ///
    /// // The `Values` iterator produces values in arbitrary order, so the
    /// // values must be sorted to test them against a sorted array.
    /// vec.sort_unstable();
    /// assert_eq!(vec, [1, 2, 3]);
    ///
    /// assert_eq!(map.len(), 3);
    /// ```
    #[cfg_attr(feature = "inline-more", inline)]
    pub fn values(&self) -> Values<'_, K1, K2, V> {
        Values { inner: self.iter() }
    }

    /// An iterator visiting all values mutably in arbitrary order.
    /// The iterator element type is `&'a mut V`.
    ///
    /// # Examples
    ///
    /// ```
    /// use double_map::DHashMap;
    ///
    /// let mut map = DHashMap::new();
    ///
    /// map.insert("a", "One",   1);
    /// map.insert("b", "Two",   2);
    /// map.insert("c", "Three", 3);
    ///
    /// assert_eq!(map.len(), 3);
    ///
    /// for value in map.values_mut() {
    ///     *value = *value + 10;
    /// }
    ///
    /// let mut vec: Vec<i32> = Vec::new();
    ///
    /// for val in map.values() {
    ///     println!("{}", val);
    ///     vec.push(*val);
    /// }
    ///
    /// // The `Values` iterator produces values in arbitrary order, so the
    /// // values must be sorted to test them against a sorted array.
    /// vec.sort_unstable();
    /// assert_eq!(vec, [11, 12, 13]);
    ///
    /// assert_eq!(map.len(), 3);
    /// ```
    #[cfg_attr(feature = "inline-more", inline)]
    pub fn values_mut(&mut self) -> ValuesMut<'_, K1, K2, V> {
        ValuesMut {
            inner: self.iter_mut(),
        }
    }

    /// An iterator visiting all keys-value tuples in arbitrary order.
    /// The iterator element is tuple of type `(&'a K1, &'a K2, &'a V)`.
    ///
    /// # Examples
    ///
    /// ```
    /// use double_map::DHashMap;
    ///
    /// let mut map = DHashMap::new();
    /// map.insert("a", 1, "One");
    /// map.insert("b", 2, "Two");
    /// map.insert("c", 3, "Three");
    ///
    /// assert_eq!(map.len(), 3);
    ///
    /// let mut vec: Vec<(&str, i32, &str)> = Vec::new();
    ///
    /// for (key1, key2, value) in map.iter() {
    ///     println!("key1: {}, key2: {}, value: {}", key1, key2, value);
    ///     vec.push((*key1, *key2, *value));
    /// }
    ///
    /// // The `Iter` iterator produces items in arbitrary order, so the
    /// // items must be sorted to test them against a sorted array.
    /// vec.sort_unstable();
    /// assert_eq!(vec, [("a", 1, "One"), ("b", 2, "Two"), ("c", 3, "Three")]);
    ///
    /// assert_eq!(map.len(), 3);
    /// ```
    #[cfg_attr(feature = "inline-more", inline)]
    pub fn iter(&self) -> Iter<'_, K1, K2, V> {
        // Here we tie the lifetime of self to the iter.
        unsafe {
            Iter {
                inner: self.table.iter(),
                marker: PhantomData,
            }
        }
    }

    /// An iterator visiting all keys-value tuples in arbitrary order,
    /// with mutable references to the values.
    /// The iterator element is tuple of type`(&'a K1, &'a K2, &'a mut V)`.
    ///
    /// # Examples
    ///
    /// ```
    /// use double_map::DHashMap;
    ///
    /// let mut map = DHashMap::new();
    /// map.insert("a", 10, 1);
    /// map.insert("b", 20, 2);
    /// map.insert("c", 30, 3);
    ///
    /// assert_eq!(map.len(), 3);
    ///
    /// // Update all values
    /// for (_, _, value) in map.iter_mut() {
    ///     *value *= 2;
    /// }
    ///
    /// let mut vec: Vec<(&str, i32, i32)> = Vec::new();
    ///
    /// for (key1, key2, value) in map.iter() {
    ///     println!("key1: {}, key2: {}, value: {}", key1, key2, value);
    ///     vec.push((*key1, *key2, *value));
    /// }
    ///
    ///
    /// // The `Iter` iterator produces items in arbitrary order, so the
    /// // items must be sorted to test them against a sorted array.
    /// vec.sort_unstable();
    /// assert_eq!(vec, [("a", 10, 2), ("b", 20, 4), ("c", 30, 6)]);
    ///
    /// assert_eq!(map.len(), 3);
    /// ```
    #[cfg_attr(feature = "inline-more", inline)]
    pub fn iter_mut(&mut self) -> IterMut<'_, K1, K2, V> {
        // Here we tie the lifetime of self to the iter.
        unsafe {
            IterMut {
                inner: self.table.iter(),
                marker: PhantomData,
            }
        }
    }

    #[cfg(test)]
    #[cfg_attr(feature = "inline-more", inline)]
    fn raw_capacity(&self) -> usize {
        self.table.buckets()
    }

    /// Returns the number of elements in the map.
    ///
    /// # Examples
    ///
    /// ```
    /// use double_map::{DHashMap, dhashmap};
    ///
    /// let mut a = DHashMap::new();
    /// // The created DHashMap doesn't hold any elements
    /// assert_eq!(a.len(), 0);
    /// // We insert one element
    /// a.insert(1, "Breakfast", "Pancakes");
    /// // And can be sure that DHashMap holds one element
    /// assert_eq!(a.len(), 1);
    ///
    /// let map = dhashmap![
    ///    1, "Breakfast" => "Pancakes",
    ///    2, "Lunch" => "Sandwich",
    /// ];
    /// assert_eq!(map.len(), 2);
    /// ```
    #[cfg_attr(feature = "inline-more", inline)]
    pub fn len(&self) -> usize {
        self.table.len()
    }

    /// Returns `true` if the map contains no elements.
    ///
    /// # Examples
    ///
    /// ```
    /// use double_map::DHashMap;
    ///
    /// let mut a = DHashMap::new();
    /// // The created DHashMap doesn't hold any elements, so it's empty
    /// assert!(a.is_empty() && a.len() == 0);
    /// // We insert one element
    /// a.insert(1, "a", "One");
    /// // And can be sure that DHashMap is not empty but holds one element
    /// assert!(!a.is_empty() && a.len() == 1);
    /// ```
    #[cfg_attr(feature = "inline-more", inline)]
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Clears the map, returning all keys-value tuples as an arbitrary
    /// order iterator. The iterator element is tuple of type `(K1, K2, V)`.
    /// Keeps the allocated memory for reuse.
    ///
    /// If the returned iterator is dropped before being fully consumed, it
    /// drops the remaining key-value pairs. The returned iterator keeps a
    /// mutable borrow on the vector to optimize its implementation.
    ///
    /// # Examples
    ///
    /// ```
    /// use double_map::DHashMap;
    ///
    /// // We insert three elements
    /// let mut a = DHashMap::new();
    /// a.insert("apple",  1, "a");
    /// a.insert("banana", 2, "b");
    /// a.insert("Cherry", 3, "c");
    ///
    /// // We can see that DHashMap hold three elements
    /// assert_eq!(a.len(), 3);
    ///
    /// // Also we reserve memory for holding additionally at least 20 elements,
    /// // so that DHashMap can now hold 23 elements or more
    /// a.reserve(20);
    /// let capacity_before_drain = a.capacity();
    ///
    /// for (key1, key2, value) in a.drain() {
    ///     println!{"key1: {}, key2: {}, value: {}", key1, key2, value}
    ///     assert!(
    ///         (key1, key2, value)  == ("apple",  1, "a") ||
    ///         (key1, key2, value)  == ("banana", 2, "b") ||
    ///         (key1, key2, value)  == ("Cherry", 3, "c")
    ///     );
    /// }
    ///
    /// // As we can see, the map is empty and contain no element
    /// assert!(a.is_empty() && a.len() == 0);
    /// // But map capacity is equal to old one.
    /// assert!(a.capacity() == capacity_before_drain);
    ///
    /// let mut a = DHashMap::new();
    /// a.insert(1, "a", "One");
    /// a.insert(2, "b", "Two");
    ///
    /// {   // Iterator is dropped without being consumed.
    ///     let d = a.drain();
    /// }
    ///
    /// // But the map is empty even if we do not use Drain iterator.
    /// assert!(a.is_empty());
    /// ```
    #[cfg_attr(feature = "inline-more", inline)]
    pub fn drain(&mut self) -> Drain<'_, K1, K2, V, A> {
        Drain {
            inner: self.table.drain(),
        }
    }

    /// Retains only the elements specified by the predicate. Keeps the
    /// allocated memory for reuse.
    ///
    /// In other words, remove all pairs `(K1, K2, V)` such that
    /// `f(&K1, &mut V)` returns `false`. The elements are visited in
    /// unsorted (and unspecified) order.
    ///
    /// # Examples
    ///
    /// ```
    /// use double_map::DHashMap;
    ///
    /// let mut map: DHashMap<i32, i32, i32> = (0..8).map(|x| (x, x + 1, x * 100)).collect();
    /// assert_eq!(map.len(), 8);
    ///
    /// map.retain_key1(|&k1, _| k1 % 2 == 0);
    ///
    /// // We can see, that the number of elements inside map is changed.
    /// assert_eq!(map.len(), 4);
    ///
    /// let mut vec: Vec<(i32, i32, i32)> = map.iter().map(|(&k1, &k2, &v)| (k1, k2, v)).collect();
    /// vec.sort_unstable();
    /// assert_eq!(vec, [(0, 1, 0), (2, 3, 200), (4, 5, 400), (6, 7, 600)]);
    /// ```
    pub fn retain_key1<F>(&mut self, mut f: F)
    where
        F: FnMut(&K1, &mut V) -> bool,
    {
        // Here we only use `pointers_iter` as a temporary, preventing use-after-free
        unsafe {
            for item in self.table.pointers_iter() {
                let &mut (ref key1, _, ref mut value) = item.as_data_mut();
                if !f(key1, value) {
                    self.table.erase(item);
                }
            }
        }
    }

    /// Retains only the elements specified by the predicate. Keeps the
    /// allocated memory for reuse.
    ///
    /// In other words, remove all pairs `(K1, K2, V)` such that
    /// `f(&K2, &mut V)` returns `false`. The elements are visited in
    /// unsorted (and unspecified) order.
    ///
    /// # Examples
    ///
    /// ```
    /// use double_map::DHashMap;
    ///
    /// let mut map: DHashMap<i32, i32, i32> = (0..8).map(|x| (x, x + 1, x * 100)).collect();
    /// assert_eq!(map.len(), 8);
    ///
    /// map.retain_key2(|&k2, _| k2 % 2 == 0);
    ///
    /// // We can see, that the number of elements inside map is changed.
    /// assert_eq!(map.len(), 4);
    ///
    /// let mut vec: Vec<(i32, i32, i32)> = map.iter().map(|(&k1, &k2, &v)| (k1, k2, v)).collect();
    /// vec.sort_unstable();
    /// assert_eq!(vec, [(1, 2, 100), (3, 4, 300), (5, 6, 500), (7, 8, 700)]);
    /// ```
    pub fn retain_key2<F>(&mut self, mut f: F)
    where
        F: FnMut(&K2, &mut V) -> bool,
    {
        // Here we only use `pointers_iter` as a temporary, preventing use-after-free
        unsafe {
            for item in self.table.pointers_iter() {
                let &mut (_, ref key2, ref mut value) = item.as_data_mut();
                if !f(key2, value) {
                    self.table.erase(item);
                }
            }
        }
    }

    /// Retains only the elements specified by the predicate. Keeps the
    /// allocated memory for reuse.
    ///
    /// In other words, remove all pairs `(K1, K2, V)` such that
    /// `f(&K1, &K2, &mut V)` returns `false`. The elements are visited in
    /// unsorted (and unspecified) order.
    ///
    /// # Examples
    ///
    /// ```
    /// use double_map::DHashMap;
    ///
    /// let mut map: DHashMap<i32, i32, i32> = (0..12).map(|x| (x, x + 1, x * 100)).collect();
    /// assert_eq!(map.len(), 12);
    ///
    /// map.retain_keys(|&k1, &k2, _| (k1 % 3 == 0) && (k2 % 3 == 1));
    ///
    /// // We can see, that the number of elements inside map is changed.
    /// assert_eq!(map.len(), 4);
    ///
    /// let mut vec: Vec<(i32, i32, i32)> = map.iter().map(|(&k1, &k2, &v)| (k1, k2, v)).collect();
    /// vec.sort_unstable();
    /// assert_eq!(vec, [(0, 1, 0), (3, 4, 300), (6, 7, 600), (9, 10, 900)]);
    /// ```
    pub fn retain_keys<F>(&mut self, mut f: F)
    where
        F: FnMut(&K1, &K2, &mut V) -> bool,
    {
        // Here we only use `pointers_iter` as a temporary, preventing use-after-free
        unsafe {
            for item in self.table.pointers_iter() {
                let &mut (ref key1, ref key2, ref mut value) = item.as_data_mut();
                if !f(key1, key2, value) {
                    self.table.erase(item);
                }
            }
        }
    }

    /// Drains elements which are true under the given predicate,
    /// and returns an iterator over the removed items.
    ///
    /// In other words, move all pairs `(K1, K2, V)` such that
    /// `f(&K1, &K2, &mut V)` returns `true` out into another iterator.
    ///
    /// Note that `drain_filter` lets you mutate every value in the filter
    /// closure, regardless of whether you choose to keep or remove it.
    ///
    /// When the returned DrainedFilter is dropped, any remaining elements that
    /// satisfy the predicate are dropped from the table.
    ///
    /// It is unspecified how many more elements will be subjected to the closure
    /// if a panic occurs in the closure, or a panic occurs while dropping an
    /// element, or if the `DrainFilter` value is leaked.
    ///
    /// Keeps the allocated memory for reuse.
    ///
    /// # Examples
    ///
    /// ```
    /// use double_map::DHashMap;
    ///
    /// let mut map: DHashMap<i32, i32, i32> = (0..8).map(|x| (x, x, x)).collect();
    /// assert_eq!(map.len(), 8);
    ///
    /// let drained: DHashMap<i32, i32, i32> = map
    ///     .drain_filter(|&k1, &k2, _| (k1 % 3 == 0) && (k2 % 3 == 0))
    ///     .collect();
    ///
    /// let mut first: Vec<_> = map.keys().map(|(&k1, &k2)| (k1, k2)).collect();
    /// let mut second: Vec<_> = drained.keys().map(|(&k1, &k2)| (k1, k2)).collect();
    /// first.sort_unstable();
    /// second.sort_unstable();
    /// assert_eq!(first, vec![(1, 1), (2, 2), (4, 4), (5, 5), (7, 7)]);
    /// assert_eq!(second, vec![(0, 0), (3, 3), (6, 6)]);
    ///
    /// let mut map: DHashMap<i32, i32, i32> = (0..8).map(|x| (x, x + 1, x)).collect();
    /// assert_eq!(map.len(), 8);
    ///
    /// {
    ///     // Iterator is dropped without being consumed.
    ///     let _d = map.drain_filter(|k1, _, _| k1 % 2 != 0);
    /// }
    ///
    /// // But the map lens have been reduced by half
    /// // even if we do not use DrainFilter iterator.
    /// assert_eq!(map.len(), 4);
    /// ```
    #[cfg_attr(feature = "inline-more", inline)]
    pub fn drain_filter<F>(&mut self, f: F) -> DrainFilter<'_, K1, K2, V, F, A>
    where
        F: FnMut(&K1, &K2, &mut V) -> bool,
    {
        DrainFilter {
            f,
            inner: DrainFilterInner {
                iter: unsafe { self.table.pointers_iter() },
                table: &mut self.table,
            },
        }
    }

    /// Clears the map, removing all keys-value tuples.
    /// Keeps the allocated memory for reuse.
    ///
    /// # Examples
    ///
    /// ```
    /// use double_map::{DHashMap, dhashmap};
    ///
    /// let mut a = dhashmap![
    ///    1, "Breakfast" => "Pancakes",
    ///    2, "Lunch" => "Sandwich",
    /// ];
    ///
    /// // We can that see DHashMap holds two elements
    /// assert_eq!(a.len(), 2);
    /// let capacity_before_clearing = a.capacity();
    ///
    /// a.clear();
    ///
    /// // And now the map is empty and contains no elements
    /// assert!(a.is_empty() && a.len() == 0);
    /// // But map capacity is equal to the old one
    /// assert_eq!(a.capacity(), capacity_before_clearing);
    /// ```
    #[cfg_attr(feature = "inline-more", inline)]
    pub fn clear(&mut self) {
        self.table.clear();
    }

    /// Creates a consuming iterator visiting all the keys in arbitrary order.
    /// The map cannot be used after calling this. The iterator element is tuple
    /// of type `(K1, K2)`.
    ///
    /// # Examples
    ///
    /// ```
    /// use double_map::{DHashMap, dhashmap};
    ///
    /// let map = dhashmap![
    ///     ("a", 1) => "One",
    ///     ("b", 2) => "Two",
    ///     ("c", 3) => "Three",
    /// ];
    ///
    /// let mut vec: Vec<(&str, i32)> = map.into_keys().collect();
    ///
    /// // The `IntoKeys` iterator produces keys in arbitrary order, so the
    /// // keys must be sorted to test them against a sorted array.
    /// vec.sort_unstable();
    /// assert_eq!(vec, [("a", 1), ("b", 2), ("c", 3)]);
    /// ```
    #[inline]
    pub fn into_keys(self) -> IntoKeys<K1, K2, V, A> {
        IntoKeys {
            inner: self.into_iter(),
        }
    }

    /// Creates a consuming iterator visiting all the values in arbitrary order.
    /// The map cannot be used after calling this. The iterator element type is `V`.
    ///
    /// # Examples
    ///
    /// ```
    /// use double_map::{DHashMap, dhashmap};
    ///
    /// let map = dhashmap![
    ///     ("a", 1) => 10,
    ///     ("b", 2) => 20,
    ///     ("c", 3) => 30,
    /// ];
    ///
    /// let mut vec: Vec<i32> = map.into_values().collect();
    ///
    /// // The `IntoValues` iterator produces values in arbitrary order, so
    /// // the values must be sorted to test them against a sorted array.
    /// vec.sort_unstable();
    /// assert_eq!(vec, [10, 20, 30]);
    /// ```
    #[inline]
    pub fn into_values(self) -> IntoValues<K1, K2, V, A> {
        IntoValues {
            inner: self.into_iter(),
        }
    }
}

impl<K1, K2, V, S, A> DHashMap<K1, K2, V, S, A>
where
    K1: Eq + Hash,
    K2: Eq + Hash,
    S: BuildHasher,
    A: Allocator + Clone,
{
    /// Reserves capacity for at least `additional` more elements to be inserted
    /// in the `DHashMap<K1, K2, V>`. The collection may reserve more space to avoid
    /// frequent reallocations.
    ///
    /// # Panics
    ///
    /// Panics if the new allocation size overflows `isize::Max`.
    ///
    /// # Examples
    ///
    /// ```
    /// use double_map::DHashMap;
    /// let mut a = DHashMap::<&str, i128, &str>::new();
    /// a.insert("apple",  1, "a");
    /// a.insert("banana", 2, "b");
    /// a.insert("cherry", 3, "c");
    ///
    /// // We reserve space for additional 10 elements
    /// a.reserve(10);
    /// // And can see that created DHashMap can hold at least 13 elements
    /// assert!(a.capacity() >= 13);
    /// ```
    #[cfg_attr(feature = "inline-more", inline)]
    pub fn reserve(&mut self, additional: usize) {
        self.table.reserve(
            additional,
            make_hasher_key1::<_, K2, V, S>(&self.hash_builder),
            make_hasher_key2::<K1, _, V, S>(&self.hash_builder),
        );
    }

    /// Tries to reserve capacity for at least `additional` more elements to be inserted
    /// in the given `DHashMap<K1, K2, V>`. The collection may reserve more space to avoid
    /// frequent reallocations.
    ///
    /// # Errors
    ///
    /// If the capacity overflows, or the allocator reports a failure, then an error
    /// is returned.
    ///
    /// # Examples
    ///
    /// ```
    /// use double_map::DHashMap;
    ///
    /// let mut map: DHashMap<&str, isize, isize> = DHashMap::new();
    /// // Map is empty and doesn't allocate memory
    /// assert_eq!(map.capacity(), 0);
    ///
    /// map.try_reserve(10).expect("why is the test harness OOMing on 10 elements?");
    ///
    /// // And now map can hold at least 10 elements
    /// assert!(map.capacity() >= 10);
    /// ```
    /// If the capacity overflows, or the allocator reports a failure, then an error
    /// is returned:
    /// ```
    /// # fn test() {
    /// use double_map::DHashMap;
    /// use double_map::TryReserveError;
    /// let mut map: DHashMap<i32, i32, i32> = DHashMap::new();
    ///
    /// match map.try_reserve(isize::MAX as usize) {
    ///     Err(error) => match error {
    ///         TryReserveError::CapacityOverflow => {}
    ///         _ => panic!("TryReserveError::AllocError ?"),
    ///     },
    ///     _ => panic!(),
    /// }
    /// # }
    /// # fn main() {
    /// #     #[cfg(not(miri))]
    /// #     test()
    /// # }
    /// ```
    #[cfg_attr(feature = "inline-more", inline)]
    pub fn try_reserve(&mut self, additional: usize) -> Result<(), TryReserveError> {
        self.table.try_reserve(
            additional,
            make_hasher_key1::<_, K2, V, S>(&self.hash_builder),
            make_hasher_key2::<K1, _, V, S>(&self.hash_builder),
        )
    }

    /// Shrinks the capacity of the map as much as possible. It will drop
    /// down as much as possible while maintaining the internal rules
    /// and possibly leaving some space in accordance with the resize policy.
    ///
    /// Note that in general case the capacity is not *guaranteed* to shrink,
    /// but a zero-length DHashMap should generally shrink to capacity zero.
    ///
    /// # Examples
    ///
    /// ```
    /// use double_map::DHashMap;
    /// let mut a = DHashMap::<i32, &str, &str>::with_capacity(16);
    ///
    /// // This DHashMap can hold at least 16 elements
    /// let capacity_before_shrink = a.capacity();
    /// assert!(capacity_before_shrink >= 16);
    ///
    /// // And after shrinking, map capacity is less than before
    /// a.shrink_to_fit();
    /// assert!(a.capacity() < capacity_before_shrink);
    ///
    /// // If we reserve some memory and insert some elements
    /// a.reserve(10);
    /// a.insert(1, "a", "One");
    /// a.insert(2, "b", "Two");
    /// assert!(a.capacity() >= 10);
    ///
    /// // After applying shrink_to_fit method, the capacity less than
    /// // reserved before, but inserted elements are still inside map
    /// a.shrink_to_fit();
    /// assert!(a.capacity() >= 2 && a.capacity() < 10);
    /// assert_eq!(a.get_key1(&1), Some(&"One"));
    /// assert_eq!(a.get_key1(&2), Some(&"Two"))
    /// ```
    #[cfg_attr(feature = "inline-more", inline)]
    pub fn shrink_to_fit(&mut self) {
        self.table.shrink_to(
            0,
            make_hasher_key1::<_, K2, V, S>(&self.hash_builder),
            make_hasher_key2::<K1, _, V, S>(&self.hash_builder),
        );
    }

    /// Shrinks the capacity of the map with a lower limit. It will drop
    /// down no lower than the supplied limit while maintaining the internal rules
    /// and possibly leaving some space in accordance with the resize policy.
    ///
    /// If the current capacity is less than the lower limit, this is a no-op.
    ///
    /// # Examples
    ///
    /// ```
    /// use double_map::DHashMap;
    ///
    /// let mut map: DHashMap<i32, i32, i32> = DHashMap::with_capacity(100);
    /// map.insert(1, 2, 3);
    /// map.insert(4, 5, 6);
    /// map.insert(7, 8, 9);
    /// assert!(map.capacity() >= 100);
    ///
    /// // We have only 3 elements inside map, so it works
    /// map.shrink_to(10);
    /// assert!(map.capacity() >= 10 && map.capacity() < 100);
    ///
    /// // If we try shrink_to the capacity, that less than elements quantity inside map
    /// map.shrink_to(0);
    /// // So it works partially, but the resulting capacity is not less than quantity
    /// // of elements inside the map
    /// assert!(map.capacity() >= 3  && map.capacity() < 10);
    /// ```
    #[cfg_attr(feature = "inline-more", inline)]
    pub fn shrink_to(&mut self, min_capacity: usize) {
        self.table.shrink_to(
            min_capacity,
            make_hasher_key1::<_, K2, V, S>(&self.hash_builder),
            make_hasher_key2::<K1, _, V, S>(&self.hash_builder),
        );
    }

    /// Tries to get the given keys' corresponding entry in the map for in-place
    /// manipulation.
    ///
    /// Returns [`Entry`] enum if `all` of the following is `true`:
    /// - Both `K1` and `K2` keys are vacant.
    /// - If both `K1` and `K2` keys exist, they refer to the same value.
    ///
    /// When the above statements are `false`, [`entry`](DHashMap::entry) method returns
    /// [`EntryError`] structure which contains the [`ErrorKind`] enum, and the values
    /// of provided keys that were not used for creation entry (but can be used for
    /// another purpose).
    ///
    /// Depending on the points below, different [`ErrorKind`] variants may be returned:
    /// - When `K1` key is vacant, but `K2` key already exists with some value, the
    /// returned [`ErrorKind`] variant is [`ErrorKind::VacantK1AndOccupiedK2`].
    /// - When `K1` key already exists with some value, but `K2` key is vacant, the
    /// returned [`ErrorKind`] variant is [`ErrorKind::OccupiedK1AndVacantK2`].
    /// - When both `K1` key and `K2` key already exist with some values, but point
    /// to different entries (values) the returned [`ErrorKind`] variant is
    /// [`ErrorKind::KeysPointsToDiffEntries`].
    ///
    /// # Examples
    ///
    /// ```
    /// use double_map::DHashMap;
    /// use double_map::dhash_map::ErrorKind;
    ///
    /// let mut letters = DHashMap::new();
    ///
    /// for ch in "a short treatise on fungi".chars() {
    ///     if let Ok(entry) = letters.entry(ch.clone(), ch) {
    ///         let counter = entry.or_insert(0);
    ///         *counter += 1;
    ///     }
    /// }
    ///
    /// assert_eq!(letters.get_key1(&'s'), Some(&2));
    /// assert_eq!(letters.get_key1(&'t'), Some(&3));
    /// assert_eq!(letters.get_key1(&'u'), Some(&1));
    /// assert_eq!(letters.get_key1(&'y'), None);
    ///
    /// // Return `ErrorKind::OccupiedK1AndVacantK2` if `K1` key already
    /// // exists with some value, but `K2` key is vacant.
    /// let error_kind = letters.entry('s', 'y').unwrap_err().error;
    /// assert_eq!(error_kind, ErrorKind::OccupiedK1AndVacantK2);
    ///
    /// // Return `ErrorKind::VacantK1AndOccupiedK2` if `K1` key is vacant,
    /// // but `K2` key already exists with some value.
    /// let error_kind = letters.entry('y', 's').unwrap_err().error;
    /// assert_eq!(error_kind, ErrorKind::VacantK1AndOccupiedK2);
    ///
    /// // Return `ErrorKind::KeysPointsToDiffEntries` if both
    /// // `K1` key and `K2` key already exist with some values,
    /// // but point to different entries (values).
    /// let error_kind = letters.entry('s', 't').unwrap_err().error;
    /// assert_eq!(error_kind, ErrorKind::KeysPointsToDiffEntries);
    /// ```
    #[cfg_attr(feature = "inline-more", inline)]
    pub fn entry(
        &mut self,
        k1: K1,
        k2: K2,
    ) -> Result<Entry<'_, K1, K2, V, S, A>, EntryError<K1, K2>> {
        let hash_builder = &self.hash_builder;
        let hash1 = make_insert_hash::<K1, S>(hash_builder, &k1);
        let hash2 = make_insert_hash::<K2, S>(hash_builder, &k2);
        let table = &mut self.table;

        match table.find_h1(hash1, equivalent_key1(&k1)) {
            None => match table.find_h2(hash2, equivalent_key2(&k2)) {
                None => Ok(Entry::Vacant(VacantEntry {
                    hash1,
                    key1: k1,
                    hash2,
                    key2: k2,
                    table: self,
                })),
                // Error: Vacant key #1 of type K1 and occupied key # 2 of type K2
                Some(_) => Err(EntryError {
                    error: ErrorKind::VacantK1AndOccupiedK2,
                    keys: (k1, k2),
                }),
            },

            Some(data_bucket) => match table.find_h2(hash2, equivalent_key2(&k2)) {
                Some(pointer_bucket) => {
                    if unsafe { ptr::eq(data_bucket.as_ptr(), pointer_bucket.as_data_ptr()) } {
                        Ok(Entry::Occupied(OccupiedEntry {
                            hash1,
                            key1: Some(k1),
                            hash2,
                            key2: Some(k2),
                            data_bucket,
                            pointer_bucket,
                            table: self,
                        }))
                    } else {
                        // Error: key #1 and key # 2 refer to different entries / values
                        Err(EntryError {
                            error: ErrorKind::KeysPointsToDiffEntries,
                            keys: (k1, k2),
                        })
                    }
                }

                None => Err(EntryError {
                    error: ErrorKind::OccupiedK1AndVacantK2,
                    keys: (k1, k2),
                }),
            },
        }
    }

    /// Tries to get the given keys' corresponding entry by references in the map for
    /// in-place manipulation.
    ///
    /// Returns [`EntryRef`] enum if `all` of the following is `true`:
    /// - Both `K1` and `K2` keys are vacant.
    /// - If both `K1` and `K2` keys exist, they refer to the same value.
    ///
    /// When the above statements are `false`, [`entry_ref`](DHashMap::entry_ref) method
    /// returns [`ErrorKind`] enum.
    ///
    /// Depending on the points below, different [`ErrorKind`] variants may be returned:
    /// - When `K1` key is vacant, but `K2` key already exists with some value, the
    /// returned [`ErrorKind`] variant is [`ErrorKind::VacantK1AndOccupiedK2`].
    /// - When `K1` key already exists with some value, but `K2` key is vacant, the
    /// returned [`ErrorKind`] variant is [`ErrorKind::OccupiedK1AndVacantK2`].
    /// - When both `K1` key and `K2` key already exist with some values, but point
    /// to different entries (values) the returned [`ErrorKind`] variant is
    /// [`ErrorKind::KeysPointsToDiffEntries`].
    ///
    /// # Examples
    ///
    /// ```
    /// use double_map::DHashMap;
    /// use double_map::dhash_map::ErrorKind;
    ///
    /// let mut letters: DHashMap<String, String, usize>  = DHashMap::new();
    ///
    /// let source = ["zebra", "horse", "zebra", "zebra"];
    ///
    /// for (i, &s) in source.iter().enumerate() {
    ///     if let Ok(entry) = letters.entry_ref(s, s) {
    ///         let counter = entry.or_insert(0);
    ///         *counter += 1;
    ///     }
    /// }
    ///
    /// assert_eq!(letters.get_key1("zebra"), Some(&3));
    /// assert_eq!(letters.get_key1("horse"), Some(&1));
    /// assert_eq!(letters.get_key2("zebra"), Some(&3));
    /// assert_eq!(letters.get_key2("horse"), Some(&1));
    ///
    /// // Return `ErrorKind::OccupiedK1AndVacantK2` if `K1` key already
    /// // exists with some value, but `K2` key is vacant.
    /// let error_kind = letters.entry_ref("zebra", "pony").unwrap_err();
    /// assert_eq!(error_kind, ErrorKind::OccupiedK1AndVacantK2);
    ///
    /// // Return `ErrorKind::VacantK1AndOccupiedK2` if `K1` key is vacant,
    /// // but `K2` key already exists with some value.
    /// let error_kind = letters.entry_ref("pony", "horse").unwrap_err();
    /// assert_eq!(error_kind, ErrorKind::VacantK1AndOccupiedK2);
    ///
    /// // Return `ErrorKind::KeysPointsToDiffEntries` if both
    /// // `K1` key and `K2` key already exist with some values,
    /// // but point to different entries (values).
    /// let error_kind = letters.entry_ref("zebra", "horse").unwrap_err();
    /// assert_eq!(error_kind, ErrorKind::KeysPointsToDiffEntries);
    /// ```
    #[cfg_attr(feature = "inline-more", inline)]
    pub fn entry_ref<'a, 'b, Q1, Q2>(
        &'a mut self,
        k1: &'b Q1,
        k2: &'b Q2,
    ) -> Result<EntryRef<'a, 'b, K1, Q1, K2, Q2, V, S, A>, ErrorKind>
    where
        Q1: ?Sized + Hash + Equivalent<K1>,
        Q2: ?Sized + Hash + Equivalent<K2>,
    {
        let hash_builder = &self.hash_builder;
        let hash1 = make_hash::<Q1, S>(hash_builder, k1);
        let hash2 = make_hash::<Q2, S>(hash_builder, k2);
        let table = &mut self.table;

        match table.find_h1(hash1, equivalent_key1(k1)) {
            None => match table.find_h2(hash2, equivalent_key2(k2)) {
                None => Ok(EntryRef::Vacant(VacantEntryRef {
                    hash1,
                    key1: KeyOrRef::Borrowed(k1),
                    hash2,
                    key2: KeyOrRef::Borrowed(k2),
                    table: self,
                })),

                // Error: Vacant key #1 of type K1 and occupied key # 2 of type K2
                Some(_) => Err(ErrorKind::VacantK1AndOccupiedK2),
            },

            Some(data_bucket) => match table.find_h2(hash2, equivalent_key2(k2)) {
                Some(pointer_bucket) => {
                    if unsafe { ptr::eq(data_bucket.as_ptr(), pointer_bucket.as_data_ptr()) } {
                        Ok(EntryRef::Occupied(OccupiedEntryRef {
                            hash1,
                            key1: Some(KeyOrRef::Borrowed(k1)),
                            hash2,
                            key2: Some(KeyOrRef::Borrowed(k2)),
                            data_bucket,
                            pointer_bucket,
                            table: self,
                        }))
                    } else {
                        // Error: key #1 and key # 2 refer to different entries / values
                        Err(ErrorKind::KeysPointsToDiffEntries)
                    }
                }

                None => Err(ErrorKind::OccupiedK1AndVacantK2),
            },
        }
    }

    /// Returns a reference to the value corresponding to the given
    /// first key `K1`.
    ///
    /// The key may be any borrowed form of the map's key type, but
    /// [`Hash`] and [`Eq`] on the borrowed form *must* match those for
    /// the key type.
    ///
    /// # Examples
    ///
    /// ```
    /// use double_map::DHashMap;
    ///
    /// let mut map = DHashMap::new();
    /// map.insert(1, "a", "One");
    /// assert_eq!(map.get_key1(&1), Some(&"One"));
    /// assert_eq!(map.get_key1(&2), None);
    /// ```
    #[inline]
    pub fn get_key1<Q1: ?Sized>(&self, k1: &Q1) -> Option<&V>
    where
        Q1: Hash + Equivalent<K1>,
    {
        // Avoid `Option::map` because it bloats LLVM IR.
        match self.get_inner_key1(k1) {
            Some(&(_, _, ref v)) => Some(v),
            None => None,
        }
    }

    /// Returns a reference to the value corresponding to the given
    /// second key `K2`.
    ///
    /// The key may be any borrowed form of the map's key type, but
    /// [`Hash`] and [`Eq`] on the borrowed form *must* match those for
    /// the key type.
    ///
    /// # Examples
    ///
    /// ```
    /// use double_map::DHashMap;
    ///
    /// let mut map = DHashMap::new();
    /// map.insert(1, "a", "One");
    /// assert_eq!(map.get_key2(&"a"), Some(&"One"));
    /// assert_eq!(map.get_key2(&"b"), None);
    /// ```
    #[inline]
    pub fn get_key2<Q2: ?Sized>(&self, k2: &Q2) -> Option<&V>
    where
        Q2: Hash + Equivalent<K2>,
    {
        // Avoid `Option::map` because it bloats LLVM IR.
        match self.get_inner_key2(k2) {
            Some(&(_, _, ref v)) => Some(v),
            None => None,
        }
    }

    /// Returns a reference to the value corresponding to the given
    /// first `K1` and second `K2` keys if they both exist and refer
    /// to the same value.
    ///
    /// The keys may be any borrowed form of the map's keys type, but
    /// [`Hash`] and [`Eq`] on the borrowed form *must* match those for
    /// the keys type.
    ///
    /// # Note
    ///
    /// Note that this [`get_keys`](DHashMap::get_keys) method return
    /// a reference to the value only if two keys exist and refer to
    /// the same `value`.
    ///
    /// # Examples
    ///
    /// ```
    /// use double_map::{DHashMap, dhashmap};
    ///
    /// let map = dhashmap! {
    ///     1, "One" => String::from("Eins"),
    ///     2, "Two" => String::from("Zwei"),
    ///     3, "Three" => String::from("Drei"),
    /// };
    ///
    /// // two keys exist and refer to the same value ("Eins")
    /// assert_eq!(map.get_keys(&1, &"One" ), Some(&"Eins".to_owned()));
    ///
    /// // Both keys don't exist
    /// assert_eq!(map.get_keys(&4, &"Four"), None);
    ///
    /// // Both keys exist but refer to the different value (key1: 1 refers to "Eins",
    /// // key2: "Two" refers to "Zwei")
    /// assert_eq!(map.get_keys(&1, &"Two" ), None);
    /// assert_eq!(map.get_key1(&1).unwrap(),     "Eins");
    /// assert_eq!(map.get_key2(&"Two").unwrap(), "Zwei");
    /// ```
    #[inline]
    pub fn get_keys<Q1: ?Sized, Q2: ?Sized>(&self, k1: &Q1, k2: &Q2) -> Option<&V>
    where
        Q1: Hash + Equivalent<K1>,
        Q2: Hash + Equivalent<K2>,
    {
        // Avoid `Option::map` because it bloats LLVM IR.
        match self.get_inner_keys(k1, k2) {
            Some(&(_, _, ref v)) => Some(v),
            None => None,
        }
    }

    /// Returns the keys-value tuple corresponding to the supplied
    /// first key `K1`. Return the tuple of type `(&'a K1, &'a K2, &'a V)`.
    ///
    /// The supplied key may be any borrowed form of the map's key type, but
    /// [`Hash`] and [`Eq`] on the borrowed form *must* match those for
    /// the key type.
    ///
    /// # Examples
    ///
    /// ```
    /// use double_map::DHashMap;
    ///
    /// let mut map = DHashMap::new();
    /// map.insert(1, 10, "a");
    /// assert_eq!(map.get_key1_value(&1), Some((&1, &10, &"a")));
    /// assert_eq!(map.get_key1_value(&2), None);
    /// ```
    #[inline]
    pub fn get_key1_value<Q1: ?Sized>(&self, k1: &Q1) -> Option<(&K1, &K2, &V)>
    where
        Q1: Hash + Equivalent<K1>,
    {
        // Avoid `Option::map` because it bloats LLVM IR.
        match self.get_inner_key1(k1) {
            Some(&(ref k1, ref k2, ref v)) => Some((k1, k2, v)),
            None => None,
        }
    }

    /// Returns the keys-value tuple corresponding to the supplied
    /// second key `K2`. Return the tuple of type `(&'a K1, &'a K2, &'a V)`.
    ///
    /// The supplied key may be any borrowed form of the map's key type, but
    /// [`Hash`] and [`Eq`] on the borrowed form *must* match those for
    /// the key type.
    ///
    /// # Examples
    ///
    /// ```
    /// use double_map::DHashMap;
    ///
    /// let mut map = DHashMap::new();
    /// map.insert(1, 10, "a");
    /// assert_eq!(map.get_key2_value(&10), Some((&1, &10, &"a")));
    /// assert_eq!(map.get_key2_value(&20), None);
    /// ```
    #[inline]
    pub fn get_key2_value<Q2: ?Sized>(&self, k2: &Q2) -> Option<(&K1, &K2, &V)>
    where
        Q2: Hash + Equivalent<K2>,
    {
        // Avoid `Option::map` because it bloats LLVM IR.
        match self.get_inner_key2(k2) {
            Some(&(ref k1, ref k2, ref v)) => Some((k1, k2, v)),
            None => None,
        }
    }

    /// Returns a reference to the keys-value tuple corresponding to the given
    /// first `K1` and second `K2` keys if they both exist and refer to the same
    /// value. Return tuple of type `(&'a K1, &'a K2, &'a V)`.
    ///
    /// The supplied keys may be any borrowed form of the map's keys type, but
    /// [`Hash`] and [`Eq`] on the borrowed form *must* match those for
    /// the keys type.
    ///
    /// # Note
    ///
    /// Note that this [`get_keys_value`](DHashMap::get_keys_value) method return
    /// the tuple of type`(&'a K1, &'a K2, &'a V)` only if two keys exist and refer
    /// to the same `value`.
    ///
    /// # Example
    ///
    /// ```
    /// use double_map::{DHashMap, dhashmap};
    ///
    /// let map = dhashmap! {
    ///     1, "One"   => "Zebra",
    ///     2, "Two"   => "Horse",
    ///     3, "Three" => "Pony",
    /// };
    ///
    /// // two key exist and refer to the same value ("Zebra")
    /// assert_eq!(map.get_keys_value(&1, &"One").unwrap(), (&1, &"One", &"Zebra"));
    ///
    /// // Both keys don't exist
    /// assert_eq!(map.get_keys_value(&4, &"Four"), None);
    ///
    /// // Both keys exist but refer to the different value
    /// // (key1: 1 refer to "Zebra", key2: "Two" refer to "Horse")
    /// assert_eq!(map.get_keys_value(&1, &"Two" ), None);
    /// assert_eq!(map.get_key1(&1).unwrap(),     &"Zebra");
    /// assert_eq!(map.get_key2(&"Two").unwrap(), &"Horse");
    /// ```
    #[inline]
    pub fn get_keys_value<Q1: ?Sized, Q2: ?Sized>(&self, k1: &Q1, k2: &Q2) -> Option<(&K1, &K2, &V)>
    where
        Q1: Hash + Equivalent<K1>,
        Q2: Hash + Equivalent<K2>,
    {
        // Avoid `Option::map` because it bloats LLVM IR.
        match self.get_inner_keys(k1, k2) {
            Some(&(ref k1, ref k2, ref v)) => Some((k1, k2, v)),
            None => None,
        }
    }

    #[inline]
    fn get_inner_key1<Q1: ?Sized>(&self, k1: &Q1) -> Option<&(K1, K2, V)>
    where
        Q1: Hash + Equivalent<K1>,
    {
        if self.is_empty() {
            None
        } else {
            let hash = make_hash::<Q1, S>(&self.hash_builder, k1);
            self.table.get_h1(hash, equivalent_key1(k1))
        }
    }

    #[inline]
    fn get_inner_key2<Q2: ?Sized>(&self, k2: &Q2) -> Option<&(K1, K2, V)>
    where
        Q2: Hash + Equivalent<K2>,
    {
        if self.is_empty() {
            None
        } else {
            let hash = make_hash::<Q2, S>(&self.hash_builder, k2);
            self.table.get_h2(hash, equivalent_key2(k2))
        }
    }

    #[inline]
    fn get_inner_keys<Q1: ?Sized, Q2: ?Sized>(&self, k1: &Q1, k2: &Q2) -> Option<&(K1, K2, V)>
    where
        Q1: Hash + Equivalent<K1>,
        Q2: Hash + Equivalent<K2>,
    {
        if self.is_empty() {
            None
        } else {
            let hash1 = make_hash::<Q1, S>(&self.hash_builder, k1);
            let hash2 = make_hash::<Q2, S>(&self.hash_builder, k2);
            self.table
                .get(hash1, equivalent_key1(k1), hash2, equivalent_key2(k2))
        }
    }

    /// Returns the keys-value tuple corresponding to the supplied
    /// first key `K1`, with a mutable reference to value. Return
    /// the tuple of type `(&'a K1, &'a K2, &'a mut V)`.
    ///
    /// The supplied key may be any borrowed form of the map's key type, but
    /// [`Hash`] and [`Eq`] on the borrowed form *must* match those for
    /// the key type.
    ///
    /// # Examples
    ///
    /// ```
    /// use double_map::DHashMap;
    ///
    /// let mut map = DHashMap::new();
    /// map.insert(1, 10, "a");
    ///
    /// let (k1, k2, v) = map.get_key1_value_mut(&1).unwrap();
    /// assert_eq!(k1, &1);
    /// assert_eq!(k2, &10);
    /// assert_eq!(v, &mut "a");
    /// *v = "b";
    /// assert_eq!(map.get_key1_value_mut(&1), Some((&1, &10, &mut "b")));
    /// assert_eq!(map.get_key1_value_mut(&2), None);
    /// ```
    #[inline]
    pub fn get_key1_value_mut<Q1: ?Sized>(&mut self, k1: &Q1) -> Option<(&K1, &K2, &mut V)>
    where
        Q1: Hash + Equivalent<K1>,
    {
        // Avoid `Option::map` because it bloats LLVM IR.
        match self.get_inner_mut_key1(k1) {
            Some(&mut (ref k1, ref k2, ref mut v)) => Some((k1, k2, v)),
            None => None,
        }
    }

    /// Returns the keys-value tuple corresponding to the supplied
    /// second key `K2`, with a mutable reference to value. Return
    /// the tuple of type `(&'a K1, &'a K2, &'a mut V)`.
    ///
    /// The supplied key may be any borrowed form of the map's key type, but
    /// [`Hash`] and [`Eq`] on the borrowed form *must* match those for
    /// the key type.
    ///
    /// # Examples
    ///
    /// ```
    /// use double_map::DHashMap;
    ///
    /// let mut map = DHashMap::new();
    /// map.insert(1, 10, "a");
    ///
    /// let (k1, k2, v) = map.get_key2_value_mut(&10).unwrap();
    /// assert_eq!(k1, &1);
    /// assert_eq!(k2, &10);
    /// assert_eq!(v, &mut "a");
    /// *v = "b";
    /// assert_eq!(map.get_key2_value_mut(&10), Some((&1, &10, &mut "b")));
    /// assert_eq!(map.get_key2_value_mut(&20), None);
    /// ```
    #[inline]
    pub fn get_key2_value_mut<Q2: ?Sized>(&mut self, k2: &Q2) -> Option<(&K1, &K2, &mut V)>
    where
        Q2: Hash + Equivalent<K2>,
    {
        // Avoid `Option::map` because it bloats LLVM IR.
        match self.get_inner_mut_key2(k2) {
            Some(&mut (ref k1, ref k2, ref mut v)) => Some((k1, k2, v)),
            None => None,
        }
    }

    /// Returns the keys-value tuple corresponding to the supplied
    /// first `K1` and second `K2` keys, with a mutable reference
    /// to value only if they both exist and refer to the same value.
    /// Return tuple of type `(&'a K1, &'a K2, &'a V)`.
    ///
    /// The supplied keys may be any borrowed form of the map's keys type, but
    /// [`Hash`] and [`Eq`] on the borrowed form *must* match those for
    /// the keys type.
    ///
    /// # Note
    ///
    /// Note that this [`get_keys_value_mut`](DHashMap::get_keys_value_mut) method
    /// return the tuple of type`(&'a K1, &'a K2, &'a mut V)` only if two keys exist
    /// and refer to the same `value`.
    ///
    /// # Example
    ///
    /// ```
    /// use double_map::{DHashMap, dhashmap};
    ///
    /// let mut map = dhashmap! {
    ///     1, "One"   => "Zebra",
    ///     2, "Two"   => "Horse",
    ///     3, "Three" => "Pony",
    /// };
    ///
    /// // two key exist and refer to the same value ("Zebra")
    /// let (k1, k2, v) = map.get_keys_value_mut(&1, &"One").unwrap();
    /// assert_eq!(k1, &1);
    /// assert_eq!(k2, &"One");
    /// assert_eq!(v, &mut "Zebra");
    /// *v = "Elk";
    /// assert_eq!(map.get_keys_value_mut(&1, &"One").unwrap(), (&1, &"One", &mut "Elk"));
    ///
    /// // Both keys don't exist
    /// assert_eq!(map.get_keys_value_mut(&4, &"Four"), None);
    ///
    /// // Both keys exist but refer to the different value
    /// // (key1: 1 refer to "Elk", key2: "Two" refer to "Horse")
    /// assert_eq!(map.get_keys_value_mut(&1, &"Two" ), None);
    /// assert_eq!(map.get_key1(&1).unwrap(),     &"Elk");
    /// assert_eq!(map.get_key2(&"Two").unwrap(), &"Horse");
    /// ```
    #[inline]
    pub fn get_keys_value_mut<Q1, Q2>(&mut self, k1: &Q1, k2: &Q2) -> Option<(&K1, &K2, &mut V)>
    where
        Q1: ?Sized + Hash + Equivalent<K1>,
        Q2: ?Sized + Hash + Equivalent<K2>,
    {
        // Avoid `Option::map` because it bloats LLVM IR.
        match self.get_inner_mut_keys(k1, k2) {
            Some(&mut (ref k1, ref k2, ref mut v)) => Some((k1, k2, v)),
            None => None,
        }
    }

    /// Returns `true` if the map contains a value for the specified
    /// fist key `K1`.
    ///
    /// The key may be any borrowed form of the map's key type, but
    /// [`Hash`] and [`Eq`] on the borrowed form *must* match those for
    /// the key type
    ///
    /// # Example
    ///
    /// ```
    /// use double_map::{DHashMap, dhashmap};
    ///
    /// let map = dhashmap! {
    ///     1, "One" => String::from("Eins"),
    ///     2, "Two" => String::from("Zwei"),
    ///     3, "Three" => String::from("Drei"),
    /// };
    ///
    /// assert!( map.contains_key1(&1));
    /// assert!(!map.contains_key1(&4));
    /// ```
    #[cfg_attr(feature = "inline-more", inline)]
    pub fn contains_key1<Q1: ?Sized>(&self, k1: &Q1) -> bool
    where
        Q1: Hash + Equivalent<K1>,
    {
        self.get_inner_key1(k1).is_some()
    }

    /// Returns `true` if the map contains a value for the specified
    /// second key `K2`.
    ///
    /// The key may be any borrowed form of the map's key type, but
    /// [`Hash`] and [`Eq`] on the borrowed form *must* match those for
    /// the key type
    ///
    /// # Example
    ///
    /// ```
    /// use double_map::{DHashMap, dhashmap};
    ///
    /// let map = dhashmap! {
    ///     1, "One" => String::from("Eins"),
    ///     2, "Two" => String::from("Zwei"),
    ///     3, "Three" => String::from("Drei"),
    /// };
    ///
    /// assert!( map.contains_key2(&"One") );
    /// assert!(!map.contains_key2(&"Four"));
    /// ```
    #[cfg_attr(feature = "inline-more", inline)]
    pub fn contains_key2<Q2: ?Sized>(&self, k2: &Q2) -> bool
    where
        Q2: Hash + Equivalent<K2>,
    {
        self.get_inner_key2(k2).is_some()
    }

    /// Returns `true` if the map contains a value for the specified
    /// first `K1` and second `K2` keys and they both refer to the same
    /// value.
    ///
    /// The keys may be any borrowed form of the map's keys type, but
    /// [`Hash`] and [`Eq`] on the borrowed form *must* match those for
    /// the keys type.
    ///
    /// # Note
    /// Note that this [`contains_keys`](DHashMap::contains_keys) method
    /// return `true` only if two keys exist and refer to the same `value`.
    ///
    /// # Example
    ///
    /// ```
    /// use double_map::{DHashMap, dhashmap};
    ///
    /// let map = dhashmap! {
    ///     1, "One" => String::from("Eins"),
    ///     2, "Two" => String::from("Zwei"),
    ///     3, "Three" => String::from("Drei"),
    /// };
    ///
    /// // two keys exist and refer to the same value ("Eins")
    /// assert_eq!(map.contains_keys(&1, &"One" ), true );
    ///
    /// // Both keys don't exist
    /// assert_eq!(map.contains_keys(&4, &"Four"), false);
    ///
    /// // Both keys exist but refer to the different value (key1: 1 refers to "Eins",
    /// // key2: "Two" refers to "Zwei")
    /// assert_eq!(map.contains_keys(&1, &"Two" ), false);
    /// assert!(map.contains_key1(&1)     == true && map.get_key1(&1).unwrap()     == "Eins");
    /// assert!(map.contains_key2(&"Two") == true && map.get_key2(&"Two").unwrap() == "Zwei");
    /// ```
    #[cfg_attr(feature = "inline-more", inline)]
    pub fn contains_keys<Q1, Q2>(&self, k1: &Q1, k2: &Q2) -> bool
    where
        Q1: ?Sized + Hash + Equivalent<K1>,
        Q2: ?Sized + Hash + Equivalent<K2>,
    {
        self.get_inner_keys(k1, k2).is_some()
    }

    /// Returns a mutable reference to the value corresponding to
    /// the given fist key `K1`.
    ///
    /// The key may be any borrowed form of the map's key type, but
    /// [`Hash`] and [`Eq`] on the borrowed form *must* match those for
    /// the key type.
    ///
    /// # Examples
    ///
    /// ```
    /// use double_map::DHashMap;
    ///
    /// let mut map = DHashMap::new();
    /// map.insert(1, "a", "One");
    /// if let Some(x) = map.get_mut_key1(&1) {
    ///     *x = "First";
    /// }
    /// assert_eq!(map.get_key1(&1), Some(&"First"));
    /// ```
    #[inline]
    pub fn get_mut_key1<Q1: ?Sized>(&mut self, k1: &Q1) -> Option<&mut V>
    where
        Q1: Hash + Equivalent<K1>,
    {
        // Avoid `Option::map` because it bloats LLVM IR.
        match self.get_inner_mut_key1(k1) {
            Some(&mut (_, _, ref mut v)) => Some(v),
            None => None,
        }
    }

    /// Returns a mutable reference to the value corresponding to
    /// the given second key `K2`.
    ///
    /// The key may be any borrowed form of the map's key type, but
    /// [`Hash`] and [`Eq`] on the borrowed form *must* match those for
    /// the key type.
    ///
    /// # Examples
    ///
    /// ```
    /// use double_map::DHashMap;
    ///
    /// let mut map = DHashMap::new();
    /// map.insert(1, "a", "One");
    /// if let Some(x) = map.get_mut_key2(&"a") {
    ///     *x = "First";
    /// }
    /// assert_eq!(map.get_key2(&"a"), Some(&"First"));
    /// ```
    #[inline]
    pub fn get_mut_key2<Q2: ?Sized>(&mut self, k2: &Q2) -> Option<&mut V>
    where
        Q2: Hash + Equivalent<K2>,
    {
        // Avoid `Option::map` because it bloats LLVM IR.
        match self.get_inner_mut_key2(k2) {
            Some(&mut (_, _, ref mut v)) => Some(v),
            None => None,
        }
    }

    /// Returns a mutable reference to the value corresponding to the given
    /// first `K1` and second `K2` keys if they both exist and refer to the
    /// same value.
    ///
    /// The keys may be any borrowed form of the map's keys type, but
    /// [`Hash`] and [`Eq`] on the borrowed form *must* match those for
    /// the keys type.
    ///
    /// # Note
    /// Note that this [`get_mut_keys`](DHashMap::get_mut_keys) method return
    /// a reference to the value only if two keys exist and refer to the same
    /// `value`.
    ///
    /// # Examples
    ///
    /// ```
    /// use double_map::{DHashMap, dhashmap};
    ///
    /// let mut  map = dhashmap! {
    ///     1, "One" => String::from("One"),
    ///     2, "Two" => String::from("Two"),
    ///     3, "Three" => String::from("Three"),
    /// };
    ///
    /// // two keys exist and refer to the same value, so we have
    /// // a mutable reference to the value
    /// for (key_one, key_two) in (1..=3).zip(["One", "Two", "Three"]) {
    ///     if let Some(value) = map.get_mut_keys(&key_one, &key_two) {
    ///         value.push_str(" mississippi");
    ///     }
    /// }
    ///
    /// // We can see that all values updated
    /// assert_eq!(map.get_key1(&1), Some(&"One mississippi".to_owned()));
    /// assert_eq!(map.get_key1(&2), Some(&"Two mississippi".to_owned()));
    /// assert_eq!(map.get_key1(&3), Some(&"Three mississippi".to_owned()));
    ///
    /// // But if both keys don't exist we don't have a mutable reference to the value
    /// assert_eq!(map.get_mut_keys(&4, &"Four"), None);
    ///
    /// // If both keys exist but refer to the different value we also don't have
    /// // a mutable reference to the value
    /// assert_eq!(map.get_mut_keys(&1, &"Two" ), None);
    /// assert_eq!(map.get_key1(&1).unwrap(),     "One mississippi");
    /// assert_eq!(map.get_key2(&"Two").unwrap(), "Two mississippi");
    /// ```
    #[inline]
    pub fn get_mut_keys<Q1, Q2>(&mut self, k1: &Q1, k2: &Q2) -> Option<&mut V>
    where
        Q1: ?Sized + Hash + Equivalent<K1>,
        Q2: ?Sized + Hash + Equivalent<K2>,
    {
        // Avoid `Option::map` because it bloats LLVM IR.
        match self.get_inner_mut_keys(k1, k2) {
            Some(&mut (_, _, ref mut v)) => Some(v),
            None => None,
        }
    }

    #[inline]
    fn get_inner_mut_key1<Q1: ?Sized>(&self, k1: &Q1) -> Option<&mut (K1, K2, V)>
    where
        Q1: Hash + Equivalent<K1>,
    {
        if self.is_empty() {
            None
        } else {
            let hash = make_hash::<Q1, S>(&self.hash_builder, k1);
            self.table.get_mut_h1(hash, equivalent_key1(k1))
        }
    }

    #[inline]
    fn get_inner_mut_key2<Q2: ?Sized>(&self, k2: &Q2) -> Option<&mut (K1, K2, V)>
    where
        Q2: Hash + Equivalent<K2>,
    {
        if self.is_empty() {
            None
        } else {
            let hash = make_hash::<Q2, S>(&self.hash_builder, k2);
            self.table.get_mut_h2(hash, equivalent_key2(k2))
        }
    }

    #[inline]
    fn get_inner_mut_keys<Q1: ?Sized, Q2: ?Sized>(
        &self,
        k1: &Q1,
        k2: &Q2,
    ) -> Option<&mut (K1, K2, V)>
    where
        Q1: Hash + Equivalent<K1>,
        Q2: Hash + Equivalent<K2>,
    {
        if self.is_empty() {
            None
        } else {
            let hash1 = make_hash::<Q1, S>(&self.hash_builder, k1);
            let hash2 = make_hash::<Q2, S>(&self.hash_builder, k2);
            self.table
                .get_mut(hash1, equivalent_key1(k1), hash2, equivalent_key2(k2))
        }
    }

    /// Attempts to get mutable references to `N` values in the map
    /// at once corresponding to the given `N` fist `K1` keys.
    ///
    /// Returns an array of length `N` with the results of each query.
    /// For soundness, at most one mutable reference will be returned
    /// to any value. `None` will be returned if any of the keys are
    /// duplicates or missing.
    ///
    /// # Examples
    ///
    /// ```
    /// use double_map::DHashMap;
    ///
    /// let mut libraries = DHashMap::new();
    /// libraries.insert("Bogazkoy archives", "Boğazkale", "1900 B.C.");
    /// libraries.insert("Library of Ashurbanipal", "Mosul", "668 B.C.");
    /// libraries.insert("Library of Alexandria", "Alexandria", "285 B.C.");
    /// libraries.insert("Library of Antioch", "Antakya", "221 B.C.");
    /// libraries.insert("Library of Pergamum", "Bergama", "197 B.C.");
    ///
    /// let got = libraries.get_many_mut_key1(["Bogazkoy archives", "Library of Antioch"]);
    /// assert_eq!(got, Some([&mut "1900 B.C.", &mut "221 B.C."]));
    ///
    /// // Missing keys result is None
    /// let got = libraries.get_many_mut_key1(["Bogazkoy archives", "Libraries of the Forum"]);
    /// assert_eq!(got, None);
    ///
    /// // Duplicate keys result is None
    /// let got = libraries.get_many_mut_key1(["Bogazkoy archives", "Bogazkoy archives"]);
    /// assert_eq!(got, None);
    /// ```
    pub fn get_many_mut_key1<Q1, const N: usize>(&mut self, ks: [&Q1; N]) -> Option<[&'_ mut V; N]>
    where
        Q1: ?Sized + Hash + Equivalent<K1>,
    {
        self.get_many_mut_inner_key1(ks)
            .map(|arr| arr.map(|(_, _, v)| v))
    }

    /// Attempts to get mutable references to `N` values in the map
    /// at once corresponding to the given `N` second `K2` keys.
    ///
    /// Returns an array of length `N` with the results of each query.
    /// For soundness, at most one mutable reference will be returned
    /// to any value. `None` will be returned if any of the keys are
    /// duplicates or missing.
    ///
    /// # Examples
    ///
    /// ```
    /// use double_map::DHashMap;
    ///
    /// let mut libraries = DHashMap::new();
    /// libraries.insert("Bogazkoy archives", "Boğazkale", "1900 B.C.");
    /// libraries.insert("Library of Ashurbanipal", "Mosul", "668 B.C.");
    /// libraries.insert("Library of Alexandria", "Alexandria", "285 B.C.");
    /// libraries.insert("Library of Antioch", "Antakya", "221 B.C.");
    /// libraries.insert("Library of Pergamum", "Bergama", "197 B.C.");
    ///
    /// let got = libraries.get_many_mut_key2(["Boğazkale", "Antakya"]);
    /// assert_eq!(got, Some([&mut "1900 B.C.", &mut "221 B.C."]));
    ///
    /// // Missing keys result is None
    /// let got = libraries.get_many_mut_key2(["Boğazkale", "Rome"]);
    /// assert_eq!(got, None);
    ///
    /// // Duplicate keys result is None
    /// let got = libraries.get_many_mut_key2(["Boğazkale", "Boğazkale"]);
    /// assert_eq!(got, None);
    /// ```
    pub fn get_many_mut_key2<Q2, const N: usize>(&mut self, ks: [&Q2; N]) -> Option<[&'_ mut V; N]>
    where
        Q2: ?Sized + Hash + Equivalent<K2>,
    {
        self.get_many_mut_inner_key2(ks)
            .map(|arr| arr.map(|(_, _, v)| v))
    }

    /// Attempts to get mutable references to `N` values in the map
    /// at once corresponding to the given `N` first `K1` and second
    /// `K2` keys.
    ///
    /// Returns an array of length `N` with the results of each query.
    /// For soundness, at most one mutable reference will be returned
    /// to any value. `None` will be returned if any of the keys are
    /// duplicates or missing.
    ///
    /// # Note
    ///
    /// Note that this [`get_many_mut_keys`](DHashMap::get_many_mut_keys) method
    /// return array of values `[&'_ mut V; N]` only if each of given two keys'
    /// `(&Q1, &Q2)` tuples exist and refer to the same `value`.
    ///
    /// # Examples
    ///
    /// ```
    /// use double_map::DHashMap;
    ///
    /// let mut libraries = DHashMap::new();
    /// libraries.insert("Bogazkoy archives", "Boğazkale", "1900 B.C.");
    /// libraries.insert("Library of Ashurbanipal", "Mosul", "668 B.C.");
    /// libraries.insert("Library of Alexandria", "Alexandria", "285 B.C.");
    /// libraries.insert("Library of Antioch", "Antakya", "221 B.C.");
    /// libraries.insert("Library of Pergamum", "Bergama", "197 B.C.");
    ///
    /// let got = libraries.get_many_mut_keys([
    ///     ("Bogazkoy archives", "Boğazkale"),
    ///     ("Library of Antioch", "Antakya"),
    /// ]);
    /// assert_eq!(got, Some([&mut "1900 B.C.", &mut "221 B.C."]));
    ///
    /// // Missing keys result is None
    /// let got = libraries.get_many_mut_keys([
    ///     ("Bogazkoy archives", "Boğazkale"),
    ///     ("Libraries of the Forum", "Rome"),
    /// ]);
    /// assert_eq!(got, None);
    ///
    /// // Duplicate keys result is None
    /// let got = libraries.get_many_mut_keys([
    ///     ("Bogazkoy archives", "Boğazkale"),
    ///     ("Bogazkoy archives", "Boğazkale"),
    /// ]);
    /// assert_eq!(got, None);
    ///
    /// // Existing keys that refer to different values result is None
    /// let got = libraries.get_many_mut_keys([
    ///     ("Bogazkoy archives", "Mosul"),
    ///     ("Library of Ashurbanipal", "Boğazkale"),
    /// ]);
    /// assert_eq!(got, None);
    /// ```
    pub fn get_many_mut_keys<Q1, Q2, const N: usize>(
        &mut self,
        ks: [(&Q1, &Q2); N],
    ) -> Option<[&'_ mut V; N]>
    where
        Q1: ?Sized + Hash + Equivalent<K1>,
        Q2: ?Sized + Hash + Equivalent<K2>,
    {
        self.get_many_mut_inner_keys(ks)
            .map(|arr| arr.map(|(_, _, v)| v))
    }

    /// Attempts to get mutable references to `N` values in the map at once,
    /// corresponding to the given `N` first `K1` keys, without validating
    /// that the values are unique.
    ///
    /// Returns an array of length `N` with the results of each query. `None`
    /// will be returned if any of the keys are missing.
    ///
    /// For a safe alternative see [`get_many_mut_key1`](`DHashMap::get_many_mut_key1`).
    ///
    /// # Safety
    ///
    /// Calling this method with overlapping keys if they exist in map is
    /// *[undefined behavior]* even if the resulting references are not used.
    ///
    /// [undefined behavior]: https://doc.rust-lang.org/reference/behavior-considered-undefined.html
    ///
    /// # Examples
    ///
    /// ```
    /// use double_map::DHashMap;
    ///
    /// let mut libraries = DHashMap::new();
    /// libraries.insert("Bogazkoy archives", "Boğazkale", "1900 B.C.");
    /// libraries.insert("Library of Ashurbanipal", "Mosul", "668 B.C.");
    /// libraries.insert("Library of Alexandria", "Alexandria", "285 B.C.");
    /// libraries.insert("Library of Antioch", "Antakya", "221 B.C.");
    /// libraries.insert("Library of Pergamum", "Bergama", "197 B.C.");
    ///
    /// let got = unsafe {
    ///     libraries.get_many_unchecked_mut_key1(["Bogazkoy archives", "Library of Antioch"])
    /// };
    /// assert_eq!(got, Some([&mut "1900 B.C.", &mut "221 B.C."]));
    ///
    /// // Missing keys result is None
    /// let got = unsafe {
    ///     libraries.get_many_unchecked_mut_key1(["Bogazkoy archives", "Libraries of the Forum"])
    /// };
    /// assert_eq!(got, None);
    /// ```
    pub unsafe fn get_many_unchecked_mut_key1<Q1, const N: usize>(
        &mut self,
        ks: [&Q1; N],
    ) -> Option<[&'_ mut V; N]>
    where
        Q1: ?Sized + Hash + Equivalent<K1>,
    {
        self.get_many_unchecked_mut_inner_key1(ks)
            .map(|arr| arr.map(|(_, _, v)| v))
    }

    /// Attempts to get mutable references to `N` values in the map at once,
    /// corresponding to the given `N` second `K2` keys, without validating
    /// that the values are unique.
    ///
    /// Returns an array of length `N` with the results of each query. `None`
    /// will be returned if any of the keys are missing.
    ///
    /// For a safe alternative see [`get_many_mut_key2`](`DHashMap::get_many_mut_key2`).
    ///
    /// # Safety
    ///
    /// Calling this method with overlapping keys if they exist in map is
    /// *[undefined behavior]* even if the resulting references are not used.
    ///
    /// [undefined behavior]: https://doc.rust-lang.org/reference/behavior-considered-undefined.html
    ///
    /// # Examples
    ///
    /// ```
    /// use double_map::DHashMap;
    ///
    /// let mut libraries = DHashMap::new();
    /// libraries.insert("Bogazkoy archives", "Boğazkale", "1900 B.C.");
    /// libraries.insert("Library of Ashurbanipal", "Mosul", "668 B.C.");
    /// libraries.insert("Library of Alexandria", "Alexandria", "285 B.C.");
    /// libraries.insert("Library of Antioch", "Antakya", "221 B.C.");
    /// libraries.insert("Library of Pergamum", "Bergama", "197 B.C.");
    ///
    /// let got = unsafe { libraries.get_many_unchecked_mut_key2(["Boğazkale", "Antakya"]) };
    /// assert_eq!(got, Some([&mut "1900 B.C.", &mut "221 B.C."]));
    ///
    /// // Missing keys result is None
    /// let got = unsafe { libraries.get_many_unchecked_mut_key2(["Boğazkale", "Rome"]) };
    /// assert_eq!(got, None);
    /// ```
    pub unsafe fn get_many_unchecked_mut_key2<Q2, const N: usize>(
        &mut self,
        ks: [&Q2; N],
    ) -> Option<[&'_ mut V; N]>
    where
        Q2: ?Sized + Hash + Equivalent<K2>,
    {
        self.get_many_unchecked_mut_inner_key2(ks)
            .map(|arr| arr.map(|(_, _, v)| v))
    }

    /// Attempts to get mutable references to `N` values in the map at once,
    /// corresponding to the given `N` first `K1` and second `K2` keys, without
    /// validating that the values are unique.
    ///
    /// Returns an array of length `N` with the results of each query. `None`
    /// will be returned if any of the keys are missing.
    ///
    /// For a safe alternative see [`get_many_mut_keys`](`DHashMap::get_many_mut_keys`).
    ///
    /// # Safety
    ///
    /// Calling this method with overlapping keys, if they both exist in map and refer
    /// to the same value, is *[undefined behavior]* even if the resulting references
    /// are not used.
    ///
    /// In other words this [`get_many_unchecked_mut_keys`](DHashMap::get_many_unchecked_mut_keys)
    /// method return array of values `[&'_ mut V; N]` only if each of given two keys'
    /// `(&Q1, &Q2)` tuples exist and refer to the same `value`. For more information see
    /// [`get_keys_value_mut`](DHashMap::get_keys_value_mut) method.
    ///
    /// [undefined behavior]: https://doc.rust-lang.org/reference/behavior-considered-undefined.html
    ///
    /// # Examples
    ///
    /// ```
    /// use double_map::DHashMap;
    ///
    /// let mut libraries = DHashMap::new();
    /// libraries.insert("Bogazkoy archives", "Boğazkale", "1900 B.C.");
    /// libraries.insert("Library of Ashurbanipal", "Mosul", "668 B.C.");
    /// libraries.insert("Library of Alexandria", "Alexandria", "285 B.C.");
    /// libraries.insert("Library of Antioch", "Antakya", "221 B.C.");
    /// libraries.insert("Library of Pergamum", "Bergama", "197 B.C.");
    ///
    /// let got = unsafe {
    ///     libraries.get_many_unchecked_mut_keys([
    ///         ("Bogazkoy archives", "Boğazkale"),
    ///         ("Library of Antioch", "Antakya"),
    ///     ])
    /// };
    /// assert_eq!(got, Some([&mut "1900 B.C.", &mut "221 B.C."]));
    ///
    /// // Missing keys result is None
    /// let got = unsafe {
    ///     libraries.get_many_unchecked_mut_keys([
    ///         ("Bogazkoy archives", "Boğazkale"),
    ///         ("Libraries of the Forum", "Rome"),
    ///     ])
    /// };
    /// assert_eq!(got, None);
    /// ```
    pub unsafe fn get_many_unchecked_mut_keys<Q1, Q2, const N: usize>(
        &mut self,
        ks: [(&Q1, &Q2); N],
    ) -> Option<[&'_ mut V; N]>
    where
        Q1: ?Sized + Hash + Equivalent<K1>,
        Q2: ?Sized + Hash + Equivalent<K2>,
    {
        self.get_many_unchecked_mut_inner_keys(ks)
            .map(|arr| arr.map(|(_, _, v)| v))
    }

    /// Attempts to get mutable references to `N` values in the map at once
    /// using the given `N` fist `K1` keys, with immutable references to the
    /// corresponding `K1` and `K2` keys.
    ///
    /// Returns an array of length `N` with the results of each query. For
    /// soundness, at most one mutable reference will be returned to any value.
    /// `None` will be returned if any of the keys are duplicates or missing.
    ///
    /// # Examples
    ///
    /// ```
    /// use double_map::DHashMap;
    ///
    /// let mut libraries = DHashMap::new();
    /// libraries.insert("Bogazkoy archives", "Boğazkale", "1900 B.C.");
    /// libraries.insert("Library of Ashurbanipal", "Mosul", "668 B.C.");
    /// libraries.insert("Library of Alexandria", "Alexandria", "285 B.C.");
    /// libraries.insert("Library of Antioch", "Antakya", "221 B.C.");
    /// libraries.insert("Library of Pergamum", "Bergama", "197 B.C.");
    ///
    /// let got = libraries.get_many_key1_value_mut(["Bogazkoy archives", "Library of Antioch"]);
    /// assert_eq!(
    ///     got,
    ///     Some([
    ///         (&"Bogazkoy archives", &"Boğazkale", &mut "1900 B.C."),
    ///         (&"Library of Antioch", &"Antakya", &mut "221 B.C.")
    ///     ])
    /// );
    ///
    /// // Missing keys result is None
    /// let got = libraries.get_many_key1_value_mut(["Bogazkoy archives", "Libraries of the Forum"]);
    /// assert_eq!(got, None);
    ///
    /// // Duplicate keys result is None
    /// let got = libraries.get_many_key1_value_mut(["Bogazkoy archives", "Bogazkoy archives"]);
    /// assert_eq!(got, None);
    /// ```
    pub fn get_many_key1_value_mut<Q1, const N: usize>(
        &mut self,
        ks: [&Q1; N],
    ) -> Option<[(&'_ K1, &'_ K2, &'_ mut V); N]>
    where
        Q1: ?Sized + Hash + Equivalent<K1>,
    {
        self.get_many_mut_inner_key1(ks)
            .map(|arr| arr.map(|(ref k1, ref k2, v)| (k1, k2, v)))
    }

    /// Attempts to get mutable references to `N` values in the map at once
    /// using the given `N` second `K2` keys, with immutable references to the
    /// corresponding `K1` and `K2` keys.
    ///
    /// Returns an array of length `N` with the results of each query. For
    /// soundness, at most one mutable reference will be returned to any value.
    /// `None` will be returned if any of the keys are duplicates or missing.
    ///
    /// # Examples
    ///
    /// ```
    /// use double_map::DHashMap;
    ///
    /// let mut libraries = DHashMap::new();
    /// libraries.insert("Bogazkoy archives", "Boğazkale", "1900 B.C.");
    /// libraries.insert("Library of Ashurbanipal", "Mosul", "668 B.C.");
    /// libraries.insert("Library of Alexandria", "Alexandria", "285 B.C.");
    /// libraries.insert("Library of Antioch", "Antakya", "221 B.C.");
    /// libraries.insert("Library of Pergamum", "Bergama", "197 B.C.");
    ///
    /// let got = libraries.get_many_key2_value_mut(["Boğazkale", "Antakya"]);
    /// assert_eq!(
    ///     got,
    ///     Some([
    ///         (&"Bogazkoy archives", &"Boğazkale", &mut "1900 B.C."),
    ///         (&"Library of Antioch", &"Antakya", &mut "221 B.C.")
    ///     ])
    /// );
    ///
    /// // Missing keys result is None
    /// let got = libraries.get_many_key2_value_mut(["Boğazkale", "Rome"]);
    /// assert_eq!(got, None);
    ///
    /// // Duplicate keys result is None
    /// let got = libraries.get_many_key2_value_mut(["Boğazkale", "Boğazkale"]);
    /// assert_eq!(got, None);
    /// ```
    pub fn get_many_key2_value_mut<Q2, const N: usize>(
        &mut self,
        ks: [&Q2; N],
    ) -> Option<[(&'_ K1, &'_ K2, &'_ mut V); N]>
    where
        Q2: ?Sized + Hash + Equivalent<K2>,
    {
        self.get_many_mut_inner_key2(ks)
            .map(|arr| arr.map(|(ref k1, ref k2, v)| (k1, k2, v)))
    }

    /// Attempts to get mutable references to `N` values in the map at once
    /// using the given `N` first `K1` and second `K2` keys, with immutable
    /// references to the corresponding keys.
    ///
    /// Returns an array of length `N` with the results of each query. For
    /// soundness, at most one mutable reference will be returned to any value.
    /// `None` will be returned if any of the keys are duplicates or missing.
    ///
    /// # Note
    ///
    /// Note that this [`get_many_keys_value_mut`](DHashMap::get_many_keys_value_mut)
    /// method return array of values `[(&'_ K1, &'_ K2, &'_ mut V); N]` only if each
    /// of given two keys' `(&Q1, &Q2)` tuples exist and refer to the same `value`.
    ///
    /// # Examples
    ///
    /// ```
    /// use double_map::DHashMap;
    ///
    /// let mut libraries = DHashMap::new();
    /// libraries.insert("Bogazkoy archives", "Boğazkale", "1900 B.C.");
    /// libraries.insert("Library of Ashurbanipal", "Mosul", "668 B.C.");
    /// libraries.insert("Library of Alexandria", "Alexandria", "285 B.C.");
    /// libraries.insert("Library of Antioch", "Antakya", "221 B.C.");
    /// libraries.insert("Library of Pergamum", "Bergama", "197 B.C.");
    ///
    /// let got = libraries.get_many_keys_value_mut([
    ///     ("Bogazkoy archives", "Boğazkale"),
    ///     ("Library of Antioch", "Antakya"),
    /// ]);
    /// assert_eq!(
    ///     got,
    ///     Some([
    ///         (&"Bogazkoy archives", &"Boğazkale", &mut "1900 B.C."),
    ///         (&"Library of Antioch", &"Antakya", &mut "221 B.C.")
    ///     ])
    /// );
    ///
    /// // Missing keys result is None
    /// let got = libraries.get_many_keys_value_mut([
    ///     ("Bogazkoy archives", "Boğazkale"),
    ///     ("Libraries of the Forum", "Rome"),
    /// ]);
    /// assert_eq!(got, None);
    ///
    /// // Duplicate keys result is None
    /// let got = libraries.get_many_keys_value_mut([
    ///     ("Bogazkoy archives", "Boğazkale"),
    ///     ("Bogazkoy archives", "Boğazkale"),
    /// ]);
    /// assert_eq!(got, None);
    ///
    /// // Existing keys that refer to different values result is None
    /// let got = libraries.get_many_keys_value_mut([
    ///     ("Bogazkoy archives", "Mosul"),
    ///     ("Library of Ashurbanipal", "Boğazkale"),
    /// ]);
    /// assert_eq!(got, None);
    /// ```
    pub fn get_many_keys_value_mut<Q1, Q2, const N: usize>(
        &mut self,
        ks: [(&Q1, &Q2); N],
    ) -> Option<[(&'_ K1, &'_ K2, &'_ mut V); N]>
    where
        Q1: ?Sized + Hash + Equivalent<K1>,
        Q2: ?Sized + Hash + Equivalent<K2>,
    {
        self.get_many_mut_inner_keys(ks)
            .map(|arr| arr.map(|(ref k1, ref k2, v)| (k1, k2, v)))
    }

    /// Attempts to get mutable references to `N` values in the map at once
    /// using the given `N` first `K1` keys, with immutable references to the
    /// corresponding `K1` and `K2` keys. This method does not validate that
    /// the values are unique.
    ///
    /// Returns an array of length `N` with the results of each query.
    /// `None` will be returned if any of the keys are missing.
    ///
    /// For a safe alternative see [`get_many_key1_value_mut`](`HashMap::get_many_key1_value_mut`).
    ///
    /// # Safety
    ///
    /// Calling this method with overlapping keys if they exist in map is
    /// *[undefined behavior]* even if the resulting references are not used.
    ///
    /// [undefined behavior]: https://doc.rust-lang.org/reference/behavior-considered-undefined.html
    ///
    /// # Examples
    ///
    /// ```
    /// use double_map::DHashMap;
    ///
    /// let mut libraries = DHashMap::new();
    /// libraries.insert("Bogazkoy archives", "Boğazkale", "1900 B.C.");
    /// libraries.insert("Library of Ashurbanipal", "Mosul", "668 B.C.");
    /// libraries.insert("Library of Alexandria", "Alexandria", "285 B.C.");
    /// libraries.insert("Library of Antioch", "Antakya", "221 B.C.");
    /// libraries.insert("Library of Pergamum", "Bergama", "197 B.C.");
    ///
    /// let got = unsafe {
    ///     libraries.get_many_key1_value_unchecked_mut(["Bogazkoy archives", "Library of Antioch"])
    /// };
    /// assert_eq!(
    ///     got,
    ///     Some([
    ///         (&"Bogazkoy archives", &"Boğazkale", &mut "1900 B.C."),
    ///         (&"Library of Antioch", &"Antakya", &mut "221 B.C.")
    ///     ])
    /// );
    ///
    /// // Missing keys result in None
    /// let got = unsafe {
    ///     libraries.get_many_key1_value_unchecked_mut(["Bogazkoy archives", "Libraries of the Forum"])
    /// };
    /// assert_eq!(got, None);
    /// ```
    pub unsafe fn get_many_key1_value_unchecked_mut<Q1, const N: usize>(
        &mut self,
        ks: [&Q1; N],
    ) -> Option<[(&'_ K1, &'_ K2, &'_ mut V); N]>
    where
        Q1: ?Sized + Hash + Equivalent<K1>,
    {
        self.get_many_unchecked_mut_inner_key1(ks)
            .map(|arr| arr.map(|(ref k1, ref k2, v)| (k1, k2, v)))
    }

    /// Attempts to get mutable references to `N` values in the map at once
    /// using the given `N` second `K2` keys, with immutable references to the
    /// corresponding `K1` and `K2` keys. This method does not validate that
    /// the values are unique.
    ///
    /// Returns an array of length `N` with the results of each query.
    /// `None` will be returned if any of the keys are missing.
    ///
    /// For a safe alternative see [`get_many_key2_value_mut`](`HashMap::get_many_key2_value_mut`).
    ///
    /// # Safety
    ///
    /// Calling this method with overlapping keys if they exist in map is
    /// *[undefined behavior]* even if the resulting references are not used.
    ///
    /// [undefined behavior]: https://doc.rust-lang.org/reference/behavior-considered-undefined.html
    ///
    /// # Examples
    ///
    /// ```
    /// use double_map::DHashMap;
    ///
    /// let mut libraries = DHashMap::new();
    /// libraries.insert("Bogazkoy archives", "Boğazkale", "1900 B.C.");
    /// libraries.insert("Library of Ashurbanipal", "Mosul", "668 B.C.");
    /// libraries.insert("Library of Alexandria", "Alexandria", "285 B.C.");
    /// libraries.insert("Library of Antioch", "Antakya", "221 B.C.");
    /// libraries.insert("Library of Pergamum", "Bergama", "197 B.C.");
    ///
    /// let got = unsafe { libraries.get_many_key2_value_unchecked_mut(["Boğazkale", "Antakya"]) };
    /// assert_eq!(
    ///     got,
    ///     Some([
    ///         (&"Bogazkoy archives", &"Boğazkale", &mut "1900 B.C."),
    ///         (&"Library of Antioch", &"Antakya", &mut "221 B.C.")
    ///     ])
    /// );
    ///
    /// // Missing keys result in None
    /// let got = unsafe { libraries.get_many_key2_value_unchecked_mut(["Boğazkale", "Rome"]) };
    /// assert_eq!(got, None);
    /// ```
    pub unsafe fn get_many_key2_value_unchecked_mut<Q2, const N: usize>(
        &mut self,
        ks: [&Q2; N],
    ) -> Option<[(&'_ K1, &'_ K2, &'_ mut V); N]>
    where
        Q2: ?Sized + Hash + Equivalent<K2>,
    {
        self.get_many_unchecked_mut_inner_key2(ks)
            .map(|arr| arr.map(|(ref k1, ref k2, v)| (k1, k2, v)))
    }

    /// Attempts to get mutable references to `N` values in the map at once
    /// using the given `N` first `K1` and second `K2` keys, with immutable
    /// references to the corresponding keys. This method does not validate that
    /// the values are unique.
    ///
    /// Returns an array of length `N` with the results of each query.
    /// `None` will be returned if any of the keys are missing.
    ///
    /// For a safe alternative see [`get_many_keys_value_mut`](`HashMap::get_many_keys_value_mut`).
    ///
    /// # Safety
    ///
    /// Calling this method with overlapping keys, if they both exist in map and refer
    /// to the same value, is *[undefined behavior]* even if the resulting references
    /// are not used.
    ///
    /// In other words this [`get_many_keys_value_unchecked_mut`](DHashMap::get_many_keys_value_unchecked_mut)
    /// method return array of values `[(&'_ K1, &'_ K2, &'_ mut V); N]` only if each of given two keys'
    /// `(&Q1, &Q2)` tuples exist and refer to the same `value`. For more information see
    /// [`get_keys_value_mut`](DHashMap::get_keys_value_mut) method.
    ///
    /// [undefined behavior]: https://doc.rust-lang.org/reference/behavior-considered-undefined.html
    ///
    /// # Examples
    ///
    /// ```
    /// use double_map::DHashMap;
    ///
    /// let mut libraries = DHashMap::new();
    /// libraries.insert("Bogazkoy archives", "Boğazkale", "1900 B.C.");
    /// libraries.insert("Library of Ashurbanipal", "Mosul", "668 B.C.");
    /// libraries.insert("Library of Alexandria", "Alexandria", "285 B.C.");
    /// libraries.insert("Library of Antioch", "Antakya", "221 B.C.");
    /// libraries.insert("Library of Pergamum", "Bergama", "197 B.C.");
    ///
    /// let got = unsafe {
    ///     libraries.get_many_keys_value_unchecked_mut([
    ///         ("Bogazkoy archives", "Boğazkale"),
    ///         ("Library of Antioch", "Antakya"),
    ///     ])
    /// };
    /// assert_eq!(
    ///     got,
    ///     Some([
    ///         (&"Bogazkoy archives", &"Boğazkale", &mut "1900 B.C."),
    ///         (&"Library of Antioch", &"Antakya", &mut "221 B.C.")
    ///     ])
    /// );
    ///
    /// // Missing keys result in None
    /// let got = unsafe {
    ///     libraries.get_many_keys_value_unchecked_mut([
    ///         ("Bogazkoy archives", "Boğazkale"),
    ///         ("Libraries of the Forum", "Rome"),
    ///     ])
    /// };
    /// assert_eq!(got, None);
    /// ```
    pub unsafe fn get_many_keys_value_unchecked_mut<Q1, Q2, const N: usize>(
        &mut self,
        ks: [(&Q1, &Q2); N],
    ) -> Option<[(&'_ K1, &'_ K2, &'_ mut V); N]>
    where
        Q1: ?Sized + Hash + Equivalent<K1>,
        Q2: ?Sized + Hash + Equivalent<K2>,
    {
        self.get_many_unchecked_mut_inner_keys(ks)
            .map(|arr| arr.map(|(ref k1, ref k2, v)| (k1, k2, v)))
    }

    fn get_many_mut_inner_key1<Q1, const N: usize>(
        &mut self,
        ks: [&Q1; N],
    ) -> Option<[&'_ mut (K1, K2, V); N]>
    where
        Q1: ?Sized + Hash + Equivalent<K1>,
    {
        let hash_builder = &self.hash_builder;

        let hash1_iter = ks.into_iter().map(|key1| {
            (
                make_hash::<Q1, S>(hash_builder, key1),
                equivalent_key1::<Q1, K1, K2, V>(key1),
            )
        });

        // Safety: we know that given iterator length is equal to the given `const N`.
        unsafe { self.table.get_many_mut_from_h1_iter::<N>(hash1_iter) }
    }

    unsafe fn get_many_unchecked_mut_inner_key1<Q1, const N: usize>(
        &mut self,
        ks: [&Q1; N],
    ) -> Option<[&'_ mut (K1, K2, V); N]>
    where
        Q1: ?Sized + Hash + Equivalent<K1>,
    {
        let hash_builder = &self.hash_builder;

        let hash1_iter = ks.into_iter().map(|key1| {
            (
                make_hash::<Q1, S>(hash_builder, key1),
                equivalent_key1::<Q1, K1, K2, V>(key1),
            )
        });

        // we know only that given iterator length is equal to the given `const N`.
        self.table
            .get_many_unchecked_mut_from_h1_iter::<N>(hash1_iter)
    }

    fn get_many_mut_inner_key2<Q2, const N: usize>(
        &mut self,
        ks: [&Q2; N],
    ) -> Option<[&'_ mut (K1, K2, V); N]>
    where
        Q2: ?Sized + Hash + Equivalent<K2>,
    {
        let hash_builder = &self.hash_builder;

        let hash2_iter = ks.into_iter().map(|key2| {
            (
                make_hash::<Q2, S>(hash_builder, key2),
                equivalent_key2::<Q2, K1, K2, V>(key2),
            )
        });

        // Safety: we know that given iterator length is equal to the given `const N`.
        unsafe { self.table.get_many_mut_from_h2_iter::<N>(hash2_iter) }
    }

    unsafe fn get_many_unchecked_mut_inner_key2<Q2, const N: usize>(
        &mut self,
        ks: [&Q2; N],
    ) -> Option<[&'_ mut (K1, K2, V); N]>
    where
        Q2: ?Sized + Hash + Equivalent<K2>,
    {
        let hash_builder = &self.hash_builder;

        let hash2_iter = ks.into_iter().map(|key2| {
            (
                make_hash::<Q2, S>(hash_builder, key2),
                equivalent_key2::<Q2, K1, K2, V>(key2),
            )
        });

        // we know only that given iterator length is equal to the given `const N`.
        self.table
            .get_many_unchecked_mut_from_h2_iter::<N>(hash2_iter)
    }

    fn get_many_mut_inner_keys<Q1, Q2, const N: usize>(
        &mut self,
        ks: [(&Q1, &Q2); N],
    ) -> Option<[&'_ mut (K1, K2, V); N]>
    where
        Q1: ?Sized + Hash + Equivalent<K1>,
        Q2: ?Sized + Hash + Equivalent<K2>,
    {
        let hash_builder = &self.hash_builder;
        let hashes_iter = ks.into_iter().map(|(key1, key2)| {
            (
                make_hash::<Q1, S>(hash_builder, key1),
                equivalent_key1::<Q1, K1, K2, V>(key1),
                make_hash::<Q2, S>(hash_builder, key2),
                equivalent_key2::<Q2, K1, K2, V>(key2),
            )
        });

        // Safety: we know that given iterator length is equal to the given `const N`.
        unsafe { self.table.get_many_mut_from_iter::<N>(hashes_iter) }
    }

    unsafe fn get_many_unchecked_mut_inner_keys<Q1, Q2, const N: usize>(
        &mut self,
        ks: [(&Q1, &Q2); N],
    ) -> Option<[&'_ mut (K1, K2, V); N]>
    where
        Q1: ?Sized + Hash + Equivalent<K1>,
        Q2: ?Sized + Hash + Equivalent<K2>,
    {
        let hash_builder = &self.hash_builder;
        let hashes_iter = ks.into_iter().map(|(key1, key2)| {
            (
                make_hash::<Q1, S>(hash_builder, key1),
                equivalent_key1::<Q1, K1, K2, V>(key1),
                make_hash::<Q2, S>(hash_builder, key2),
                equivalent_key2::<Q2, K1, K2, V>(key2),
            )
        });

        // we know only that given iterator length is equal to the given `const N`.
        self.table
            .get_many_unchecked_mut_from_iter::<N>(hashes_iter)
    }

    /// Tries to insert given keys and value into the map. Update the value
    /// if keys are already present and refer to the same value with returning
    /// old value.
    ///
    /// If the map did not have these keys present, [`None`] is returned.
    ///
    /// If the map did have these key **present**, and **both keys refer to
    /// the same value**, the value is updated, and the old value is returned
    /// inside `Some(Ok(V))` variants. The key is not updated, though; this
    /// matters for types that can be `==` without being identical.
    /// See the [std module-level documentation] for more.
    ///
    /// The [`insert`](DHashMap::insert) method returns [`InsertError`] structure
    /// (inside of `Some(Err(_))` variants):
    /// - when `K1` key is vacant, but `K2` key already exists with some value;
    /// - when `K1` key already exists with some value, but `K2` key is vacant;
    /// - when both `K1` and `K2` keys already exist with some values, but
    /// point to different entries (values).
    ///
    /// The above mentioned error kinds can be matched through the [`ErrorKind`] enum.
    /// Returned [`InsertError`] structure also contains provided keys and value
    /// that were not inserted and can be used for another purpose.
    ///
    /// [std module-level documentation]: std::collections#insert-and-complex-keys
    ///
    /// # Examples
    ///
    /// ```
    /// use double_map::DHashMap;
    /// use double_map::dhash_map::{InsertError, ErrorKind};
    /// let mut map = DHashMap::new();
    ///
    /// // Returns None if keys are vacant
    /// assert_eq!(map.insert(1, "a", "One"), None);
    /// assert_eq!(map.is_empty(), false);
    ///
    /// // If the map did have these keys present, and both keys refer to
    /// // the same value, the value is updated, and the old value is returned
    /// // inside `Some(Ok(V))` variants
    /// map.insert(2, "b", "Two");
    /// assert_eq!(map.insert(2, "b", "Second"), Some(Ok("Two")));
    /// assert_eq!(map.get_key1(&2), Some(&"Second"));
    ///
    /// // Returns `ErrorKind::OccupiedK1AndVacantK2` if key #1 already
    /// // exists with some value, but key #2 is vacant. Error structure
    /// // also contains provided keys and value
    /// match map.insert(1, "c", "value") {
    ///     Some(Err(InsertError{ error, keys, value })) => {
    ///         assert_eq!(error, ErrorKind::OccupiedK1AndVacantK2);
    ///         assert_eq!(keys, (1, "c"));
    ///         assert_eq!(value, "value");
    ///     }
    ///     _ => unreachable!(),
    /// }
    ///
    /// // Returns `ErrorKind::VacantK1AndOccupiedK2` if key #1 is vacant,
    /// // but key #2 already exists with some value.
    /// let error_kind = map.insert(3, "a", "value").unwrap().unwrap_err().error;
    /// assert_eq!(error_kind, ErrorKind::VacantK1AndOccupiedK2);
    ///
    /// // Returns `ErrorKind::KeysPointsToDiffEntries` if both
    /// // key #1 and key #2 already exist with some values,
    /// // but point to different entries (values).
    /// let error_kind = map.insert(1, "b", "value").unwrap().unwrap_err().error;
    /// assert_eq!(error_kind, ErrorKind::KeysPointsToDiffEntries);
    /// ```
    #[cfg_attr(feature = "inline-more", inline)]
    pub fn insert(&mut self, k1: K1, k2: K2, v: V) -> Option<Result<V, InsertError<K1, K2, V>>> {
        let hash_builder = &self.hash_builder;
        let hash1 = make_insert_hash::<K1, S>(hash_builder, &k1);
        let hash2 = make_insert_hash::<K2, S>(hash_builder, &k2);
        let table = &mut self.table;

        match table.find_h1(hash1, equivalent_key1(&k1)) {
            None => match table.find_h2(hash2, equivalent_key2(&k2)) {
                None => {
                    table.insert(
                        hash1,
                        hash2,
                        (k1, k2, v),
                        make_hasher_key1::<_, K2, V, S>(hash_builder),
                        make_hasher_key2::<K1, _, V, S>(hash_builder),
                    );
                    None
                }
                // Error: Vacant key #1 of type K1 and occupied key # 2 of type K2
                Some(_) => Some(Err(InsertError {
                    error: ErrorKind::VacantK1AndOccupiedK2,
                    keys: (k1, k2),
                    value: v,
                })),
            },

            Some(data_bucket) => match table.find_h2(hash2, equivalent_key2(&k2)) {
                Some(pointer_bucket) => {
                    if unsafe { ptr::eq(data_bucket.as_ptr(), pointer_bucket.as_data_ptr()) } {
                        let old_value = unsafe { &mut data_bucket.as_mut().2 };
                        Some(Ok(mem::replace(old_value, v)))
                    } else {
                        // Error: key #1 and key # 2 refer to different entries / values
                        Some(Err(InsertError {
                            error: ErrorKind::KeysPointsToDiffEntries,
                            keys: (k1, k2),
                            value: v,
                        }))
                    }
                }

                None => Some(Err(InsertError {
                    error: ErrorKind::OccupiedK1AndVacantK2,
                    keys: (k1, k2),
                    value: v,
                })),
            },
        }
    }

    /// Insert a keys-value tuple into the map without checking
    /// if any (or both) of the keys already exists in the map.
    ///
    /// Returns a reference to the keys and mutable reference
    /// to the value just inserted.
    ///
    /// This operation is safe if a keys does not exist in the map.
    ///
    /// However, if any of the keys exists in the map already, the behavior
    /// is unspecified: this operation may panic, loop forever, or any
    /// following operation with the map may panic, loop forever or return
    /// arbitrary result.
    ///
    /// That said, this operation (and following operations) are guaranteed to
    /// not violate memory safety.
    ///
    /// This operation is faster than regular insert, because it does not perform
    /// lookup before insertion.
    ///
    /// This operation is useful during initial population of the map.
    /// For example, when constructing a map from another map, we know
    /// that keys are unique.
    ///
    /// # Examples
    ///
    /// ```
    /// use double_map::DHashMap;
    ///
    /// let mut map1 = DHashMap::new();
    /// assert_eq!(map1.insert(1, "a", "pony"), None);
    /// assert_eq!(map1.insert(2, "b", "horse"), None);
    /// assert_eq!(map1.insert(3, "c", "zebra"), None);
    /// assert_eq!(map1.len(), 3);
    ///
    /// let mut map2 = DHashMap::new();
    ///
    /// for (k1, k2, value) in map1.into_iter() {
    ///     map2.insert_unique_unchecked(k1, k2, value);
    /// }
    ///
    /// let (k1, k2, value) = map2.insert_unique_unchecked(4, "d", "elk");
    /// assert_eq!(k1, &4);
    /// assert_eq!(k2, &"d");
    /// assert_eq!(value, &mut "elk");
    /// *value = "deer";
    ///
    /// assert_eq!(map2[&1], "pony");
    /// assert_eq!(map2[&2], "horse");
    /// assert_eq!(map2[&3], "zebra");
    /// assert_eq!(map2[&4], "deer");
    /// assert_eq!(map2.len(), 4);
    /// ```
    #[cfg_attr(feature = "inline-more", inline)]
    pub fn insert_unique_unchecked(&mut self, k1: K1, k2: K2, v: V) -> (&K1, &K2, &mut V) {
        let hash_builder = &self.hash_builder;
        let hash1 = make_insert_hash::<K1, S>(hash_builder, &k1);
        let hash2 = make_insert_hash::<K2, S>(hash_builder, &k2);

        let buckets = self.table.insert(
            hash1,
            hash2,
            (k1, k2, v),
            make_hasher_key1::<_, K2, V, S>(hash_builder),
            make_hasher_key2::<K1, _, V, S>(hash_builder),
        );
        let (k1, k2, v) = unsafe { buckets.0.as_mut() };
        (k1, k2, v)
    }

    /// Tries to insert given keys and value into the map, and returns
    /// a mutable reference to the value in the entry if the map did not
    /// have these keys present.
    ///
    /// If the map did have these keys **present**, and **both keys refer to
    /// the same value**, ***nothing*** is updated, and a [`TryInsertError::Occupied`]
    /// enum variant error containing [`OccupiedError`] structure is returned.
    /// The [`OccupiedError`] contains the occupied entry [`OccupiedEntry`],
    /// and the value that was not inserted.
    ///
    /// The [`try_insert`](DHashMap::try_insert) method return [`InsertError`] structure
    /// (inside of [`TryInsertError::Insert`] variant):
    /// - when `K1` key is vacant, but `K2` key already exists with some value;
    /// - when `K1` key already exists with some value, but `K2` key is vacant;
    /// - when both `K1` and `K2` keys already exist with some values, but
    /// point to different entries (values).
    ///
    /// The above mentioned error kinds can be matched through the [`ErrorKind`] enum.
    /// Returned [`InsertError`] structure also contains provided keys and value
    /// that were not inserted and can be used for another purpose.
    ///
    /// # Examples
    ///
    /// ```
    /// use double_map::DHashMap;
    /// use double_map::dhash_map::{TryInsertError, OccupiedError, InsertError, ErrorKind};
    ///
    ///
    /// let mut map = DHashMap::new();
    ///
    /// // Returns mutable reference to the value if keys are vacant
    /// let value = map.try_insert(1, "a", "One").unwrap();
    /// assert_eq!(value, &"One");
    /// *value = "First";
    /// assert_eq!(map.get_key1(&1), Some(&"First"));
    ///
    /// // If the map did have these keys present, and both keys refer to
    /// // the same value, nothing is updated, and the provided value
    /// // is returned inside `Err(TryInsertError::Occupied(_))` variants
    /// map.try_insert(2, "b", "Two");
    /// match map.try_insert(2, "b", "Second") {
    ///     Err(error) => match error {
    ///         TryInsertError::Occupied(OccupiedError{ entry, value }) => {
    ///             assert_eq!(entry.keys(), (&2, &"b"));
    ///             assert_eq!(entry.get(), &"Two");
    ///             assert_eq!(value, "Second");
    ///         }
    ///         _ => unreachable!(),
    ///     }
    ///     _ => unreachable!(),
    /// }
    /// assert_eq!(map.get_key1(&2), Some(&"Two"));
    ///
    /// // Returns `ErrorKind::OccupiedK1AndVacantK2` if `K1` key already
    /// // exists with some value, but `K2` key is vacant. Error structure
    /// // also contains provided keys and value
    /// match map.try_insert(1, "c", "value") {
    ///     Err(error) => match error {
    ///         TryInsertError::Insert(InsertError{ error, keys, value }) => {
    ///             assert_eq!(error, ErrorKind::OccupiedK1AndVacantK2);
    ///             assert_eq!(keys, (1, "c"));
    ///             assert_eq!(value, "value");
    ///         }
    ///         _ => unreachable!()
    ///     }
    ///     _ => unreachable!(),
    /// }
    ///
    /// // Returns `ErrorKind::VacantK1AndOccupiedK2` if `K1` key is vacant,
    /// // but `K2` key already exists with some value.
    /// match map.try_insert(3, "a", "value") {
    ///     Err(error) => match error {
    ///         TryInsertError::Insert(InsertError{ error, .. }) => {
    ///             assert_eq!(error, ErrorKind::VacantK1AndOccupiedK2);
    ///         }
    ///         _ => unreachable!()
    ///     }
    ///     _ => unreachable!(),
    /// }
    ///
    /// // Returns `ErrorKind::KeysPointsToDiffEntries` if both
    /// // `K1` and `K2` keys already exist with some values,
    /// // but point to different entries (values).
    /// match map.try_insert(1, "b", "value") {
    ///     Err(error) => match error {
    ///         TryInsertError::Insert(InsertError{ error, .. }) => {
    ///             assert_eq!(error, ErrorKind::KeysPointsToDiffEntries);
    ///         }
    ///         _ => unreachable!()
    ///     }
    ///     _ => unreachable!(),
    /// }
    /// ```
    #[cfg_attr(feature = "inline-more", inline)]
    pub fn try_insert(
        &mut self,
        k1: K1,
        k2: K2,
        v: V,
    ) -> Result<&mut V, TryInsertError<'_, K1, K2, V, S, A>> {
        match self.entry(k1, k2) {
            Ok(entry) => match entry {
                Entry::Occupied(entry) => {
                    Err(TryInsertError::Occupied(OccupiedError { entry, value: v }))
                }
                Entry::Vacant(entry) => Ok(entry.insert(v)),
            },
            Err(EntryError { error, keys }) => Err(TryInsertError::Insert(InsertError {
                error,
                keys,
                value: v,
            })),
        }
    }

    /// Removes element from the map using a first key `K1`,
    /// returning the value corresponding to the key if the key was
    /// previously in the map. Keeps the allocated memory for reuse.
    ///
    /// The key may be any borrowed form of the map's key type, but
    /// [`Hash`] and [`Eq`] on the borrowed form *must* match those for
    /// the key type.
    ///
    /// # Examples
    ///
    /// ```
    /// use double_map::{DHashMap, dhashmap};
    ///
    /// let mut map = DHashMap::new();
    /// map.insert(1, "One", "Pony");
    ///
    /// // We can see that DHashMap holds one elements
    /// assert_eq!(map.len(), 1);
    ///
    /// // We remove element with key `K1` from the map and get corresponding value
    /// assert_eq!(map.remove_key1(&1), Some("Pony"));
    /// // If we try to remove the same element with key `K1` twice we get None,
    /// // because that element was already removed
    /// assert_eq!(map.remove_key1(&1), None);
    /// // And the map is empty
    /// assert!(map.is_empty());
    /// ```
    #[cfg_attr(feature = "inline-more", inline)]
    pub fn remove_key1<Q1: ?Sized>(&mut self, k1: &Q1) -> Option<V>
    where
        Q1: Hash + Equivalent<K1>,
    {
        // Avoid `Option::map` because it bloats LLVM IR.
        match self.remove_entry_key1(k1) {
            Some((_, _, v)) => Some(v),
            None => None,
        }
    }

    /// Removes element from the map using a second key `K2`,
    /// returning the value corresponding to the key if the key was
    /// previously in the map. Keeps the allocated memory for reuse.
    ///
    /// The key may be any borrowed form of the map's key type, but
    /// [`Hash`] and [`Eq`] on the borrowed form *must* match those for
    /// the key type.
    ///
    /// # Examples
    ///
    /// ```
    /// use double_map::{DHashMap, dhashmap};
    ///
    /// let mut map = DHashMap::new();
    /// map.insert(1, "One", "Pony");
    ///
    /// // We can see that DHashMap holds one elements
    /// assert_eq!(map.len(), 1);
    ///
    /// // We remove element with key `K1` from the map and get corresponding value
    /// assert_eq!(map.remove_key2(&"One"), Some("Pony"));
    /// // If we try to remove the same element with key `K1` twice we get None,
    /// // because that element was already removed
    /// assert_eq!(map.remove_key2(&"One"), None);
    /// // And the map is empty
    /// assert!(map.is_empty());
    /// ```
    #[cfg_attr(feature = "inline-more", inline)]
    pub fn remove_key2<Q2: ?Sized>(&mut self, k2: &Q2) -> Option<V>
    where
        Q2: Hash + Equivalent<K2>,
    {
        // Avoid `Option::map` because it bloats LLVM IR.
        match self.remove_entry_key2(k2) {
            Some((_, _, v)) => Some(v),
            None => None,
        }
    }

    /// Removes element from the map corresponding to the given first `K1`
    /// and second `K2` keys returning the value at the keys, if the keys was
    /// previously in the map and refer to the same value. Keeps the allocated
    /// memory for reuse.
    ///
    /// The key may be any borrowed form of the map's key type, but
    /// [`Hash`] and [`Eq`] on the borrowed form *must* match those for
    /// the key type.
    ///
    /// # Examples
    ///
    /// ```
    /// use double_map::{DHashMap, dhashmap};
    ///
    /// // We create map with three elements
    /// let mut map = dhashmap! {
    ///     1, "One"   => "Pony",
    ///     2, "Two"   => "Horse",
    ///     3, "Three" => "Zebra",
    /// };
    ///
    /// // We can see that DHashMap holds three elements
    /// assert_eq!(map.len(), 3);
    ///
    /// // We remove element from the map and get corresponding value
    /// assert_eq!(map.remove_keys(&1, &"One"), Some("Pony"));
    ///
    /// // If we try to remove the same element with these keys twice we get
    /// // None, because that element was already removed
    /// assert_eq!(map.remove_keys(&1, &"One"), None);
    ///
    /// // And the map contains two element
    /// assert_eq!(map.len(), 2);
    ///
    /// // We get None if both keys don't exist in the map
    /// assert_eq!(map.remove_keys(&4, &"Four"), None);
    ///
    /// // Also we get None if both keys exist but refer to the different value
    /// assert_eq!(map.remove_keys(&2, &"Three"), None);
    /// assert_eq!(map.get_key1(&2), Some(&"Horse"));
    /// assert_eq!(map.get_key2(&"Three"), Some(&"Zebra"));
    /// ```
    #[cfg_attr(feature = "inline-more", inline)]
    pub fn remove_keys<Q1, Q2>(&mut self, k1: &Q1, k2: &Q2) -> Option<V>
    where
        Q1: ?Sized + Hash + Equivalent<K1>,
        Q2: ?Sized + Hash + Equivalent<K2>,
    {
        match self.remove_entry_keys(k1, k2) {
            Some((_, _, v)) => Some(v),
            None => None,
        }
    }

    /// Removes element from the map using a first key `K1`,
    /// returning the stored keys and value if the key was
    /// previously in the map. Keeps the allocated memory
    /// for reuse.
    ///
    /// The key may be any borrowed form of the map's key type, but
    /// [`Hash`] and [`Eq`] on the borrowed form *must* match those for
    /// the key type.
    ///
    /// # Examples
    ///
    /// ```
    /// use double_map::{DHashMap, dhashmap};
    ///
    /// let mut map = DHashMap::new();
    /// map.insert(1, "One", "Pony");
    ///
    /// // We can see that DHashMap holds one elements
    /// assert_eq!(map.len(), 1);
    ///
    /// // We remove element with key `K1` from the map and get corresponding value
    /// assert_eq!(map.remove_entry_key1(&1), Some((1, "One", "Pony")));
    /// // If we try to remove the same element with key `K1` twice we get None,
    /// // because that element was already removed
    /// assert_eq!(map.remove_entry_key1(&1), None);
    /// // And the map is empty
    /// assert!(map.is_empty());
    /// ```
    #[cfg_attr(feature = "inline-more", inline)]
    pub fn remove_entry_key1<Q1: ?Sized>(&mut self, k1: &Q1) -> Option<(K1, K2, V)>
    where
        Q1: Hash + Equivalent<K1>,
    {
        let hash_builder = &self.hash_builder;
        let hash1 = make_hash::<Q1, S>(hash_builder, k1);
        match self.table.find_h1(hash1, equivalent_key1(k1)) {
            Some(bucket) => {
                let (_, k2, _) = unsafe { bucket.as_ref() };
                let hash2 = make_hash::<K2, S>(hash_builder, k2);
                self.table.remove_entry_h2(hash2, equivalent_key2(k2))
            }
            None => None,
        }
    }

    /// Removes element from the map using a second key `K2`,
    /// returning the stored keys and value if the key was
    /// previously in the map. Keeps the allocated memory
    /// for reuse.
    ///
    /// The key may be any borrowed form of the map's key type, but
    /// [`Hash`] and [`Eq`] on the borrowed form *must* match those for
    /// the key type.
    ///
    /// # Examples
    ///
    /// ```
    /// use double_map::{DHashMap, dhashmap};
    ///
    /// let mut map = DHashMap::new();
    /// map.insert(1, "One", "Pony");
    ///
    /// // We can see that DHashMap holds one elements
    /// assert_eq!(map.len(), 1);
    ///
    /// // We remove element with key `K1` from the map and get corresponding value
    /// assert_eq!(map.remove_entry_key2(&"One"), Some((1, "One", "Pony")));
    /// // If we try to remove the same element with key `K1` twice we get None,
    /// // because that element was already removed
    /// assert_eq!(map.remove_entry_key2(&"One"), None);
    /// // And the map is empty
    /// assert!(map.is_empty());
    /// ```
    #[cfg_attr(feature = "inline-more", inline)]
    pub fn remove_entry_key2<Q2: ?Sized>(&mut self, k2: &Q2) -> Option<(K1, K2, V)>
    where
        Q2: Hash + Equivalent<K2>,
    {
        let hash2 = make_hash::<Q2, S>(&self.hash_builder, k2);
        self.table.remove_entry_h2(hash2, equivalent_key2(k2))
    }

    /// Removes element from the map corresponding to the given first `K1`
    /// and second `K2` keys returning the stored keys and value, if the keys was
    /// previously in the map and refer to the same value. Keeps the allocated
    /// memory for reuse.
    ///
    /// The key may be any borrowed form of the map's key type, but
    /// [`Hash`] and [`Eq`] on the borrowed form *must* match those for
    /// the key type.
    ///
    /// # Examples
    ///
    /// ```
    /// use double_map::{DHashMap, dhashmap};
    ///
    /// // We create map with three elements
    /// let mut map = dhashmap! {
    ///     1, "One"   => "Pony",
    ///     2, "Two"   => "Horse",
    ///     3, "Three" => "Zebra",
    /// };
    ///
    /// // We can see that DHashMap holds three elements
    /// assert_eq!(map.len(), 3);
    ///
    /// // We remove element from the map and get corresponding value
    /// assert_eq!(map.remove_entry_keys(&1, &"One"), Some((1, "One", "Pony")));
    ///
    /// // If we try to remove the same element with these keys twice we get
    /// // None, because that element was already removed
    /// assert_eq!(map.remove_entry_keys(&1, &"One"), None);
    ///
    /// // And the map contains two element
    /// assert_eq!(map.len(), 2);
    ///
    /// // We get None if both keys don't exist in the map
    /// assert_eq!(map.remove_entry_keys(&4, &"Four"), None);
    ///
    /// // Also we get None if both keys exist but refer to the different value
    /// assert_eq!(map.remove_entry_keys(&2, &"Three"), None);
    /// assert_eq!(map.get_key1(&2), Some(&"Horse"));
    /// assert_eq!(map.get_key2(&"Three"), Some(&"Zebra"));
    /// ```
    #[cfg_attr(feature = "inline-more", inline)]
    pub fn remove_entry_keys<Q1, Q2>(&mut self, k1: &Q1, k2: &Q2) -> Option<(K1, K2, V)>
    where
        Q1: ?Sized + Hash + Equivalent<K1>,
        Q2: ?Sized + Hash + Equivalent<K2>,
    {
        let hash_builder = &self.hash_builder;
        let hash1 = make_hash::<Q1, S>(hash_builder, k1);
        let hash2 = make_hash::<Q2, S>(hash_builder, k2);
        self.table
            .remove_entry(hash1, equivalent_key1(k1), hash2, equivalent_key2(k2))
    }
}

impl<K1, K2, V, S, A: Allocator + Clone> DHashMap<K1, K2, V, S, A> {
    /// Creates a raw entry builder for the HashMap.
    ///
    /// Raw entries provide the lowest level of control for searching and
    /// manipulating a map. They must be manually initialized with a hash and
    /// then manually searched. After this, insertions into a vacant entry
    /// still require an owned key to be provided.
    ///
    /// Raw entries are useful for such exotic situations as:
    ///
    /// * Hash memoization
    /// * Deferring the creation of an owned key until it is known to be required
    /// * Using a search key that doesn't work with the Borrow trait
    /// * Using custom comparison logic without newtype wrappers
    ///
    /// Because raw entries provide much more low-level control, it's much easier
    /// to put the HashMap into an inconsistent state which, while memory-safe,
    /// will cause the map to produce seemingly random results. Higher-level and
    /// more foolproof APIs like `entry` should be preferred when possible.
    ///
    /// In particular, the hash used to initialized the raw entry must still be
    /// consistent with the hash of the key that is ultimately stored in the entry.
    /// This is because implementations of HashMap may need to recompute hashes
    /// when resizing, at which point only the keys are available.
    ///
    /// Raw entries give mutable access to the keys. This must not be used
    /// to modify how the key would compare or hash, as the map will not re-evaluate
    /// where the key should go, meaning the keys may become "lost" if their
    /// location does not reflect their state. For instance, if you change a key
    /// so that the map now contains keys which compare equal, search may start
    /// acting erratically, with two keys randomly masking each other. Implementations
    /// are free to assume this doesn't happen (within the limits of memory-safety).
    ///
    /// # Examples
    ///
    /// ```
    /// use core::hash::{BuildHasher, Hash};
    /// use double_map::dhash_map::{DHashMap, ErrorKind, RawEntryMut};
    ///
    /// let mut map = DHashMap::new();
    /// map.extend([("a", "one", 100), ("b", "two", 200), ("c", "three", 300)]);
    ///
    /// fn compute_hash<K: Hash + ?Sized, S: BuildHasher>(hash_builder: &S, key: &K) -> u64 {
    ///     use core::hash::Hasher;
    ///     let mut state = hash_builder.build_hasher();
    ///     key.hash(&mut state);
    ///     state.finish()
    /// }
    ///
    /// // Existing key (insert and update)
    /// match map.raw_entry_mut().from_keys(&"a", &"one") {
    ///     Ok(raw_entry) => match raw_entry {
    ///         RawEntryMut::Vacant(_) => panic!(),
    ///         RawEntryMut::Occupied(mut view) => {
    ///             assert_eq!(view.get(), &100);
    ///             let v = view.get_mut();
    ///             let new_v = (*v) * 10;
    ///             *v = new_v;
    ///             assert_eq!(view.insert(1111), 1000);
    ///         }
    ///     },
    ///     Err(_) => panic!(),
    /// }
    ///
    /// assert_eq!(map[&"a"], 1111);
    /// assert_eq!(map.len(), 3);
    ///
    /// // Existing key (take)
    /// let hash1 = compute_hash(map.hasher(), &"c");
    /// let hash2 = compute_hash(map.hasher(), &"three");
    /// match map
    ///     .raw_entry_mut()
    ///     .from_keys_hashed_nocheck(hash1, &"c", hash2, &"three")
    /// {
    ///     Ok(raw_entry) => match raw_entry {
    ///         RawEntryMut::Vacant(_) => panic!(),
    ///         RawEntryMut::Occupied(view) => {
    ///             assert_eq!(view.remove_entry(), ("c", "three", 300));
    ///         }
    ///     },
    ///     Err(_) => panic!(),
    /// }
    /// assert_eq!(map.raw_entry().from_keys(&"c", &"three"), None);
    /// assert_eq!(map.len(), 2);
    ///
    /// // Nonexistent key (insert and update)
    /// let key1 = "d";
    /// let hash1 = compute_hash(map.hasher(), &key1);
    /// let key2 = "four";
    /// let hash2 = compute_hash(map.hasher(), &key2);
    /// match map
    ///     .raw_entry_mut()
    ///     .from_hash(hash1, |q| *q == key1, hash2, |q| *q == key2)
    /// {
    ///     Ok(raw_entry) => match raw_entry {
    ///         RawEntryMut::Occupied(_) => panic!(),
    ///         RawEntryMut::Vacant(view) => {
    ///             let (k1, k2, value) = view.insert("d", "four", 4000);
    ///             assert_eq!((*k1, *k2, *value), ("d", "four", 4000));
    ///             *value = 40000;
    ///         }
    ///     },
    ///     Err(_) => panic!(),
    /// }
    /// assert_eq!(map[&"d"], 40000);
    /// assert_eq!(map.len(), 3);
    ///
    /// match map
    ///     .raw_entry_mut()
    ///     .from_hash(hash1, |q| *q == key1, hash2, |q| *q == key2)
    /// {
    ///     Ok(raw_entry) => match raw_entry {
    ///         RawEntryMut::Vacant(_) => unreachable!(),
    ///         RawEntryMut::Occupied(view) => {
    ///             assert_eq!(view.remove_entry(), ("d", "four", 40000));
    ///         }
    ///     },
    ///     Err(_) => panic!(),
    /// }
    /// assert_eq!(map.get_key1(&"d"), None);
    /// assert_eq!(map.len(), 2);
    ///
    /// // Return `ErrorKind::OccupiedK1AndVacantK2` if `K1` key already
    /// // exists with some value, but `K2` key is vacant.
    /// let error_kind = map.raw_entry_mut().from_keys("a", "five").unwrap_err();
    /// assert_eq!(error_kind, ErrorKind::OccupiedK1AndVacantK2);
    ///
    /// // Return `ErrorKind::VacantK1AndOccupiedK2` if `K1` key is vacant,
    /// // but `K2` key already exists with some value.
    /// let hash1 = compute_hash(map.hasher(), &"e");
    /// let hash2 = compute_hash(map.hasher(), &"two");
    /// let error_kind = map
    ///     .raw_entry_mut()
    ///     .from_keys_hashed_nocheck(hash1, "e", hash2, "two")
    ///     .unwrap_err();
    /// assert_eq!(error_kind, ErrorKind::VacantK1AndOccupiedK2);
    ///
    /// // Return `ErrorKind::KeysPointsToDiffEntries` if both
    /// // `K1` key and `K2` key already exist with some values,
    /// // but point to different entries (values).
    /// let hash1 = compute_hash(map.hasher(), &"a");
    /// let hash2 = compute_hash(map.hasher(), &"two");
    /// let error_kind = map
    ///     .raw_entry_mut()
    ///     .from_hash(hash1, |q| *q == "a", hash2, |q| *q == "two")
    ///     .unwrap_err();
    /// assert_eq!(error_kind, ErrorKind::KeysPointsToDiffEntries);
    /// ```
    #[cfg_attr(feature = "inline-more", inline)]
    pub fn raw_entry_mut(&mut self) -> RawEntryBuilderMut<'_, K1, K2, V, S, A> {
        RawEntryBuilderMut { map: self }
    }

    #[cfg_attr(feature = "inline-more", inline)]
    pub fn raw_entry(&self) -> RawEntryBuilder<'_, K1, K2, V, S, A> {
        RawEntryBuilder { map: self }
    }

    // #[cfg(feature = "raw")]
    #[cfg_attr(feature = "inline-more", inline)]
    pub fn raw_table(&mut self) -> &mut RawTable<(K1, K2, V), A> {
        &mut self.table
    }
}

impl<K1, K2, V, S, A> PartialEq for DHashMap<K1, K2, V, S, A>
where
    K1: Eq + Hash,
    K2: Eq + Hash,
    V: PartialEq,
    S: BuildHasher,
    A: Allocator + Clone,
{
    fn eq(&self, other: &Self) -> bool {
        if self.len() != other.len() {
            return false;
        }

        self.iter().all(|(k1_left, k2_left, v_left)| {
            other
                .get_inner_key1(k1_left)
                .map_or(false, |(_, k2_right, v_right)| {
                    *k2_left == *k2_right && *v_left == *v_right
                })
        })
    }
}

impl<K1, K2, V, S, A> Eq for DHashMap<K1, K2, V, S, A>
where
    K1: Eq + Hash,
    K2: Eq + Hash,
    V: Eq,
    S: BuildHasher,
    A: Allocator + Clone,
{
}

impl<K1, K2, V, S, A> Debug for DHashMap<K1, K2, V, S, A>
where
    K1: Debug,
    K2: Debug,
    V: Debug,
    A: Allocator + Clone,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_map()
            .entries(self.iter().map(|(k1, k2, v)| ((k1, k2), v)))
            .finish()
    }
}

impl<K1, K2, V, S, A> Default for DHashMap<K1, K2, V, S, A>
where
    S: Default,
    A: Default + Allocator + Clone,
{
    #[cfg_attr(feature = "inline-more", inline)]
    fn default() -> Self {
        Self::with_hasher_in(Default::default(), Default::default())
    }
}

impl<K1, K2, Q1: ?Sized, V, S, A> Index<&Q1> for DHashMap<K1, K2, V, S, A>
where
    K1: Eq + Hash,
    K2: Eq + Hash,
    Q1: Hash + Equivalent<K1>,
    S: BuildHasher,
    A: Allocator + Clone,
{
    type Output = V;

    #[cfg_attr(feature = "inline-more", inline)]
    fn index(&self, key: &Q1) -> &V {
        self.get_key1(key).expect("no entry found for key")
    }
}

impl<K1, K2, V, A, const N: usize> From<[(K1, K2, V); N]>
    for DHashMap<K1, K2, V, DefaultHashBuilder, A>
where
    K1: Eq + Hash,
    K2: Eq + Hash,
    A: Default + Allocator + Clone,
{
    fn from(arr: [(K1, K2, V); N]) -> Self {
        Self::from_iter(arr)
    }
}

impl<K1, K2, V, S, A> FromIterator<(K1, K2, V)> for DHashMap<K1, K2, V, S, A>
where
    K1: Eq + Hash,
    K2: Eq + Hash,
    S: BuildHasher + Default,
    A: Default + Allocator + Clone,
{
    #[cfg_attr(feature = "inline-more", inline)]
    fn from_iter<T: IntoIterator<Item = (K1, K2, V)>>(iter: T) -> Self {
        let iter = iter.into_iter();
        let mut map =
            Self::with_capacity_and_hasher_in(iter.size_hint().0, S::default(), A::default());
        iter.for_each(|(k1, k2, v)| {
            map.insert(k1, k2, v);
        });
        map
    }
}

impl<K1, K2, V, S, A> Extend<(K1, K2, V)> for DHashMap<K1, K2, V, S, A>
where
    K1: Eq + Hash,
    K2: Eq + Hash,
    S: BuildHasher,
    A: Allocator + Clone,
{
    #[cfg_attr(feature = "inline-more", inline)]
    fn extend<T: IntoIterator<Item = (K1, K2, V)>>(&mut self, iter: T) {
        // Keys may be already present or show multiple times in the iterator.
        // Reserve the entire hint lower bound if the map is empty.
        // Otherwise reserve half the hint (rounded up), so the map
        // will only resize twice in the worst case.
        let iter = iter.into_iter();
        let reserve = if self.is_empty() {
            iter.size_hint().0
        } else {
            (iter.size_hint().0 + 1) / 2
        };
        self.reserve(reserve);
        iter.for_each(move |(k1, k2, v)| {
            self.insert(k1, k2, v);
        });
    }

    #[inline]
    #[cfg(feature = "nightly")]
    fn extend_one(&mut self, (k1, k2, v): (K1, K2, V)) {
        self.insert(k1, k2, v);
    }

    #[inline]
    #[cfg(feature = "nightly")]
    fn extend_reserve(&mut self, additional: usize) {
        // Keys may be already present or show multiple times in the iterator.
        // Reserve the entire hint lower bound if the map is empty.
        // Otherwise reserve half the hint (rounded up), so the map
        // will only resize twice in the worst case.
        let reserve = if self.is_empty() {
            additional
        } else {
            (additional + 1) / 2
        };
        self.reserve(reserve);
    }
}

impl<'a, K1, K2, V, S, A> Extend<(&'a K1, &'a K2, &'a V)> for DHashMap<K1, K2, V, S, A>
where
    K1: Eq + Hash + Copy,
    K2: Eq + Hash + Copy,
    V: Copy,
    S: BuildHasher,
    A: Allocator + Clone,
{
    #[cfg_attr(feature = "inline-more", inline)]
    fn extend<T: IntoIterator<Item = (&'a K1, &'a K2, &'a V)>>(&mut self, iter: T) {
        self.extend(iter.into_iter().map(|(&k1, &k2, &v)| (k1, k2, v)))
    }
    #[inline]
    #[cfg(feature = "nightly")]
    fn extend_one(&mut self, (k1, k2, v): (&'a K1, &'a K2, &'a V)) {
        self.insert(*k1, *k2, *v);
    }

    #[inline]
    #[cfg(feature = "nightly")]
    fn extend_reserve(&mut self, additional: usize) {
        Extend::<(K1, K2, V)>::extend_reserve(self, additional);
    }
}

/// Inserts all new key-values from the iterator and replaces values with existing
/// keys with new values returned from the iterator.
impl<'a, K1, K2, V, S, A> Extend<&'a (K1, K2, V)> for DHashMap<K1, K2, V, S, A>
where
    K1: Eq + Hash + Copy,
    K2: Eq + Hash + Copy,
    V: Copy,
    S: BuildHasher,
    A: Allocator + Clone,
{
    #[cfg_attr(feature = "inline-more", inline)]
    fn extend<T: IntoIterator<Item = &'a (K1, K2, V)>>(&mut self, iter: T) {
        self.extend(iter.into_iter().map(|&(k1, k2, v)| (k1, k2, v)));
    }

    #[inline]
    #[cfg(feature = "nightly")]
    fn extend_one(&mut self, &(k1, k2, v): &'a (K1, K2, V)) {
        self.insert(k1, k2, v);
    }

    #[inline]
    #[cfg(feature = "nightly")]
    fn extend_reserve(&mut self, additional: usize) {
        Extend::<(K1, K2, V)>::extend_reserve(self, additional);
    }
}

impl<K1, K2, V, S, A: Allocator + Clone> IntoIterator for DHashMap<K1, K2, V, S, A> {
    type Item = (K1, K2, V);
    type IntoIter = IntoIter<K1, K2, V, A>;

    #[cfg_attr(feature = "inline-more", inline)]
    fn into_iter(self) -> IntoIter<K1, K2, V, A> {
        IntoIter {
            inner: self.table.into_iter(),
        }
    }
}

impl<'a, K1, K2, V, S, A: Allocator + Clone> IntoIterator for &'a DHashMap<K1, K2, V, S, A> {
    type Item = (&'a K1, &'a K2, &'a V);
    type IntoIter = Iter<'a, K1, K2, V>;

    #[cfg_attr(feature = "inline-more", inline)]
    fn into_iter(self) -> Iter<'a, K1, K2, V> {
        self.iter()
    }
}

impl<'a, K1, K2, V, S, A: Allocator + Clone> IntoIterator for &'a mut DHashMap<K1, K2, V, S, A> {
    type Item = (&'a K1, &'a K2, &'a mut V);
    type IntoIter = IterMut<'a, K1, K2, V>;

    #[cfg_attr(feature = "inline-more", inline)]
    fn into_iter(self) -> IterMut<'a, K1, K2, V> {
        self.iter_mut()
    }
}

/// Create a [`DHashMap<K1, K2, V, DefaultHashBuilder, Global>`]
/// from a list of sequentially given keys and values.
///
/// Input data list must follow one of these rules:
/// - `K1, K2 => V, K1, K2 => V` ... and so on;
/// - `(K1, K2) => V, (K1, K2) => V` ... and so on.
///
/// Last comma separator can be omitted.
/// If this macros is called without arguments, i.e. like
/// ```
/// # use double_map::{DHashMap, dhashmap};
/// let map: DHashMap<i32, String, String>  = dhashmap![];
/// ```
/// it is equivalent to [`DHashMap::new()`] function
///
/// # Examples
///
/// ```
/// use double_map::{DHashMap, dhashmap};
///
/// // Calling macros without arguments is equivalent to DHashMap::new() function
/// let _map0: DHashMap<i32, i32, i32> = dhashmap![];
///
/// let map = dhashmap!{
///     1, "a" => "One",
///     2, "b" => "Two", // last comma separator can be omitted
/// };
///
/// assert_eq!(map.get_key1(&1),   Some(&"One"));
/// assert_eq!(map.get_key1(&2),   Some(&"Two"));
/// assert_eq!(map.get_key2(&"a"), Some(&"One"));
/// assert_eq!(map.get_key2(&"b"), Some(&"Two"));
///
/// let map2 = dhashmap!{
///     (3, "c") => "Three",
///     (4, "d") => "Four" // last comma separator can be omitted
/// };
///
/// assert_eq!(map2.get_key1(&3),   Some(&"Three"));
/// assert_eq!(map2.get_key1(&4),   Some(&"Four"));
/// assert_eq!(map2.get_key2(&"c"), Some(&"Three"));
/// assert_eq!(map2.get_key2(&"d"), Some(&"Four"));
/// ```
#[macro_export]
macro_rules! dhashmap {
    () => (DHashMap::new());
    ($($key1:expr, $key2:expr => $value:expr),+ $(,)?) => (
        DHashMap::<_, _, _, double_map::dhash_map::DefaultHashBuilder>::from_iter([$(($key1, $key2, $value)),+])
    );
    ($(($key1:expr, $key2:expr) => $value:expr),+ $(,)?) => (
        DHashMap::<_, _, _, double_map::dhash_map::DefaultHashBuilder>::from_iter([$(($key1, $key2, $value)),+])
    );
}
