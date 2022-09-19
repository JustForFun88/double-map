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
    /// Creates an empty [`DHashMap`] using the given allocator.
    ///
    /// The hash map is initially created with a capacity of 0, so it
    /// will not allocate until it is first inserted into.
    ///
    /// # Examples
    ///
    /// ```ignore
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
    /// ```
    #[cfg_attr(feature = "inline-more", inline)]
    pub fn new_in(alloc: A) -> Self {
        Self::with_hasher_in(DefaultHashBuilder::default(), alloc)
    }

    /// Creates an empty [`DHashMap`] with the specified capacity and
    /// [`DefaultHashBuilder`] type of hash builder to hash keys using
    /// the given allocator.
    ///
    /// The hash map will be able to hold at least `capacity` elements without
    /// reallocating. If `capacity` is 0, the hash map will not allocate.
    ///
    /// # Examples
    ///
    /// ```ignore
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
    /// The `hash_builder` passed should implement the [`BuildHasher`] trait for
    /// the [`DHashMap`] to be useful, see its documentation for details.
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
    /// The `hash_builder` passed should implement the [`BuildHasher`] trait for
    /// the [`DHashMap`] to be useful, see its documentation for details.
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

    #[cfg_attr(feature = "inline-more", inline)]
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    #[cfg_attr(feature = "inline-more", inline)]
    pub fn drain(&mut self) -> Drain<'_, K1, K2, V, A> {
        Drain {
            inner: self.table.drain(),
        }
    }

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

    #[cfg_attr(feature = "inline-more", inline)]
    pub fn clear(&mut self) {
        self.table.clear();
    }

    #[inline]
    pub fn into_keys(self) -> IntoKeys<K1, K2, V, A> {
        IntoKeys {
            inner: self.into_iter(),
        }
    }

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
    #[cfg_attr(feature = "inline-more", inline)]
    pub fn reserve(&mut self, additional: usize) {
        self.table.reserve(
            additional,
            make_hasher_key1::<_, K2, V, S>(&self.hash_builder),
            make_hasher_key2::<K1, _, V, S>(&self.hash_builder),
        );
    }

    #[cfg_attr(feature = "inline-more", inline)]
    pub fn try_reserve(&mut self, additional: usize) -> Result<(), TryReserveError> {
        self.table.try_reserve(
            additional,
            make_hasher_key1::<_, K2, V, S>(&self.hash_builder),
            make_hasher_key2::<K1, _, V, S>(&self.hash_builder),
        )
    }

    #[cfg_attr(feature = "inline-more", inline)]
    pub fn shrink_to_fit(&mut self) {
        self.table.shrink_to(
            0,
            make_hasher_key1::<_, K2, V, S>(&self.hash_builder),
            make_hasher_key2::<K1, _, V, S>(&self.hash_builder),
        );
    }

    #[cfg_attr(feature = "inline-more", inline)]
    pub fn shrink_to(&mut self, min_capacity: usize) {
        self.table.shrink_to(
            min_capacity,
            make_hasher_key1::<_, K2, V, S>(&self.hash_builder),
            make_hasher_key2::<K1, _, V, S>(&self.hash_builder),
        );
    }

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

    #[cfg_attr(feature = "inline-more", inline)]
    pub fn contains_key1<Q1: ?Sized>(&self, k1: &Q1) -> bool
    where
        Q1: Hash + Equivalent<K1>,
    {
        self.get_inner_key1(k1).is_some()
    }

    #[cfg_attr(feature = "inline-more", inline)]
    pub fn contains_key2<Q2: ?Sized>(&self, k2: &Q2) -> bool
    where
        Q2: Hash + Equivalent<K2>,
    {
        self.get_inner_key2(k2).is_some()
    }

    #[cfg_attr(feature = "inline-more", inline)]
    pub fn contains_keys<Q1, Q2>(&self, k1: &Q1, k2: &Q2) -> bool
    where
        Q1: ?Sized + Hash + Equivalent<K1>,
        Q2: ?Sized + Hash + Equivalent<K2>,
    {
        self.get_inner_keys(k1, k2).is_some()
    }

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

    pub fn get_many_mut_key1<Q1, const N: usize>(&mut self, ks: [&Q1; N]) -> Option<[&'_ mut V; N]>
    where
        Q1: ?Sized + Hash + Equivalent<K1>,
    {
        self.get_many_mut_inner_key1(ks)
            .map(|arr| arr.map(|(_, _, v)| v))
    }

    pub fn get_many_mut_key2<Q2, const N: usize>(&mut self, ks: [&Q2; N]) -> Option<[&'_ mut V; N]>
    where
        Q2: ?Sized + Hash + Equivalent<K2>,
    {
        self.get_many_mut_inner_key2(ks)
            .map(|arr| arr.map(|(_, _, v)| v))
    }

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

    #[cfg_attr(feature = "inline-more", inline)]
    pub fn remove_entry_key2<Q2: ?Sized>(&mut self, k2: &Q2) -> Option<(K1, K2, V)>
    where
        Q2: Hash + Equivalent<K2>,
    {
        let hash2 = make_hash::<Q2, S>(&self.hash_builder, k2);
        self.table.remove_entry_h2(hash2, equivalent_key2(k2))
    }

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