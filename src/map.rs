#[cfg(test)]
mod tests_double_map;

use core::borrow::Borrow;
use core::convert::From;
use core::default::Default;
use core::fmt::{self, Debug};
use core::hash::{BuildHasher, Hash};
use core::hint::unreachable_unchecked;
use core::iter::{Extend, FromIterator, FusedIterator};
use core::mem;
use core::ops::Index;
use std::collections::{HashMap, hash_map, TryReserveError};

/// A hash map with double keys implemented as wrapper above two
/// [`HashMaps`](`std::collections::HashMap`).
///
/// Internally, two [`HashMap`](`std::collections::HashMap`) are created. One of type
/// `HashMap<K1, (K2, V)>` to hold the `(K2, V)` tuple, and second one of type
/// `HashMap<K2, K1>` just for holding the primary key of type `K1`.
/// We hold the `(K2, V)` tuple inside first `Hashmap` for synchronization purpose,
/// so that we can organize checking that both primary key of type `K1` and the
/// secondary key is of type `K2` refer to the same value, and so on.
/// Keys may be the same or different type.
///
/// By default, [`DHashMap`] as [`HashMap`](`std::collections::HashMap`)
/// uses a hashing algorithm selected to provide
/// resistance against HashDoS attacks. The algorithm is randomly seeded, and a
/// reasonable best-effort is made to generate this seed from a high quality,
/// secure source of randomness provided by the host without blocking the
/// program. Because of this, the randomness of the seed depends on the output
/// quality of the system's random number generator when the seed is created.
/// In particular, seeds generated when the system's entropy pool is abnormally
/// low such as during system boot may be of a lower quality.
///
/// The default hashing algorithm, like in [`HashMap`](`std::collections::HashMap`),
/// is currently SipHash 1-3, though this is
/// subject to change at any point in the future. While its performance is very
/// competitive for medium sized keys, other hashing algorithms will outperform
/// it for small keys like integers as well as large keys like long
/// strings, though those algorithms will typically *not* protect against
/// attacks such as HashDoS.
///
/// The hashing algorithm can be replaced on a per-[`DHashMap`] basis using the
/// [`default`](`std::default::Default::default`), [`with_hasher`](`DHashMap::with_hasher`),
/// and [`with_capacity_and_hasher`](`DHashMap::with_capacity_and_hasher`) methods.
/// There are many alternative [hashing algorithms available on crates.io].
///
/// It is required that the keys implement the [`Eq`] and
/// [`Hash`](`core::hash::Hash`) traits, although
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
/// possible through [`Cell`](`std::cell::Cell`), [`RefCell`](`std::cell::RefCell`),
/// global state, I/O, or unsafe code.
/// The behavior resulting from such a logic error is not specified, but will
/// not result in undefined behavior. This could include panics, incorrect results,
/// aborts, memory leaks, and non-termination.
///
/// [hashing algorithms available on crates.io]: https://crates.io/keywords/hasher

#[derive(Clone, Debug)]
pub struct DHashMap<K1, K2, V, S = hash_map::RandomState> {
    value_map: HashMap<K1, (K2, V), S>,
    key_map: HashMap<K2, K1, S>,
}

impl<K1, K2, V> DHashMap<K1, K2, V, hash_map::RandomState> {
    /// Creates a new empty [`DHashMap`]s with [`RandomState`](std::collections::hash_map::RandomState)
    /// type of hash builder to hash keys.
    ///
    /// The primary key is of type `K1` and the secondary key is of type `K2`.
    /// The value is of type `V`.
    ///
    /// Internally, two [`HashMap`](`std::collections::HashMap`) are created. One of type
    /// `HashMap<K1, (K2, V)>` to hold the `(K2, V)` tuple, and second one of type
    /// `HashMap<K2, K1>` just for holding the primary key of type `K1`.
    /// We hold the `(K2, V)` tuple inside first `Hashmap` for synchronization purpose,
    /// so that we can organize checking both primary key of type `K1` and the
    /// secondary key is of type `K2` refer to the same value, and so on.
    ///
    /// The hash map is initially created with a capacity of 0, so it will not allocate until
    /// it is first inserted into.
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
    /// // And it also allocates some capacity (by default it starts from 3 elements)
    /// assert!(map.capacity() > 1);
    /// ```
    #[inline]
    #[must_use]
    pub fn new() -> DHashMap<K1, K2, V, hash_map::RandomState> {
        DHashMap {
            value_map: HashMap::new(),
            key_map: HashMap::new(),
        }
    }

    /// Creates an empty [`DHashMap`] with the specified capacity.
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
    #[inline]
    #[must_use]
    pub fn with_capacity(capacity: usize) -> DHashMap<K1, K2, V, hash_map::RandomState> {
        DHashMap {
            value_map: HashMap::with_capacity(capacity),
            key_map: HashMap::with_capacity(capacity),
        }
    }
}

impl<K1, K2, V, S> DHashMap<K1, K2, V, S>
where
    S: Clone,
{
    /// Creates an empty [`DHashMap`] which will use the given hash builder to hash
    /// keys.
    ///
    /// The created map has the default initial capacity, witch is equal to 0, so
    /// it will not allocate until it is first inserted into.
    ///
    /// Warning: `hash_builder` is normally randomly generated, and
    /// is designed to allow [`DHashMap`] to be resistant to attacks that
    /// cause many collisions and very poor performance. Setting it
    /// manually using this function can expose a DoS attack vector.
    ///
    /// The `hash_builder` passed should implement the [`BuildHasher`] trait for
    /// the [`DHashMap`] to be useful, see its documentation for details.
    /// It also should implement the [`Clone`] trait because we create two
    /// [`HashMap`]s inside the [`DHashMap`], so that we need to
    /// [`clone`](core::clone::Clone::clone) hash_builder for passing it inside
    /// two inner `HashMaps`.
    ///
    /// # Examples
    ///
    /// ```
    /// use double_map::DHashMap;
    /// use std::collections::hash_map::RandomState;
    ///
    /// let s = RandomState::new();
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
    /// // And it also allocates some capacity (by default it starts from 3 elements)
    /// assert!(map.capacity() > 1);
    /// ```
    #[inline]
    pub fn with_hasher(hash_builder: S) -> DHashMap<K1, K2, V, S> {
        DHashMap {
            value_map: HashMap::with_hasher(hash_builder.clone()),
            key_map: HashMap::with_hasher(hash_builder),
        }
    }

    /// Creates an empty [`DHashMap`] with the specified capacity, using `hash_builder`
    /// to hash the keys.
    ///
    /// The hash map will be able to hold at least `capacity` elements without
    /// reallocating. If `capacity` is 0, the hash map will not allocate.
    ///
    /// Warning: `hash_builder` is normally randomly generated, and
    /// is designed to allow HashMaps to be resistant to attacks that
    /// cause many collisions and very poor performance. Setting it
    /// manually using this function can expose a DoS attack vector.
    ///
    /// The `hash_builder` passed should implement the [`BuildHasher`] trait for
    /// the [`DHashMap`] to be useful, see its documentation for details.
    /// It also should implement the [`Clone`] trait because we create two
    /// [`HashMap`]s inside the [`DHashMap`], so that we need to
    /// [`clone`](core::clone::Clone::clone) hash_builder for passing it inside
    /// two inner `HashMaps`.
    ///
    /// # Examples
    ///
    /// ```
    /// use double_map::DHashMap;
    /// use std::collections::hash_map::RandomState;
    ///
    /// let s = RandomState::new();
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
    #[inline]
    pub fn with_capacity_and_hasher(capacity: usize, hash_builder: S) -> DHashMap<K1, K2, V, S> {
        DHashMap {
            value_map: HashMap::with_capacity_and_hasher(capacity, hash_builder.clone()),
            key_map: HashMap::with_capacity_and_hasher(capacity, hash_builder),
        }
    }
}

impl<K1, K2, V, S> DHashMap<K1, K2, V, S> {
    /// Returns the number of elements the map can hold without reallocating.
    ///
    /// This number is a lower bound; the `DHashMap<K1, K2, V>` collection might
    /// be able to hold more, but is guaranteed to be able to hold at least this many.
    ///
    /// # Note
    ///
    /// Internally [`DHashMap`] use two [`HashMap`](`std::collections::HashMap`). One of type
    /// `HashMap<K1, (K2, V)>` to hold the `(K2, V)` tuple, and second one of type
    /// `HashMap<K2, K1>` just for holding the primary key of type `K1`.
    ///
    /// The [`capacity`](`DHashMap::capacity`) method return the capacity of first
    /// [`HashMap`](`std::collections::HashMap`) of type `HashMap<K1, (K2, V)>`.
    /// So that, if you previously used [`insert_unchecked`](DHashMap::insert_unchecked) method,
    /// the returned capacity may be not equal to actual capacity of second internal
    /// `HashMap<K2, K1>` in case of **unsynchronization** between first keys of type `K1`
    /// and second keys of type `K2`. See [`insert_unchecked`](DHashMap::insert_unchecked)
    /// method documentation for more.
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
    #[inline]
    pub fn capacity(&self) -> usize {
        // we only take it into account because it contains the most important part of
        // hashtable - the value
        self.value_map.capacity()
    }

    /// An iterator visiting all keys in arbitrary order.
    /// The iterator element is tuple of type `(&'a K1, &'a K2)`.
    ///
    /// # Note
    ///
    /// Internally [`DHashMap`] use two [`HashMap`](`std::collections::HashMap`). One of type
    /// `HashMap<K1, (K2, V)>` to hold the `(K2, V)` tuple, and second one of type
    /// `HashMap<K2, K1>` just for holding the primary key of type `K1`.
    ///
    /// Created iterator iterate only through first [`HashMap`](`std::collections::HashMap`)
    /// of type `HashMap<K1, (K2, V)>`.
    /// So that, if you previously used [`insert_unchecked`](DHashMap::insert_unchecked) method,
    /// this method can return false second keys (key #2) in case of **unsynchronization**
    /// between first keys of type `K1` and second keys of type `K2`. See
    /// [`insert_unchecked`](DHashMap::insert_unchecked) method documentation for more.
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
    /// for (key1, key2) in map.keys() {
    ///     println!("key1: {}, key2: {}", key1, key2);
    ///     assert!(
    ///         (key1, key2) == (&"a", &1) ||
    ///         (key1, key2) == (&"b", &2) ||
    ///         (key1, key2) == (&"c", &3)
    ///     );
    /// }
    ///
    /// assert_eq!(map.len(), 3);
    /// ```
    pub fn keys(&self) -> Keys<'_, K1, K2, V> {
        Keys { inner: self.iter() }
    }

    /// Creates a consuming iterator visiting all the keys in arbitrary order.
    /// The map cannot be used after calling this. The iterator element is tuple
    /// of type `(K1, K2)`.
    ///
    /// # Note
    ///
    /// Created iterator contains only content of the first [`HashMap<K1, (K2, V)>`](`std::collections::HashMap`)
    /// which is used underneath of the [`DHashMap`].
    ///
    /// So that, if you previously used [`insert_unchecked`](DHashMap::insert_unchecked) method,
    /// this method can return false second keys (key #2) in case of **unsynchronization**
    /// between first keys of type `K1` and second keys of type `K2`. See
    /// [`insert_unchecked`](DHashMap::insert_unchecked) method documentation for more.
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
    /// // The `IntoKeys` iterator produces keys in arbitrary order, so the
    /// // keys must be sorted to test them against a sorted array.
    /// vec.sort_unstable();
    /// assert_eq!(vec, [("a", 1), ("b", 2), ("c", 3)]);
    /// ```
    #[inline]
    pub fn into_keys(self) -> IntoKeys<K1, K2, V> {
        IntoKeys {
            inner: self.into_iter(),
        }
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
    /// map.insert("a", 1, "One");
    /// map.insert("b", 2, "Two");
    /// map.insert("c", 3, "Three");
    ///
    /// assert_eq!(map.len(), 3);
    ///
    /// for value in map.values() {
    ///     println!("value = {}", value);
    ///     assert!(value == &"One" || value == &"Two" || value == &"Three");
    /// }
    ///
    /// assert_eq!(map.len(), 3);
    /// ```
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
    /// for value in map.values() {
    ///     println!("value = {}", value);
    ///     assert!(value == &11 || value == &12 || value == &13);
    /// }
    ///
    /// assert_eq!(map.len(), 3);
    /// ```
    pub fn values_mut(&mut self) -> ValuesMut<'_, K1, K2, V> {
        ValuesMut {
            inner: self.iter_mut(),
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
    /// // The `IntoValues` iterator produces values in arbitrary order, so
    /// // the values must be sorted to test them against a sorted array.
    /// vec.sort_unstable();
    /// assert_eq!(vec, [10, 20, 30]);
    /// ```
    #[inline]
    pub fn into_values(self) -> IntoValues<K1, K2, V> {
        IntoValues {
            inner: self.into_iter(),
        }
    }

    /// An iterator visiting all keys-value tuples in arbitrary order.
    /// The iterator element is tuple of type `(&'a K1, &'a K2, &'a V)`.
    ///
    /// # Note
    ///
    /// Internally [`DHashMap`] use two [`HashMap`](`std::collections::HashMap`). One of type
    /// `HashMap<K1, (K2, V)>` to hold the `(K2, V)` tuple, and second one of type
    /// `HashMap<K2, K1>` just for holding the primary key of type `K1`.
    ///
    /// Created iterator iterate only through first [`HashMap`](`std::collections::HashMap`)
    /// of type `HashMap<K1, (K2, V)>`.
    /// So that, if you previously used [`insert_unchecked`](DHashMap::insert_unchecked) method,
    /// this method can return false second keys (key #2) in case of **unsynchronization**
    /// between first keys of type `K1` and second keys of type `K2`. See
    /// [`insert_unchecked`](DHashMap::insert_unchecked) method documentation for more.
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
    /// for (key1, key2, value) in map.iter() {
    ///     println!("key1: {}, key2: {}, value: {}", key1, key2, value);
    ///     assert!(
    ///         (key1, key2, value) == (&"a", &1, &"One") ||
    ///         (key1, key2, value) == (&"b", &2, &"Two") ||
    ///         (key1, key2, value) == (&"c", &3, &"Three")
    ///     );
    /// }
    ///
    /// assert_eq!(map.len(), 3);
    /// ```
    pub fn iter(&self) -> Iter<'_, K1, K2, V> {
        Iter {
            base: self.value_map.iter(),
        }
    }

    /// An iterator visiting all keys-value tuples in arbitrary order,
    /// with mutable references to the values.
    /// The iterator element is tuple of type`(&'a K1, &'a K2, &'a mut V)`.
    ///
    /// # Note
    ///
    /// Internally [`DHashMap`] use two [`HashMap`](`std::collections::HashMap`). One of type
    /// `HashMap<K1, (K2, V)>` to hold the `(K2, V)` tuple, and second one of type
    /// `HashMap<K2, K1>` just for holding the primary key of type `K1`.
    ///
    /// Created iterator iterate only through first [`HashMap`](`std::collections::HashMap`)
    /// of type `HashMap<K1, (K2, V)>`.
    /// So that, if you previously used [`insert_unchecked`](DHashMap::insert_unchecked) method,
    /// this method can return false second keys (key #2) in case of **unsynchronization**
    /// between first keys of type `K1` and second keys of type `K2`. See
    /// [`insert_unchecked`](DHashMap::insert_unchecked) method documentation for more.
    ///
    /// # Examples
    ///
    /// ```
    /// use double_map::DHashMap;
    ///
    /// let mut map = DHashMap::new();
    /// map.insert("a", "One",   1);
    /// map.insert("b", "Two",   2);
    /// map.insert("c", "Three", 3);
    ///
    /// assert_eq!(map.len(), 3);
    ///
    /// // Update all values
    /// for (_, _, value) in map.iter_mut() {
    ///     *value *= 2;
    /// }
    ///
    /// for (key1, key2, value) in map.iter() {
    ///     println!("key1: {}, key2: {}, value: {}", key1, key2, value);
    ///     assert!(
    ///         (key1, key2, value) == (&"a", &"One",   &2) ||
    ///         (key1, key2, value) == (&"b", &"Two",   &4) ||
    ///         (key1, key2, value) == (&"c", &"Three", &6)
    ///     );
    /// }
    ///
    /// assert_eq!(map.len(), 3);
    /// ```
    pub fn iter_mut(&mut self) -> IterMut<'_, K1, K2, V> {
        IterMut {
            base: self.value_map.iter_mut(),
        }
    }

    /// Returns the number of elements in the map.
    ///
    /// # Note
    ///
    /// Internally [`DHashMap`] use two [`HashMap`](`std::collections::HashMap`). One of type
    /// `HashMap<K1, (K2, V)>` to hold the `(K2, V)` tuple, and second one of type
    /// `HashMap<K2, K1>` just for holding the primary key of type `K1`.
    ///
    /// The [`len`](`DHashMap::len`) method return the number of elements contained inside first
    /// [`HashMap`](`std::collections::HashMap`) of type `HashMap<K1, (K2, V)>`.
    /// So that, if you previously used [`insert_unchecked`](DHashMap::insert_unchecked) method,
    /// the returned length may be not equal to actual number of elements inside of second internal
    /// `HashMap<K2, K1>` in case of **unsynchronization** between first keys of type `K1`
    /// and second keys of type `K2`. See [`insert_unchecked`](DHashMap::insert_unchecked)
    /// method documentation for more.
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
    #[inline]
    pub fn len(&self) -> usize {
        // we only take it into account because it contains the most important part of
        // hashtable - the value
        self.value_map.len()
    }

    /// Returns `true` if the map contains no elements.
    ///
    /// # Note
    ///
    /// Internally [`DHashMap`] use two [`HashMap`](`std::collections::HashMap`). One of type
    /// `HashMap<K1, (K2, V)>` to hold the `(K2, V)` tuple, and second one of type
    /// `HashMap<K2, K1>` just for holding the primary key of type `K1`.
    ///
    /// The [`is_empty`](`DHashMap::is_empty`) method return the status of first
    /// [`HashMap`](`std::collections::HashMap`) of type `HashMap<K1, (K2, V)>`.
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
    #[inline]
    pub fn is_empty(&self) -> bool {
        // we only take it into account because it contains the most important part of
        // hashtable - the value
        self.value_map.is_empty()
    }

    /// Clears the map, returning all keys-value tuples as an arbitrary
    /// order iterator. The iterator element is tuple of type `(K1, K2, V)`.
    /// Keeps the allocated memory for reuse.
    ///
    /// # Note
    ///
    /// Internally [`DHashMap`] use two [`HashMap`](`std::collections::HashMap`). One of type
    /// `HashMap<K1, (K2, V)>` to hold the `(K2, V)` tuple, and second one of type
    /// `HashMap<K2, K1>` just for holding the primary key of type `K1`.
    ///
    /// Created iterator contain elements only the first [`HashMap`](`std::collections::HashMap`)
    /// of type `HashMap<K1, (K2, V)>`.
    /// So that, if you previously used [`insert_unchecked`](DHashMap::insert_unchecked) method,
    /// this method can return false second keys (key #2) in case of **unsynchronization**
    /// between first keys of type `K1` and second keys of type `K2`. See
    /// [`insert_unchecked`](DHashMap::insert_unchecked) method documentation for more.
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
    /// // But map capacity is equal to old one and can hold at least 23 elements
    /// assert!(a.capacity() == capacity_before_drain && a.capacity() >= 23);
    /// ```
    #[inline]
    pub fn drain(&mut self) -> Drain<'_, K1, K2, V> {
        self.key_map.drain();
        Drain {
            base: self.value_map.drain(),
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
    #[inline]
    pub fn clear(&mut self) {
        self.value_map.clear();
        self.key_map.clear();
    }

    /// Returns a reference to the map's [`BuildHasher`].
    ///
    /// # Examples
    ///
    /// ```
    /// use double_map::DHashMap;
    /// use std::collections::hash_map::RandomState;
    ///
    /// let hasher = RandomState::new();
    /// let map: DHashMap<i32, i32, i32> = DHashMap::with_hasher(hasher);
    /// let hasher: &RandomState = map.hasher();
    /// ```
    #[inline]
    pub fn hasher(&self) -> &S {
        self.value_map.hasher()
    }
}

impl<K1, K2, V, S> DHashMap<K1, K2, V, S>
where
    K1: Eq + Hash,
    K2: Eq + Hash,
    S: BuildHasher,
{
    /// Reserves capacity for at least `additional` more elements to be inserted
    /// in the `DHashMap<K1, K2, V>`. The collection may reserve more space to avoid
    /// frequent reallocations.
    ///
    /// # Panics
    ///
    /// Panics if the new allocation size overflows `usize::Max / 2`.
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
    #[inline]
    pub fn reserve(&mut self, additional: usize) {
        self.value_map.reserve(additional);
        self.key_map.reserve(additional);
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
    /// use std::collections::TryReserveError;
    /// use double_map::DHashMap;
    ///
    /// let mut map: DHashMap<i32, &str, isize> = DHashMap::new();
    /// map.try_reserve(20).expect("something go wrong");
    ///
    /// // So everything is Ok
    /// let capacity = map.capacity();
    /// assert!(capacity >= 20);
    ///
    /// // Let's check that it returns error if it can not reserve asked capacity
    /// let result = map.try_reserve(usize::MAX);
    /// match result {
    ///     Err(_) => println!("It is ok, error was expected"),
    ///     Ok(_) => unreachable!(),
    /// }
    /// // And capacity of the map isn't changed
    /// assert_eq!(map.capacity(), capacity);
    /// ```
    #[inline]
    pub fn try_reserve(&mut self, additional: usize) -> Result<(), TryReserveError> {
        self.value_map.try_reserve(additional)?;
        self.key_map.try_reserve(additional)
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
    #[inline]
    pub fn shrink_to_fit(&mut self) {
        self.value_map.shrink_to_fit();
        self.key_map.shrink_to_fit();
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
    #[inline]
    pub fn shrink_to(&mut self, min_capacity: usize) {
        self.value_map.shrink_to(min_capacity);
        self.key_map.shrink_to(min_capacity);
    }

    /// Returns a reference to the value corresponding to the given primary key `(key #1)`.
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
    pub fn get_key1<Q: ?Sized>(&self, k1: &Q) -> Option<&V>
    where
        K1: Borrow<Q>,
        Q: Hash + Eq,
    {
        match self.value_map.get(k1) {
            Some((_, value)) => Some(value),
            None => None,
        }
    }

    /// Returns a reference to the value corresponding to the given secondary key `(key #2)`.
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
    pub fn get_key2<Q: ?Sized>(&self, k2: &Q) -> Option<&V>
    where
        K2: Borrow<Q>,
        Q: Hash + Eq,
    {
        match self.key_map.get(k2) {
            Some(k1) => match self.value_map.get(k1) {
                Some((_, value)) => Some(value),
                None => None,
            },
            None => None,
        }
    }

    /// Returns a reference to the value corresponding to the given primary key `(key #1)`
    /// and secondary key `(key #2)` if they both exist and refer to the same value.
    ///
    /// The keys may be any borrowed form of the map's keys type, but
    /// [`Hash`] and [`Eq`] on the borrowed form *must* match those for
    /// the keys type.
    ///
    /// # Note
    /// Note that this [`get_keys`](DHashMap::get_keys) method return a reference to the value
    /// only if two keys exist and refer to the same `value`.
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
        K1: Borrow<Q1>,
        K2: Borrow<Q2>,
        Q1: Hash + Eq,
        Q2: Hash + Eq,
    {
        match self.value_map.get_key_value(k1) {
            Some((k1_v, (k2_v, val))) => match self.key_map.get_key_value(k2) {
                Some((k2_k, k1_k)) if k1_v == k1_k && k2_v == k2_k => Some(val),
                _ => None,
            },
            None => None,
        }
    }

    /// Returns the key-value pair corresponding to the supplied primary key `(key #1)`.
    /// Return the tuple of type `(&'a K1, &'a V)`.
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
    /// assert_eq!(map.get_key1_value(&1), Some((&1, &"a")));
    /// assert_eq!(map.get_key1_value(&2), None);
    /// ```
    #[inline]
    pub fn get_key1_value<Q: ?Sized>(&self, k1: &Q) -> Option<(&K1, &V)>
    where
        K1: Borrow<Q>,
        Q: Hash + Eq,
    {
        match self.value_map.get_key_value(k1) {
            Some((key_one, (_, value))) => Some((key_one, value)),
            None => None,
        }
    }

    /// Returns the key-value pair corresponding to the supplied secondary key `(key #2)`.
    /// Return the tuple of type `(&'a K2, &'a V)`.
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
    /// assert_eq!(map.get_key2_value(&10), Some((&10, &"a")));
    /// assert_eq!(map.get_key2_value(&20), None);
    /// ```
    #[inline]
    pub fn get_key2_value<Q: ?Sized>(&self, k2: &Q) -> Option<(&K2, &V)>
    where
        K2: Borrow<Q>,
        Q: Hash + Eq,
    {
        match self.key_map.get_key_value(k2) {
            Some((key_two, key_one)) => match self.value_map.get(key_one) {
                Some((_, value)) => Some((key_two, value)),
                None => None,
            },
            None => None,
        }
    }

    /// Returns a reference to the keys-value tuple corresponding to the given primary
    /// ans secondary keys if they both exist and refer to the same value.
    /// Return tuple of type `(&'a K1, &'a K2, &'a V)`.
    ///
    /// The supplied keys may be any borrowed form of the map's keys type, but
    /// [`Hash`] and [`Eq`] on the borrowed form *must* match those for
    /// the keys type.
    ///
    /// # Note
    ///
    /// Note that this [`get_keys_value`](DHashMap::get_keys_value) method return the
    /// tuple of type`(&'a K1, &'a K2, &'a V)` only if two keys exist and refer to
    /// the same `value`.
    ///
    /// # Example
    ///
    /// ```
    /// use double_map::{DHashMap, dhashmap};
    ///
    /// let map = dhashmap! {
    ///     1, "One"   => "Eins",
    ///     2, "Two"   => "Zwei",
    ///     3, "Three" => "Drei",
    /// };
    ///
    /// // two key exist and refer to the same value ("Eins")
    /// assert_eq!(map.get_keys_value(&1, &"One").unwrap(), (&1, &"One", &"Eins"));
    ///
    /// // Both keys don't exist
    /// assert_eq!(map.get_keys_value(&4, &"Four"), None);
    ///
    /// // Both keys exist but refer to the different value
    /// // (key1: 1 refer to "Eins", key2: "Two" refer to "Zwei")
    /// assert_eq!(map.get_keys_value(&1, &"Two" ), None);
    /// assert_eq!(map.get_key1(&1).unwrap(),     &"Eins");
    /// assert_eq!(map.get_key2(&"Two").unwrap(), &"Zwei");
    /// ```
    #[inline]
    pub fn get_keys_value<Q1: ?Sized, Q2: ?Sized>(&self, k1: &Q1, k2: &Q2) -> Option<(&K1, &K2, &V)>
    where
        K1: Borrow<Q1>,
        K2: Borrow<Q2>,
        Q1: Hash + Eq,
        Q2: Hash + Eq,
    {
        match self.value_map.get_key_value(k1) {
            Some((k1_v, (k2_v, val))) => match self.key_map.get_key_value(k2) {
                Some((k2_k, k1_k)) if k1_v == k1_k && k2_v == k2_k => Some((k1_v, k2_k, val)),
                _ => None,
            },
            None => None,
        }
    }

    /// Returns `true` if the map contains a value for the specified primary key `(key #1)`.
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
    #[inline]
    pub fn contains_key1<Q: ?Sized>(&self, k1: &Q) -> bool
    where
        K1: Borrow<Q>,
        Q: Hash + Eq,
    {
        self.value_map.contains_key(k1)
    }

    /// Returns `true` if the map contains a value for the specified secondary key `(key #2)`.
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
    #[inline]
    pub fn contains_key2<Q: ?Sized>(&self, k2: &Q) -> bool
    where
        K2: Borrow<Q>,
        Q: Hash + Eq,
    {
        self.key_map.contains_key(k2)
    }

    /// Returns `true` if the map contains a value for the specified primary key `(key #1)`
    /// and secondary key `(key #2)` and they both refer to the same value.
    ///
    /// The keys may be any borrowed form of the map's keys type, but
    /// [`Hash`] and [`Eq`] on the borrowed form *must* match those for
    /// the keys type.
    ///
    /// # Note
    /// Note that this [`contains_keys`](DHashMap::contains_keys) method return `true` only
    /// if two keys exist and refer to the same `value`.
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
    #[inline]
    pub fn contains_keys<Q1: ?Sized, Q2: ?Sized>(&self, k1: &Q1, k2: &Q2) -> bool
    where
        K1: Borrow<Q1>,
        K2: Borrow<Q2>,
        Q1: Hash + Eq,
        Q2: Hash + Eq,
    {
        match self.value_map.get_key_value(k1) {
            Some((k1_v, (k2_v, _))) => match self.key_map.get_key_value(k2) {
                Some((k2_k, k1_k)) => k1_v == k1_k && k2_v == k2_k,
                None => false,
            },
            None => false,
        }
    }

    /// Returns a mutable reference to the value corresponding to
    /// the given primary key `(key #1)`.
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
    pub fn get_mut_key1<Q: ?Sized>(&mut self, k1: &Q) -> Option<&mut V>
    where
        K1: Borrow<Q>,
        Q: Hash + Eq,
    {
        match self.value_map.get_mut(k1) {
            Some((_, value)) => Some(value),
            None => None,
        }
    }

    /// Returns a mutable reference to the value corresponding to
    /// the given secondary key `(key #2)`.
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
    pub fn get_mut_key2<Q: ?Sized>(&mut self, k2: &Q) -> Option<&mut V>
    where
        K2: Borrow<Q>,
        Q: Hash + Eq,
    {
        match self.key_map.get(k2) {
            Some(key) => match self.value_map.get_mut(key) {
                Some((_, value)) => Some(value),
                None => None,
            },
            None => None,
        }
    }

    /// Returns a mutable reference to the value corresponding to the given primary key `(key #1)`
    /// and secondary key `(key #2)` if they both exist and refer to the same value.
    ///
    /// The keys may be any borrowed form of the map's keys type, but
    /// [`Hash`] and [`Eq`] on the borrowed form *must* match those for
    /// the keys type.
    ///
    /// # Note
    /// Note that this [`get_mut_keys`](DHashMap::get_mut_keys) method return a reference
    /// to the value only if two keys exist and refer to the same `value`.
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
    pub fn get_mut_keys<Q1: ?Sized, Q2: ?Sized>(&mut self, k1: &Q1, k2: &Q2) -> Option<&mut V>
    where
        K1: Borrow<Q1>,
        K2: Borrow<Q2>,
        Q1: Hash + Eq,
        Q2: Hash + Eq,
    {
        match self.value_map.get_mut(k1) {
            Some((ref k2_v, val)) => match self.key_map.get_key_value(k2) {
                Some((k2_k, k1_k)) if k2_v == k2_k && k1 == k1_k.borrow() => Some(val),
                _ => None,
            },
            None => None,
        }
    }

    /// Removes element from the map using a primary key `(key #1)`,
    /// returning the value corresponding to the key if the key was
    /// previously in the map. Keeps the allocated memory for reuse.
    ///
    /// The key may be any borrowed form of the map's key type, but
    /// [`Hash`] and [`Eq`] on the borrowed form *must* match those for
    /// the key type.
    ///
    /// # Note
    ///
    /// This method removes not only value, but whole element including
    /// primary `K1` and secondary `K2` keys.
    ///
    /// # Examples
    ///
    /// ```
    /// use double_map::{DHashMap, dhashmap};
    ///
    /// // We create map with three elements
    /// let mut map = dhashmap! {
    ///     1, "One"   => String::from("Eins"),
    ///     2, "Two"   => String::from("Zwei"),
    ///     3, "Three" => String::from("Drei"),
    /// };
    ///
    /// // We can see that DHashMap holds three elements
    /// assert!(map.len() == 3 && map.capacity() >= 3);
    ///
    /// // Also we reserve memory for holding additionally at least 20 elements,
    /// // so that DHashMap can hold 23 elements or more
    /// map.reserve(20);
    /// let capacity_before_remove = map.capacity();
    ///
    /// // We remove element with key #1 from the map and get corresponding value
    /// assert_eq!(map.remove_key1(&1), Some("Eins".to_owned()));
    /// // If we try to remove the same element with key #1 twice we get None,
    /// // because that element was already removed
    /// assert_eq!(map.remove_key1(&1), None);
    ///
    /// // Now we remove all elements one by one, and can see that map holds nothing
    /// map.remove_key1(&2);
    /// map.remove_key1(&3);
    /// assert_eq!(map.len(), 0);
    ///
    /// // But map capacity is equal to the old one and can hold at least 23 elements
    /// assert!(map.capacity() == capacity_before_remove && map.capacity() >= 23);
    /// ```
    #[inline]
    pub fn remove_key1<Q: ?Sized>(&mut self, k1: &Q) -> Option<V>
    where
        K1: Borrow<Q>,
        Q: Hash + Eq,
    {
        match self.value_map.remove(k1) {
            Some((key, value)) => {
                self.key_map.remove(&key);
                Some(value)
            }
            None => None,
        }
    }

    /// Removes element from the map using a secondary key `(key #2)`,
    /// returning the value corresponding to the key if the key was
    /// previously in the map. Keeps the allocated memory for reuse.
    ///
    /// The key may be any borrowed form of the map's key type, but
    /// [`Hash`] and [`Eq`] on the borrowed form *must* match those for
    /// the key type.
    ///
    /// # Note
    ///
    /// This method removes not only value, but whole element including
    /// primary `K1` and secondary `K2` keys.
    ///
    /// # Examples
    ///
    /// ```
    /// use double_map::{DHashMap, dhashmap};
    ///
    /// // We create map with three elements
    /// let mut map = dhashmap! {
    ///     1, "One"   => String::from("Eins"),
    ///     2, "Two"   => String::from("Zwei"),
    ///     3, "Three" => String::from("Drei"),
    /// };
    ///
    /// // We can see that DHashMap holds three elements
    /// assert!(map.len() == 3 && map.capacity() >= 3);
    ///
    /// // Also we reserve memory for holding additionally at least 20 elements,
    /// // so that DHashMap can hold 23 elements or more
    /// map.reserve(20);
    /// let capacity_before_remove = map.capacity();
    ///
    /// // We remove element with key #1 from the map and get corresponding value
    /// assert_eq!(map.remove_key2(&"One"), Some("Eins".to_owned()));
    /// // If we try to remove the same element with key #1 twice we get None,
    /// // because that element was already removed
    /// assert_eq!(map.remove_key2(&"One"), None);
    ///
    /// // Now we remove all elements one by one, and can see that map holds nothing
    /// map.remove_key2(&"Two");
    /// map.remove_key2(&"Three");
    /// assert_eq!(map.len(), 0);
    ///
    /// // But map capacity is equal to the old one and can hold at least 23 elements
    /// assert!(map.capacity() == capacity_before_remove && map.capacity() >= 23);
    /// ```
    #[inline]
    pub fn remove_key2<Q: ?Sized>(&mut self, k2: &Q) -> Option<V>
    where
        K2: Borrow<Q>,
        Q: Hash + Eq,
    {
        match self.key_map.remove(k2) {
            Some(key) => match self.value_map.remove(&key) {
                Some((_, value)) => Some(value),
                None => None,
            },
            None => None,
        }
    }

    /// Removes element from the map corresponding to the given primary key `(key #1)`
    /// and secondary key `(key #2)` returning the value at the keys if the keys was
    /// previously in the map and refer to the same value. Keeps the allocated memory
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
    /// // We create map with three elements
    /// let mut map = dhashmap! {
    ///     1, "One"   => String::from("Eins"),
    ///     2, "Two"   => String::from("Zwei"),
    ///     3, "Three" => String::from("Drei"),
    /// };
    ///
    /// // We can see that DHashMap holds three elements
    /// assert!(map.len() == 3 && map.capacity() >= 3);
    ///
    /// // Also we reserve memory for holding additionally at least 20 elements,
    /// // so that DHashMap can hold 23 elements or more
    /// map.reserve(20);
    /// let capacity_before_remove = map.capacity();
    ///
    /// // We remove element from the map and get corresponding value
    /// assert_eq!(map.remove_keys(&1, &"One"), Some("Eins".to_owned()));
    /// // If we try to remove the same element with these keys twice we get None,
    /// // because that element was already removed
    /// assert_eq!(map.remove_keys(&1, &"One"), None);
    ///
    /// // We get None if both keys don't exist in the map
    /// assert_eq!(map.remove_keys(&4, &"Four"), None);
    /// // Also we get None if both keys exist but refer to the different value
    /// assert_eq!(map.remove_keys(&2, &"Three"), None);
    /// assert_eq!(map.get_key1(&2).unwrap(),     "Zwei");
    /// assert_eq!(map.get_key2(&"Three").unwrap(), "Drei");
    ///
    /// // Now we remove all elements one by one, and can see that map holds nothing
    /// map.remove_keys(&2, &"Two");
    /// map.remove_keys(&3, &"Three");
    /// assert_eq!(map.len(), 0);
    ///
    /// // But map capacity is equal to the old one and can hold at least 23 elements
    /// assert!(map.capacity() == capacity_before_remove && map.capacity() >= 23);
    /// ```
    #[inline]
    pub fn remove_keys<Q1: ?Sized, Q2: ?Sized>(&mut self, k1: &Q1, k2: &Q2) -> Option<V>
    where
        K1: Borrow<Q1>,
        K2: Borrow<Q2>,
        Q1: Hash + Eq,
        Q2: Hash + Eq,
    {
        match self.value_map.get_key_value(k1) {
            Some((k1_v, (k2_v, _))) => match self.key_map.get_key_value(k2) {
                Some((k2_k, k1_k)) if k1_v == k1_k && k2_v == k2_k => {
                    self.key_map.remove(k2);
                    match self.value_map.remove(k1) {
                        Some((_, value)) => Some(value),
                        None => None,
                    }
                }
                _ => None,
            },
            None => None,
        }
    }
}

impl<K1, K2, V, S> DHashMap<K1, K2, V, S>
where
    K1: Eq + Hash + Clone,
    K2: Eq + Hash + Clone,
    S: BuildHasher,
{
    /// Tries to get the given keys' corresponding entry in the map for in-place
    /// manipulation.
    ///
    /// Returns [`Entry`] enum if `all` of the following is `true`:
    /// - Both key #1 and key #2 are vacant.
    /// - If both key #1 and key #2 exist, they refer to the same value.
    ///
    /// When the above statements are `false`, [`entry`](DHashMap::entry) method returns
    /// [`EntryError`] structure which contains the [`ErrorKind`] enum, and the values
    /// of provided keys that were not used for creation entry (that can be used for
    /// another purpose).
    ///
    /// Depending on the points below, different [`ErrorKind`] variants may be returned:
    /// - When key #1 is vacant, but key #2 already exists with some value, the
    /// returned [`ErrorKind`] variant is [`ErrorKind::VacantK1AndOccupiedK2`].
    /// - When key #1 already exists with some value, but key #2 is vacant, the
    /// returned [`ErrorKind`] variant is [`ErrorKind::OccupiedK1AndVacantK2`].
    /// - When both key #1 and key #2 already exist with some values, but point
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
    /// // Return `ErrorKind::OccupiedK1AndVacantK2` if key #1 already
    /// // exists with some value, but key #2 is vacant.
    /// let error_kind = letters.entry('s', 'y').unwrap_err().error;
    /// assert_eq!(error_kind, ErrorKind::OccupiedK1AndVacantK2);
    ///
    /// // Return `ErrorKind::VacantK1AndOccupiedK2` if key #1 is vacant,
    /// // but key #2 already exists with some value.
    /// let error_kind = letters.entry('y', 's').unwrap_err().error;
    /// assert_eq!(error_kind, ErrorKind::VacantK1AndOccupiedK2);
    ///
    /// // Return `ErrorKind::KeysPointsToDiffEntries` if both
    /// // key #1 and key #2 already exist with some values,
    /// // but point to different entries (values).
    /// let error_kind = letters.entry('s', 't').unwrap_err().error;
    /// assert_eq!(error_kind, ErrorKind::KeysPointsToDiffEntries);
    /// ```
    #[inline]
    pub fn entry(&mut self, k1: K1, k2: K2) -> Result<Entry<'_, K1, K2, V>, EntryError<K1, K2>> {
        // I don't like the way this function is done. But it looks like Hashmap::entry
        // (which internally uses hashbrown::rustc_entry::HashMap::rustc_entry) calls
        // self.reserve(1) when no key is found (vacant). It seems this one will lead
        // to constant allocation and deallocation, given that value_map.entry and
        // key_map.entry may not be vacant and occupied at the same time, so I'll
        // leave the implementation this way for now
        match self.value_map.get(&k1) {
            None => match self.key_map.get(&k2) {
                None => {
                    // SAFETY: We already check that both key vacant
                    Ok(unsafe { self.map_vacant_entry(k1, k2) })
                }
                // Error: Vacant key #1 of type K1 and occupied key # 2 of type K2
                Some(_) => Err(EntryError {
                    error: ErrorKind::VacantK1AndOccupiedK2,
                    keys: (k1, k2),
                }),
            },
            Some((key2_exist, _)) => match self.key_map.get(&k2) {
                Some(key1_exist) => {
                    return if k1 == *key1_exist && k2 == *key2_exist {
                        // SAFETY: We already check that both key exist and refer to the same value
                        Ok(unsafe { self.map_occupied_entry(k1, k2) })
                    } else {
                        // Error: key #1 and key # 2 refer to different entries / values
                        Err(EntryError {
                            error: ErrorKind::KeysPointsToDiffEntries,
                            keys: (k1, k2),
                        })
                    };
                }
                None => Err(EntryError {
                    error: ErrorKind::OccupiedK1AndVacantK2,
                    keys: (k1, k2),
                }),
            },
        }
    }

    // This function used only inside this crate. Return Entry::Occupied
    // because we know exactly that both entry are occupied
    #[inline(always)]
    unsafe fn map_occupied_entry(&mut self, k1: K1, k2: K2) -> Entry<'_, K1, K2, V> {
        let raw_v = self.value_map.entry(k1);
        let raw_k = self.key_map.entry(k2);
        match raw_v {
            hash_map::Entry::Occupied(base_v) => match raw_k {
                hash_map::Entry::Occupied(base_k) => {
                    Entry::Occupied(OccupiedEntry { base_v, base_k })
                }
                _ => unreachable_unchecked(),
            },
            _ => unreachable_unchecked(),
        }
    }

    // This function used only inside this crate. Return Entry::Vacant
    // because we know exactly that both entry are vacant
    #[inline(always)]
    unsafe fn map_vacant_entry(&mut self, k1: K1, k2: K2) -> Entry<'_, K1, K2, V> {
        let raw_v = self.value_map.entry(k1);
        let raw_k = self.key_map.entry(k2);
        match raw_v {
            hash_map::Entry::Vacant(base_v) => match raw_k {
                hash_map::Entry::Vacant(base_k) => Entry::Vacant(VacantEntry { base_v, base_k }),
                _ => unreachable_unchecked(),
            },
            _ => unreachable_unchecked(),
        }
    }

    /// Inserts given keys and value into the map **`without checking`**. Update the value
    /// if key #1 of type `K1` already presents with returning old value.
    ///
    /// If the map did not have these keys present, [`None`] is returned.
    ///
    /// # Warning
    ///
    /// **Using this method can lead to unsynchronization between key #1 and key #1,
    /// so that they can refer to different values.** It also can lead to different
    /// quantity of keys, so that quantity of keys #2 `K2` can be ***less*** than
    /// quantity of keys #1 `K1`.
    ///
    /// If the map did have these keys vacant or **present** and **both keys refer to
    /// the same value** it is ***Ok***, the value is updated, and the old value is
    /// returned inside `Some(V)` variant.
    ///
    /// **But** for this method, it doesn't matter if key # 2 exists or not,
    /// it returns updated value also if the map contains only key #1.
    /// It is ***because*** this method **doesn't check** that:
    /// - key #1 is vacant, but key #2 already exists with some value;
    /// - key #1 already exists with some value, but key #2 is vacant;
    /// - both key #1 and key #2 already exist with some values, but
    /// point to different entries (values).
    ///
    /// The keys are not updated, though; this matters for types that can
    /// be `==` without being identical. See the [std module-level documentation]
    /// for more.
    ///
    /// # Note
    ///
    /// Using this method is cheaper than using another insertion
    /// [`entry`](DHashMap::entry), [`insert`](DHashMap::insert) and
    /// [`try_insert`](DHashMap::try_insert) methods.
    ///
    /// Links between keys #1 `K1` and the values that they refer are adequate.
    /// **Unsynchronization** between key #1 and key #2, lead only to that the key # 2
    /// may refer to unexpected value.
    ///
    /// It is recommended to use this method only if you are sure that
    /// key #1 and key #2 are unique. For example if key #1 of type `K1` is generated
    /// automatically and you check only that there is no key #2 of type `K2`.
    ///
    /// [std module-level documentation]: std::collections#insert-and-complex-keys
    ///
    /// # Examples
    ///
    /// ```
    /// use double_map::DHashMap;
    /// use core::hash::Hash;
    ///
    /// let mut map = DHashMap::new();
    ///
    /// // Returns None if keys are vacant
    /// assert_eq!(map.insert_unchecked(1, "a", "One"), None);
    /// assert_eq!(map.is_empty(), false);
    ///
    /// // If the map did have these keys present, the value is updated,
    /// // and the old value is returned inside `Some(V)` variants
    /// map.insert_unchecked(2, "b", "Two");
    /// assert_eq!(map.insert_unchecked(2, "b", "Second"), Some("Two"));
    /// assert_eq!(map.get_key1(&2), Some(&"Second"));
    ///
    /// // But method does not care about key #2
    /// assert_eq!(map.insert_unchecked(1, "b", "First"), Some("One"));
    /// // So key # 2 refers to unexpected value, and now we have double second keys
    /// // referring to the same value
    /// assert_eq!(map.get_key2(&"a"), Some(&"First"));
    /// assert_eq!(map.get_key2(&"b"), Some(&"First"));
    ///
    /// // But it can be safe if you generate one key automatically, and check
    /// // existence only other key. It can be for example like that:
    /// #[derive(Copy, Clone, PartialEq, Eq, Hash)]
    /// pub struct PupilID(usize);
    ///
    /// pub struct Pupil {
    ///     name: String
    /// }
    ///
    /// pub struct Class {
    ///     pupils: DHashMap<PupilID, String, Pupil>,
    ///     len: usize,
    /// }
    ///
    /// impl Class {
    ///     pub fn new() -> Class {
    ///         Self{
    ///             pupils: DHashMap::new(),
    ///             len: 0
    ///         }
    ///     }
    ///     pub fn contains_name(&self, name: &String) -> bool {
    ///         self.pupils.get_key2(name).is_some()
    ///     }
    ///     pub fn add_pupil(&mut self, name: String) -> Option<PupilID> {
    ///         if !self.contains_name(&name) {
    ///             let len = &mut self.len;
    ///             let id = PupilID(*len);
    ///             self.pupils.insert_unchecked( id, name.clone(), Pupil { name } );
    ///             *len += 1;
    ///             Some(id)
    ///         } else {
    ///             None
    ///         }
    ///     }
    /// }
    /// ```
    #[inline]
    pub fn insert_unchecked(&mut self, k1: K1, k2: K2, v: V) -> Option<V> {
        self.key_map.insert(k2.clone(), k1.clone());
        match self.value_map.insert(k1, (k2, v)) {
            Some((_, v)) => Some(v),
            None => None,
        }
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
    /// - when key #1 is vacant, but key #2 already exists with some value;
    /// - when key #1 already exists with some value, but key #2 is vacant;
    /// - when both key #1 and key #2 already exist with some values, but
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
    #[inline]
    pub fn insert(&mut self, k1: K1, k2: K2, v: V) -> Option<Result<V, InsertError<K1, K2, V>>> {
        match self.entry(k1, k2) {
            Ok(entry) => match entry {
                Entry::Occupied(mut entry) => {
                    let v = entry.insert(v);
                    Some(Ok(v))
                }
                Entry::Vacant(entry) => {
                    entry.insert(v);
                    None
                }
            },
            Err(EntryError { error, keys }) => Some(Err(InsertError {
                error,
                keys,
                value: v,
            })),
        }
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
    /// - when key #1 is vacant, but key #2 already exists with some value;
    /// - when key #1 already exists with some value, but key #2 is vacant;
    /// - when both key #1 and key #2 already exist with some values, but
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
    /// // Returns `ErrorKind::OccupiedK1AndVacantK2` if key #1 already
    /// // exists with some value, but key #2 is vacant. Error structure
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
    /// // Returns `ErrorKind::VacantK1AndOccupiedK2` if key #1 is vacant,
    /// // but key #2 already exists with some value.
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
    /// // key #1 and key #2 already exist with some values,
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
    #[inline]
    pub fn try_insert(
        &mut self,
        k1: K1,
        k2: K2,
        v: V,
    ) -> Result<&mut V, TryInsertError<K1, K2, V>> {
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
}

/// Create a `DHashMap<K1, K2, V, `[`RandomState`](std::collections::hash_map::RandomState)`>`
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
        DHashMap::<_, _, _, std::collections::hash_map::RandomState>::from_iter([$(($key1, $key2, $value)),+])
    );
    ($(($key1:expr, $key2:expr) => $value:expr),+ $(,)?) => (
        DHashMap::<_, _, _, std::collections::hash_map::RandomState>::from_iter([$(($key1, $key2, $value)),+])
    );
}

/// Equality comparisons which are
/// [partial equivalence relations](https://en.wikipedia.org/wiki/Partial_equivalence_relation).
///
/// `x.eq(y)` can also be written `x == y`, and `x.ne(y)` can be written `x != y`.
///
/// ## Note
///
/// Internally [`DHashMap`] use two [`HashMap`](`std::collections::HashMap`). One of type
/// `HashMap<K1, (K2, V)>` to hold the `(K2, V)` tuple, and second one of type
/// `HashMap<K2, K1>` just for holding the primary key of type `K1`.
///
/// Two maps `m: DHashMap<K1, K2, V, S>` and `n: DHashMap<K1, K2, V, S>` may be equal `m == n`
/// only if (a) both `HashMap<K1, (K2, V)>` equal each other and (b) both `HashMap<K2, K1>`
/// also equal each other.
///
/// This means that, if you previously used [`insert_unchecked`](DHashMap::insert_unchecked) method,
/// this equality comparisons can return `false` in case of **unsynchronization**
/// between first keys of type `K1` and second keys of type `K2`. See
/// [`insert_unchecked`](DHashMap::insert_unchecked) method documentation for more.
///
/// # Examples
///
/// ```
/// use double_map::{DHashMap, dhashmap};
///
/// let mut map1: DHashMap<i32, &str, &str> = dhashmap!{
///     1, "a" => "One",
///     2, "b" => "Two",
///     3, "c" => "Three",
/// };
///
/// let mut map2: DHashMap<i32, &str, &str> = dhashmap!{
///     1, "a" => "One",
///     2, "b" => "Two",
///     3, "c" => "Three",
/// };
/// // Now map1 and map2 equal each other
/// assert_eq!(map1, map2);
///
/// // But insert_unchecked method does not care that two keys refer to the same value,
/// map2.insert_unchecked(1, "b", "One");
/// // so key # 2 refers to unexpected value, and now we have double second keys
/// // referring to the same value
/// assert_eq!(map2.get_key2(&"a"), Some(&"One"));
/// assert_eq!(map2.get_key2(&"b"), Some(&"One"));
///
/// // So that two map don't equal each other,
/// assert_ne!(map1, map2);
/// // even if all values and first keys equal each other
/// assert_eq!(map1.get_key1(&1), map2.get_key1(&1));
/// assert_eq!(map1.get_key1(&2), map2.get_key1(&2));
/// assert_eq!(map1.get_key1(&3), map2.get_key1(&3));
/// ```
impl<K1, K2, V, S> PartialEq for DHashMap<K1, K2, V, S>
where
    K1: Eq + Hash,
    K2: Eq + Hash,
    V: PartialEq,
    S: BuildHasher,
{
    fn eq(&self, other: &DHashMap<K1, K2, V, S>) -> bool {
        let DHashMap {
            value_map: lv_map,
            key_map: lk_map,
        } = self;
        let DHashMap {
            value_map: rv_map,
            key_map: rk_map,
        } = other;
        if lv_map.len() != rv_map.len() && lk_map.len() != rk_map.len() {
            return false;
        }
        lv_map
            .iter()
            .all(|(k1, tuple)| rv_map.get(k1).map_or(false, |tup| *tuple == *tup))
            && lk_map
                .iter()
                .all(|(k1, k2)| rk_map.get(k1).map_or(false, |k| *k2 == *k))
    }
}

impl<K1, K2, V, S> Eq for DHashMap<K1, K2, V, S>
where
    K1: Eq + Hash,
    K2: Eq + Hash,
    V: Eq,
    S: BuildHasher,
{
}

/// Creates an empty `DHashMap<K1, K2, V, S>`, with the `Default` value for the hasher.
impl<K1, K2, V, S> Default for DHashMap<K1, K2, V, S>
where
    S: Default + Clone,
{
    /// Creates an empty `DHashMap<K1, K2, V, S>`, with the `Default` value for the hasher.
    ///
    /// # Examples
    ///
    /// ```
    /// use double_map::DHashMap;
    /// use std::collections::hash_map::RandomState;
    ///
    /// // You need to specify all types of DHashMap, including hasher.
    /// // Created map is empty and don't allocate memory
    /// let map: DHashMap<u32, String, String, RandomState> = Default::default();
    /// assert_eq!(map.capacity(), 0);
    /// let map: DHashMap<u32, String, String, RandomState> = DHashMap::default();
    /// assert_eq!(map.capacity(), 0);
    /// ```
    #[inline]
    fn default() -> DHashMap<K1, K2, V, S> {
        DHashMap::with_hasher(Default::default())
    }
}

/// Get a reference to the value through indexing operations (`DHashMap[index]`)
/// in immutable contexts.
impl<K1, K2, Q: ?Sized, V, S> Index<&Q> for DHashMap<K1, K2, V, S>
where
    K1: Eq + Hash + Borrow<Q>,
    K2: Eq + Hash,
    Q: Eq + Hash,
    S: BuildHasher,
{
    type Output = V;

    /// Returns a reference to the value corresponding to the supplied primary key `(key #1)`.
    ///
    /// The key may be any borrowed form of the map's key type, but
    /// [`Hash`] and [`Eq`] on the borrowed form *must* match those for
    /// the key type.
    ///
    /// # Panics
    ///
    /// Panics if the key is not present in the `DHashMap`.
    ///
    /// # Examples
    ///
    /// ```
    /// use double_map::{DHashMap, dhashmap};
    ///
    /// let map = dhashmap!{
    ///     1, "a" => "One",
    ///     2, "b" => "Two",
    /// };
    ///
    /// assert_eq!(map[&1], "One");
    /// assert_eq!(map[&2], "Two");
    /// ```
    #[inline]
    fn index(&self, key: &Q) -> &V {
        self.get_key1(key).expect("no entry found for key")
    }
}

/// Create a new `DHashMap<K1, K2, V, `[`RandomState`](std::collections::hash_map::RandomState)`>`
/// from an array list of sequentially given keys and values.
impl<K1, K2, V, const N: usize> From<[(K1, K2, V); N]>
    for DHashMap<K1, K2, V, hash_map::RandomState>
where
    K1: Eq + Hash + Clone,
    K2: Eq + Hash + Clone,
{
    /// # Examples
    ///
    /// ```
    /// use double_map::DHashMap;
    ///
    /// let map1 = DHashMap::from([(1, 2, 3), (4, 5, 6)]);
    /// let map2: DHashMap<_, _, _> = [(1, 2, 3), (4, 5, 6)].into();
    /// assert_eq!(map1, map2);
    /// ```
    fn from(arr: [(K1, K2, V); N]) -> Self {
        Self::from_iter(arr)
    }
}

/// Creates an new `DHashMap<K1, K2, V, S>`, with the `Default` value
/// for the hasher from from an iterator.
impl<K1, K2, V, S> FromIterator<(K1, K2, V)> for DHashMap<K1, K2, V, S>
where
    K1: Eq + Hash + Clone,
    K2: Eq + Hash + Clone,
    S: BuildHasher + Default + Clone,
{
    /// Creates an new `DHashMap<K1, K2, V, [`RandomState`]>`, with the `Default` value
    /// for the hasher from from an iterator.
    ///
    /// You need to specify the type of `hasher`
    ///
    /// # Examples
    ///
    /// ```
    /// use double_map::DHashMap;
    /// use std::collections::hash_map::RandomState;
    ///
    /// let mut number = 0;
    /// let some_iter = std::iter::repeat_with(move || {
    ///     number +=1;
    ///     (number, number, number * 10)
    /// }).take(5);
    /// // You need to specify hasher
    /// let map: DHashMap<_, _, _, RandomState> = DHashMap::from_iter(some_iter.clone());
    /// assert_eq!(map.get_key1(&1), Some(&10));
    /// assert_eq!(map.get_key1(&5), Some(&50));
    /// assert_eq!(map.get_key1(&6), None);
    ///
    /// let some_vec: Vec<_> = some_iter.collect();
    /// let map: DHashMap<_, _, _, RandomState> = DHashMap::from_iter(some_vec);
    /// assert_eq!(map.get_key1(&1), Some(&10));
    /// assert_eq!(map.get_key1(&5), Some(&50));
    /// assert_eq!(map.get_key1(&6), None);
    ///
    /// let some_arr = [(1, 1, 10), (2, 2, 20), (3, 3, 30), (4, 4, 40), (5, 5, 50)];
    /// let map: DHashMap<_, _, _, RandomState> = DHashMap::from_iter(some_arr);
    /// assert_eq!(map.get_key1(&1), Some(&10));
    /// assert_eq!(map.get_key1(&5), Some(&50));
    /// assert_eq!(map.get_key1(&6), None);
    /// ```
    fn from_iter<T: IntoIterator<Item = (K1, K2, V)>>(iter: T) -> DHashMap<K1, K2, V, S> {
        let mut map = DHashMap::with_hasher(Default::default());
        map.extend(iter);
        map
    }
}

/// Inserts all new keys and values from the iterator to existing `DHashMap<K1, K2, V, S>`.
impl<K1, K2, V, S> Extend<(K1, K2, V)> for DHashMap<K1, K2, V, S>
where
    K1: Eq + Hash + Clone,
    K2: Eq + Hash + Clone,
    S: BuildHasher,
{
    /// Inserts all new keys and values from the iterator to existing `DHashMap<K1, K2, V, S>`.
    ///
    /// Replace values with existing keys with new values returned from the iterator.
    ///
    /// # Examples
    ///
    /// ```
    /// use double_map::DHashMap;
    ///
    /// // Let's create `DHashMap` with std::collections::hash_map::RandomState hasher
    /// let mut map = DHashMap::new();
    /// map.insert(1, 1, 999);
    ///
    /// let mut number = 0;
    /// let some_iter = std::iter::repeat_with(move || {
    ///     number +=1;
    ///     (number, number, number * 10)
    /// }).take(5);
    ///
    /// // You don't need to specify the hasher
    /// map.extend(some_iter);
    /// // Replace values with existing keys with new values returned from the iterator.
    /// // So that the map.get_key1(&1) doesn't return Some(&999).
    /// assert_eq!(map.get_key1(&1), Some(&10));
    ///
    /// let some_vec: Vec<_> = std::iter::repeat_with(move || {
    ///     number +=100;
    ///     (number, number, number * 10)
    /// }).take(5).collect();
    /// map.extend(some_vec);
    ///
    /// let some_arr = [(11, 11, 111), (22, 22, 222), (33, 33, 333), (44, 44, 4444), (55, 55, 555)];
    /// map.extend(some_arr);
    ///
    /// // Keys and values from some_iter
    /// assert_eq!(map.get_key1(&1), Some(&10));
    /// assert_eq!(map.get_key1(&5), Some(&50));
    /// assert_eq!(map.get_key1(&6), None);
    ///
    /// // Keys and values from some_vec
    /// assert_eq!(map.get_key1(&100), Some(&1000));
    /// assert_eq!(map.get_key1(&500), Some(&5000));
    /// assert_eq!(map.get_key1(&600), None);
    ///
    /// // Keys and values from some_arr
    /// assert_eq!(map.get_key1(&11), Some(&111));
    /// assert_eq!(map.get_key1(&55), Some(&555));
    /// assert_eq!(map.get_key1(&66), None);
    /// ```
    #[inline]
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
}

/// Inserts all new keys and values from the iterator to existing `DHashMap<K1, K2, V, S>`.
impl<'a, K1, K2, V, S> Extend<(&'a K1, &'a K2, &'a V)> for DHashMap<K1, K2, V, S>
where
    K1: Eq + Hash + Copy,
    K2: Eq + Hash + Copy,
    V: Copy,
    S: BuildHasher,
{
    /// Inserts all new keys and values from the iterator to existing `DHashMap<K1, K2, V, S>`.
    ///
    /// Replace values with existing keys with new values returned from the iterator.
    /// The keys and values must implement [`Copy`] trait.
    ///
    /// # Examples
    ///
    /// ```
    /// use double_map::DHashMap;
    ///
    /// // Let's create `DHashMap` with std::collections::hash_map::RandomState hasher
    /// let mut map = DHashMap::new();
    /// map.insert(1, 1, 999);
    ///
    /// let mut number = 0;
    /// let some_vec: Vec<_> = std::iter::repeat_with(move || {
    ///     number +=1;
    ///     (number, number, number * 10)
    /// }).take(5).collect();
    ///
    /// // You don't need to specify the hasher
    /// let some_iter = some_vec.iter().map(|(k1, k2, v)| (k1, k2, v));
    /// map.extend(some_iter);
    ///
    /// // Replace values with existing keys with new values returned from the iterator.
    /// // So that the map.get_key1(&1) doesn't return Some(&999).
    /// assert_eq!(map.get_key1(&1), Some(&10));
    /// assert_eq!(map.get_key1(&5), Some(&50));
    /// assert_eq!(map.get_key1(&6), None);
    ///
    /// // Created vector are still can be used
    /// assert_eq!(some_vec[4], (5, 5, 50));
    ///
    /// // Also you can use for extending already existing map
    /// let mut map2 = DHashMap::new();
    /// map2.extend(&map);
    /// assert_eq!(map, map2);
    /// ```
    #[inline]
    fn extend<T: IntoIterator<Item = (&'a K1, &'a K2, &'a V)>>(&mut self, iter: T) {
        self.extend(iter.into_iter().map(|(&k1, &k2, &v)| (k1, k2, v)))
    }
}

/// Inserts all new keys and values from the iterator to existing `DHashMap<K1, K2, V, S>`.
impl<'a, K1, K2, V, S> Extend<&'a (K1, K2, V)> for DHashMap<K1, K2, V, S>
where
    K1: Eq + Hash + Copy,
    K2: Eq + Hash + Copy,
    V: Copy,
    S: BuildHasher,
{
    /// Inserts all new keys and values from the iterator to existing `DHashMap<K1, K2, V, S>`.
    ///
    /// Replace values with existing keys with new values returned from the iterator.
    /// The keys and values must implement [`Copy`] trait.
    ///
    /// # Examples
    ///
    /// ```
    /// use double_map::DHashMap;
    ///
    /// // Let's create `DHashMap` with std::collections::hash_map::RandomState hasher
    /// let mut map = DHashMap::new();
    /// map.insert(1, 1, 999);
    ///
    /// let mut number = 0;
    /// let some_vec: Vec<_> = std::iter::repeat_with(move || {
    ///     number +=1;
    ///     (number, number, number * 10)
    /// }).take(5).collect();
    ///
    /// // You don't need to specify the hasher
    /// map.extend(&some_vec);
    ///
    /// // Replace values with existing keys with new values returned from the iterator.
    /// // So that the map.get_key1(&1) doesn't return Some(&999).
    /// assert_eq!(map.get_key1(&1), Some(&10));
    /// assert_eq!(map.get_key1(&5), Some(&50));
    /// assert_eq!(map.get_key1(&6), None);
    ///
    /// // And created vector are still can be used.
    /// assert_eq!(some_vec[4], (5, 5, 50));
    /// ```
    #[inline]
    fn extend<T: IntoIterator<Item = &'a (K1, K2, V)>>(&mut self, iter: T) {
        self.extend(iter.into_iter().map(|&(k1, k2, v)| (k1, k2, v)))
    }
}

/// An iterator over the entries of a `DHashMap` in arbitrary order.
/// The iterator element is tuple of type `(&'a K1, &'a K2, &'a V)`.
///
/// This `struct` is created by the [`iter`](DHashMap::iter) method
/// on [`DHashMap`]. See its documentation for more.
///
/// # Example
///
/// ```
/// use double_map::{DHashMap, dhashmap};
///
/// let map = dhashmap!{
///     1, "a" => "One",
///     2, "b" => "Two",
///     3, "c" => "Three",
/// };
///
/// let mut iter = map.iter();
/// let mut vec = vec![iter.next(), iter.next(), iter.next()];
///
/// // The `Iter` iterator produces tuples in arbitrary order, so the
/// // tuples must be sorted to test them against a sorted array.
/// vec.sort_unstable();
/// assert_eq!(vec, [Some((&1, &"a", &"One")), Some((&2, &"b", &"Two")), Some((&3, &"c", &"Three"))]);
///
/// // It is fused iterator
/// assert_eq!(iter.next(), None);
/// assert_eq!(iter.next(), None);
/// ```
#[derive(Clone, Debug)]
pub struct Iter<'a, K1: 'a, K2: 'a, V: 'a> {
    base: hash_map::Iter<'a, K1, (K2, V)>,
}

impl<'a, K1, K2, V> Iterator for Iter<'a, K1, K2, V> {
    type Item = (&'a K1, &'a K2, &'a V);

    #[inline]
    fn next(&mut self) -> Option<(&'a K1, &'a K2, &'a V)> {
        // We do not use Option::map for performance purpose
        match self.base.next() {
            Some((k1, (k2, val))) => Some((k1, k2, val)),
            None => None,
        }
    }
    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.base.size_hint()
    }
}

impl<K1, K2, V> ExactSizeIterator for Iter<'_, K1, K2, V> {
    #[inline]
    fn len(&self) -> usize {
        self.base.len()
    }
}

impl<K1, K2, V> FusedIterator for Iter<'_, K1, K2, V> {}

/// An iterator over the keys of a `DHashMap` in arbitrary order.
/// The iterator element is tuple of type `(&'a K1, &'a K2)`.
///
/// This `struct` is created by the [`keys`](DHashMap::keys) method
/// on [`DHashMap`]. See its documentation for more.
///
/// # Example
///
/// ```
/// use double_map::{DHashMap, dhashmap};
///
/// let map = dhashmap!{
///     1, "a" => "One",
///     2, "b" => "Two",
///     3, "c" => "Three",
/// };
///
/// let mut keys = map.keys();
/// let mut vec = vec![keys.next(), keys.next(), keys.next()];
///
/// // The `Keys` iterator produces tuples in arbitrary order, so the
/// // tuples must be sorted to test them against a sorted array.
/// vec.sort_unstable();
/// assert_eq!(vec, [Some((&1, &"a")), Some((&2, &"b")), Some((&3, &"c"))]);
///
/// // It is fused iterator
/// assert_eq!(keys.next(), None);
/// assert_eq!(keys.next(), None);
/// ```
#[derive(Clone, Debug)]
pub struct Keys<'a, K1: 'a, K2: 'a, V: 'a> {
    inner: Iter<'a, K1, K2, V>,
}

impl<'a, K1, K2, V> Iterator for Keys<'a, K1, K2, V> {
    type Item = (&'a K1, &'a K2);

    #[inline]
    fn next(&mut self) -> Option<(&'a K1, &'a K2)> {
        // We do not use Option::map for performance purpose
        match self.inner.next() {
            Some((k1, k2, _)) => Some((k1, k2)),
            None => None,
        }
    }
    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.inner.size_hint()
    }
}

impl<K1, K2, V> ExactSizeIterator for Keys<'_, K1, K2, V> {
    #[inline]
    fn len(&self) -> usize {
        self.inner.len()
    }
}

impl<K1, K2, V> FusedIterator for Keys<'_, K1, K2, V> {}

/// An iterator over the values of a `DHashMap` in arbitrary order.
/// The iterator element is `&'a V`.
///
/// This `struct` is created by the [`values`](DHashMap::values) method
/// on [`DHashMap`]. See its documentation for more.
///
/// # Example
///
/// ```
/// use double_map::{DHashMap, dhashmap};
///
/// let map = dhashmap!{
///     1, "a" => 10,
///     2, "b" => 20,
///     3, "c" => 30,
/// };
///
/// let mut values = map.values();
/// let mut vec = vec![values.next(), values.next(), values.next()];
///
/// // The `Values` iterator produces values in arbitrary order, so the
/// // values must be sorted to test them against a sorted array.
/// vec.sort_unstable();
/// assert_eq!(vec, [Some(&10), Some(&20), Some(&30)]);
///
/// // It is fused iterator
/// assert_eq!(values.next(), None);
/// assert_eq!(values.next(), None);
/// ```
#[derive(Clone, Debug)]
pub struct Values<'a, K1: 'a, K2: 'a, V: 'a> {
    inner: Iter<'a, K1, K2, V>,
}

impl<'a, K1, K2, V> Iterator for Values<'a, K1, K2, V> {
    type Item = &'a V;

    #[inline]
    fn next(&mut self) -> Option<&'a V> {
        // We do not use Option::map for performance purpose
        match self.inner.next() {
            Some((_, _, val)) => Some(val),
            None => None,
        }
    }
    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.inner.size_hint()
    }
}

impl<K1, K2, V> ExactSizeIterator for Values<'_, K1, K2, V> {
    #[inline]
    fn len(&self) -> usize {
        self.inner.len()
    }
}

impl<K1, K2, V> FusedIterator for Values<'_, K1, K2, V> {}

/// A mutable iterator over the entries of a `DHashMap` in arbitrary order.
/// The iterator element is tuple of type`(&'a K1, &'a K2, &'a mut V)`.
///
/// This `struct` is created by the [`iter_mut`](DHashMap::iter_mut) method
/// on [`DHashMap`]. See its documentation for more.
///
/// # Example
///
/// ```
/// use double_map::{DHashMap, dhashmap};
///
/// let mut map = dhashmap!{
///     1, "a" => "One".to_owned(),
///     2, "b" => "Two".to_owned(),
///     3, "c" => "Three".to_owned(),
/// };
///
/// let mut iter = map.iter_mut();
/// iter.next().map(|(_, _, v)| v.push_str(" coin"));
/// iter.next().map(|(_, _, v)| v.push_str(" coin"));
/// iter.next().map(|(_, _, v)| v.push_str(" coin"));
///
/// // It is fused iterator
/// assert_eq!(iter.next(), None);
/// assert_eq!(iter.next(), None);
///
/// assert_eq!(map.get_key1(&1).unwrap(), &"One coin".to_owned()  );
/// assert_eq!(map.get_key1(&2).unwrap(), &"Two coin".to_owned()  );
/// assert_eq!(map.get_key1(&3).unwrap(), &"Three coin".to_owned());
/// ```
#[derive(Debug)]
pub struct IterMut<'a, K1: 'a, K2: 'a, V: 'a> {
    base: hash_map::IterMut<'a, K1, (K2, V)>,
}

impl<'a, K1, K2, V> Iterator for IterMut<'a, K1, K2, V> {
    type Item = (&'a K1, &'a K2, &'a mut V);

    #[inline]
    fn next(&mut self) -> Option<(&'a K1, &'a K2, &'a mut V)> {
        // We do not use Option::map for performance purpose
        match self.base.next() {
            Some((k1, (ref k2, val))) => Some((k1, k2, val)),
            None => None,
        }
    }
    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.base.size_hint()
    }
}

impl<K1, K2, V> ExactSizeIterator for IterMut<'_, K1, K2, V> {
    #[inline]
    fn len(&self) -> usize {
        self.base.len()
    }
}

impl<K1, K2, V> FusedIterator for IterMut<'_, K1, K2, V> {}

/// A mutable iterator over the values of a `DHashMap` in arbitrary order.
/// The iterator element is `&'a mut V`.
///
/// This `struct` is created by the [`values_mut`](DHashMap::values_mut) method
/// on [`DHashMap`]. See its documentation for more.
///
/// # Example
///
/// ```
/// use double_map::{DHashMap, dhashmap};
///
/// let mut map = dhashmap!{
///     1, "a" => "One".to_owned(),
///     2, "b" => "Two".to_owned(),
///     3, "c" => "Three".to_owned(),
/// };
///
/// let mut values = map.values_mut();
/// values.next().map(|v| v.push_str(" coin"));
/// values.next().map(|v| v.push_str(" coin"));
/// values.next().map(|v| v.push_str(" coin"));
///
/// // It is fused iterator
/// assert_eq!(values.next(), None);
/// assert_eq!(values.next(), None);
///
/// assert_eq!(map.get_key1(&1).unwrap(), &"One coin".to_owned()  );
/// assert_eq!(map.get_key1(&2).unwrap(), &"Two coin".to_owned()  );
/// assert_eq!(map.get_key1(&3).unwrap(), &"Three coin".to_owned());
/// ```
#[derive(Debug)]
pub struct ValuesMut<'a, K1: 'a, K2: 'a, V: 'a> {
    inner: IterMut<'a, K1, K2, V>,
}

impl<'a, K1, K2, V> Iterator for ValuesMut<'a, K1, K2, V> {
    type Item = &'a mut V;

    #[inline]
    fn next(&mut self) -> Option<&'a mut V> {
        // We do not use Option::map for performance purpose
        match self.inner.next() {
            Some((_, _, val)) => Some(val),
            None => None,
        }
    }
    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.inner.size_hint()
    }
}

impl<K1, K2, V> ExactSizeIterator for ValuesMut<'_, K1, K2, V> {
    #[inline]
    fn len(&self) -> usize {
        self.inner.len()
    }
}

impl<K1, K2, V> FusedIterator for ValuesMut<'_, K1, K2, V> {}

/// A draining iterator over the entries of a `DHashMap` in arbitrary order.
/// The iterator element is tuple of type`(K1, K2, V)`.
///
/// This `struct` is created by the [`drain`](DHashMap::drain) method
/// on [`DHashMap`]. See its documentation for more.
///
/// # Example
///
/// ```
/// use double_map::{DHashMap, dhashmap};
///
/// let mut map = dhashmap!{
///     1, "a" => "One",
///     2, "b" => "Two",
///     3, "c" => "Three",
/// };
///
/// let mut drain_iter = map.drain();
/// let mut vec = vec![drain_iter.next(), drain_iter.next(), drain_iter.next()];
///
/// // The `Drain` iterator produces tuples in arbitrary order, so the
/// // tuples must be sorted to test them against a sorted array.
/// vec.sort_unstable();
/// assert_eq!(vec, [Some((1, "a", "One")), Some((2, "b", "Two")), Some((3, "c", "Three"))]);
///
/// // It is fused iterator
/// assert_eq!(drain_iter.next(), None);
/// assert_eq!(drain_iter.next(), None);
/// ```
#[derive(Debug)]
pub struct Drain<'a, K1: 'a, K2: 'a, V: 'a> {
    base: hash_map::Drain<'a, K1, (K2, V)>,
}

impl<'a, K1, K2, V> Iterator for Drain<'a, K1, K2, V> {
    type Item = (K1, K2, V);

    #[inline]
    fn next(&mut self) -> Option<(K1, K2, V)> {
        match self.base.next() {
            Some((key_one, (key_two, value))) => Some((key_one, key_two, value)),
            None => None,
        }
    }
    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.base.size_hint()
    }
}

impl<K1, K2, V> ExactSizeIterator for Drain<'_, K1, K2, V> {
    #[inline]
    fn len(&self) -> usize {
        self.base.len()
    }
}

impl<K1, K2, V> FusedIterator for Drain<'_, K1, K2, V> {}

/// An owning iterator over the entries of a `DHashMap`.
///
/// This `struct` is created by the [`into_iter`] method on [`DHashMap`]
/// (provided by the [`IntoIterator`] trait). See its documentation for more.
///
/// [`into_iter`]: IntoIterator::into_iter
/// [`IntoIterator`]: core::iter::IntoIterator
///
/// # Example
///
/// ```
/// use double_map::{DHashMap, dhashmap};
///
/// let mut map = dhashmap!{
///     1, "a" => "One",
///     2, "b" => "Two",
///     3, "c" => "Three",
/// };
///
/// let mut iter = map.into_iter();
/// let mut vec = vec![iter.next(), iter.next(), iter.next()];
///
/// // The `IntoIter` iterator produces tuples in arbitrary order, so the
/// // tuples must be sorted to test them against a sorted array.
/// vec.sort_unstable();
/// assert_eq!(vec, [Some((1, "a", "One")), Some((2, "b", "Two")), Some((3, "c", "Three"))]);
///
/// // It is fused iterator
/// assert_eq!(iter.next(), None);
/// assert_eq!(iter.next(), None);
/// ```
#[derive(Debug)]
pub struct IntoIter<K1, K2, V> {
    base: hash_map::IntoIter<K1, (K2, V)>,
}

impl<K1, K2, V> Iterator for IntoIter<K1, K2, V> {
    type Item = (K1, K2, V);

    #[inline]
    fn next(&mut self) -> Option<(K1, K2, V)> {
        match self.base.next() {
            Some((k1, (k2, v))) => Some((k1, k2, v)),
            None => None,
        }
    }
    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.base.size_hint()
    }
}

impl<K1, K2, V> ExactSizeIterator for IntoIter<K1, K2, V> {
    #[inline]
    fn len(&self) -> usize {
        self.base.len()
    }
}

impl<K1, K2, V> FusedIterator for IntoIter<K1, K2, V> {}

/// An owning iterator over the keys of a `DHashMap`.
///
/// This `struct` is created by the [`into_keys`] method on [`DHashMap`].
/// See its documentation for more.
///
/// [`into_keys`]: DHashMap::into_keys
///
/// # Example
///
/// ```
/// use double_map::{DHashMap, dhashmap};
///
/// let mut map = dhashmap!{
///     1, "a" => "One",
///     2, "b" => "Two",
///     3, "c" => "Three",
/// };
///
/// let mut keys = map.into_keys();
/// let mut vec = vec![keys.next(), keys.next(), keys.next()];
///
/// // The `IntoKeys` iterator produces keys in arbitrary order, so the
/// // keys must be sorted to test them against a sorted array.
/// vec.sort_unstable();
/// assert_eq!(vec, [Some((1, "a")), Some((2, "b")), Some((3, "c"))]);
///
/// // It is fused iterator
/// assert_eq!(keys.next(), None);
/// assert_eq!(keys.next(), None);
/// ```
#[derive(Debug)]
pub struct IntoKeys<K1, K2, V> {
    inner: IntoIter<K1, K2, V>,
}

impl<K1, K2, V> Iterator for IntoKeys<K1, K2, V> {
    type Item = (K1, K2);

    #[inline]
    fn next(&mut self) -> Option<(K1, K2)> {
        match self.inner.next() {
            Some((k1, k2, _)) => Some((k1, k2)),
            None => None,
        }
    }
    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.inner.size_hint()
    }
}

impl<K1, K2, V> ExactSizeIterator for IntoKeys<K1, K2, V> {
    #[inline]
    fn len(&self) -> usize {
        self.inner.len()
    }
}

impl<K1, K2, V> FusedIterator for IntoKeys<K1, K2, V> {}

/// An owning iterator over the values of a `DHashMap`.
///
/// This `struct` is created by the [`into_values`] method on [`DHashMap`].
/// See its documentation for more.
///
/// [`into_values`]: DHashMap::into_values
///
/// # Example
///
/// ```
/// use double_map::{DHashMap, dhashmap};
///
/// let mut map = dhashmap!{
///     1, "One"   => "a",
///     2, "Two"   => "b",
///     3, "Three" => "c",
/// };
///
/// let mut values = map.into_values();
/// let mut vec = vec![values.next(), values.next(), values.next()];
///
/// // The `IntoValues` iterator produces values in arbitrary order, so
/// // the values must be sorted to test them against a sorted array.
/// vec.sort_unstable();
/// assert_eq!(vec, [Some("a"), Some("b"), Some("c")]);
///
/// // It is fused iterator
/// assert_eq!(values.next(), None);
/// assert_eq!(values.next(), None);
/// ```
#[derive(Debug)]
pub struct IntoValues<K1, K2, V> {
    inner: IntoIter<K1, K2, V>,
}

impl<K1, K2, V> Iterator for IntoValues<K1, K2, V> {
    type Item = V;

    #[inline]
    fn next(&mut self) -> Option<V> {
        match self.inner.next() {
            Some((_, _, v)) => Some(v),
            None => None,
        }
    }
    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.inner.size_hint()
    }
}

impl<K1, K2, V> ExactSizeIterator for IntoValues<K1, K2, V> {
    #[inline]
    fn len(&self) -> usize {
        self.inner.len()
    }
}

impl<K1, K2, V> FusedIterator for IntoValues<K1, K2, V> {}

impl<'a, K1, K2, V, S> IntoIterator for &'a DHashMap<K1, K2, V, S> {
    type Item = (&'a K1, &'a K2, &'a V);
    type IntoIter = Iter<'a, K1, K2, V>;

    /// Creates an iterator visiting all keys-value tuples in arbitrary order.
    /// The iterator element is tuple of type `(&'a K1, &'a K2, &'a V)`.
    ///
    /// # Note
    ///
    /// Created iterator iterates only through the first [`HashMap<K1, (K2, V)>`](`std::collections::HashMap`)
    /// which is used underneath of the [`DHashMap`].
    ///
    /// So that, if you previously used [`insert_unchecked`](DHashMap::insert_unchecked) method,
    /// this method can return false second keys (key #2) in case of **unsynchronization**
    /// between first keys of type `K1` and second keys of type `K2`. See
    /// [`insert_unchecked`](DHashMap::insert_unchecked) and [`iter`](DHashMap::iter)
    /// methods documentation for more.
    ///
    /// # Examples
    ///
    /// ```
    /// use double_map::{DHashMap, dhashmap};
    ///
    /// let mut map = dhashmap!{
    ///     "a", 1 => "One",
    ///     "b", 2 => "Two",
    ///     "c", 3 => "Three",
    /// };
    /// assert_eq!(map.len(), 3);
    ///
    /// for (key1, key2, value) in &map {
    ///     println!("key1: {}, key2: {}, value: {}", key1, key2, value);
    ///     assert!(
    ///         (key1, key2, value) == (&"a", &1, &"One") ||
    ///         (key1, key2, value) == (&"b", &2, &"Two") ||
    ///         (key1, key2, value) == (&"c", &3, &"Three")
    ///     );
    /// }
    ///
    /// assert_eq!(map.len(), 3);
    /// ```
    fn into_iter(self) -> Iter<'a, K1, K2, V> {
        self.iter()
    }
}

impl<'a, K1, K2, V, S> IntoIterator for &'a mut DHashMap<K1, K2, V, S> {
    type Item = (&'a K1, &'a K2, &'a mut V);
    type IntoIter = IterMut<'a, K1, K2, V>;

    /// Creates an iterator visiting all keys-value tuples in arbitrary order,
    /// with mutable references to the values. The iterator element is tuple
    /// of type `(&'a K1, &'a K2, &'a mut V)`.
    ///
    /// # Note
    ///
    /// Created iterator iterates only through the first [`HashMap<K1, (K2, V)>`](`std::collections::HashMap`)
    /// which is used underneath of the [`DHashMap`].
    ///
    /// So that, if you previously used [`insert_unchecked`](DHashMap::insert_unchecked) method,
    /// this method can return false second keys (key #2) in case of **unsynchronization**
    /// between first keys of type `K1` and second keys of type `K2`. See
    /// [`insert_unchecked`](DHashMap::insert_unchecked) and [`iter_mut`](DHashMap::iter_mut)
    /// methods documentation for more.
    ///
    /// # Examples
    ///
    /// ```
    /// use double_map::{DHashMap, dhashmap};
    ///
    /// let mut map = dhashmap!{
    ///     "a", "One"   => 1,
    ///     "b", "Two"   => 2,
    ///     "c", "Three" => 3,
    /// };
    ///
    /// assert_eq!(map.len(), 3);
    ///
    /// // Update all values
    /// for (_, _, value) in &mut map {
    ///     *value *= 2;
    /// }
    ///
    /// for (key1, key2, value) in &map {
    ///     println!("key1: {}, key2: {}, value: {}", key1, key2, value);
    ///     assert!(
    ///         (key1, key2, value) == (&"a", &"One",   &2) ||
    ///         (key1, key2, value) == (&"b", &"Two",   &4) ||
    ///         (key1, key2, value) == (&"c", &"Three", &6)
    ///     );
    /// }
    ///
    /// assert_eq!(map.len(), 3);
    /// ```
    fn into_iter(self) -> IterMut<'a, K1, K2, V> {
        self.iter_mut()
    }
}

impl<K1, K2, V, S> IntoIterator for DHashMap<K1, K2, V, S> {
    type Item = (K1, K2, V);
    type IntoIter = IntoIter<K1, K2, V>;

    /// Creates a consuming iterator, that is, one that moves each keys-value
    /// tuple out of the map in arbitrary order. The map cannot be used after
    /// calling this.
    ///
    /// # Note
    ///
    /// Created iterator contains only content of the first [`HashMap<K1, (K2, V)>`](`std::collections::HashMap`)
    /// which is used underneath of the [`DHashMap`].
    ///
    /// So that, if you previously used [`insert_unchecked`](DHashMap::insert_unchecked) method,
    /// this method can return false second keys (key #2) in case of **unsynchronization**
    /// between first keys of type `K1` and second keys of type `K2`. See
    /// [`insert_unchecked`](DHashMap::insert_unchecked) method documentation for more.
    ///
    /// # Examples
    ///
    /// ```
    /// use double_map::{DHashMap, dhashmap};
    ///
    /// let mut map = dhashmap!{
    ///     1, "a" => "One",
    ///     2, "b" => "Two",
    ///     3, "c" => "Three",
    /// };
    ///
    /// // Not possible with .iter()
    /// let mut vec: Vec<(i32, &str, &str)> = map.into_iter().collect();
    /// // The `IntoIter` iterator produces tuples in arbitrary order, so
    /// // the tuples must be sorted to test them against a sorted array.
    /// vec.sort_unstable();
    /// assert_eq!(vec, [(1, "a", "One"), (2, "b", "Two"), (3, "c", "Three")])
    /// ```
    fn into_iter(self) -> IntoIter<K1, K2, V> {
        IntoIter {
            base: self.value_map.into_iter(),
        }
    }
}

/// A view into an occupied entry in a [`DHashMap`].
/// It is part of the [`Entry`] enum and [`OccupiedError`] struct.
#[derive(Debug)]
pub struct OccupiedEntry<'a, K1: 'a, K2: 'a, V: 'a> {
    base_v: hash_map::OccupiedEntry<'a, K1, (K2, V)>,
    base_k: hash_map::OccupiedEntry<'a, K2, K1>,
}

impl<'a, K1, K2, V> OccupiedEntry<'a, K1, K2, V> {
    /// Gets a reference to the key #1 of type `K1` in the entry.
    ///
    /// # Examples
    ///
    /// ```
    /// use double_map::DHashMap;
    /// use double_map::dhash_map::Entry;
    ///
    /// let mut map: DHashMap<&str, u32, i32> = DHashMap::new();
    /// map.insert("poneyland", 0, 12);
    ///
    /// if let Ok(entry) = map.entry("poneyland", 0) {
    ///     match entry {
    ///         Entry::Occupied(oc_entry) => {
    ///             assert_eq!(oc_entry.key1(), &"poneyland");
    ///         }
    ///         Entry::Vacant(_) => panic!("Something go wrong!!!")
    ///     }
    /// }
    /// ```
    #[inline]
    pub fn key1(&self) -> &K1 {
        self.base_v.key()
    }

    /// Gets a reference to the key #2 of type `K2` in the entry.
    ///
    /// # Examples
    ///
    /// ```
    /// use double_map::DHashMap;
    /// use double_map::dhash_map::Entry;
    ///
    /// let mut map: DHashMap<&str, u32, i32> = DHashMap::new();
    /// map.insert("poneyland", 0, 12);
    ///
    /// if let Ok(entry) = map.entry("poneyland", 0) {
    ///     match entry {
    ///         Entry::Occupied(oc_entry) => {
    ///             assert_eq!(oc_entry.key2(), &0);
    ///         }
    ///         Entry::Vacant(_) => panic!("Something go wrong!!!")
    ///     }
    /// }
    /// ```
    #[inline]
    pub fn key2(&self) -> &K2 {
        self.base_k.key()
    }

    /// Gets a reference to the keys of type `K1` and `K2` in the entry.
    /// Return tuple of type `(&'a K1, &'a K2)`.
    ///
    /// # Examples
    ///
    /// ```
    /// use double_map::DHashMap;
    /// use double_map::dhash_map::Entry;
    ///
    /// let mut map: DHashMap<&str, u32, i32> = DHashMap::new();
    /// map.insert("poneyland", 0, 12);
    ///
    /// if let Ok(entry) = map.entry("poneyland", 0) {
    ///     match entry {
    ///         Entry::Occupied(oc_entry) => {
    ///             assert_eq!(oc_entry.keys(), (&"poneyland", &0));
    ///         }
    ///         Entry::Vacant(_) => panic!("Something go wrong!!!")
    ///     }
    /// }
    /// ```
    #[inline]
    pub fn keys(&self) -> (&K1, &K2) {
        (self.base_v.key(), self.base_k.key())
    }

    /// Take the ownership of the keys and value from the map.
    /// Keeps the allocated memory for reuse.
    ///
    /// # Examples
    ///
    /// ```
    /// use double_map::DHashMap;
    /// use double_map::dhash_map::Entry;
    ///
    /// // So lets create some map and insert some element
    /// let mut map: DHashMap<&str, u32, i32> = DHashMap::new();
    /// map.insert("poneyland", 0, 10);
    /// map.insert("bearland",  1, 11);
    ///
    /// // And also reserve some space for additional elements
    /// map.reserve(15);
    /// // Now our map can hold at least 17 elements
    /// let capacity_before_entries_remove = map.capacity();
    /// assert!(capacity_before_entries_remove >= 17);
    ///
    /// assert!(map.get_key1("poneyland") == Some(&10) && map.get_key2(&0) == Some(&10));
    /// if let Ok(entry) = map.entry("poneyland", 0) {
    ///     match entry {
    ///         Entry::Occupied(oc_entry) => {
    ///             // We delete the entry from the map.
    ///             let tuple = oc_entry.remove_entry();
    ///             assert_eq!(tuple, ("poneyland", 0, 10));
    ///         }
    ///         Entry::Vacant(_) => panic!("Something go wrong!!!")
    ///     }
    /// }
    /// assert!(map.get_key1("poneyland") == None && map.get_key2(&0) == None);
    ///
    /// assert!(map.get_key1("bearland") == Some(&11) && map.get_key2(&1) == Some(&11));
    /// if let Ok(entry) = map.entry("bearland", 1) {
    ///     match entry {
    ///         Entry::Occupied(oc_entry) => {
    ///             // We delete the entry from the map.
    ///             let tuple = oc_entry.remove_entry();
    ///             assert_eq!(tuple, ("bearland",  1, 11));
    ///         }
    ///         Entry::Vacant(_) => panic!("Something go wrong!!!")
    ///     }
    /// }
    /// assert!(map.get_key1("bearland") == None && map.get_key2(&1) == None);
    ///
    /// // But the capacity of our map isn't changed and still equals to the capacity before
    /// // using `remove_entry` method
    /// assert_eq!(map.capacity(), capacity_before_entries_remove);
    /// ```
    #[inline]
    pub fn remove_entry(self) -> (K1, K2, V) {
        self.base_k.remove_entry();
        let (k1, (k2, v)) = self.base_v.remove_entry();
        (k1, k2, v)
    }

    /// Gets a reference to the value in the entry.
    ///
    /// # Examples
    ///
    /// ```
    /// use double_map::DHashMap;
    /// use double_map::dhash_map::Entry;
    ///
    /// let mut map: DHashMap<&str, u32, i32> = DHashMap::new();
    /// map.insert("poneyland", 0, 12);
    ///
    /// if let Ok(entry) = map.entry("poneyland", 0) {
    ///     match entry {
    ///         Entry::Occupied(oc_entry) => {
    ///             assert_eq!(oc_entry.get(), &12);
    ///         }
    ///         Entry::Vacant(_) => panic!("Something go wrong!!!")
    ///     }
    /// }
    /// ```
    #[inline]
    pub fn get(&self) -> &V {
        let (_, v) = self.base_v.get();
        v
    }

    /// Gets a mutable reference to the value in the entry.
    ///
    /// If you need a reference to the `OccupiedEntry` which may outlive the
    /// destruction of the `Entry` value, see [`into_mut`](`OccupiedEntry::into_mut`).
    ///
    /// # Examples
    ///
    /// ```
    /// use double_map::DHashMap;
    /// use double_map::dhash_map::Entry;
    ///
    /// let mut map: DHashMap<&str, u32, i32> = DHashMap::new();
    /// map.insert("poneyland", 0, 12);
    /// assert_eq!(map.get_key1("poneyland"), Some(&12));
    /// assert_eq!(map.get_key2(&0),          Some(&12));
    ///
    /// if let Ok(entry) = map.entry("poneyland", 0) {
    ///     match entry {
    ///         Entry::Occupied(mut oc_entry) => {
    ///             *oc_entry.get_mut() += 10;
    ///             assert_eq!(oc_entry.get(), &22);
    ///
    ///             // We can use the same Entry multiple times.
    ///             *oc_entry.get_mut() += 2;
    ///         }
    ///         Entry::Vacant(_) => panic!("Something go wrong!!!")
    ///     }
    /// }
    /// assert_eq!(map.get_key1("poneyland"), Some(&24));
    /// assert_eq!(map.get_key2(&0),          Some(&24));
    /// ```
    #[inline]
    pub fn get_mut(&mut self) -> &mut V {
        let (_, v) = self.base_v.get_mut();
        v
    }

    /// Converts the `OccupiedEntry` into a mutable reference to the value in the entry
    /// with a lifetime bound to the map itself.
    ///
    /// # Examples
    ///
    /// ```
    /// use double_map::DHashMap;
    /// use double_map::dhash_map::Entry;
    ///
    /// let mut map: DHashMap<&str, u32, i32> = DHashMap::new();
    /// map.insert("poneyland", 0, 12);
    /// assert_eq!(map.get_key1("poneyland"), Some(&12));
    /// assert_eq!(map.get_key2(&0),          Some(&12));
    ///
    /// // Let's create a variable that outlives the OccupiedEntry (with some initial value)
    /// let mut value: &mut i32 = &mut 0;
    ///
    /// if let Ok(entry) = map.entry("poneyland", 0) {
    ///     match entry {
    ///         Entry::Occupied(oc_entry) => {
    ///             // So we can convert the OccupiedEntry into a mutable reference to the value.
    ///             value = oc_entry.into_mut();
    ///             *value += 10;
    ///         }
    ///         Entry::Vacant(_) => panic!("Something go wrong!!!")
    ///     }
    /// }
    /// // We can use the same reference outside the created oc_entry (OccupiedEntry) scope.
    /// *value += 20;
    /// assert_eq!(map.get_key1("poneyland"), Some(&42)); // 12 + 10 + 20
    /// assert_eq!(map.get_key2(&0),          Some(&42));
    /// ```
    #[inline]
    pub fn into_mut(self) -> &'a mut V {
        let (_, v) = self.base_v.into_mut();
        v
    }

    /// Sets the value of the entry, and returns the entry's old value.
    ///
    /// # Examples
    ///
    /// ```
    /// use double_map::DHashMap;
    /// use double_map::dhash_map::Entry;
    ///
    /// let mut map: DHashMap<&str, u32, i32> = DHashMap::new();
    /// map.insert("poneyland", 0, 12);
    /// assert_eq!(map.get_key1("poneyland"), Some(&12));
    /// assert_eq!(map.get_key2(&0),          Some(&12));
    ///
    /// // Let's create a variable that holds value
    /// let mut owner: i32 = 100;
    ///
    /// if let Ok(entry) = map.entry("poneyland", 0) {
    ///     match entry {
    ///         Entry::Occupied(mut oc_entry) => {
    ///             // So we can swap our created owner value with value inside the map.
    ///             owner = oc_entry.insert(owner);
    ///         }
    ///         Entry::Vacant(_) => panic!("Something go wrong!!!")
    ///     }
    /// }
    /// assert_eq!(owner, 12);
    /// assert_eq!(map.get_key1("poneyland"), Some(&100));
    /// assert_eq!(map.get_key2(&0),          Some(&100));
    /// ```
    #[inline]
    pub fn insert(&mut self, mut value: V) -> V {
        let old_value = self.get_mut();
        mem::swap(&mut value, old_value);
        value
    }

    /// Take the value out of the entry (map), and return it.
    /// Keeps the allocated memory for reuse.
    ///
    /// # Examples
    ///
    /// ```
    /// use double_map::DHashMap;
    /// use double_map::dhash_map::Entry;
    ///
    /// // So lets create some map and insert some element
    /// let mut map: DHashMap<&str, u32, i32> = DHashMap::new();
    /// map.insert("poneyland", 0, 10);
    /// map.insert("bearland",  1, 11);
    ///
    /// // And also reserve some space for additional elements
    /// map.reserve(15);
    /// // Now our map can hold at least 17 elements
    /// let capacity_before_remove = map.capacity();
    /// assert!(capacity_before_remove >= 17);
    ///
    /// assert!(map.get_key1("poneyland") == Some(&10) && map.get_key2(&0) == Some(&10));
    /// if let Ok(entry) = map.entry("poneyland", 0) {
    ///     match entry {
    ///         Entry::Occupied(oc_entry) => {
    ///             // We delete the entry from the map.
    ///             let value = oc_entry.remove();
    ///             assert_eq!(value, 10);
    ///         }
    ///         Entry::Vacant(_) => panic!("Something go wrong!!!")
    ///     }
    /// }
    /// assert!(map.get_key1("poneyland") == None && map.get_key2(&0) == None);
    ///
    /// assert!(map.get_key1("bearland") == Some(&11) && map.get_key2(&1) == Some(&11));
    /// if let Ok(entry) = map.entry("bearland", 1) {
    ///     match entry {
    ///         Entry::Occupied(oc_entry) => {
    ///             // We delete the entry from the map.
    ///             let value = oc_entry.remove();
    ///             assert_eq!(value, 11);
    ///         }
    ///         Entry::Vacant(_) => panic!("Something go wrong!!!")
    ///     }
    /// }
    /// assert!(map.get_key1("bearland") == None && map.get_key2(&1) == None);
    ///
    /// // But the capacity of our map isn't changed and still equals to the capacity before
    /// // using `remove_entry` method
    /// assert_eq!(map.capacity(), capacity_before_remove);
    /// ```
    #[inline]
    pub fn remove(self) -> V {
        self.remove_entry().2
    }
}

/// A view into a vacant entry in a [`DHashMap`].
/// It is part of the [`Entry`] enum.
#[derive(Debug)]
pub struct VacantEntry<'a, K1: 'a, K2: 'a, V: 'a> {
    base_v: hash_map::VacantEntry<'a, K1, (K2, V)>,
    base_k: hash_map::VacantEntry<'a, K2, K1>,
}

impl<'a, K1: 'a, K2: 'a, V: 'a> VacantEntry<'a, K1, K2, V> {
    /// Gets a reference to the key #1 of type `K1` that would be used
    /// when inserting a value through the `VacantEntry`.
    ///
    /// # Examples
    ///
    /// ```
    /// use double_map::DHashMap;
    /// use double_map::dhash_map::Entry;
    ///
    /// let mut map: DHashMap<&str, u32, i32> = DHashMap::new();
    ///
    /// if let Ok(entry) = map.entry("poneyland", 0) {
    ///     match entry {
    ///         Entry::Occupied(_) => panic!("Something go wrong!!!"),
    ///         Entry::Vacant(vac_entry) => assert_eq!(vac_entry.key1(), &"poneyland"),
    ///     }
    /// }
    /// ```
    #[inline]
    pub fn key1(&self) -> &K1 {
        self.base_v.key()
    }

    /// Gets a reference to the key #2 of type `K2` that would be used
    /// when inserting a value through the `VacantEntry`.
    ///
    /// # Examples
    ///
    /// ```
    /// use double_map::DHashMap;
    /// use double_map::dhash_map::Entry;
    ///
    /// let mut map: DHashMap<&str, u32, i32> = DHashMap::new();
    ///
    /// if let Ok(entry) = map.entry("poneyland", 0) {
    ///     match entry {
    ///         Entry::Occupied(_) => panic!("Something go wrong!!!"),
    ///         Entry::Vacant(vac_entry) => assert_eq!(vac_entry.key2(), &0),
    ///     }
    /// }
    /// ```
    #[inline]
    pub fn key2(&self) -> &K2 {
        self.base_k.key()
    }

    /// Gets a reference to the keys of type `K1` and `K2` that would be used
    /// when inserting a value through the `VacantEntry`.
    /// Return tuple of type `(&'a K1, &'a K2)`.
    ///
    /// # Examples
    ///
    /// ```
    /// use double_map::DHashMap;
    /// use double_map::dhash_map::Entry;
    ///
    /// let mut map: DHashMap<&str, u32, i32> = DHashMap::new();
    ///
    /// if let Ok(entry) = map.entry("poneyland", 0) {
    ///     match entry {
    ///         Entry::Occupied(_) => panic!("Something go wrong!!!"),
    ///         Entry::Vacant(vac_entry) => {
    ///             assert_eq!(vac_entry.keys(), (&"poneyland", &0))
    ///         }
    ///     }
    /// }
    /// ```
    #[inline]
    pub fn keys(&self) -> (&K1, &K2) {
        (self.base_v.key(), self.base_k.key())
    }

    /// Take the ownership of the keys from the entry.
    ///
    /// # Examples
    ///
    /// ```
    /// use double_map::DHashMap;
    /// use double_map::dhash_map::Entry;
    ///
    /// // So lets create some map and also reserve some space for additional elements
    /// let mut map: DHashMap<&str, u32, i32> = DHashMap::with_capacity(3);
    ///
    /// let capacity_before_into_keys = map.capacity();
    /// assert!(capacity_before_into_keys >= 3);
    ///
    /// if let Ok(entry) = map.entry("poneyland", 0) {
    ///     match entry {
    ///         Entry::Occupied(_) => panic!("Something go wrong!!!"),
    ///         Entry::Vacant(vac_entry) => {
    ///             // We take the keys from the entry.
    ///             let tuple = vac_entry.into_keys();
    ///             assert_eq!(tuple, ("poneyland", 0));
    ///         }
    ///     }
    /// }
    ///
    /// if let Ok(entry) = map.entry("bearland", 1) {
    ///     match entry {
    ///         Entry::Occupied(_) => panic!("Something go wrong!!!"),
    ///         Entry::Vacant(vac_entry) => {
    ///             // We take the keys from the entry.
    ///             let tuple = vac_entry.into_keys();
    ///             assert_eq!(tuple, ("bearland", 1));
    ///         }
    ///     }
    /// }
    ///
    /// map.entry("some_key", 2);
    /// map.entry("another_key", 3);
    ///
    /// // The capacity of our map is not changed
    /// assert_eq!(map.capacity(), capacity_before_into_keys);
    /// ```
    #[inline]
    pub fn into_keys(self) -> (K1, K2) {
        (self.base_v.into_key(), self.base_k.into_key())
    }
}

impl<'a, K1: 'a + Clone, K2: 'a + Clone, V: 'a> VacantEntry<'a, K1, K2, V> {
    /// Sets the value of the entry with the `VacantEntry`'s keys,
    /// and returns a mutable reference to it.
    ///
    /// # Examples
    ///
    /// ```
    /// use double_map::DHashMap;
    /// use double_map::dhash_map::Entry;
    ///
    /// // So lets create some map
    /// let mut map: DHashMap<&str, u32, i32> = DHashMap::new();
    ///
    /// if let Ok(entry) = map.entry("poneyland", 0) {
    ///     match entry {
    ///         Entry::Occupied(_) => panic!("Something go wrong!!!"),
    ///         Entry::Vacant(vac_entry) => {
    ///             vac_entry.insert(37);
    ///         }
    ///     }
    /// }
    /// assert_eq!(map.get_key1(&"poneyland"), Some(&37));
    /// ```
    #[inline]
    pub fn insert(self, value: V) -> &'a mut V {
        let k2 = self.base_k.key().clone();
        self.base_k.insert(self.base_v.key().clone());
        let (_, v) = self.base_v.insert((k2, value));
        v
    }
}

/// A view into a single entry in a map, which may either be vacant or occupied.
///
/// This `enum` is constructed from the [`entry`] method on [`DHashMap`].
///
/// [`entry`]: DHashMap::entry
#[derive(Debug)]
pub enum Entry<'a, K1: 'a, K2: 'a, V: 'a> {
    /// An occupied entry.
    Occupied(OccupiedEntry<'a, K1, K2, V>),
    /// A vacant entry.
    Vacant(VacantEntry<'a, K1, K2, V>),
}

impl<'a, K1: Clone, K2: Clone, V> Entry<'a, K1, K2, V> {
    /// Ensures a value is in the entry by inserting the default if empty, and returns
    /// a mutable reference to the value in the entry.
    ///
    /// # Examples
    ///
    /// ```
    /// use double_map::DHashMap;
    ///
    /// let mut map: DHashMap<&str, u32, i32> = DHashMap::new();
    ///
    /// match map.entry("poneyland", 0) {
    ///     Ok(entry) => {
    ///         entry.or_insert(3);
    ///     }
    ///     Err(_) => unreachable!(),
    /// }
    /// assert_eq!(map.get_key1(&"poneyland"), Some(&3));
    ///
    /// map.entry("poneyland", 0).map(|entry| *entry.or_insert(10) *= 2);
    /// assert_eq!(map.get_key1(&"poneyland"), Some(&6));
    /// ```
    #[inline]
    pub fn or_insert(self, default: V) -> &'a mut V {
        match self {
            Entry::Occupied(entry) => entry.into_mut(),
            Entry::Vacant(entry) => entry.insert(default),
        }
    }

    /// Ensures a value is in the entry by inserting the result of the default function if empty,
    /// and returns a mutable reference to the value in the entry.
    ///
    /// # Examples
    ///
    /// ```
    /// use double_map::DHashMap;
    ///
    /// let mut map: DHashMap<&str, u32, String> = DHashMap::new();
    /// let s = "hoho".to_owned();
    ///
    /// match map.entry("poneyland", 0) {
    ///     Ok(entry) => {
    ///         entry.or_insert_with(|| s);
    ///     }
    ///     Err(_) => unreachable!(),
    /// }
    /// assert_eq!(map.get_key1("poneyland"), Some(&"hoho".to_owned()));
    ///
    /// let k = "another string".to_owned();
    /// map.entry("poneyland", 0).map(|entry| entry.or_insert_with(|| k).push_str("ho"));
    /// assert_eq!(map.get_key1(&"poneyland"), Some(&"hohoho".to_owned()));
    /// ```
    #[inline]
    pub fn or_insert_with<F: FnOnce() -> V>(self, default: F) -> &'a mut V {
        match self {
            Entry::Occupied(entry) => entry.into_mut(),
            Entry::Vacant(entry) => entry.insert(default()),
        }
    }

    /// Ensures a value is in the entry by inserting, if empty, the result of the default function.
    /// This method allows generating key-derived (with using key # 1 `K1`) value for
    /// insertion by providing the default function a reference to the key that was moved
    /// during the `.entry(key)` method call.
    ///
    /// The reference to the moved key is provided so that cloning or copying the key is
    /// unnecessary, unlike with `.or_insert_with(|| ... )`.
    ///
    /// # Examples
    ///
    /// ```
    /// use double_map::DHashMap;
    ///
    /// let mut map: DHashMap<&str, usize, u64> = DHashMap::new();
    ///
    ///  match map.entry("poneyland", 0) {
    ///     Ok(entry) => {
    ///         entry.or_insert_with_key1(|k1| k1.chars().count() as u64);
    ///     },
    ///     Err(_) => unreachable!(),
    /// }
    /// assert_eq!(map.get_key1(&"poneyland"), Some(&9));
    ///
    /// map.entry("bearland", 1).map(
    ///     |ent| ent.or_insert_with_key1(|k1| (k1.chars().count() * 2) as u64)
    /// );
    /// assert_eq!(map.get_key1(&"bearland"), Some(&16));
    /// ```
    #[inline]
    pub fn or_insert_with_key1<F: FnOnce(&K1) -> V>(self, default: F) -> &'a mut V {
        match self {
            Entry::Occupied(entry) => entry.into_mut(),
            Entry::Vacant(entry) => {
                let value = default(entry.key1());
                entry.insert(value)
            }
        }
    }

    /// Ensures a value is in the entry by inserting, if empty, the result of the default function.
    /// This method allows generating key-derived (with using key # 2 `K2`) value for
    /// insertion by providing the default function a reference to the key that was moved
    /// during the `.entry(key)` method call.
    ///
    /// The reference to the moved key is provided so that cloning or copying the key is
    /// unnecessary, unlike with `.or_insert_with(|| ... )`.
    ///
    /// # Examples
    ///
    /// ```
    /// use double_map::DHashMap;
    ///
    /// let mut map: DHashMap<&str, usize, u64> = DHashMap::new();
    ///
    ///  match map.entry("poneyland", 10) {
    ///     Ok(entry) => {
    ///         entry.or_insert_with_key2(|k2| (k2 + 10) as u64);
    ///     },
    ///     Err(_) => unreachable!(),
    /// }
    /// assert_eq!(map.get_key1(&"poneyland"), Some(&20));
    ///
    /// map.entry("bearland", 11).map(
    ///     |ent| ent.or_insert_with_key2(|k1| (k1 * 3) as u64)
    /// );
    /// assert_eq!(map.get_key1(&"bearland"), Some(&33));
    /// ```
    #[inline]
    pub fn or_insert_with_key2<F: FnOnce(&K2) -> V>(self, default: F) -> &'a mut V {
        match self {
            Entry::Occupied(entry) => entry.into_mut(),
            Entry::Vacant(entry) => {
                let value = default(entry.key2());
                entry.insert(value)
            }
        }
    }

    /// Ensures a value is in the entry by inserting, if empty, the result of the default function.
    /// This method allows generating key-derived (with using key #1 of type `K1` and
    /// key # 2 of type `K2`) values for insertion by providing the default function
    /// a reference to the keys that were moved during the `.entry(key)` method call.
    ///
    /// The reference to the moved keys is provided so that cloning or copying the key is
    /// unnecessary, unlike with `.or_insert_with(|| ... )`.
    ///
    /// # Examples
    ///
    /// ```
    /// use double_map::DHashMap;
    ///
    /// let mut map: DHashMap<&str, usize, u64> = DHashMap::new();
    ///
    ///  match map.entry("poneyland", 10) {
    ///     Ok(entry) => {
    ///         entry.or_insert_with_keys(|k1, k2| (k1.chars().count() + k2) as u64);
    ///     },
    ///     Err(_) => unreachable!(),
    /// }
    /// assert_eq!(map.get_key1(&"poneyland"), Some(&19));
    ///
    /// map.entry("bearland", 11).map(
    ///     |ent| ent.or_insert_with_keys(|k1, k2| (k1.chars().count() + k2 * 3) as u64)
    /// );
    /// assert_eq!(map.get_key1(&"bearland"), Some(&41));
    /// ```
    #[inline]
    pub fn or_insert_with_keys<F: FnOnce(&K1, &K2) -> V>(self, default: F) -> &'a mut V {
        match self {
            Entry::Occupied(entry) => entry.into_mut(),
            Entry::Vacant(entry) => {
                let value = default(entry.key1(), entry.key2());
                entry.insert(value)
            }
        }
    }
}

impl<'a, K1, K2, V> Entry<'a, K1, K2, V> {
    /// Returns a reference to this entry's first key (key #1).
    ///
    /// # Examples
    ///
    /// ```
    /// use double_map::DHashMap;
    ///
    /// let mut map: DHashMap<&str, u32, i32> = DHashMap::new();
    ///
    /// // It is VacantEntry
    /// match map.entry("poneyland", 0) {
    ///     Ok(entry) => {
    ///         // key equal to provided one
    ///         assert_eq!(entry.key1(), &"poneyland");
    ///         // we insert some value
    ///         entry.or_insert(25);
    ///     },
    ///     Err(_) => unreachable!(),
    /// }
    /// // As we can see, now this element exists
    /// assert_eq!(map.get_key1(&"poneyland"), Some(&25));
    ///
    /// // So now it is OccupiedEntry
    /// match map.entry("poneyland", 0) {
    ///     Ok(entry) => {
    ///         // And key equals to provided one too
    ///         assert_eq!(entry.key1(), &"poneyland");
    ///         entry.or_insert(25);
    ///     },
    ///     Err(_) => unreachable!(),
    /// }
    /// ```
    #[inline]
    pub fn key1(&self) -> &K1 {
        match *self {
            Entry::Occupied(ref entry) => entry.key1(),
            Entry::Vacant(ref entry) => entry.key1(),
        }
    }

    /// Returns a reference to this entry's second key (key #2).
    ///
    /// # Examples
    ///
    /// ```
    /// use double_map::DHashMap;
    ///
    /// let mut map: DHashMap<&str, u32, i32> = DHashMap::new();
    ///
    /// // It is VacantEntry
    /// match map.entry("poneyland", 10) {
    ///     Ok(entry) => {
    ///         // key equal to provided one
    ///         assert_eq!(entry.key2(), &10);
    ///         // we insert some value
    ///         entry.or_insert(25);
    ///     },
    ///     Err(_) => unreachable!(),
    /// }
    /// // As we can see, now this element exists
    /// assert_eq!(map.get_key2(&10), Some(&25));
    ///
    /// // So now it is OccupiedEntry
    /// match map.entry("poneyland", 10) {
    ///     Ok(entry) => {
    ///         // And key equals to provided one too
    ///         assert_eq!(entry.key2(), &10);
    ///         entry.or_insert(25);
    ///     },
    ///     Err(_) => unreachable!(),
    /// }
    /// ```
    #[inline]
    pub fn key2(&self) -> &K2 {
        match *self {
            Entry::Occupied(ref entry) => entry.key2(),
            Entry::Vacant(ref entry) => entry.key2(),
        }
    }

    /// Returns a reference to this entry's keys.
    /// Return tuple of type (&'a K1, &'a K2).
    ///
    /// # Examples
    ///
    /// ```
    /// use double_map::DHashMap;
    ///
    /// let mut map: DHashMap<&str, u32, i32> = DHashMap::new();
    ///
    /// // It is VacantEntry
    /// match map.entry("poneyland", 10) {
    ///     Ok(entry) => {
    ///         // keys equal to provided one
    ///         assert_eq!(entry.keys(), (&"poneyland", &10));
    ///         // we insert some value
    ///         entry.or_insert(25);
    ///     },
    ///     Err(_) => unreachable!(),
    /// }
    /// // As we can see, now this element exists
    /// assert_eq!(map.get_key1(&"poneyland"), Some(&25));
    ///
    /// // So now it is OccupiedEntry
    /// match map.entry("poneyland", 10) {
    ///     Ok(entry) => {
    ///         // And keys equal to provided one too
    ///         assert_eq!(entry.keys(), (&"poneyland", &10));
    ///         entry.or_insert(25);
    ///     },
    ///     Err(_) => unreachable!(),
    /// }
    /// ```
    #[inline]
    pub fn keys(&self) -> (&K1, &K2) {
        match *self {
            Entry::Occupied(ref entry) => entry.keys(),
            Entry::Vacant(ref entry) => entry.keys(),
        }
    }

    /// Provides in-place mutable access to an occupied entry before any
    /// potential inserts into the map.
    ///
    /// # Examples
    ///
    /// ```
    /// use double_map::DHashMap;
    ///
    /// let mut map: DHashMap<&str, u32, u32> = DHashMap::new();
    ///
    /// map.entry("poneyland", 1).map( |entry|
    ///    entry.and_modify(|value| { *value += 100 })
    ///    .or_insert(42)
    /// );
    /// assert_eq!(map.get_key1(&"poneyland"), Some(&42));
    ///
    /// map.entry("poneyland", 1).map( |entry|
    ///    entry.and_modify(|value| { *value += 100 })
    ///    .or_insert(42)
    /// );
    /// assert_eq!(map.get_key1(&"poneyland"), Some(&142));
    /// ```
    #[inline]
    pub fn and_modify<F>(self, f: F) -> Self
    where
        F: FnOnce(&mut V),
    {
        match self {
            Entry::Occupied(mut entry) => {
                f(entry.get_mut());
                Entry::Occupied(entry)
            }
            Entry::Vacant(entry) => Entry::Vacant(entry),
        }
    }
}

impl<'a, K1: Clone, K2: Clone, V: Default> Entry<'a, K1, K2, V> {
    /// Ensures a value is in the entry by inserting the default value if empty,
    /// and returns a mutable reference to the value in the entry.
    ///
    /// # Examples
    ///
    /// ```
    /// # fn main() {
    /// use double_map::DHashMap;
    ///
    /// let mut map: DHashMap<&str, usize, Option<u32>> = DHashMap::new();
    /// map.entry("poneyland", 1).map(|entry| entry.or_default());
    ///
    /// assert_eq!(map.get_key1(&"poneyland"), Option::<&Option<u32>>::Some(&None));
    /// # }
    /// ```
    #[inline]
    pub fn or_default(self) -> &'a mut V {
        match self {
            Entry::Occupied(entry) => entry.into_mut(),
            Entry::Vacant(entry) => entry.insert(Default::default()),
        }
    }
}

/// A view into an error kind returned by [`entry`](DHashMap::entry), [`insert`](DHashMap::insert),
/// [`try_insert`](DHashMap::try_insert) methods of the [`DHashMap`].
/// It is part of the [`EntryError`] structure, [`InsertError`] structure and [`TryInsertError`]
/// enum.
///
/// Explains why [`entry`](DHashMap::entry), [`insert`](DHashMap::insert),
/// [`try_insert`](DHashMap::try_insert) methods fail.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum ErrorKind {
    /// Returns when key #1 is vacant, but key #2 already exists with some value.
    VacantK1AndOccupiedK2,
    /// Returns when key #1 already exists with some value, but key #2 is vacant.
    OccupiedK1AndVacantK2,
    /// Returns when both key #1 and key #2 already exist with some values, but point
    /// to different entries (values).
    KeysPointsToDiffEntries,
}

impl fmt::Display for ErrorKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let error_txt = match *self {
            ErrorKind::OccupiedK1AndVacantK2 => "occupied key #1 but vacant key #2",
            ErrorKind::VacantK1AndOccupiedK2 => "vacant key #1 but occupied key #2",
            ErrorKind::KeysPointsToDiffEntries => {
                "key #1 and key #2 exist, but point to different entries"
            }
        };
        write!(f, "{}", error_txt)
    }
}

impl std::error::Error for ErrorKind {}

/// The error returned by [`entry`](DHashMap::entry) method when there is no way to distinguish
/// which entry should be returned. For more information about error kinds look at [`ErrorKind`]
/// enum.
///
/// Contains the [`ErrorKind`] enum, and the values of provided keys (that can be used for another
/// purpose).
#[derive(Debug, PartialEq)]
pub struct EntryError<K1, K2> {
    /// A view into an error kind returned by [`entry`](DHashMap::entry),
    /// [`insert`](DHashMap::insert), [`try_insert`](DHashMap::try_insert) methods of the [`DHashMap`].
    /// It is part of the [`EntryError`] structure, [`InsertError`] structure and [`TryInsertError`]
    /// enum. Explains [`entry`](DHashMap::entry), [`insert`](DHashMap::insert),
    /// [`try_insert`](DHashMap::try_insert) methods fail. For more information about error
    /// kind look at [`ErrorKind`] enum.
    pub error: ErrorKind,
    /// The provided values of keys that were returned because of error. For more information about
    /// error kind look at [`ErrorKind`] enum.
    pub keys: (K1, K2),
}

impl<K1: Debug, K2: Debug> fmt::Display for EntryError<K1, K2> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let key_txt = match self.error {
            ErrorKind::VacantK1AndOccupiedK2 => format!(
                "key #1 = {:?} - vacant, but key #2 = {:?} - exists",
                self.keys.0, self.keys.1
            ),
            ErrorKind::OccupiedK1AndVacantK2 => format!(
                "key #1 = {:?} - exists, but key #2 = {:?} - vacant",
                self.keys.0, self.keys.1
            ),
            ErrorKind::KeysPointsToDiffEntries => format!(
                "key #1 = {:?} and key #2 = {:?} point to different entries",
                self.keys.0, self.keys.1
            ),
        };
        write!(f, "failed to get entry, because {}", key_txt)
    }
}

impl<K1: Debug, K2: Debug> std::error::Error for EntryError<K1, K2> {}

/// The error returned by [`insert`](DHashMap::insert) method (and also
/// [`try_insert`](DHashMap::try_insert) method) when there is no way to distinguish
/// how given value with key #1 and key #2 should be inserted. It is also part of the
/// [`TryInsertError`] enum which is returned by [`try_insert`](DHashMap::try_insert) method
/// of [`DHashMap`]. For more information about error kinds look at [`ErrorKind`] enum.
///
/// Contains the [`ErrorKind`] enum, the provided keys and value that were not inserted.
/// These returned keys and value can be used for another purpose.
#[derive(Debug, PartialEq)]
pub struct InsertError<K1, K2, V> {
    /// A view into an error kind returned by [`entry`](DHashMap::entry),
    /// [`insert`](DHashMap::insert), [`try_insert`](DHashMap::try_insert) methods of the [`DHashMap`].
    /// It is part of the [`EntryError`] structure, [`InsertError`] structure and [`TryInsertError`]
    /// enum. Explains [`entry`](DHashMap::entry), [`insert`](DHashMap::insert),
    /// [`try_insert`](DHashMap::try_insert) methods fail. For more information about error
    /// kind look at [`ErrorKind`] enum.
    pub error: ErrorKind,
    /// The provided keys that were returned because of error. For more information about
    /// error kind look at [`ErrorKind`] enum.
    pub keys: (K1, K2),
    /// The value which was not inserted because of the error. For more information about error
    /// kind look at [`ErrorKind`] enum.
    pub value: V,
}

impl<K1: Debug, K2: Debug, V: Debug> fmt::Display for InsertError<K1, K2, V> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let key_txt = match self.error {
            ErrorKind::VacantK1AndOccupiedK2 => format!(
                "key #1 = {:?} - vacant, but key #2 = {:?} - exists",
                self.keys.0, self.keys.1
            ),
            ErrorKind::OccupiedK1AndVacantK2 => format!(
                "key #1 = {:?} - exists, but key #2 = {:?} - vacant",
                self.keys.0, self.keys.1
            ),
            ErrorKind::KeysPointsToDiffEntries => format!(
                "key #1 = {:?} and key #2 = {:?} point to different entries",
                self.keys.0, self.keys.1
            ),
        };
        write!(
            f,
            "failed to insert {:?}, because of {}",
            self.value, key_txt
        )
    }
}

impl<K1: Debug, K2: Debug, V: Debug> std::error::Error for InsertError<K1, K2, V> {}

/// The error returned by [`try_insert`](DHashMap::try_insert) (as a part of the [`TryInsertError`]
/// enum) when the keys already exist and point to the same value.
///
/// Contains the occupied entry, and the value that was not inserted. It is part of the
/// [`TryInsertError`] enum.
#[derive(Debug)]
pub struct OccupiedError<'a, K1: 'a, K2: 'a, V: 'a> {
    /// The entry in the map that was already occupied. It contains [`OccupiedEntry`] structure
    /// which is also a part of the [`Entry`] enum.
    pub entry: OccupiedEntry<'a, K1, K2, V>,
    /// The value which was not inserted, because the entry was already occupied.
    pub value: V,
}

impl<'a, K1: Debug, K2: Debug, V: Debug> fmt::Display for OccupiedError<'a, K1, K2, V> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "failed to insert {:?}, key #1 = {:?} and key #2 = {:?} already exist with value {:?}",
            self.value,
            self.entry.key1(),
            self.entry.key2(),
            self.entry.get(),
        )
    }
}

impl<'a, K1: Debug, K2: Debug, V: Debug> std::error::Error for OccupiedError<'a, K1, K2, V> {}

/// The error returned by [`try_insert`](DHashMap::try_insert) method when the keys already exist
/// and point to the same value (look at [`OccupiedError`]) or there is no way to distinguish how
/// given value with key #1 and key #2 should be inserted. For more information about error kinds
/// look at [`OccupiedError`], [`InsertError`] structures and [`ErrorKind`] enum.
///
/// Depending of error kind, this enum can contain:
/// - When there is [`TryInsertError::Occupied`] variant, it contains the occupied entry, and
/// the value that was not inserted (through [`OccupiedError`] structure).
/// - When there is [`TryInsertError::Insert`] variant, it contains the [`ErrorKind`] enum,
/// the provided keys and value that were not inserted (through [`InsertError`] structure).
#[derive(Debug)]
pub enum TryInsertError<'a, K1: 'a, K2: 'a, V: 'a> {
    /// The error kind returned by [`try_insert`](DHashMap::try_insert) when the keys already
    /// exist and point to the same value. Contains the [`OccupiedError`] structure.
    Occupied(OccupiedError<'a, K1, K2, V>),
    /// The error kind returned by [`try_insert`](DHashMap::try_insert) method when there is no
    /// way to distinguish how given value with key #1 and key #2 should be inserted. For more
    /// information about error kinds look at [`InsertError`] structure and [`ErrorKind`] enum.
    ///
    /// Contains the [`InsertError`] structure.
    Insert(InsertError<K1, K2, V>),
}

impl<'a, K1: Debug, K2: Debug, V: Debug> fmt::Display for TryInsertError<'a, K1, K2, V> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let txt = match self {
            TryInsertError::Occupied(error) => error.to_string(),
            TryInsertError::Insert(error) => error.to_string(),
        };
        write!(f, "{}", txt)
    }
}

impl<'a, K1: Debug, K2: Debug, V: Debug> std::error::Error for TryInsertError<'a, K1, K2, V> {}
