//! double-map
//!
//! `DHashMap` is like a `std::collection::HashMap`, but allow to use double key to single data/value
//!

#![warn(rustdoc::broken_intra_doc_links)]
#![warn(missing_docs)]

#[cfg(test)]
mod tests_double_map;

use core::hash::{BuildHasher, Hash};
use core::borrow::Borrow;
use std::collections::hash_map;
use std::collections::HashMap;
use std::collections::TryReserveError;
use core::fmt::{self, Debug};
use core::hint::unreachable_unchecked;
use core::mem;

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
/// it for small keys such as integers as well as large keys such as long
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

#[derive(Clone)]
pub struct DHashMap<K1, K2, V, S = hash_map::RandomState> {
    value_map: HashMap<K1, (K2, V), S>,
    key_map: HashMap<K2, K1, S>,
}

impl<K1, K2, V> DHashMap<K1, K2, V, hash_map::RandomState> {
    /// Creates a new empty [`DHashMap`] with [`RandomState`](std::collections::hash_map::RandomState)
    /// type of hash builder to hash keys.
    ///
    /// The primary key is of type `K1` and the secondary key is of type `K2`.
    /// The value is of type `V`.
    ///
    /// Internally, two [`HashMap`](`std::collections::HashMap`) are created. One of type
    /// `HashMap<K1, (K2, V)>` to hold the `(K2, V)` tuple, and second one of type
    /// `HashMap<K2, K1>` just for holding the primary key of type `K1`.
    /// We hold the `(K2, V)` tuple inside first `Hashmap` for synchronization purpose,
    /// so that we can organize checking that both primary key of type `K1` and the
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
    /// // The created DHashMap hold none elements
    /// assert_eq!(map.len(), 0);
    ///
    /// // The created DHashMap also didn't allocate memory
    /// assert_eq!(map.capacity(), 0);
    ///
    /// // Now we insert elements inside created DHashMap
    /// map.insert(1, "One", 1);
    /// // We can see that the DHashMap hold 1 element
    /// assert_eq!(map.len(), 1);
    /// // And it also allocate some capacity (by default it starts from 3 element)
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
    /// // The created DHashMap hold none elements
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
    /// // We can see that the DHashMap hold 5 elements
    /// assert_eq!(map.len(), 5);
    /// // But it capacity dosn't changed
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
    /// [`HashMap`] inside [`DHashMap`], so that we need to
    /// [`clone`](core::clone::Clone::clone) hash_builder for passing it inside
    /// two inner `HashMap`.
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
    /// // The created DHashMap hold none elements
    /// assert_eq!(map.len(), 0);
    ///
    /// // The created DHashMap also didn't allocate memory
    /// assert_eq!(map.capacity(), 0);
    ///
    /// // Now we insert elements inside created DHashMap
    /// map.insert("One", 1, 2);
    /// // We can see that the DHashMap hold 1 element
    /// assert_eq!(map.len(), 1);
    /// // And it also allocate some capacity (by default it starts from 3 element)
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
    /// [`HashMap`] inside [`DHashMap`], so that we need to
    /// [`clone`](core::clone::Clone::clone) hash_builder for passing it inside
    /// two inner `HashMap`.
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
    /// // The created DHashMap hold none elements
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
    /// // We can see that the DHashMap hold 5 elements
    /// assert_eq!(map.len(), 5);
    /// // But it capacity dosn't changed
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
    /// # Examples
    ///
    /// ```
    /// use double_map::DHashMap;
    /// let map = DHashMap::<i32, &str, &str>::with_capacity(16);
    ///
    /// // The created DHashMap can hold at least 16 elements
    /// assert!(map.capacity() >= 16);
    /// // But for not it dosn't hold any element
    /// assert_eq!(map.len(), 0);
    /// ```
    #[inline]
    pub fn capacity(&self) -> usize {
        // we only take into account because it contain the most important part of
        // hashtable - the value
        self.value_map.capacity()
    }

    /// Returns the number of elements in the map.
    ///
    /// # Examples
    ///
    /// ```
    /// use double_map::{DHashMap, dhashmap};
    ///
    /// let mut a = DHashMap::new();
    /// // The created DHashMap didn't hold any element
    /// assert_eq!(a.len(), 0);
    /// // We insert one element
    /// a.insert(1, "Breakfast", "Pancakes");
    /// // And can be sure that DHashMap hold one element
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
        // we only take into account because it contain the most important part of
        // hashtable - the value
        self.value_map.len()
    }

    /// Returns `true` if the map contains no elements.
    ///
    /// # Examples
    ///
    /// ```
    /// use double_map::DHashMap;
    ///
    /// let mut a = DHashMap::new();
    /// // The created DHashMap didn't hold any element, so it's empty
    /// assert!(a.is_empty() && a.len() == 0);
    /// // We insert one element
    /// a.insert(1, "a", "One");
    /// // And can be sure that DHashMap is not empty but hold one element
    /// assert!(!a.is_empty() && a.len() == 1);
    /// ```
    #[inline]
    pub fn is_empty(&self) -> bool {
        // we only take into account because it contain the most important part of
        // hashtable - the value
        self.value_map.is_empty()
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
    /// // We can that see DHashMap hold two elements
    /// assert_eq!(a.len(), 2);
    /// let capacity_before_clearing = a.capacity();
    ///
    /// a.clear();
    ///
    /// // And now the map is empty and contain no element
    /// assert!(a.is_empty() && a.len() == 0);
    /// // But map capacity is equal to old one
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
    /// // Let's check that it return error if can not reserve asked capacity
    /// let result = map.try_reserve(usize::MAX);
    /// match result {
    ///     Err(_) => println!("It is ok, error was expected"),
    ///     Ok(_) => unreachable!(),
    /// }
    /// // And capacity of the map didn't changed
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
    /// Note that in the general case the capacity is not *guaranteed* to shrink,
    /// but a zero-length DHashMap should generally shrink to capacity zero.
    ///
    /// # Examples
    ///
    /// ```
    /// use double_map::DHashMap;
    /// let mut a = DHashMap::<i32, &str, &str>::with_capacity(16);
    ///
    /// // This DHashMap can hold at least 16 element
    /// let capacity_before_shrink = a.capacity();
    /// assert!(capacity_before_shrink >= 16);
    ///
    /// // And after shrinking, map capacity is less that before
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
    /// // reserved before, but inserted elements still inside map
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
    /// // We have only 3 elements inside map, so it work
    /// map.shrink_to(10);
    /// assert!(map.capacity() >= 10 && map.capacity() < 100);
    ///
    /// // If we try shrink_to the capacity, that less then elements quantity inside map
    /// map.shrink_to(0);
    /// // So it work partially, but the resulting capacity not less than quantity
    /// // of elements inside map
    /// assert!(map.capacity() >= 3  && map.capacity() < 10);
    /// ```
    #[inline]
    pub fn shrink_to(&mut self, min_capacity: usize) {
        self.value_map.shrink_to(min_capacity);
        self.key_map.shrink_to(min_capacity);
    }

    /// Returns a reference to the value corresponding to the given primary key (key #1).
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
        let (_, value) = self.value_map.get(k1)?;
        Some(value)
    }

    /// Returns a reference to the value corresponding to the given secondary key (key #2).
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
        let key = self.key_map.get(k2)?;
        let (_, value) = self.value_map.get(key)?;
        Some(value)
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
        let (_, value) = self.value_map.get_mut(k1)?;
        Some(value)
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
        let key = self.key_map.get(k2)?;
        let (_, value) = self.value_map.get_mut(key)?;
        Some(value)
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
    /// This method removes not only value, but whole element includng
    /// primary `K1` and secondary `K2` keys
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
    /// // We can see that DHashMap hold three elements
    /// assert!(map.len() == 3 && map.capacity() >= 3);
    ///
    /// // Also we reserve memory for holdind additionally at least 20 elements,
    /// // so that DHashMap can hold 23 elements or more
    /// map.reserve(20);
    /// let capacity_before_remove = map.capacity();
    ///
    /// // We remove element with key #1 from the map and get corresponding value
    /// assert_eq!(map.remove_key1(&1), Some("Eins".to_owned()));
    /// // If we try remove the same element with key #1 twise we get None,
    /// // because that element already removed
    /// assert_eq!(map.remove_key1(&1), None);
    ///
    /// // Now we remove all elements one by one, and can see that map hold nothing
    /// map.remove_key1(&2);
    /// map.remove_key1(&3);
    /// assert_eq!(map.len(), 0);
    ///
    /// // But map capacity is equal to old one and can hold at least 23 elements
    /// assert!(map.capacity() == capacity_before_remove && map.capacity() >= 23);
    /// ```
    #[inline]
    pub fn remove_key1<Q: ?Sized>(&mut self, key: &Q) -> Option<V>
    where
        K1: Borrow<Q>,
        Q: Hash + Eq,
    {
        let (key, value) = self.value_map.remove(key)?;
        self.key_map.remove(&key);
        Some(value)
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
    /// This method removes not only value, but whole element includng
    /// primary `K1` and secondary `K2` keys
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
    /// // We can see that DHashMap hold three elements
    /// assert!(map.len() == 3 && map.capacity() >= 3);
    ///
    /// // Also we reserve memory for holdind additionally at least 20 elements,
    /// // so that DHashMap can hold 23 elements or more
    /// map.reserve(20);
    /// let capacity_before_remove = map.capacity();
    ///
    /// // We remove element with key #1 from the map and get corresponding value
    /// assert_eq!(map.remove_key2(&"One"), Some("Eins".to_owned()));
    /// // If we try remove the same element with key #1 twise we get None,
    /// // because that element already removed
    /// assert_eq!(map.remove_key2(&"One"), None);
    ///
    /// // Now we remove all elements one by one, and can see that map hold nothing
    /// map.remove_key2(&"Two");
    /// map.remove_key2(&"Three");
    /// assert_eq!(map.len(), 0);
    ///
    /// // But map capacity is equal to old one and can hold at least 23 elements
    /// assert!(map.capacity() == capacity_before_remove && map.capacity() >= 23);
    /// ```
    #[inline]
    pub fn remove_key2<Q: ?Sized>(&mut self, key: &Q) -> Option<V>
    where
        K2: Borrow<Q>,
        Q: Hash + Eq,
    {
        let key = self.key_map.remove(key)?;
        let (_, value) = self.value_map.remove(&key)?;
        Some(value)
    }
}

impl<K1, K2, V, S> DHashMap<K1, K2, V, S>
where
    K1: Eq + Hash + Clone,
    K2: Eq + Hash + Clone,
    S: BuildHasher,
{
    /// Tries to gets the given keys' corresponding entry in the map for in-place
    /// manipulation.
    ///
    /// Returns [`Entry`] enum if `all` of the following is `true`:
    /// - Both key #1 and key #2 are vacant.
    /// - If both key #1 and key #2 exist, they refer to the same value.
    ///
    /// When the above statements is `false`, [`entry`](DHashMap::entry) method return
    /// [`EntryError`] structure which contains the [`ErrorKind`] enum, and the values
    /// of provided keys that were not used for creation entry (that can be used for
    /// another purpose).
    ///
    /// Depending on the points below, different [`ErrorKind`] variants may be returned:
    /// - When key #1 is vacant, but key #2 is already exists with some value the
    /// returned [`ErrorKind`] variant is [`ErrorKind::VacantK1AndOccupiedK2`].
    /// - When key #1 is already exists with some value, but key #2 is vacant the
    /// returned [`ErrorKind`] variant is [`ErrorKind::OccupiedK1AndVacantK2`].
    /// - When both key #1 and key #2 is already exists with some values, but points
    /// to different entries (values) the returned [`ErrorKind`] variant is
    /// [`ErrorKind::KeysPointsToDiffEntries`].
    ///
    /// # Examples
    ///
    /// ```
    /// use double_map::{DHashMap, ErrorKind};
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
    /// // Return `ErrorKind::OccupiedK1AndVacantK2` if key #1 is already
    /// // exists with some value, but key #2 is vacant.
    /// let error_kind = letters.entry('s', 'y').unwrap_err().error;
    /// assert_eq!(error_kind, ErrorKind::OccupiedK1AndVacantK2);
    ///
    /// // Return `ErrorKind::VacantK1AndOccupiedK2` if key #1 is vacant,
    /// // but key #2 is already exists with some value.
    /// let error_kind = letters.entry('y', 's').unwrap_err().error;
    /// assert_eq!(error_kind, ErrorKind::VacantK1AndOccupiedK2);
    ///
    /// // Return `ErrorKind::KeysPointsToDiffEntries` if both
    /// // key #1 and key #2 are already exists with some values,
    /// // but points to different entries (values).
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
        // leave this implementation this way for now
        match self.value_map.get(&k1) {
            None => match self.key_map.get(&k2) {
                None => {
                    // SAFETY: We already check that both key vacant
                    Ok( unsafe { self.map_vacant_entry(k1, k2) } )
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
                        Ok( unsafe { self.map_occupied_entry(k1, k2) } )
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
                hash_map::Entry::Vacant(base_k) => {
                    Entry::Vacant(VacantEntry { base_v, base_k })
                },
                _ => unreachable_unchecked(),
            },
            _ => unreachable_unchecked(),
        }
    }

    /// Inserts given keys and value into the map **`without checking`**. Update the value
    /// if key #1 of type `K1` already present with returning old value.
    ///
    /// If the map did not have these keys present, [`None`] is returned.
    ///
    /// # Warning
    ///
    /// **Using this method can lead to unsynchronization between key #1 and key #1,
    /// so that they can refer to different values.** It also can lead to different
    /// quantity of keys, so that quantity of keys #2 `K2` can be ***less**** than
    /// quantity of keys #1 `K1`.
    ///
    /// If the map did have these keys vacant or **present** and **both keys refer to
    /// the same value** it is ***Ok***, the value is updated, and the old value is
    /// returned inside `Some(V)` variant.
    ///
    /// **But** for this method, it doesn't matter if key # 2 exist or not,
    /// it return updated value also if the map contain only key #1.
    /// It is ***because*** this method **don't check** that:
    /// - key #1 is vacant, but key #2 is already exists with some value;
    /// - key #1 is already exists with some value, but key #2 is vacant;
    /// - both key #1 and key #2 is already exists with some values, but
    /// points to different entries (values).
    ///
    /// The keys is not updated, though; this matters for types that can
    /// be `==` without being identical. See the [std module-level documentation]
    /// for more.
    ///
    /// # Note
    ///
    /// Using this method is cheaper that using another insertion
    /// [`entry`](DHashMap::entry), [`insert`](DHashMap::insert) and
    /// [`try_insert`](DHashMap::try_insert) methods.
    ///
    /// Links between keys #1 `K1` and the values that they refer are adequate.
    /// **Unsynchronization** between key #1 and key #1, lead only to that the key # 2
    /// may refer to unexpected value.
    ///
    /// It is recommended to use this method only if you are sure that
    /// key #1 and key #2 are unique. For example if key #1 `K1` are generated automatically
    /// and you check only that there is no key #2 `K2`.
    ///
    /// [std module-level documentation]: std::collections#insert-and-complex-keys
    ///
    /// # Examples
    ///
    /// ```
    /// use double_map::{DHashMap, ErrorKind, InsertError};
    /// use core::hash::Hash;
    ///
    /// let mut map = DHashMap::new();
    ///
    /// // Return None if keys vacant
    /// assert_eq!(map.insert_unchecked(1, "a", "One"), None);
    /// assert_eq!(map.is_empty(), false);
    ///
    /// // If the map did have these key present, the value is updated,
    /// // and the old value is returned inside `Some(V)` variants
    /// map.insert_unchecked(2, "b", "Two");
    /// assert_eq!(map.insert_unchecked(2, "b", "Second"), Some("Two"));
    /// assert_eq!(map.get_key1(&2), Some(&"Second"));
    ///
    /// // But methods does not care about key #2
    /// assert_eq!(map.insert_unchecked(1, "b", "First"), Some("One"));
    /// // So key # 2 refer to unexpected value, and now we have double second keys
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
        let (_, v) = self.value_map.insert(k1, (k2, v))?;
        Some(v)
    }

    /// Tries to inserts given keys and value into the map. Update the value
    /// if keys already present and refer to the same value with returning
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
    /// The [`insert`](DHashMap::insert) method return [`InsertError`] structure
    /// (inside of `Some(Err(_))` variants):
    /// - when key #1 is vacant, but key #2 is already exists with some value;
    /// - when key #1 is already exists with some value, but key #2 is vacant;
    /// - when both key #1 and key #2 is already exists with some values, but
    /// points to different entries (values).
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
    /// use double_map::{DHashMap, ErrorKind, InsertError};
    ///
    /// let mut map = DHashMap::new();
    ///
    /// // Return None if keys vacant
    /// assert_eq!(map.insert(1, "a", "One"), None);
    /// assert_eq!(map.is_empty(), false);
    ///
    /// // If the map did have these key present, and both keys refer to
    /// // the same value, the value is updated, and the old value is returned
    /// // inside `Some(Ok(V))` variants
    /// map.insert(2, "b", "Two");
    /// assert_eq!(map.insert(2, "b", "Second"), Some(Ok("Two")));
    /// assert_eq!(map.get_key1(&2), Some(&"Second"));
    ///
    /// // Return `ErrorKind::OccupiedK1AndVacantK2` if key #1 is already
    /// // exists with some value, but key #2 is vacant. Error structure
    /// // also contain provided keys and value
    /// match map.insert(1, "c", "value") {
    ///     Some(Err(InsertError{ error, keys, value })) => {
    ///         assert_eq!(error, ErrorKind::OccupiedK1AndVacantK2);
    ///         assert_eq!(keys, (1, "c"));
    ///         assert_eq!(value, "value");
    ///     }
    ///     _ => unreachable!(),
    /// }
    ///
    /// // Return `ErrorKind::VacantK1AndOccupiedK2` if key #1 is vacant,
    /// // but key #2 is already exists with some value.
    /// let error_kind = map.insert(3, "a", "value").unwrap().unwrap_err().error;
    /// assert_eq!(error_kind, ErrorKind::VacantK1AndOccupiedK2);
    ///
    /// // Return `ErrorKind::KeysPointsToDiffEntries` if both
    /// // key #1 and key #2 are already exists with some values,
    /// // but points to different entries (values).
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

    /// Tries to inserts given keys and value into the map, and returns
    /// a mutable reference to the value in the entry if the map did not
    /// have these keys present.
    ///
    /// If the map did have these key **present**, and **both keys refer to
    /// the same value**, ***nothing*** is updated, and a [`TryInsertError::Occupied`]
    /// enum variant error containing [`OccupiedError`] structure is returned.
    /// The [`OccupiedError`] contains the occupied entry [`OccupiedEntry`],
    /// and the value that was not inserted.
    ///
    /// The [`try_insert`](DHashMap::try_insert) method return [`InsertError`] structure
    /// (inside of [`TryInsertError::Insert`] variant):
    /// - when key #1 is vacant, but key #2 is already exists with some value;
    /// - when key #1 is already exists with some value, but key #2 is vacant;
    /// - when both key #1 and key #2 is already exists with some values, but
    /// points to different entries (values).
    ///
    /// The above mentioned error kinds can be matched through the [`ErrorKind`] enum.
    /// Returned [`InsertError`] structure also contain provided keys and value
    /// that were not inserted and can be used for another purpose.
    ///
    /// # Examples
    ///
    /// ```
    ///  use double_map::{DHashMap, TryInsertError, ErrorKind, OccupiedEntry,
    ///  OccupiedError, InsertError};
    ///
    /// let mut map = DHashMap::new();
    ///
    /// // Return mutable reference to the value if keys vacant
    /// let value = map.try_insert(1, "a", "One").unwrap();
    /// assert_eq!(value, &"One");
    /// *value = "First";
    /// assert_eq!(map.get_key1(&1), Some(&"First"));
    ///
    /// // If the map did have these key present, and both keys refer to
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
    /// // Return `ErrorKind::OccupiedK1AndVacantK2` if key #1 is already
    /// // exists with some value, but key #2 is vacant. Error structure
    /// // also contain provided keys and value
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
    /// // Return `ErrorKind::VacantK1AndOccupiedK2` if key #1 is vacant,
    /// // but key #2 is already exists with some value.
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
    /// // Return `ErrorKind::KeysPointsToDiffEntries` if both
    /// // key #1 and key #2 are already exists with some values,
    /// // but points to different entries (values).
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

/// Create a `DHashMap<K1, K2, V,` [`RandomState`](std::collections::hash_map::RandomState)`>`
/// from a list of sequentially given keys and values.
///
/// Input data list must follow one of this rules:
/// - `K1`, `K2` => `V`, `K1`, `K2` => `V` ... and so on;
/// - (`K1`, `K2`) => `V`, (`K1`, `K2`) => `V` ... and so on.
///
/// Last comma separator can be omitted.
/// If this macros called without arguments, i.e. like
/// ```
/// # use double_map::{DHashMap, dhashmap};
/// let map: DHashMap<i32, String, String>  = dhashmap![];
/// ```
/// it equivalent to [`DHashMap::new()`] function
///
/// ## Example
///
/// ```
/// use double_map::{DHashMap, dhashmap};
///
/// // Calling macros without arguments equivalent to DHashMap::new() function
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

impl<K1, K2, V, S> FromIterator<(K1, K2, V)> for DHashMap<K1, K2, V, S>
where
    K1: Eq + Hash + Clone,
    K2: Eq + Hash + Clone,
    S: BuildHasher + Default + Clone,
{
    fn from_iter<T: IntoIterator<Item = (K1, K2, V)>>(iter: T) -> DHashMap<K1, K2, V, S> {
        let mut map = DHashMap::with_hasher(Default::default());
        map.extend(iter);
        map
    }
}

impl<K1, K2, V, S> Extend<(K1, K2, V)> for DHashMap<K1, K2, V, S>
where
    K1: Eq + Hash + Clone,
    K2: Eq + Hash + Clone,
    S: BuildHasher,
{
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
    /// use double_map::{DHashMap, Entry};
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
    /// use double_map::{DHashMap, Entry};
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
    /// use double_map::{DHashMap, Entry};
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
    /// use double_map::{DHashMap, Entry};
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
    /// // But the capacity of our map didn't changed and still equal to the capacity before
    /// // using `remove_entry` method
    /// assert_eq!(map.capacity(), capacity_before_entries_remove);
    /// ```
    #[inline]
    pub fn remove_entry(self) -> (K1, K2, V) {
        self.base_k.remove_entry();
        let (k1, (k2, v)) = self.base_v.remove_entry();
        (k1, k2, v)
    }

    /// Gets a reference to the value of type `V` in the entry.
    ///
    /// # Examples
    ///
    /// ```
    /// use double_map::{DHashMap, Entry};
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
    /// use double_map::{DHashMap, Entry};
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
    /// use double_map::{DHashMap, Entry};
    ///
    /// let mut map: DHashMap<&str, u32, i32> = DHashMap::new();
    /// map.insert("poneyland", 0, 12);
    /// assert_eq!(map.get_key1("poneyland"), Some(&12));
    /// assert_eq!(map.get_key2(&0),          Some(&12));
    ///
    /// // Let's create a variable that outlive the OccupiedEntry (with some initial value)
    /// let mut value: &mut i32 = &mut 0;
    ///
    /// if let Ok(entry) = map.entry("poneyland", 0) {
    ///     match entry {
    ///         Entry::Occupied(oc_entry) => {
    ///             // So we can converts the OccupiedEntry into a mutable reference to the value.
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
    /// use double_map::{DHashMap, Entry};
    ///
    /// let mut map: DHashMap<&str, u32, i32> = DHashMap::new();
    /// map.insert("poneyland", 0, 12);
    /// assert_eq!(map.get_key1("poneyland"), Some(&12));
    /// assert_eq!(map.get_key2(&0),          Some(&12));
    ///
    /// // Let's create a variable that hold value
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
    /// use double_map::{DHashMap, Entry};
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
    /// // But the capacity of our map didn't changed and still equal to the capacity before
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

impl<'a, K1: 'a, K2: 'a, V: 'a> VacantEntry<'a, K1, K2, V>
where
    K1: Clone,
    K2: Clone,
{
    /// Gets a reference to the key #1 of type `K1` that would be used
    /// when inserting a value through the `VacantEntry`.
    ///
    /// # Examples
    ///
    /// ```
    /// use double_map::{DHashMap, Entry};
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
    /// use double_map::{DHashMap, Entry};
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
    /// use double_map::{DHashMap, Entry};
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
    /// use double_map::{DHashMap, Entry};
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
    /// // The capacity of our map not changed
    /// assert_eq!(map.capacity(), capacity_before_into_keys);
    /// ```
    #[inline]
    pub fn into_keys(self) -> (K1, K2) {
        (self.base_v.into_key(), self.base_k.into_key())
    }

    /// Sets the value of the entry with the `VacantEntry`'s keys,
    /// and returns a mutable reference to it.
    ///
    /// # Examples
    ///
    /// ```
    /// use double_map::{DHashMap, Entry};
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

impl<'a, K1, K2, V> Entry<'a, K1, K2, V>
where
    K1: Eq + Hash + Clone,
    K2: Eq + Hash + Clone,
{
    /// Ensures a value is in the entry by inserting the default if empty, and returns
    /// a mutable reference to the value in the entry.
    ///
    /// # Examples
    ///
    /// ```
    /// use double_map::{DHashMap, Entry};
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
    /// use double_map::{DHashMap, Entry};
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
    /// This method allows for generating key-derived (with using key # 1 `K1`) values for
    /// insertion by providing the default function a reference to the key that was moved
    /// during the `.entry(key)` method call.
    ///
    /// The reference to the moved key is provided so that cloning or copying the key is
    /// unnecessary, unlike with `.or_insert_with(|| ... )`.
    ///
    /// # Examples
    ///
    /// ```
    /// use double_map::{DHashMap, Entry};
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
    /// This method allows for generating key-derived (with using key # 2 `K2`) values for
    /// insertion by providing the default function a reference to the key that was moved
    /// during the `.entry(key)` method call.
    ///
    /// The reference to the moved key is provided so that cloning or copying the key is
    /// unnecessary, unlike with `.or_insert_with(|| ... )`.
    ///
    /// # Examples
    ///
    /// ```
    /// use double_map::{DHashMap, Entry};
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
    /// This method allows for generating key-derived (with using key #1 `K1` and key # 2 `K2`)
    /// values for insertion by providing the default function a reference to the keys that
    /// were moved during the `.entry(key)` method call.
    ///
    /// The reference to the moved keys is provided so that cloning or copying the key is
    /// unnecessary, unlike with `.or_insert_with(|| ... )`.
    ///
    /// # Examples
    ///
    /// ```
    /// use double_map::{DHashMap, Entry};
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

    /// Returns a reference to this entry's first key (key #1).
    ///
    /// # Examples
    ///
    /// ```
    /// use double_map::{DHashMap, Entry};
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
    /// // As we can see, now this element exist
    /// assert_eq!(map.get_key1(&"poneyland"), Some(&25));
    ///
    /// // So now it is OccupiedEntry
    /// match map.entry("poneyland", 0) {
    ///     Ok(entry) => {
    ///         // And key equal to provided one too
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
    /// use double_map::{DHashMap, Entry};
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
    /// // As we can see, now this element exist
    /// assert_eq!(map.get_key2(&10), Some(&25));
    ///
    /// // So now it is OccupiedEntry
    /// match map.entry("poneyland", 10) {
    ///     Ok(entry) => {
    ///         // And key equal to provided one too
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
    /// use double_map::{DHashMap, Entry};
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
    /// // As we can see, now this element exist
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

impl<'a, K1, K2, V: Default> Entry<'a, K1, K2, V>
where
    K1: Eq + Hash + Clone,
    K2: Eq + Hash + Clone,
{
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
    /// Returns when key #1 is vacant, but key #2 is already exists with some value.
    VacantK1AndOccupiedK2,
    /// Returns when key #1 is already exists with some value, but key #2 is vacant.
    OccupiedK1AndVacantK2,
    /// Returns when both key #1 and key #2 is already exists with some values, but points
    /// to different entries (values).
    KeysPointsToDiffEntries,
}

impl fmt::Display for ErrorKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let error_txt = match *self {
            ErrorKind::OccupiedK1AndVacantK2 => "occupied key #1 but vacant key #2",
            ErrorKind::VacantK1AndOccupiedK2 => "vacant key #1 but occupied key #2",
            ErrorKind::KeysPointsToDiffEntries => {
                "key #1 and key #2 exists, but points to different entries"
            }
        };
        write!(f, "{}", error_txt)
    }
}

impl std::error::Error for ErrorKind {}

/// The error returned by [`entry`](DHashMap::entry) method when there is no way to distinguish
/// which entry should be returned. For more information about error kinds look to [`ErrorKind`]
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
    /// kind look to [`ErrorKind`] enum.
    pub error: ErrorKind,
    /// The provided values of keys that was returned because of error. For more information about
    /// error kind look to [`ErrorKind`] enum.
    pub keys: (K1, K2),
}

impl<K1: Debug, K2: Debug> fmt::Display for EntryError<K1, K2> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let key_txt = match self.error {
            ErrorKind::VacantK1AndOccupiedK2 => format!(
                "key #1 = {:?} - vacant, but key #2 = {:?} - exist",
                self.keys.0, self.keys.1
            ),
            ErrorKind::OccupiedK1AndVacantK2 => format!(
                "key #1 = {:?} - exist, but key #2 = {:?} - vacant",
                self.keys.0, self.keys.1
            ),
            ErrorKind::KeysPointsToDiffEntries => format!(
                "key #1 = {:?} and key #2 = {:?} points to different entries",
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
/// [`TryInsertError`] enum which if returned by [`try_insert`](DHashMap::try_insert) method
/// of [`DHashMap`]. For more information about error kinds look to [`ErrorKind`] enum.
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
    /// kind look to [`ErrorKind`] enum.
    pub error: ErrorKind,
    /// The provided keys that was returned because of error. For more information about
    /// error kind look to [`ErrorKind`] enum.
    pub keys: (K1, K2),
    /// The value which was not inserted because of the error. For more information about error
    /// kind look to [`ErrorKind`] enum.
    pub value: V,
}

impl<K1: Debug, K2: Debug, V: Debug> fmt::Display for InsertError<K1, K2, V> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let key_txt = match self.error {
            ErrorKind::VacantK1AndOccupiedK2 => format!(
                "key #1 = {:?} - vacant, but key #2 = {:?} - exist",
                self.keys.0, self.keys.1
            ),
            ErrorKind::OccupiedK1AndVacantK2 => format!(
                "key #1 = {:?} - exist, but key #2 = {:?} - vacant",
                self.keys.0, self.keys.1
            ),
            ErrorKind::KeysPointsToDiffEntries => format!(
                "key #1 = {:?} and key #2 = {:?} points to different entries",
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
/// enum) when the keys already exists and points to the same value.
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

impl<'a, K1, K2, V> fmt::Display for OccupiedError<'a, K1, K2, V>
where
    K1: Eq + Hash + Clone + Debug,
    K2: Eq + Hash + Clone + Debug,
    V: Debug,
{
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

impl<'a, K1, K2, V> std::error::Error for OccupiedError<'a, K1, K2, V>
where
    K1: Eq + Hash + Clone + Debug,
    K2: Eq + Hash + Clone + Debug,
    V: Debug,
{
}

/// The error returned by [`try_insert`](DHashMap::try_insert) method when the keys already exists
/// and points to the same value (look to [`OccupiedError`]) or there is no way to distinguish how
/// given value with key #1 and key #2 should be inserted. For more information about error kinds
/// look to [`OccupiedError`], [`InsertError`] structures and [`ErrorKind`] enum.
///
/// Depending of error kind, this enum can contain:
/// - When there is [`TryInsertError::Occupied`] variant, it contains the occupied entry, and
/// the value that was not inserted (through [`OccupiedError`] structure).
/// - When there is [`TryInsertError::Insert`] variant, it contains the [`ErrorKind`] enum,
/// the provided keys and value that were not inserted (through [`InsertError`] structure).
#[derive(Debug)]
pub enum TryInsertError<'a, K1: 'a, K2: 'a, V: 'a> {
    /// The error kind returned by [`try_insert`](DHashMap::try_insert) when the keys already
    /// exists and points to the same value. Contains the [`OccupiedError`] structure.
    Occupied(OccupiedError<'a, K1, K2, V>),
    /// The error kind returned by [`try_insert`](DHashMap::try_insert) method when there is no
    /// way to distinguish how given value with key #1 and key #2 should be inserted. For more
    /// information about error kinds look to [`InsertError`] structure and [`ErrorKind`] enum.
    ///
    /// Contains the [`InsertError`] structure.
    Insert(InsertError<K1, K2, V>),
}

impl<'a, K1, K2, V> fmt::Display for TryInsertError<'a, K1, K2, V>
where
    K1: Eq + Hash + Clone + Debug,
    K2: Eq + Hash + Clone + Debug,
    V: Debug,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let txt = match self {
            TryInsertError::Occupied(error) => error.to_string(),
            TryInsertError::Insert(error) => error.to_string(),
        };
        write!(f, "{}", txt)
    }
}

impl<'a, K1, K2, V> std::error::Error for TryInsertError<'a, K1, K2, V>
where
    K1: Eq + Hash + Clone + Debug,
    K2: Eq + Hash + Clone + Debug,
    V: Debug,
{
}