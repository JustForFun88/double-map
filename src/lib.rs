//! double-map
//!
//! `DHashMap` is like a `std::collection::HashMap`, but allow to use double key to single data/value
//! 

use std::collections::hash_map;
use std::collections::HashMap;
use std::collections::TryReserveError;
use core::hash::{BuildHasher, Hash};
use std::borrow::Borrow;
use std::mem;
use std::fmt::{self, Debug};

#[derive(Clone)]
pub struct DHashMap<K1, K2, V, S = hash_map::RandomState>
{
    value_map: HashMap<K1, (K2, V), S>,
    key_map: HashMap<K2, K1, S>,
}

impl<K1, K2, V> DHashMap<K1, K2, V, hash_map::RandomState>
{
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
    /// secondary key is of type `K2` refers to the same value, and so on.
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
    S: Clone
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

impl<K1, K2, V, S> DHashMap<K1, K2, V, S>
{
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
    /// assert!(a.is_empty()  && a.len() == 0);
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
    /// Panics if the new allocation size overflows [`usize::Max`] / 2.
    ///
    /// # Examples
    ///
    /// ```
    /// use double_map::DHashMap;
    /// let mut a = DHashMap::<&str, i128, &str>::new();
    /// a.insert("apple",  1, "a");
    /// a.insert("banana", 2, "b");
    /// a.insert("Cherry", 3, "c");
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
    /// use double_map::DHashMap;
    ///
    /// let mut map: DHashMap<i32, &str, isize> = DHashMap::new();
    /// map.try_reserve(10).expect("something go wrong");
    /// assert!(map.capacity() >= 10);
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
    /// // And after shrink it capacity is less that before
    /// a.shrink_to_fit();
    /// assert!(a.capacity() < capacity_before_shrink);
    /// 
    /// // If we reserve some memory and insert some elements
    /// a.reserve(100);
    /// a.insert(1, "a", "One");
    /// a.insert(1, "b", "Two");
    /// assert!(a.capacity() >= 100);
    /// 
    /// // After shrink_to_fit method the capacity If we reserve some memory and insert some elements
    /// a.shrink_to_fit();
    /// assert!(a.capacity() >= 2 && a.capacity() < 100);
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
    /// map.shrink_to(10);
    /// assert!(map.capacity() >= 10 && map.capacity() < 100);
    /// map.shrink_to(0);
    /// assert!(map.capacity() >= 3  && map.capacity() < 10);
    /// ```
    #[inline]
    pub fn shrink_to(&mut self, min_capacity: usize) {
        self.value_map.shrink_to(min_capacity);
        self.key_map.shrink_to(min_capacity);
    }

    /// Tries to gets the given keys' corresponding entry in the map for in-place manipulation.
    /// 
    /// Returns [`Entry`] enum if `all` of the following is `true`:
    /// - Both key #1 and key #2 are vacant or already exists with some value.
    /// - Both key #1 and key #2 refer to the same value.
    /// 
    /// When the above statements is `false`, [`entry`](DHashMap::entry) method return [`EntryError`] structure
    /// which contains the [`ErrorKind`] enum, and the values of provided keys (that can be used for another purpose).
    /// 
    /// Depending on the points below, different [`ErrorKind`] variants may be returned:
    /// - When key #1 is vacant, but key #2 is already exists with some value the returned [`ErrorKind`] variant
    /// is [`ErrorKind::VacantK1AndOccupiedK2`].
    /// - When key #1 is already exists with some value, but key #2 is vacant the returned [`ErrorKind`] variant
    /// is [`ErrorKind::OccupiedK1AndVacantK2`].
    /// - When both key #1 and key #2 is already exists with some values, but points to different entries (values)
    /// the returned [`ErrorKind`] variant is [`ErrorKind::KeysPointsToDiffEntries`].
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
    /// // Return [`ErrorKind::OccupiedK1AndVacantK2`] if key #1 is already exists with some value, but key #2 is vacant.
    /// let error_kind = letters.entry('s', 'y').unwrap_err().error;
    /// assert_eq!(error_kind, ErrorKind::OccupiedK1AndVacantK2); 
    /// // Return [`ErrorKind::VacantK1AndOccupiedK2`] if key #1 is vacant, but key #2 is already exists with some value.
    /// let error_kind = letters.entry('y', 's').unwrap_err().error;
    /// assert_eq!(error_kind, ErrorKind::VacantK1AndOccupiedK2);
    /// 
    /// // Return [`ErrorKind::KeysPointsToDiffEntries`] if both key #1 and key #2 are already exists with some values,
    /// // but points to different entries (values).
    /// let error_kind = letters.entry('s', 't').unwrap_err().error;
    /// assert_eq!(error_kind, ErrorKind::KeysPointsToDiffEntries);
    /// ```
    #[inline]
    pub fn entry(&mut self, k1: K1, k2: K2) -> Result<Entry<'_, K1, K2, V>, EntryError<K1, K2>> {
        if let Some((key2_exist, _)) = self.value_map.get(&k1) {
            if let Some(key1_exist) = self.key_map.get(&k2) {
                return if k1 == *key1_exist && k2 == *key2_exist {
                    Ok(self.map_occupied_entry(k1, k2))
                } else {
                    Err(EntryError {
                        error: ErrorKind::KeysPointsToDiffEntries,
                        keys: (k1, k2),
                    })
                };
            } else {
                Err(EntryError {
                    error: ErrorKind::OccupiedK1AndVacantK2,
                    keys: (k1, k2),
                })
            }
        } else {
            return if self.key_map.get(&k2).is_some() {
                Err(EntryError {
                    error: ErrorKind::VacantK1AndOccupiedK2,
                    keys: (k1, k2),
                })
            } else {
                Ok(self.map_vacant_entry(k1, k2))
            };
        }
    }

    // This function used only inside this crate. Both entry are occupied
    #[inline]
    fn map_occupied_entry(&mut self, k1: K1, k2: K2) -> Entry<'_, K1, K2, V> {
        let raw_v = self.value_map.entry(k1);
        let raw_k = self.key_map.entry(k2);
        match raw_v {
            hash_map::Entry::Occupied(base_v) => match raw_k {
                hash_map::Entry::Occupied(base_k) => {
                    Entry::Occupied(OccupiedEntry { base_v, base_k })
                }
                _ => unreachable!(),
            },
            _ => unreachable!(),
        }
    }

    // This function used only inside this crate. Both entry are vacant
    #[inline]
    fn map_vacant_entry(&mut self, k1: K1, k2: K2) -> Entry<'_, K1, K2, V> {
        let raw_v = self.value_map.entry(k1);
        let raw_k = self.key_map.entry(k2);
        match raw_v {
            hash_map::Entry::Vacant(base_v) => match raw_k {
                hash_map::Entry::Vacant(base_k) => Entry::Vacant(VacantEntry { base_v, base_k }),
                _ => unreachable!(),
            },
            _ => unreachable!(),
        }
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

    #[inline]
    pub fn get_mut_key1<Q: ?Sized>(&mut self, k1: &Q) -> Option<&mut V>
    where
        K1: Borrow<Q>,
        Q: Hash + Eq,
    {
        let (_, value) = self.value_map.get_mut(k1)?;
        Some(value)
    }

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
}

impl<K1, K2, V, S> DHashMap<K1, K2, V, S>
where
    K1: Eq + Hash + Clone,
    K2: Eq + Hash + Clone,
    S: BuildHasher,
{
    #[inline]
    pub fn insert_unchecked(&mut self, k1: K1, k2: K2, v: V) -> Option<V> {
        self.key_map.insert(k2.clone(), k1.clone());
        let (_, v) = self.value_map.insert(k1, (k2, v))?;
        Some(v)
    }

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
            Err(EntryError { error, keys }) => Err(TryInsertError::Other(InsertError {
                error,
                keys,
                value: v,
            })),
        }
    }

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



/// A view into an occupied entry in a [`DHashMap`].
/// It is part of the [`Entry`] enum and [`OccupiedError`] struct.
#[derive(Debug)]
pub struct OccupiedEntry<'a, K1: 'a, K2: 'a, V: 'a> {
    base_v: hash_map::OccupiedEntry<'a, K1, (K2, V)>,
    base_k: hash_map::OccupiedEntry<'a, K2, K1>,
}

impl<'a, K1, K2, V> OccupiedEntry<'a, K1, K2, V>
where
    K1: Eq + Hash + Clone,
    K2: Eq + Hash + Clone,
{
    /// Gets a reference to the key #1 in the entry.
    ///
    /// # Examples
    ///
    /// ```
    /// use double_map::DHashMap;
    ///
    /// let mut map: DHashMap<&str, u32, i32> = DHashMap::new();
    /// map.entry("poneyland", 0).unwrap().or_insert(12);
    /// assert_eq!(map.entry("poneyland", 0).unwrap().key1(), &"poneyland");
    /// ```
    #[inline]
    pub fn key1(&self) -> &K1 {
        self.base_v.key()
    }

    #[inline]
    pub fn key2(&self) -> &K2 {
        self.base_k.key()
    }

    #[inline]
    pub fn keys(&self) -> (&K1, &K2) {
        (self.base_v.key(), self.base_k.key())
    }

    #[inline]
    pub fn remove_entry(self) -> (K1, K2, V) {
        self.base_k.remove_entry();
        let (k1, (k2, v)) = self.base_v.remove_entry();
        (k1, k2, v)
    }

    #[inline]
    pub fn get(&self) -> &V {
        let (_, v) = self.base_v.get();
        v
    }

    #[inline]
    pub fn get_mut(&mut self) -> &mut V {
        let (_, v) = self.base_v.get_mut();
        v
    }

    #[inline]
    pub fn into_mut(self) -> &'a mut V {
        let (_, v) = self.base_v.into_mut();
        v
    }

    #[inline]
    pub fn insert(&mut self, mut value: V) -> V {
        let old_value = self.get_mut();
        mem::swap(&mut value, old_value);
        value
    }

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
    K1: Eq + Hash + Clone,
    K2: Eq + Hash + Clone,
{
    #[inline]
    pub fn key1(&self) -> &K1 {
        self.base_v.key()
    }

    #[inline]
    pub fn key2(&self) -> &K2 {
        self.base_k.key()
    }

    #[inline]
    pub fn keys(&self) -> (&K1, &K2) {
        (self.base_v.key(), self.base_k.key())
    }

    #[inline]
    pub fn into_keys(self) -> (K1, K2) {
        (self.base_v.into_key(), self.base_k.into_key())
    }

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
    #[inline]
    pub fn or_insert(self, default: V) -> &'a mut V {
        match self {
            Entry::Occupied(entry) => entry.into_mut(),
            Entry::Vacant(entry) => entry.insert(default),
        }
    }

    #[inline]
    pub fn or_insert_with<F: FnOnce() -> V>(self, default: F) -> &'a mut V {
        match self {
            Entry::Occupied(entry) => entry.into_mut(),
            Entry::Vacant(entry) => entry.insert(default()),
        }
    }

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

    #[inline]
    pub fn key1(&self) -> &K1 {
        match *self {
            Entry::Occupied(ref entry) => entry.key1(),
            Entry::Vacant(ref entry) => entry.key1(),
        }
    }

    #[inline]
    pub fn key2(&self) -> &K2 {
        match *self {
            Entry::Occupied(ref entry) => entry.key2(),
            Entry::Vacant(ref entry) => entry.key2(),
        }
    }

    #[inline]
    pub fn keys(&self) -> (&K1, &K2) {
        match *self {
            Entry::Occupied(ref entry) => entry.keys(),
            Entry::Vacant(ref entry) => entry.keys(),
        }
    }

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
#[derive(Debug)]
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
#[derive(Debug)]
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
/// - When there is [`TryInsertError::Other`] variant, it contains the [`ErrorKind`] enum,
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
    Other(InsertError<K1, K2, V>),
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
            TryInsertError::Other(error) => error.to_string(),
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
