use super::*;

/// A view into a single entry in a map, which may either be vacant or occupied.
///
/// This `enum` is constructed from the [`entry`] method on [`DoubleMap`].
///
/// [`DoubleMap`]: struct.DoubleMap.html
/// [`entry`]: struct.DoubleMap.html#method.entry
///
/// # Examples
///
/// ```
/// use double_map::shash_map::{DoubleMap, Entry, OccupiedEntry};
///
/// let mut map = DoubleMap::new();
/// map.extend([(1, "a", 10), (2, "b", 20), (3, "c", 30)]);
/// assert_eq!(map.len(), 3);
///
/// // Existing key (insert)
/// let entry: Entry<_, _, _, _> = map.entry(1, "a").unwrap();
/// let _raw_o: OccupiedEntry<_, _, _, _> = entry.insert(1);
/// assert_eq!(map.len(), 3);
/// // Nonexistent key (insert)
/// map.entry(4, "d").unwrap().insert(4);
///
/// // Existing key (or_insert)
/// let v = map.entry(2, "b").unwrap().or_insert(2);
/// assert_eq!(std::mem::replace(v, 2), 20);
/// // Nonexistent key (or_insert)
/// map.entry(5, "e").unwrap().or_insert(5);
///
/// // Existing key (or_insert_with)
/// let v = map.entry(3, "c").unwrap().or_insert_with(|| 3);
/// assert_eq!(std::mem::replace(v, 3), 30);
/// // Nonexistent key (or_insert_with)
/// map.entry(6, "f").unwrap().or_insert_with(|| 6);
///
/// println!("Our DoubleMap: {:?}", map);
///
/// let mut vec: Vec<_> = map.iter().map(|(&k1, &k2, &v)| (k1, k2, v)).collect();
/// // The `Iter` iterator produces items in arbitrary order, so the
/// // items must be sorted to test them against a sorted array.
/// vec.sort_unstable();
/// assert_eq!(
///     vec,
///     [
///         (1, "a", 1),
///         (2, "b", 2),
///         (3, "c", 3),
///         (4, "d", 4),
///         (5, "e", 5),
///         (6, "f", 6)
///     ]
/// );
/// ```
pub enum Entry<'a, K1, K2, V, S, A = Global>
where
    A: Allocator + Clone,
{
    /// An occupied entry.
    ///
    /// # Examples
    ///
    /// ```
    /// use double_map::shash_map::{DoubleMap, Entry};
    /// let mut map: DoubleMap<i32, &str, i32> = [(1, "a", 100), (2, "b", 200)].into();
    ///
    /// match map.entry(1, "a") {
    ///     Ok(Entry::Occupied(_)) => {}
    ///     _ => panic!(),
    /// }
    /// ```
    Occupied(OccupiedEntry<'a, K1, K2, V, S, A>),
    /// A vacant entry.
    ///
    /// # Examples
    ///
    /// ```
    /// use double_map::shash_map::{DoubleMap, Entry};
    /// let mut map: DoubleMap<i32, &str, i32> = DoubleMap::new();
    ///
    /// match map.entry(1, "a") {
    ///     Ok(Entry::Vacant(_)) => {}
    ///     _ => panic!(),
    /// }
    /// ```
    Vacant(VacantEntry<'a, K1, K2, V, S, A>),
}

impl<K1: Debug, K2: Debug, V: Debug, S, A: Allocator + Clone> Debug for Entry<'_, K1, K2, V, S, A> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match *self {
            Entry::Vacant(ref v) => f.debug_tuple("Entry").field(v).finish(),
            Entry::Occupied(ref o) => f.debug_tuple("Entry").field(o).finish(),
        }
    }
}

impl<'a, K1, K2, V, S, A: Allocator + Clone> Entry<'a, K1, K2, V, S, A> {
    /// Sets the value of the entry, and returns an `OccupiedEntry`.
    ///
    /// # Examples
    ///
    /// ```
    /// use double_map::DoubleMap;
    ///
    /// let mut map: DoubleMap<i32, &str, i32> = DoubleMap::new();
    /// let entry = map.entry(1, "horseyland").unwrap().insert(37);
    ///
    /// assert_eq!(entry.key1(), &1);
    /// assert_eq!(entry.key2(), &"horseyland");
    /// assert_eq!(entry.keys(), (&1, &"horseyland"));
    /// ```
    #[cfg_attr(feature = "inline-more", inline)]
    pub fn insert(self, value: V) -> OccupiedEntry<'a, K1, K2, V, S, A>
    where
        K1: Hash,
        K2: Hash,
        S: BuildHasher,
    {
        match self {
            Entry::Occupied(mut entry) => {
                entry.insert(value);
                entry
            }
            Entry::Vacant(entry) => entry.insert_entry(value),
        }
    }

    /// Ensures a value is in the entry by inserting the default if empty, and returns
    /// a mutable reference to the value in the entry.
    ///
    /// # Examples
    ///
    /// ```
    /// use double_map::DoubleMap;
    ///
    /// let mut map: DoubleMap<&str, u32, i32> = DoubleMap::new();
    ///
    /// // nonexistent key
    /// match map.entry("poneyland", 0) {
    ///     Ok(entry) => {
    ///         entry.or_insert(3);
    ///     }
    ///     Err(_) => unreachable!(),
    /// }
    /// assert_eq!(map.get_key1(&"poneyland"), Some(&3));
    ///
    /// // existing key
    /// let _ = map
    ///     .entry("poneyland", 0)
    ///     .map(|entry| *entry.or_insert(10) *= 2);
    /// assert_eq!(map.get_key1(&"poneyland"), Some(&6));
    /// ```
    #[cfg_attr(feature = "inline-more", inline)]
    pub fn or_insert(self, default: V) -> &'a mut V
    where
        K1: Hash,
        K2: Hash,
        S: BuildHasher,
    {
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
    /// use double_map::DoubleMap;
    ///
    /// let mut map: DoubleMap<&str, u32, String> = DoubleMap::new();
    /// let s = "hoho".to_owned();
    ///
    /// // nonexistent key
    /// match map.entry("poneyland", 0) {
    ///     Ok(entry) => {
    ///         entry.or_insert_with(|| s);
    ///     }
    ///     Err(_) => unreachable!(),
    /// }
    /// assert_eq!(map.get_key1("poneyland"), Some(&"hoho".to_owned()));
    ///
    /// // existing key
    /// let k = "another string".to_owned();
    /// let _ = map
    ///     .entry("poneyland", 0)
    ///     .map(|entry| entry.or_insert_with(|| k).push_str("ho"));
    /// assert_eq!(map.get_key1(&"poneyland"), Some(&"hohoho".to_owned()));
    /// ```
    #[cfg_attr(feature = "inline-more", inline)]
    pub fn or_insert_with<F: FnOnce() -> V>(self, default: F) -> &'a mut V
    where
        K1: Hash,
        K2: Hash,
        S: BuildHasher,
    {
        match self {
            Entry::Occupied(entry) => entry.into_mut(),
            Entry::Vacant(entry) => entry.insert(default()),
        }
    }

    /// Ensures a value is in the entry by inserting, if empty, the result of the default function.
    /// This method allows generating key-derived (with using `K1` key) value for
    /// insertion by providing the default function a reference to the key that was moved
    /// during the `.entry(k1, k2)` method call.
    ///
    /// The reference to the moved key is provided so that cloning or copying the key is
    /// unnecessary, unlike with `.or_insert_with(|| ... )`.
    ///
    /// # Examples
    ///
    /// ```
    /// use double_map::DoubleMap;
    ///
    /// let mut map: DoubleMap<&str, usize, u64> = DoubleMap::new();
    ///
    /// // nonexistent key
    /// match map.entry("poneyland", 0) {
    ///     Ok(entry) => {
    ///         entry.or_insert_with_key1(|k1| k1.chars().count() as u64);
    ///     }
    ///     Err(_) => unreachable!(),
    /// }
    /// assert_eq!(map.get_key1(&"poneyland"), Some(&9));
    ///
    /// // existing key
    /// let _ = map
    ///     .entry("poneyland", 0)
    ///     .map(|ent| ent.or_insert_with_key1(|k1| (k1.chars().count() * 2) as u64 * 10))
    ///     .map(|value| *value *= 2);
    ///
    /// assert_eq!(map.get_key1(&"poneyland"), Some(&18));
    ///
    /// let _ = map
    ///     .entry("bearland", 1)
    ///     .map(|ent| ent.or_insert_with_key1(|k1| (k1.chars().count() * 2) as u64));
    /// assert_eq!(map.get_key1(&"bearland"), Some(&16));
    /// ```
    #[cfg_attr(feature = "inline-more", inline)]
    pub fn or_insert_with_key1<F: FnOnce(&K1) -> V>(self, default: F) -> &'a mut V
    where
        K1: Hash,
        K2: Hash,
        S: BuildHasher,
    {
        match self {
            Entry::Occupied(entry) => entry.into_mut(),
            Entry::Vacant(entry) => {
                let value = default(entry.key1());
                entry.insert(value)
            }
        }
    }

    /// Ensures a value is in the entry by inserting, if empty, the result of the default function.
    /// This method allows generating key-derived (with using `K2` key) value for
    /// insertion by providing the default function a reference to the key that was moved
    /// during the `.entry(k1, k2)` method call.
    ///
    /// The reference to the moved key is provided so that cloning or copying the key is
    /// unnecessary, unlike with `.or_insert_with(|| ... )`.
    ///
    /// # Examples
    ///
    /// ```
    /// use double_map::DoubleMap;
    ///
    /// let mut map: DoubleMap<&str, usize, u64> = DoubleMap::new();
    ///
    /// // nonexistent key
    /// match map.entry("poneyland", 10) {
    ///     Ok(entry) => {
    ///         entry.or_insert_with_key2(|&k2| k2 as u64 * 10);
    ///     }
    ///     Err(_) => unreachable!(),
    /// }
    /// assert_eq!(map.get_key2(&10), Some(&100));
    ///
    /// // existing key
    /// let _ = map
    ///     .entry("poneyland", 10)
    ///     .map(|ent| ent.or_insert_with_key2(|&k1| k1 as u64 / 10))
    ///     .map(|value| *value *= 2);
    ///
    /// assert_eq!(map.get_key2(&10), Some(&200));
    ///
    /// let _ = map
    ///     .entry("bearland", 20)
    ///     .map(|ent| ent.or_insert_with_key2(|&k2| k2 as u64 + 10));
    /// assert_eq!(map.get_key2(&20), Some(&30));
    /// ```
    #[cfg_attr(feature = "inline-more", inline)]
    pub fn or_insert_with_key2<F: FnOnce(&K2) -> V>(self, default: F) -> &'a mut V
    where
        K1: Hash,
        K2: Hash,
        S: BuildHasher,
    {
        match self {
            Entry::Occupied(entry) => entry.into_mut(),
            Entry::Vacant(entry) => {
                let value = default(entry.key2());
                entry.insert(value)
            }
        }
    }

    /// Ensures a value is in the entry by inserting, if empty, the result of the default function.
    /// This method allows generating key-derived (with using `K1` and `K2` keys) values for
    /// insertion by providing the default function references to the keys that were moved
    /// during the `.entry(k1, k2)` method call.
    ///
    /// The reference to the moved keys is provided so that cloning or copying the key is
    /// unnecessary, unlike with `.or_insert_with(|| ... )`.
    ///
    /// # Examples
    ///
    /// ```
    /// use double_map::DoubleMap;
    ///
    /// let mut map: DoubleMap<&str, usize, u64> = DoubleMap::new();
    ///
    /// // nonexistent key
    /// match map.entry("poneyland", 10) {
    ///     Ok(entry) => {
    ///         entry.or_insert_with_keys(|&k1, &k2| (k1.chars().count() + k2) as u64);
    ///     }
    ///     Err(_) => unreachable!(),
    /// }
    /// assert_eq!(map.get_keys(&"poneyland", &10), Some(&19));
    ///
    /// // existing key
    /// let _ = map
    ///     .entry("poneyland", 10)
    ///     .map(|ent| ent.or_insert_with_keys(|&k1, &k2| (k1.chars().count() + k2 * 3) as u64))
    ///     .map(|value| *value *= 2);
    ///
    /// assert_eq!(map.get_keys(&"poneyland", &10), Some(&38));
    ///
    /// let _ = map
    ///     .entry("bearland", 20)
    ///     .map(|ent| ent.or_insert_with_keys(|&k1, &k2| (k1.chars().count() + k2 * 3) as u64));
    /// assert_eq!(map.get_keys(&"bearland", &20), Some(&68));
    /// ```
    #[cfg_attr(feature = "inline-more", inline)]
    pub fn or_insert_with_keys<F: FnOnce(&K1, &K2) -> V>(self, default: F) -> &'a mut V
    where
        K1: Hash,
        K2: Hash,
        S: BuildHasher,
    {
        match self {
            Entry::Occupied(entry) => entry.into_mut(),
            Entry::Vacant(entry) => {
                let value = default(entry.key1(), entry.key2());
                entry.insert(value)
            }
        }
    }

    /// Returns a reference to this entry's first `K1` key.
    ///
    /// # Examples
    ///
    /// ```
    /// use double_map::DoubleMap;
    ///
    /// let mut map: DoubleMap<&str, u32, i32> = DoubleMap::new();
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
    ///         entry.or_insert(50);
    ///     },
    ///     Err(_) => unreachable!(),
    /// }
    /// // The value does not changed
    /// assert_eq!(map.get_key1(&"poneyland"), Some(&25));
    /// ```
    #[cfg_attr(feature = "inline-more", inline)]
    pub fn key1(&self) -> &K1 {
        match *self {
            Entry::Occupied(ref entry) => entry.key1(),
            Entry::Vacant(ref entry) => entry.key1(),
        }
    }

    /// Returns a reference to this entry's second `K2` key.
    ///
    /// # Examples
    ///
    /// ```
    /// use double_map::DoubleMap;
    ///
    /// let mut map: DoubleMap<&str, u32, i32> = DoubleMap::new();
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
    ///         entry.or_insert(50);
    ///     },
    ///     Err(_) => unreachable!(),
    /// }
    /// // The value does not changed
    /// assert_eq!(map.get_key2(&10), Some(&25));
    /// ```
    #[cfg_attr(feature = "inline-more", inline)]
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
    /// use double_map::DoubleMap;
    ///
    /// let mut map: DoubleMap<&str, u32, i32> = DoubleMap::new();
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
    /// assert_eq!(map.get_keys(&"poneyland", &10), Some(&25));
    ///
    /// // So now it is OccupiedEntry
    /// match map.entry("poneyland", 10) {
    ///     Ok(entry) => {
    ///         // And keys equal to provided one too
    ///         assert_eq!(entry.keys(), (&"poneyland", &10));
    ///         entry.or_insert(50);
    ///     },
    ///     Err(_) => unreachable!(),
    /// }
    /// // The value does not changed
    /// assert_eq!(map.get_keys(&"poneyland", &10), Some(&25));
    /// ```
    #[cfg_attr(feature = "inline-more", inline)]
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
    /// use double_map::DoubleMap;
    ///
    /// let mut map: DoubleMap<&str, u32, u32> = DoubleMap::new();
    ///
    /// let _ = map
    ///     .entry("poneyland", 1)
    ///     .map(|entry| entry.and_modify(|value| *value += 100).or_insert(42));
    /// assert_eq!(map.get_key1(&"poneyland"), Some(&42));
    ///
    /// let _ = map
    ///     .entry("poneyland", 1)
    ///     .map(|entry| entry.and_modify(|value| *value += 100).or_insert(42));
    /// assert_eq!(map.get_key1(&"poneyland"), Some(&142));
    /// ```
    #[cfg_attr(feature = "inline-more", inline)]
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

    /// Provides shared access to the first `K1` key and owned access to the
    /// value of an occupied entry and allows to replace or remove it based on the
    /// value of the returned option.
    ///
    /// # Examples
    ///
    /// ```
    /// use double_map::shash_map::{DoubleMap, Entry};
    ///
    /// let mut map: DoubleMap<&str, i32, String> = DoubleMap::new();
    ///
    /// let entry = map
    ///     .entry("poneyland", 1)
    ///     .unwrap()
    ///     .and_replace_entry_with_key1(|_k1, _v| panic!());
    ///
    /// match entry {
    ///     Entry::Vacant(e) => {
    ///         assert_eq!(e.key1(), &"poneyland");
    ///         assert_eq!(e.key2(), &1);
    ///     }
    ///     Entry::Occupied(_) => panic!(),
    /// }
    ///
    /// map.insert("poneyland", 1, "land".to_owned());
    ///
    /// let entry = map
    ///     .entry("poneyland", 1)
    ///     .unwrap()
    ///     .and_replace_entry_with_key1(|k1, v| {
    ///         assert_eq!(k1, &"poneyland");
    ///         assert_eq!(v.as_str(), "land");
    ///         Some("dream land".to_owned())
    ///     });
    ///
    /// match entry {
    ///     Entry::Occupied(e) => {
    ///         assert_eq!(e.key1(), &"poneyland");
    ///         assert_eq!(e.key2(), &1);
    ///         assert_eq!(e.get(), "dream land");
    ///     }
    ///     Entry::Vacant(_) => panic!(),
    /// }
    ///
    /// assert_eq!(map["poneyland"], "dream land");
    ///
    /// let entry = map
    ///     .entry("poneyland", 1)
    ///     .unwrap()
    ///     .and_replace_entry_with_key1(|_k1, _v| None);
    ///
    /// match entry {
    ///     Entry::Vacant(e) => {
    ///         assert_eq!(e.key1(), &"poneyland");
    ///         assert_eq!(e.key2(), &1);
    ///     }
    ///     Entry::Occupied(_) => panic!(),
    /// }
    ///
    /// assert!(!map.contains_key1("poneyland"));
    /// assert!(map.is_empty());
    /// ```
    #[cfg_attr(feature = "inline-more", inline)]
    pub fn and_replace_entry_with_key1<F>(self, f: F) -> Self
    where
        F: FnOnce(&K1, V) -> Option<V>,
    {
        match self {
            Entry::Occupied(entry) => entry.replace_entry_with_key1(f),
            Entry::Vacant(_) => self,
        }
    }

    /// Provides shared access to the second `K2` key and owned access to the
    /// value of an occupied entry and allows to replace or remove it based on the
    /// value of the returned option.
    ///
    /// # Examples
    ///
    /// ```
    /// use double_map::shash_map::{DoubleMap, Entry};
    ///
    /// let mut map: DoubleMap<&str, i32, String> = DoubleMap::new();
    ///
    /// let entry = map
    ///     .entry("poneyland", 1)
    ///     .unwrap()
    ///     .and_replace_entry_with_key2(|_k2, _v| panic!());
    ///
    /// match entry {
    ///     Entry::Vacant(e) => {
    ///         assert_eq!(e.key1(), &"poneyland");
    ///         assert_eq!(e.key2(), &1);
    ///     }
    ///     Entry::Occupied(_) => panic!(),
    /// }
    ///
    /// map.insert("poneyland", 1, "land".to_owned());
    ///
    /// let entry = map
    ///     .entry("poneyland", 1)
    ///     .unwrap()
    ///     .and_replace_entry_with_key2(|k2, v| {
    ///         assert_eq!(k2, &1);
    ///         assert_eq!(v.as_str(), "land");
    ///         Some("dream land".to_owned())
    ///     });
    ///
    /// match entry {
    ///     Entry::Occupied(e) => {
    ///         assert_eq!(e.key1(), &"poneyland");
    ///         assert_eq!(e.key2(), &1);
    ///         assert_eq!(e.get(), "dream land");
    ///     }
    ///     Entry::Vacant(_) => panic!(),
    /// }
    ///
    /// assert_eq!(map["poneyland"], "dream land");
    ///
    /// let entry = map
    ///     .entry("poneyland", 1)
    ///     .unwrap()
    ///     .and_replace_entry_with_key2(|_k2, _v| None);
    ///
    /// match entry {
    ///     Entry::Vacant(e) => {
    ///         assert_eq!(e.key1(), &"poneyland");
    ///         assert_eq!(e.key2(), &1);
    ///     }
    ///     Entry::Occupied(_) => panic!(),
    /// }
    ///
    /// assert!(!map.contains_key2(&1));
    /// assert!(map.is_empty());
    /// ```
    #[cfg_attr(feature = "inline-more", inline)]
    pub fn and_replace_entry_with_key2<F>(self, f: F) -> Self
    where
        F: FnOnce(&K2, V) -> Option<V>,
    {
        match self {
            Entry::Occupied(entry) => entry.replace_entry_with_key2(f),
            Entry::Vacant(_) => self,
        }
    }

    /// Provides shared access to the `K1` and `K2` keys and owned access to the
    /// value of an occupied entry and allows to replace or remove it based on the
    /// value of the returned option.
    ///
    /// # Examples
    ///
    /// ```
    /// use double_map::shash_map::{DoubleMap, Entry};
    ///
    /// let mut map: DoubleMap<&str, i32, String> = DoubleMap::new();
    ///
    /// let entry = map
    ///     .entry("poneyland", 1)
    ///     .unwrap()
    ///     .and_replace_entry_with_keys(|_k1, _k2, _v| panic!());
    ///
    /// match entry {
    ///     Entry::Vacant(e) => {
    ///         assert_eq!(e.key1(), &"poneyland");
    ///         assert_eq!(e.key2(), &1);
    ///     }
    ///     Entry::Occupied(_) => panic!(),
    /// }
    ///
    /// map.insert("poneyland", 1, "land".to_owned());
    ///
    /// let entry = map
    ///     .entry("poneyland", 1)
    ///     .unwrap()
    ///     .and_replace_entry_with_keys(|k1, k2, v| {
    ///         assert_eq!(*k1, "poneyland");
    ///         assert_eq!(*k2, 1);
    ///         assert_eq!(v.as_str(), "land");
    ///         Some("dream land".to_owned())
    ///     });
    ///
    /// match entry {
    ///     Entry::Occupied(e) => {
    ///         assert_eq!(e.key1(), &"poneyland");
    ///         assert_eq!(e.key2(), &1);
    ///         assert_eq!(e.get(), "dream land");
    ///     }
    ///     Entry::Vacant(_) => panic!(),
    /// }
    ///
    /// assert_eq!(map["poneyland"], "dream land");
    ///
    /// let entry = map
    ///     .entry("poneyland", 1)
    ///     .unwrap()
    ///     .and_replace_entry_with_keys(|_k1, _k2, _v| None);
    ///
    /// match entry {
    ///     Entry::Vacant(e) => {
    ///         assert_eq!(e.key1(), &"poneyland");
    ///         assert_eq!(e.key2(), &1);
    ///     }
    ///     Entry::Occupied(_) => panic!(),
    /// }
    ///
    /// assert!(!map.contains_keys(&"poneyland", &1));
    /// assert!(map.is_empty());
    /// ```
    #[cfg_attr(feature = "inline-more", inline)]
    pub fn and_replace_entry_with_keys<F>(self, f: F) -> Self
    where
        F: FnOnce(&K1, &K2, V) -> Option<V>,
    {
        match self {
            Entry::Occupied(entry) => entry.replace_entry_with_keys(f),
            Entry::Vacant(_) => self,
        }
    }
}

impl<'a, K1, K2, V: Default, S, A: Allocator + Clone> Entry<'a, K1, K2, V, S, A> {
    /// Ensures a value is in the entry by inserting the default value if empty,
    /// and returns a mutable reference to the value in the entry.
    ///
    /// # Examples
    ///
    /// ```
    /// use double_map::DoubleMap;
    ///
    /// let mut map: DoubleMap<&str, i32, Option<u32>> = DoubleMap::new();
    ///
    /// // nonexistent key
    /// map.entry("poneyland", 1).unwrap().or_default();
    /// assert_eq!(map["poneyland"], None);
    ///
    /// map.insert("horseland", 2, Some(3));
    ///
    /// // existing key
    /// assert_eq!(
    ///     map.entry("horseland", 2).unwrap().or_default(),
    ///     &mut Some(3)
    /// );
    /// ```
    #[cfg_attr(feature = "inline-more", inline)]
    pub fn or_default(self) -> &'a mut V
    where
        K1: Hash,
        K2: Hash,
        S: BuildHasher,
    {
        match self {
            Entry::Occupied(entry) => entry.into_mut(),
            Entry::Vacant(entry) => entry.insert(Default::default()),
        }
    }
}

/// A view into an occupied entry in a `DoubleMap`.
/// It is part of the [`Entry`] enum.
///
/// [`Entry`]: enum.Entry.html
///
/// # Examples
///
/// ```
/// use double_map::shash_map::{DoubleMap, Entry, OccupiedEntry};
///
/// let mut map = DoubleMap::new();
/// map.extend([(1, "a", 10), (2, "b", 20), (3, "c", 30)]);
///
/// let _entry_o: OccupiedEntry<_, _, _, _> = map.entry(1, "a").unwrap().insert(100);
/// assert_eq!(map.len(), 3);
///
/// // Existing key (insert and update)
/// match map.entry(1, "a") {
///     Ok(Entry::Occupied(mut view)) => {
///         assert_eq!(view.get(), &100);
///         let v = view.get_mut();
///         *v *= 10;
///         assert_eq!(view.insert(1111), 1000);
///     }
///     _ => panic!("Not existing key?"),
/// }
///
/// assert_eq!(map[&1], 1111);
/// assert_eq!(map.len(), 3);
///
/// // Existing key (take)
/// match map.entry(3, "c") {
///     Ok(Entry::Occupied(view)) => {
///         assert_eq!(view.remove_entry(), (3, "c", 30));
///     }
///     _ => panic!("It should be existing key"),
/// }
/// assert_eq!(map.get_key2(&"c"), None);
/// assert_eq!(map.len(), 2);
/// ```
pub struct OccupiedEntry<'a, K1, K2, V, S, A: Allocator + Clone = Global> {
    pub(super) hash1: u64,
    pub(super) key1: Option<K1>,
    pub(super) hash2: u64,
    pub(super) key2: Option<K2>,
    pub(super) data_bucket: DataBucket<(K1, K2, V)>,
    pub(super) pointer_bucket: PointerBucket<DataBucket<(K1, K2, V)>>,
    pub(super) table: &'a mut DoubleMap<K1, K2, V, S, A>,
}

unsafe impl<K1, K2, V, S, A> Send for OccupiedEntry<'_, K1, K2, V, S, A>
where
    K1: Send,
    K2: Send,
    V: Send,
    S: Send,
    A: Send + Allocator + Clone,
{
}

unsafe impl<K1, K2, V, S, A> Sync for OccupiedEntry<'_, K1, K2, V, S, A>
where
    K1: Sync,
    K2: Sync,
    V: Sync,
    S: Sync,
    A: Sync + Allocator + Clone,
{
}

impl<K1: Debug, K2: Debug, V: Debug, S, A> Debug for OccupiedEntry<'_, K1, K2, V, S, A>
where
    A: Allocator + Clone,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("OccupiedEntry")
            .field("key1", self.key1())
            .field("key2", self.key2())
            .field("value", self.get())
            .finish()
    }
}

impl<'a, K1, K2, V, S, A: Allocator + Clone> OccupiedEntry<'a, K1, K2, V, S, A> {
    /// Gets a reference to the first `K1` key in the entry.
    ///
    /// # Examples
    ///
    /// ```
    /// use double_map::shash_map::{DoubleMap, Entry};
    ///
    /// let mut map: DoubleMap<&str, u32, i32> = DoubleMap::new();
    /// map.insert("poneyland", 0, 12);
    ///
    /// match map.entry("poneyland", 0) {
    ///     Ok(Entry::Occupied(entry)) => {
    ///         assert_eq!(entry.key1(), &"poneyland");
    ///     }
    ///     _ => panic!(),
    /// }
    /// ```
    #[cfg_attr(feature = "inline-more", inline)]
    pub fn key1(&self) -> &K1 {
        unsafe { &self.data_bucket.as_ref().0 }
    }

    /// Gets a reference to the second `K2` key in the entry.
    ///
    /// # Examples
    ///
    /// ```
    /// use double_map::shash_map::{DoubleMap, Entry};
    ///
    /// let mut map: DoubleMap<&str, u32, i32> = DoubleMap::new();
    /// map.insert("poneyland", 0, 12);
    ///
    /// match map.entry("poneyland", 0) {
    ///     Ok(Entry::Occupied(entry)) => {
    ///         assert_eq!(entry.key2(), &0);
    ///     }
    ///     _ => panic!(),
    /// }
    /// ```
    #[cfg_attr(feature = "inline-more", inline)]
    pub fn key2(&self) -> &K2 {
        unsafe { &self.data_bucket.as_ref().1 }
    }

    /// Gets a reference to the `K1` and `K2` keys in the entry.
    /// Return tuple of type `(&'a K1, &'a K2)`.
    ///
    /// # Examples
    ///
    /// ```
    /// use double_map::shash_map::{DoubleMap, Entry};
    ///
    /// let mut map: DoubleMap<&str, u32, i32> = DoubleMap::new();
    /// map.insert("poneyland", 0, 12);
    ///
    /// match map.entry("poneyland", 0) {
    ///     Ok(Entry::Occupied(entry)) => {
    ///         assert_eq!(entry.keys(), (&"poneyland", &0));
    ///     }
    ///     _ => panic!(),
    /// }
    /// ```
    #[cfg_attr(feature = "inline-more", inline)]
    pub fn keys(&self) -> (&K1, &K2) {
        let &(ref k1, ref k2, _) = unsafe { self.data_bucket.as_ref() };
        (k1, k2)
    }

    /// Take the ownership of the keys and value from the map.
    /// Keeps the allocated memory for reuse.
    ///
    /// # Examples
    ///
    /// ```
    /// use double_map::shash_map::{DoubleMap, Entry};
    ///
    /// // So lets create some map and insert some element
    /// let mut map: DoubleMap<&str, u32, i32> = DoubleMap::new();
    /// map.insert("poneyland", 0, 10);
    /// map.insert("bearland", 1, 11);
    ///
    /// assert!(map.get_key1("poneyland") == Some(&10) && map.get_key2(&0) == Some(&10));
    /// match map.entry("poneyland", 0) {
    ///     Ok(Entry::Occupied(entry)) => {
    ///         // We delete the entry from the map.
    ///         let tuple = entry.remove_entry();
    ///         assert_eq!(tuple, ("poneyland", 0, 10));
    ///     }
    ///     _ => panic!("poneyland"),
    /// }
    /// assert!(map.get_key1("poneyland") == None && map.get_key2(&0) == None);
    ///
    /// assert!(map.get_key1("bearland") == Some(&11) && map.get_key2(&1) == Some(&11));
    /// match map.entry("bearland", 1) {
    ///     Ok(Entry::Occupied(entry)) => {
    ///         // We delete the entry from the map.
    ///         let tuple = entry.remove_entry();
    ///         assert_eq!(tuple, ("bearland", 1, 11));
    ///     }
    ///     _ => panic!("bearland"),
    /// }
    /// assert!(map.get_key1("bearland") == None && map.get_key2(&1) == None);
    /// ```
    #[cfg_attr(feature = "inline-more", inline)]
    pub fn remove_entry(self) -> (K1, K2, V) {
        let (k1, k2, v) = unsafe { self.table.table.remove(self.pointer_bucket) };
        (k1, k2, v)
    }

    /// Gets a reference to the value in the entry.
    ///
    /// # Examples
    ///
    /// ```
    /// use double_map::shash_map::{DoubleMap, Entry};
    ///
    /// let mut map: DoubleMap<&str, u32, i32> = DoubleMap::new();
    /// map.insert("poneyland", 0, 12);
    ///
    /// match map.entry("poneyland", 0) {
    ///     Ok(Entry::Occupied(entry)) => {
    ///         assert_eq!(entry.get(), &12);
    ///     }
    ///     _ => panic!(),
    /// }
    /// ```
    #[cfg_attr(feature = "inline-more", inline)]
    pub fn get(&self) -> &V {
        unsafe { &self.data_bucket.as_ref().2 }
    }

    /// Gets a mutable reference to the value in the entry.
    ///
    /// If you need a reference to the `OccupiedEntry` which may outlive the
    /// destruction of the `Entry` value, see [`into_mut`](`OccupiedEntry::into_mut`).
    ///
    /// # Examples
    ///
    /// ```
    /// use double_map::shash_map::{DoubleMap, Entry};
    ///
    /// let mut map: DoubleMap<&str, u32, i32> = DoubleMap::new();
    /// map.insert("poneyland", 0, 12);
    /// assert_eq!(map.get_key1("poneyland"), Some(&12));
    /// assert_eq!(map.get_key2(&0), Some(&12));
    ///
    /// match map.entry("poneyland", 0) {
    ///     Ok(Entry::Occupied(mut entry)) => {
    ///         *entry.get_mut() += 10;
    ///         assert_eq!(entry.get(), &22);
    ///         // We can use the same Entry multiple times.
    ///         *entry.get_mut() += 2;
    ///     }
    ///     _ => panic!(),
    /// }
    /// assert_eq!(map.get_key1("poneyland"), Some(&24));
    /// assert_eq!(map.get_key2(&0), Some(&24));
    /// ```
    #[cfg_attr(feature = "inline-more", inline)]
    pub fn get_mut(&mut self) -> &mut V {
        unsafe { &mut self.data_bucket.as_mut().2 }
    }

    /// Converts the `OccupiedEntry` into a mutable reference to the value in the entry
    /// with a lifetime bound to the map itself.
    ///
    /// If you need multiple references to the `OccupiedEntry`, see [`get_mut`].
    ///
    /// [`get_mut`]: #method.get_mut
    ///
    /// # Examples
    ///
    /// ```
    /// use double_map::shash_map::{DoubleMap, Entry};
    ///
    /// let mut map: DoubleMap<&str, u32, i32> = DoubleMap::new();
    /// map.insert("poneyland", 0, 12);
    /// assert_eq!(map.get_key1("poneyland"), Some(&12));
    /// assert_eq!(map.get_key2(&0), Some(&12));
    ///
    /// // Let's create a variable that outlives the OccupiedEntry
    /// // (with some initial value)
    /// let mut value: &mut i32 = &mut 0;
    ///
    /// match map.entry("poneyland", 0) {
    ///     Ok(Entry::Occupied(entry)) => {
    ///         // So we can convert the OccupiedEntry into a mutable
    ///         // reference to the value.
    ///         value = entry.into_mut();
    ///         *value += 10;
    ///     }
    ///     _ => panic!(),
    /// }
    /// // We can use the same reference outside the created entry
    /// // (OccupiedEntry) scope.
    /// *value += 20;
    /// assert_eq!(map.get_key1("poneyland"), Some(&42));
    /// assert_eq!(map.get_key2(&0), Some(&42));
    /// ```
    #[cfg_attr(feature = "inline-more", inline)]
    pub fn into_mut(self) -> &'a mut V {
        unsafe { &mut self.data_bucket.as_mut().2 }
    }

    /// Sets the value of the entry, and returns the entry's old value.
    ///
    /// # Examples
    ///
    /// ```
    /// use double_map::shash_map::{DoubleMap, Entry};
    ///
    /// let mut map: DoubleMap<&str, u32, i32> = DoubleMap::new();
    /// map.insert("poneyland", 0, 12);
    /// assert_eq!(map.get_key1("poneyland"), Some(&12));
    /// assert_eq!(map.get_key2(&0), Some(&12));
    ///
    /// // Let's create a variable that holds value
    /// let mut owner: i32 = 100;
    ///
    /// match map.entry("poneyland", 0) {
    ///     Ok(Entry::Occupied(mut entry)) => {
    ///         // So we can swap our created owner value with
    ///         // value inside the map.
    ///         owner = entry.insert(owner);
    ///     }
    ///     _ => panic!(),
    /// }
    /// assert_eq!(owner, 12);
    /// assert_eq!(map.get_key1("poneyland"), Some(&100));
    /// assert_eq!(map.get_key2(&0), Some(&100));
    /// ```
    #[cfg_attr(feature = "inline-more", inline)]
    pub fn insert(&mut self, value: V) -> V {
        mem::replace(self.get_mut(), value)
    }

    /// Take the value out of the entry (map), and return it.
    /// Keeps the allocated memory for reuse.
    ///
    /// # Examples
    ///
    /// ```
    /// use double_map::shash_map::{DoubleMap, Entry};
    ///
    /// // So lets create some map and insert some element
    /// let mut map: DoubleMap<&str, u32, i32> = DoubleMap::new();
    /// map.insert("poneyland", 0, 10);
    /// map.insert("bearland", 1, 11);
    ///
    /// assert!(map.get_key1("poneyland") == Some(&10) && map.get_key2(&0) == Some(&10));
    ///
    /// match map.entry("poneyland", 0) {
    ///     Ok(Entry::Occupied(entry)) => {
    ///         // We delete the entry from the map.
    ///         let value = entry.remove();
    ///         assert_eq!(value, 10);
    ///     }
    ///     _ => panic!(),
    /// }
    /// assert!(map.get_key1("poneyland") == None && map.get_key2(&0) == None);
    ///
    /// assert!(map.get_key1("bearland") == Some(&11) && map.get_key2(&1) == Some(&11));
    /// match map.entry("bearland", 1) {
    ///     Ok(Entry::Occupied(entry)) => {
    ///         // We delete the entry from the map.
    ///         let value = entry.remove();
    ///         assert_eq!(value, 11);
    ///     }
    ///     _ => panic!(),
    /// }
    /// assert!(map.get_key1("bearland") == None && map.get_key2(&1) == None);
    /// assert!(map.is_empty());
    /// ```
    #[cfg_attr(feature = "inline-more", inline)]
    pub fn remove(self) -> V {
        self.remove_entry().2
    }

    /// Replaces the entry, returning the old keys and value. The new keys
    /// in the hash map will be the keys used to create this entry.
    ///
    /// # Panics
    ///
    /// Will panic if this `OccupiedEntry` was created through
    /// [`Entry::insert`].
    ///
    /// # Examples
    ///
    /// ```
    /// use double_map::shash_map::{DoubleMap, Entry};
    /// use std::rc::Rc;
    ///
    /// let mut map: DoubleMap<Rc<String>, Rc<String>, i32> = DoubleMap::new();
    /// let key1_first = Rc::new("First key".to_string());
    /// let key2_first = Rc::new("Second key".to_string());
    ///
    /// let key1_second = Rc::new("First key".to_string());
    /// let key2_second = Rc::new("Second key".to_string());
    ///
    /// map.insert(key1_first.clone(), key2_first.clone(), 15);
    /// assert!(Rc::strong_count(&key1_first) == 2 && Rc::strong_count(&key1_second) == 1);
    /// assert!(Rc::strong_count(&key2_first) == 2 && Rc::strong_count(&key2_second) == 1);
    ///
    /// match map.entry(key1_second.clone(), key2_second.clone()) {
    ///     Ok(Entry::Occupied(entry)) => {
    ///         let (old_key1, old_key2, old_value): (Rc<String>, Rc<String>, i32) =
    ///             entry.replace_entry(16);
    ///         assert!(Rc::ptr_eq(&key1_first, &old_key1));
    ///         assert!(Rc::ptr_eq(&key2_first, &old_key2));
    ///         assert_eq!(old_value, 15);
    ///     }
    ///     _ => panic!(),
    /// }
    ///
    /// assert!(Rc::strong_count(&key1_first) == 1 && Rc::strong_count(&key1_second) == 2);
    /// assert!(Rc::strong_count(&key2_first) == 1 && Rc::strong_count(&key2_second) == 2);
    /// assert_eq!(map[&"First key".to_owned()], 16);
    /// ```
    #[cfg_attr(feature = "inline-more", inline)]
    pub fn replace_entry(self, value: V) -> (K1, K2, V) {
        let &mut (ref mut k1, ref mut k2, ref mut v) = unsafe { self.data_bucket.as_mut() };

        let old_key1 = mem::replace(k1, self.key1.unwrap());
        let old_key2 = mem::replace(k2, self.key2.unwrap());
        let old_value = mem::replace(v, value);
        (old_key1, old_key2, old_value)
    }

    /// Replaces the `K1` key in the hash map with the key used
    /// to create this entry.
    ///
    /// # Panics
    ///
    /// Will panic if this `OccupiedEntry` was created through
    /// [`Entry::insert`].
    ///
    /// # Examples
    ///
    /// ```
    /// use double_map::shash_map::{DoubleMap, Entry};
    /// use std::rc::Rc;
    ///
    /// let mut map: DoubleMap<Rc<String>, usize, usize> = DoubleMap::with_capacity(6);
    /// let mut keys_one: Vec<Rc<String>> = Vec::with_capacity(6);
    /// let mut keys_two: Vec<Rc<String>> = Vec::with_capacity(6);
    ///
    /// for (index, key1) in ["a", "b", "c", "d", "e", "f"].into_iter().enumerate() {
    ///     let rc_key = Rc::new(key1.to_owned());
    ///     keys_one.push(rc_key.clone());
    ///     map.insert(rc_key.clone(), index, index);
    ///     keys_two.push(Rc::new(key1.to_owned()));
    /// }
    ///
    /// assert!(
    ///     keys_one.iter().all(|key| Rc::strong_count(key) == 2)
    ///         && keys_two.iter().all(|key| Rc::strong_count(key) == 1)
    /// );
    ///
    /// reclaim_memory(&mut map, &keys_two);
    ///
    /// assert!(
    ///     keys_one.iter().all(|key| Rc::strong_count(key) == 1)
    ///         && keys_two.iter().all(|key| Rc::strong_count(key) == 2)
    /// );
    ///
    /// fn reclaim_memory(map: &mut DoubleMap<Rc<String>, usize, usize>, keys: &[Rc<String>]) {
    ///     for (index, key) in keys.iter().enumerate() {
    ///         if let Ok(Entry::Occupied(entry)) = map.entry(key.clone(), index) {
    ///             // Replaces the entry's key with our version of it in `keys`.
    ///             entry.replace_key1();
    ///         }
    ///     }
    /// }
    /// ```
    #[cfg_attr(feature = "inline-more", inline)]
    pub fn replace_key1(self) -> K1 {
        let entry = unsafe { self.data_bucket.as_mut() };
        mem::replace(&mut entry.0, self.key1.unwrap())
    }

    /// Replaces the `K2` key in the hash map with the key used
    /// to create this entry.
    ///
    /// # Panics
    ///
    /// Will panic if this `OccupiedEntry` was created through
    /// [`Entry::insert`].
    ///
    /// # Examples
    ///
    /// ```
    /// use double_map::shash_map::{DoubleMap, Entry};
    /// use std::rc::Rc;
    ///
    /// let mut map: DoubleMap<usize, Rc<String>, usize> = DoubleMap::with_capacity(6);
    /// let mut keys_one: Vec<Rc<String>> = Vec::with_capacity(6);
    /// let mut keys_two: Vec<Rc<String>> = Vec::with_capacity(6);
    ///
    /// for (index, key1) in ["a", "b", "c", "d", "e", "f"].into_iter().enumerate() {
    ///     let rc_key = Rc::new(key1.to_owned());
    ///     keys_one.push(rc_key.clone());
    ///     map.insert(index, rc_key.clone(), index);
    ///     keys_two.push(Rc::new(key1.to_owned()));
    /// }
    ///
    /// assert!(
    ///     keys_one.iter().all(|key| Rc::strong_count(key) == 2)
    ///         && keys_two.iter().all(|key| Rc::strong_count(key) == 1)
    /// );
    ///
    /// reclaim_memory(&mut map, &keys_two);
    ///
    /// assert!(
    ///     keys_one.iter().all(|key| Rc::strong_count(key) == 1)
    ///         && keys_two.iter().all(|key| Rc::strong_count(key) == 2)
    /// );
    ///
    /// fn reclaim_memory(map: &mut DoubleMap<usize, Rc<String>, usize>, keys: &[Rc<String>]) {
    ///     for (index, key) in keys.iter().enumerate() {
    ///         if let Ok(Entry::Occupied(entry)) = map.entry(index, key.clone()) {
    ///             // Replaces the entry's key with our version of it in `keys`.
    ///             entry.replace_key2();
    ///         }
    ///     }
    /// }
    /// ```
    #[cfg_attr(feature = "inline-more", inline)]
    pub fn replace_key2(self) -> K2 {
        let entry = unsafe { self.data_bucket.as_mut() };
        mem::replace(&mut entry.1, self.key2.unwrap())
    }

    /// Replaces the `K1` and `K2` keys in the hash map with the keys
    /// used to create this entry.
    ///
    /// # Panics
    ///
    /// Will panic if this `OccupiedEntry` was created through
    /// [`Entry::insert`].
    ///
    /// # Examples
    ///
    /// ```
    /// use double_map::shash_map::{DoubleMap, Entry};
    /// use std::rc::Rc;
    ///
    /// let mut map: DoubleMap<Rc<String>, Rc<String>, usize> = DoubleMap::with_capacity(6);
    /// let mut keys_one: Vec<Rc<String>> = Vec::with_capacity(6);
    /// let mut keys_two: Vec<Rc<String>> = Vec::with_capacity(6);
    ///
    /// for (index, key1) in ["a", "b", "c", "d", "e", "f"].into_iter().enumerate() {
    ///     let rc_key = Rc::new(key1.to_owned());
    ///     keys_one.push(rc_key.clone());
    ///     map.insert(rc_key.clone(), rc_key.clone(), index);
    ///     keys_two.push(Rc::new(key1.to_owned()));
    /// }
    ///
    /// assert!(
    ///     keys_one.iter().all(|key| Rc::strong_count(key) == 3)
    ///         && keys_two.iter().all(|key| Rc::strong_count(key) == 1)
    /// );
    ///
    /// reclaim_memory(&mut map, &keys_two);
    ///
    /// assert!(
    ///     keys_one.iter().all(|key| Rc::strong_count(key) == 1)
    ///         && keys_two.iter().all(|key| Rc::strong_count(key) == 3)
    /// );
    ///
    /// fn reclaim_memory(map: &mut DoubleMap<Rc<String>, Rc<String>, usize>, keys: &[Rc<String>]) {
    ///     for key in keys {
    ///         if let Ok(Entry::Occupied(entry)) = map.entry(key.clone(), key.clone()) {
    ///             // Replaces the entry's keys with our version of it in `keys`.
    ///             entry.replace_keys();
    ///         }
    ///     }
    /// }
    /// ```
    #[cfg_attr(feature = "inline-more", inline)]
    pub fn replace_keys(self) -> (K1, K2) {
        let &mut (ref mut k1, ref mut k2, _) = unsafe { self.data_bucket.as_mut() };

        let old_key1 = mem::replace(k1, self.key1.unwrap());
        let old_key2 = mem::replace(k2, self.key2.unwrap());
        (old_key1, old_key2)
    }

    /// Provides shared access to the `K1` key and owned access to the value of
    /// the entry and allows to replace or remove it based on the
    /// value of the returned option.
    ///
    /// # Examples
    ///
    /// ```
    /// use double_map::shash_map::{DoubleMap, Entry};
    ///
    /// let mut map: DoubleMap<i32, &str, i32> = DoubleMap::new();
    /// map.insert(1, "poneyland", 42);
    ///
    /// let entry = match map.entry(1, "poneyland") {
    ///     Ok(Entry::Occupied(e)) => e.replace_entry_with_key1(|k1, v| {
    ///         assert_eq!(k1, &1);
    ///         assert_eq!(v, 42);
    ///         Some(v + 1)
    ///     }),
    ///     _ => panic!(),
    /// };
    ///
    /// match entry {
    ///     Entry::Occupied(e) => {
    ///         assert_eq!(e.key1(), &1);
    ///         assert_eq!(e.key2(), &"poneyland");
    ///         assert_eq!(e.get(), &43);
    ///     }
    ///     Entry::Vacant(_) => panic!(),
    /// }
    ///
    /// assert_eq!(map[&1], 43);
    ///
    /// let entry = match map.entry(1, "poneyland") {
    ///     Ok(Entry::Occupied(e)) => e.replace_entry_with_key1(|_k1, _v| None),
    ///     _ => panic!(),
    /// };
    ///
    /// match entry {
    ///     Entry::Vacant(e) => {
    ///         assert_eq!(e.key1(), &1);
    ///         assert_eq!(e.key2(), &"poneyland");
    ///     }
    ///     Entry::Occupied(_) => panic!(),
    /// }
    ///
    /// assert!(!map.contains_key1(&1));
    /// ```
    #[cfg_attr(feature = "inline-more", inline)]
    pub fn replace_entry_with_key1<F>(self, f: F) -> Entry<'a, K1, K2, V, S, A>
    where
        F: FnOnce(&K1, V) -> Option<V>,
    {
        let mut spare_key = None;
        unsafe {
            self.table.table.replace_data_with(
                self.pointer_bucket.clone(),
                |(key1, key2, value)| {
                    if let Some(new_value) = f(&key1, value) {
                        Some((key1, key2, new_value))
                    } else {
                        spare_key = Some((key1, key2));
                        None
                    }
                },
            );
        }
        if let Some((key1, key2)) = spare_key {
            Entry::Vacant(VacantEntry {
                hash1: self.hash1,
                key1,
                hash2: self.hash2,
                key2,
                table: self.table,
            })
        } else {
            Entry::Occupied(self)
        }
    }

    /// Provides shared access to the `K2` key and owned access to the value of
    /// the entry and allows to replace or remove it based on the
    /// value of the returned option.
    ///
    /// # Examples
    ///
    /// ```
    /// use double_map::shash_map::{DoubleMap, Entry};
    ///
    /// let mut map: DoubleMap<i32, &str, i32> = DoubleMap::new();
    /// map.insert(1, "poneyland", 42);
    ///
    /// let entry = match map.entry(1, "poneyland") {
    ///     Ok(Entry::Occupied(e)) => e.replace_entry_with_key2(|k2, v| {
    ///         assert_eq!(k2, &"poneyland");
    ///         assert_eq!(v, 42);
    ///         Some(v + 1)
    ///     }),
    ///     _ => panic!(),
    /// };
    ///
    /// match entry {
    ///     Entry::Occupied(e) => {
    ///         assert_eq!(e.key1(), &1);
    ///         assert_eq!(e.key2(), &"poneyland");
    ///         assert_eq!(e.get(), &43);
    ///     }
    ///     Entry::Vacant(_) => panic!(),
    /// }
    ///
    /// assert_eq!(map[&1], 43);
    ///
    /// let entry = match map.entry(1, "poneyland") {
    ///     Ok(Entry::Occupied(e)) => e.replace_entry_with_key2(|_k2, _v| None),
    ///     _ => panic!(),
    /// };
    ///
    /// match entry {
    ///     Entry::Vacant(e) => {
    ///         assert_eq!(e.key1(), &1);
    ///         assert_eq!(e.key2(), &"poneyland");
    ///     }
    ///     Entry::Occupied(_) => panic!(),
    /// }
    ///
    /// assert!(!map.contains_key2("poneyland"));
    /// ```
    #[cfg_attr(feature = "inline-more", inline)]
    pub fn replace_entry_with_key2<F>(self, f: F) -> Entry<'a, K1, K2, V, S, A>
    where
        F: FnOnce(&K2, V) -> Option<V>,
    {
        let mut spare_key = None;
        unsafe {
            self.table.table.replace_data_with(
                self.pointer_bucket.clone(),
                |(key1, key2, value)| {
                    if let Some(new_value) = f(&key2, value) {
                        Some((key1, key2, new_value))
                    } else {
                        spare_key = Some((key1, key2));
                        None
                    }
                },
            );
        }
        if let Some((key1, key2)) = spare_key {
            Entry::Vacant(VacantEntry {
                hash1: self.hash1,
                key1,
                hash2: self.hash2,
                key2,
                table: self.table,
            })
        } else {
            Entry::Occupied(self)
        }
    }

    /// Provides shared access to the `K1` and `K2` keys and owned
    /// access to the value of the entry and allows to replace or
    /// remove it based on the value of the returned option.
    ///
    /// # Examples
    ///
    /// ```
    /// use double_map::shash_map::{DoubleMap, Entry};
    ///
    /// let mut map: DoubleMap<i32, &str, i32> = DoubleMap::new();
    /// map.insert(1, "poneyland", 42);
    ///
    /// let entry = match map.entry(1, "poneyland") {
    ///     Ok(Entry::Occupied(e)) => e.replace_entry_with_keys(|k1, k2, v| {
    ///         assert_eq!(k1, &1);
    ///         assert_eq!(k2, &"poneyland");
    ///         assert_eq!(v, 42);
    ///         Some(v + 1)
    ///     }),
    ///     _ => panic!(),
    /// };
    ///
    /// match entry {
    ///     Entry::Occupied(e) => {
    ///         assert_eq!(e.key1(), &1);
    ///         assert_eq!(e.key2(), &"poneyland");
    ///         assert_eq!(e.get(), &43);
    ///     }
    ///     Entry::Vacant(_) => panic!(),
    /// }
    ///
    /// assert_eq!(map[&1], 43);
    ///
    /// let entry = match map.entry(1, "poneyland") {
    ///     Ok(Entry::Occupied(e)) => e.replace_entry_with_keys(|_k1, _k2, _v| None),
    ///     _ => panic!(),
    /// };
    ///
    /// match entry {
    ///     Entry::Vacant(e) => {
    ///         assert_eq!(e.key1(), &1);
    ///         assert_eq!(e.key2(), &"poneyland");
    ///     }
    ///     Entry::Occupied(_) => panic!(),
    /// }
    ///
    /// assert!(!map.contains_keys(&1, &"poneyland"));
    /// ```
    #[cfg_attr(feature = "inline-more", inline)]
    pub fn replace_entry_with_keys<F>(self, f: F) -> Entry<'a, K1, K2, V, S, A>
    where
        F: FnOnce(&K1, &K2, V) -> Option<V>,
    {
        let mut spare_key = None;
        unsafe {
            self.table.table.replace_data_with(
                self.pointer_bucket.clone(),
                |(key1, key2, value)| {
                    if let Some(new_value) = f(&key1, &key2, value) {
                        Some((key1, key2, new_value))
                    } else {
                        spare_key = Some((key1, key2));
                        None
                    }
                },
            );
        }
        if let Some((key1, key2)) = spare_key {
            Entry::Vacant(VacantEntry {
                hash1: self.hash1,
                key1,
                hash2: self.hash2,
                key2,
                table: self.table,
            })
        } else {
            Entry::Occupied(self)
        }
    }
}

/// A view into a vacant entry in a `DoubleMap`.
/// It is part of the [`Entry`] enum.
///
/// [`Entry`]: enum.Entry.html
///
/// # Examples
///
/// ```
/// use double_map::shash_map::{DoubleMap, Entry, VacantEntry};
///
/// let mut map = DoubleMap::<i32, &str, i32>::new();
///
/// let entry_v: VacantEntry<_, _, _, _> = match map.entry(1, "a").unwrap() {
///     Entry::Vacant(view) => view,
///     Entry::Occupied(_) => unreachable!(),
/// };
/// entry_v.insert(10);
/// assert!(map[&1] == 10 && map.len() == 1);
///
/// // Nonexistent key (insert and update)
/// match map.entry(2, "b") {
///     Ok(Entry::Vacant(view)) => {
///         let value = view.insert(2);
///         assert_eq!(*value, 2);
///         *value = 20;
///     }
///     _ => panic!("It should be nonexistent key"),
/// }
/// assert!(map[&2] == 20 && map.len() == 2);
/// ```
pub struct VacantEntry<'a, K1, K2, V, S, A: Allocator + Clone = Global> {
    pub(super) hash1: u64,
    pub(super) key1: K1,
    pub(super) hash2: u64,
    pub(super) key2: K2,
    pub(super) table: &'a mut DoubleMap<K1, K2, V, S, A>,
}

impl<K1: Debug, K2: Debug, V, S, A: Allocator + Clone> Debug for VacantEntry<'_, K1, K2, V, S, A> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("VacantEntry")
            .field("key1", self.key1())
            .field("key2", self.key2())
            .finish()
    }
}

impl<'a, K1, K2, V, S, A: Allocator + Clone> VacantEntry<'a, K1, K2, V, S, A> {
    /// Gets a reference to the `K1` key that would be used
    /// when inserting a value through the `VacantEntry`.
    ///
    /// # Examples
    ///
    /// ```
    /// use double_map::shash_map::{DoubleMap, Entry};
    ///
    /// let mut map: DoubleMap<&str, u32, i32> = DoubleMap::new();
    ///
    /// match map.entry("poneyland", 0) {
    ///     Ok(Entry::Vacant(vac_entry)) => assert_eq!(vac_entry.key1(), &"poneyland"),
    ///     _ => panic!(),
    /// }
    /// ```
    #[cfg_attr(feature = "inline-more", inline)]
    pub fn key1(&self) -> &K1 {
        &self.key1
    }

    /// Gets a reference to the `K2` key that would be used
    /// when inserting a value through the `VacantEntry`.
    ///
    /// # Examples
    ///
    /// ```
    /// use double_map::shash_map::{DoubleMap, Entry};
    ///
    /// let mut map: DoubleMap<&str, u32, i32> = DoubleMap::new();
    ///
    /// match map.entry("poneyland", 0) {
    ///     Ok(Entry::Vacant(vac_entry)) => assert_eq!(vac_entry.key2(), &0),
    ///     _ => panic!(),
    /// }
    /// ```
    #[cfg_attr(feature = "inline-more", inline)]
    pub fn key2(&self) -> &K2 {
        &self.key2
    }

    /// Gets a reference to the `K1` and `K2` keys that would be
    /// used when inserting a value through the `VacantEntry`.
    ///
    /// # Examples
    ///
    /// ```
    /// use double_map::shash_map::{DoubleMap, Entry};
    ///
    /// let mut map: DoubleMap<&str, u32, i32> = DoubleMap::new();
    ///
    /// match map.entry("poneyland", 0) {
    ///     Ok(Entry::Vacant(vac_entry)) => {
    ///         assert_eq!(vac_entry.keys(), (&"poneyland", &0));
    ///     }
    ///     _ => panic!(),
    /// }
    /// ```
    #[cfg_attr(feature = "inline-more", inline)]
    pub fn keys(&self) -> (&K1, &K2) {
        (&self.key1, &self.key2)
    }

    /// Take ownership of the `K1` key.
    ///
    /// # Examples
    ///
    /// ```
    /// use double_map::shash_map::{DoubleMap, Entry};
    ///
    /// let mut map: DoubleMap<&str, u32, i32> = DoubleMap::new();
    ///
    /// match map.entry("poneyland", 0) {
    ///     Ok(Entry::Vacant(v)) => assert_eq!(v.into_key1(), "poneyland"),
    ///     _ => panic!(),
    /// }
    /// ```
    #[cfg_attr(feature = "inline-more", inline)]
    pub fn into_key1(self) -> K1 {
        self.key1
    }

    /// Take ownership of the `K2` key.
    ///
    /// # Examples
    ///
    /// ```
    /// use double_map::shash_map::{DoubleMap, Entry};
    ///
    /// let mut map: DoubleMap<&str, u32, i32> = DoubleMap::new();
    ///
    /// match map.entry("poneyland", 0) {
    ///     Ok(Entry::Vacant(v)) => assert_eq!(v.into_key2(), 0),
    ///     _ => panic!(),
    /// }
    /// ```
    #[cfg_attr(feature = "inline-more", inline)]
    pub fn into_key2(self) -> K2 {
        self.key2
    }

    /// Take the ownership of the `K1` and `K2` keys.
    ///
    /// # Examples
    ///
    /// ```
    /// use double_map::shash_map::{DoubleMap, Entry};
    ///
    /// let mut map: DoubleMap<&str, u32, i32> = DoubleMap::new();
    ///
    /// match map.entry("poneyland", 0) {
    ///     Ok(Entry::Vacant(v)) => assert_eq!(v.into_keys(), ("poneyland", 0)),
    ///     _ => panic!(),
    /// }
    /// ```
    #[cfg_attr(feature = "inline-more", inline)]
    pub fn into_keys(self) -> (K1, K2) {
        (self.key1, self.key2)
    }

    /// Sets the value of the entry with the `VacantEntry`'s keys,
    /// and returns a mutable reference to it.
    ///
    /// # Examples
    ///
    /// ```
    /// use double_map::shash_map::{DoubleMap, Entry};
    ///
    /// let mut map: DoubleMap<&str, u32, i32> = DoubleMap::new();
    ///
    /// match map.entry("poneyland", 0) {
    ///     Ok(Entry::Vacant(vacant_entry)) => {
    ///         vacant_entry.insert(37);
    ///     }
    ///     _ => panic!(),
    /// }
    /// assert_eq!(map.get_key1(&"poneyland"), Some(&37));
    /// ```
    #[cfg_attr(feature = "inline-more", inline)]
    pub fn insert(self, value: V) -> &'a mut V
    where
        K1: Hash,
        K2: Hash,
        S: BuildHasher,
    {
        let hash_builder = &self.table.hash_builder;
        let table = &mut self.table.table;

        let entry = table.insert_entry(
            self.hash1,
            self.hash2,
            (self.key1, self.key2, value),
            make_hasher_key1::<_, K2, V, S>(hash_builder),
            make_hasher_key2::<K1, _, V, S>(hash_builder),
        );
        &mut entry.2
    }

    #[cfg_attr(feature = "inline-more", inline)]
    fn insert_entry(self, value: V) -> OccupiedEntry<'a, K1, K2, V, S, A>
    where
        K1: Hash,
        K2: Hash,
        S: BuildHasher,
    {
        let hash_builder = &self.table.hash_builder;
        let (data_bucket, pointer_bucket) = self.table.table.insert(
            self.hash1,
            self.hash2,
            (self.key1, self.key2, value),
            make_hasher_key1::<_, K2, V, S>(hash_builder),
            make_hasher_key2::<K1, _, V, S>(hash_builder),
        );
        OccupiedEntry {
            hash1: self.hash1,
            key1: None,
            hash2: self.hash2,
            key2: None,
            data_bucket,
            pointer_bucket,
            table: self.table,
        }
    }
}
