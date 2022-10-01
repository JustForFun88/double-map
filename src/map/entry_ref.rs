use super::*;

/// A view into a single entry in a map, which may either be vacant or occupied,
/// with any borrowed form of the map's keys type.
///
/// This `enum` is constructed from the [`entry_ref`] method on [`DHashMap`].
///
/// [`Hash`] and [`Eq`] on the borrowed form of the map's keys type *must* match those
/// for the keys type. It also require that keys may be constructed from the borrowed
/// form through the [`From`] trait.
///
/// [`DHashMap`]: struct.DHashMap.html
/// [`entry_ref`]: struct.DHashMap.html#method.entry_ref
/// [`Eq`]: https://doc.rust-lang.org/core/cmp/trait.Eq.html
/// [`Hash`]: https://doc.rust-lang.org/core/hash/trait.Hash.html
/// [`From`]: https://doc.rust-lang.org/core/convert/trait.From.html
///
/// # Examples
///
/// ```
/// use double_map::dhash_map::{DHashMap, EntryRef, OccupiedEntryRef};
///
/// #[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
/// struct Wrapper<T>(T);
///
/// impl<T: Copy> From<&Wrapper<T>> for Wrapper<T> {
///     fn from(id: &Wrapper<T>) -> Self {
///         Wrapper(id.0)
///     }
/// }
///
/// let mut map = DHashMap::new();
/// map.extend([
///     (Wrapper(1), "a".to_owned(), 10),
///     (Wrapper(2), "b".into(), 20),
///     (Wrapper(3), "c".into(), 30),
/// ]);
/// assert_eq!(map.len(), 3);
///
/// // Existing key (insert)
/// let key2 = "a";
/// let entry: EntryRef<_, _, _, _, _, _> = map.entry_ref(&Wrapper(1), key2).unwrap();
/// let _raw_o: OccupiedEntryRef<_, _, _, _, _, _> = entry.insert(1);
/// assert_eq!(map.len(), 3);
/// // Nonexistent key (insert)
/// map.entry_ref(&Wrapper(4), "d").unwrap().insert(4);
///
/// // Existing key (or_insert)
/// let v = map.entry_ref(&Wrapper(2), "b").unwrap().or_insert(2);
/// assert_eq!(std::mem::replace(v, 2), 20);
/// // Nonexistent key (or_insert)
/// map.entry_ref(&Wrapper(5), "e").unwrap().or_insert(5);
///
/// // Existing key (or_insert_with)
/// let v = map.entry_ref(&Wrapper(3), "c").unwrap().or_insert_with(|| 3);
/// assert_eq!(std::mem::replace(v, 3), 30);
/// // Nonexistent key (or_insert_with)
/// map.entry_ref(&Wrapper(6), "f").unwrap().or_insert_with(|| 6);
///
/// println!("Our DHashMap: {:?}", map);
///
/// let mut vec: Vec<_> = map.iter().map(|(k1, k2, v)| (k1, k2.as_str(), v)).collect();
/// // The `Iter` iterator produces items in arbitrary order, so the
/// // items must be sorted to test them against a sorted array.
/// vec.sort_unstable();
/// assert_eq!(
///     vec,
///     [
///         (&Wrapper(1), "a", &1),
///         (&Wrapper(2), "b", &2),
///         (&Wrapper(3), "c", &3),
///         (&Wrapper(4), "d", &4),
///         (&Wrapper(5), "e", &5),
///         (&Wrapper(6), "f", &6)
///     ]
/// );
/// ```
pub enum EntryRef<'a, 'b, K1, Q1: ?Sized, K2, Q2: ?Sized, V, S, A = Global>
where
    A: Allocator + Clone,
{
    /// An occupied entry.
    ///
    /// # Examples
    ///
    /// ```
    /// use double_map::dhash_map::{DHashMap, EntryRef};
    /// let mut map = DHashMap::<String, String, i32>::from([
    ///     ("a".to_owned(), "one".into(), 100),
    ///     ("b".into(), "two".into(), 200),
    /// ]);
    ///
    /// match map.entry_ref("a", "one") {
    ///     Ok(EntryRef::Occupied(_)) => {}
    ///     _ => panic!(),
    /// }
    /// ```
    Occupied(OccupiedEntryRef<'a, 'b, K1, Q1, K2, Q2, V, S, A>),

    /// A vacant entry.
    ///
    /// # Examples
    ///
    /// ```
    /// use double_map::dhash_map::{DHashMap, EntryRef};
    /// let mut map = DHashMap::<String, String, i32>::new();
    ///
    /// match map.entry_ref("a", "one") {
    ///     Ok(EntryRef::Vacant(_)) => {}
    ///     _ => panic!(),
    /// }
    /// ```
    Vacant(VacantEntryRef<'a, 'b, K1, Q1, K2, Q2, V, S, A>),
}

impl<K1, K2, Q1, Q2, V, S, A> Debug for EntryRef<'_, '_, K1, Q1, K2, Q2, V, S, A>
where
    K1: Borrow<Q1>,
    Q1: ?Sized + Debug,
    K2: Borrow<Q2>,
    Q2: ?Sized + Debug,
    V: Debug,
    A: Allocator + Clone,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match *self {
            EntryRef::Vacant(ref v) => f.debug_tuple("EntryRef").field(v).finish(),
            EntryRef::Occupied(ref o) => f.debug_tuple("EntryRef").field(o).finish(),
        }
    }
}

impl<'a, 'b, K1, Q1: ?Sized, K2, Q2: ?Sized, V, S, A> EntryRef<'a, 'b, K1, Q1, K2, Q2, V, S, A>
where
    A: Allocator + Clone,
{
    /// Sets the value of the entry, and returns an `OccupiedEntryRef`.
    ///
    /// # Examples
    ///
    /// ```
    /// use double_map::DHashMap;
    ///
    /// #[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
    /// struct Wrapper<T>(T);
    ///
    /// impl<T: Copy> From<&Wrapper<T>> for Wrapper<T> {
    ///     fn from(id: &Wrapper<T>) -> Self {
    ///         Wrapper(id.0)
    ///     }
    /// }
    ///
    /// let mut map: DHashMap<Wrapper<usize>, String, i32> = DHashMap::new();
    /// let entry = map.entry_ref(&Wrapper(1), "horseyland").unwrap().insert(37);
    ///
    /// assert_eq!(entry.key1(), &Wrapper(1));
    /// assert_eq!(entry.key2(), "horseyland");
    /// assert_eq!(entry.keys(), (&Wrapper(1), "horseyland"));
    /// ```
    #[cfg_attr(feature = "inline-more", inline)]
    pub fn insert(self, value: V) -> OccupiedEntryRef<'a, 'b, K1, Q1, K2, Q2, V, S, A>
    where
        K1: Hash + From<&'b Q1>,
        K2: Hash + From<&'b Q2>,
        S: BuildHasher,
    {
        match self {
            EntryRef::Occupied(mut entry) => {
                entry.insert(value);
                entry
            }
            EntryRef::Vacant(entry) => entry.insert_entry(value),
        }
    }

    /// Ensures a value is in the entry by inserting the default if empty, and returns
    /// a mutable reference to the value in the entry.
    ///
    /// # Examples
    ///
    /// ```
    /// use double_map::DHashMap;
    ///
    /// #[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
    /// struct Wrapper<T>(T);
    ///
    /// impl<T: Copy> From<&Wrapper<T>> for Wrapper<T> {
    ///     fn from(id: &Wrapper<T>) -> Self {
    ///         Wrapper(id.0)
    ///     }
    /// }
    ///
    /// let mut map: DHashMap<String, Wrapper<usize>, i32> = DHashMap::new();
    ///
    /// // nonexistent key
    /// match map.entry_ref("poneyland", &Wrapper(0)) {
    ///     Ok(entry) => {
    ///         entry.or_insert(3);
    ///     }
    ///     Err(_) => unreachable!(),
    /// }
    /// assert_eq!(map.get_key1("poneyland"), Some(&3));
    ///
    /// // existing key
    /// let _ = map
    ///     .entry_ref("poneyland", &Wrapper(0))
    ///     .map(|entry| *entry.or_insert(10) *= 2);
    /// assert_eq!(map.get_key1("poneyland"), Some(&6));
    /// ```
    #[cfg_attr(feature = "inline-more", inline)]
    pub fn or_insert(self, default: V) -> &'a mut V
    where
        K1: Hash + From<&'b Q1>,
        K2: Hash + From<&'b Q2>,
        S: BuildHasher,
    {
        match self {
            EntryRef::Occupied(entry) => entry.into_mut(),
            EntryRef::Vacant(entry) => entry.insert(default),
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
    /// #[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
    /// struct Wrapper<T>(T);
    ///
    /// impl<T: Copy> From<&Wrapper<T>> for Wrapper<T> {
    ///     fn from(id: &Wrapper<T>) -> Self {
    ///         Wrapper(id.0)
    ///     }
    /// }
    ///
    /// let mut map: DHashMap<String, Wrapper<usize>, String> = DHashMap::new();
    /// let s = "hoho".to_owned();
    ///
    /// // nonexistent key
    /// match map.entry_ref("poneyland", &Wrapper(0)) {
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
    ///     .entry_ref("poneyland", &Wrapper(0))
    ///     .map(|entry| entry.or_insert_with(|| k).push_str("ho"));
    /// assert_eq!(map.get_key1("poneyland"), Some(&"hohoho".to_owned()));
    /// ```
    #[cfg_attr(feature = "inline-more", inline)]
    pub fn or_insert_with<F: FnOnce() -> V>(self, default: F) -> &'a mut V
    where
        K1: Hash + From<&'b Q1>,
        K2: Hash + From<&'b Q2>,
        S: BuildHasher,
    {
        match self {
            EntryRef::Occupied(entry) => entry.into_mut(),
            EntryRef::Vacant(entry) => entry.insert(default()),
        }
    }

    /// Ensures a value is in the entry by inserting, if empty, the result of the default function.
    /// This method allows generating key-derived value for insertion by providing the default
    /// function a reference to the `Q1` key.
    ///
    /// # Examples
    ///
    /// ```
    /// use double_map::DHashMap;
    ///
    /// #[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
    /// struct Wrapper<T>(T);
    ///
    /// impl<T: Copy> From<&Wrapper<T>> for Wrapper<T> {
    ///     fn from(id: &Wrapper<T>) -> Self {
    ///         Wrapper(id.0)
    ///     }
    /// }
    ///
    /// let mut map: DHashMap<String, Wrapper<usize>, u64> = DHashMap::new();
    ///
    /// // nonexistent key
    /// match map.entry_ref("poneyland", &Wrapper(0)) {
    ///     Ok(entry) => {
    ///         entry.or_insert_with_key1(|k1| k1.chars().count() as u64);
    ///     }
    ///     Err(_) => unreachable!(),
    /// }
    /// assert_eq!(map.get_key1("poneyland"), Some(&9));
    ///
    /// // existing key
    /// let _ = map
    ///     .entry_ref("poneyland", &Wrapper(0))
    ///     .map(|ent| ent.or_insert_with_key1(|k1| (k1.chars().count() * 2) as u64 * 10))
    ///     .map(|value| *value *= 2);
    ///
    /// assert_eq!(map.get_key1("poneyland"), Some(&18));
    ///
    /// let _ = map
    ///     .entry_ref("bearland", &Wrapper(1))
    ///     .map(|ent| ent.or_insert_with_key1(|k1| (k1.chars().count() * 2) as u64));
    /// assert_eq!(map.get_key1("bearland"), Some(&16));
    /// ```
    #[cfg_attr(feature = "inline-more", inline)]
    pub fn or_insert_with_key1<F: FnOnce(&Q1) -> V>(self, default: F) -> &'a mut V
    where
        K1: Hash + Borrow<Q1> + From<&'b Q1>,
        K2: Hash + From<&'b Q2>,
        S: BuildHasher,
    {
        match self {
            EntryRef::Occupied(entry) => entry.into_mut(),
            EntryRef::Vacant(entry) => {
                let value = default(entry.key1());
                entry.insert(value)
            }
        }
    }

    /// Ensures a value is in the entry by inserting, if empty, the result of the default function.
    /// This method allows generating key-derived value for insertion by providing the default
    /// function a reference to the `Q2` key.
    ///
    /// # Examples
    ///
    /// ```
    /// use double_map::DHashMap;
    ///
    /// #[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
    /// struct Wrapper<T>(T);
    ///
    /// impl<T: Copy> From<&Wrapper<T>> for Wrapper<T> {
    ///     fn from(id: &Wrapper<T>) -> Self {
    ///         Wrapper(id.0)
    ///     }
    /// }
    ///
    /// let mut map: DHashMap<String, Wrapper<usize>, u64> = DHashMap::new();
    ///
    /// // nonexistent key
    /// match map.entry_ref("poneyland", &Wrapper(10)) {
    ///     Ok(entry) => {
    ///         entry.or_insert_with_key2(|k2| k2.0 as u64 * 10);
    ///     }
    ///     Err(_) => unreachable!(),
    /// }
    /// assert_eq!(map.get_key2(&Wrapper(10)), Some(&100));
    ///
    /// // existing key
    /// let _ = map
    ///     .entry_ref("poneyland", &Wrapper(10))
    ///     .map(|ent| ent.or_insert_with_key2(|k1| k1.0 as u64 / 10))
    ///     .map(|value| *value *= 2);
    ///
    /// assert_eq!(map.get_key2(&Wrapper(10)), Some(&200));
    ///
    /// let _ = map
    ///     .entry_ref("bearland", &Wrapper(20))
    ///     .map(|ent| ent.or_insert_with_key2(|k2| k2.0 as u64 + 10));
    /// assert_eq!(map.get_key2(&Wrapper(20)), Some(&30));
    /// ```
    #[cfg_attr(feature = "inline-more", inline)]
    pub fn or_insert_with_key2<F: FnOnce(&Q2) -> V>(self, default: F) -> &'a mut V
    where
        K1: Hash + From<&'b Q1>,
        K2: Hash + Borrow<Q2> + From<&'b Q2>,
        S: BuildHasher,
    {
        match self {
            EntryRef::Occupied(entry) => entry.into_mut(),
            EntryRef::Vacant(entry) => {
                let value = default(entry.key2());
                entry.insert(value)
            }
        }
    }

    /// Ensures a value is in the entry by inserting, if empty, the result of the default function.
    /// This method allows generating key-derived value for insertion by providing the default
    /// function references to the `Q1` and `Q2` keys.
    ///
    /// The reference to the moved keys is provided so that cloning or copying the key is
    /// unnecessary, unlike with `.or_insert_with(|| ... )`.
    ///
    /// # Examples
    ///
    /// ```
    /// use double_map::DHashMap;
    ///
    /// #[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
    /// struct Wrapper<T>(T);
    ///
    /// impl<T: Copy> From<&Wrapper<T>> for Wrapper<T> {
    ///     fn from(id: &Wrapper<T>) -> Self {
    ///         Wrapper(id.0)
    ///     }
    /// }
    ///
    /// let mut map: DHashMap<String, Wrapper<usize>, u64> = DHashMap::new();
    ///
    /// // nonexistent key
    /// match map.entry_ref("poneyland", &Wrapper(10)) {
    ///     Ok(entry) => {
    ///         entry.or_insert_with_keys(|k1, k2| (k1.chars().count() + k2.0) as u64);
    ///     }
    ///     Err(_) => unreachable!(),
    /// }
    /// assert_eq!(map.get_keys("poneyland", &Wrapper(10)), Some(&19));
    ///
    /// // existing key
    /// let _ = map
    ///     .entry_ref("poneyland", &Wrapper(10))
    ///     .map(|ent| ent.or_insert_with_keys(|k1, k2| (k1.chars().count() + k2.0 * 3) as u64))
    ///     .map(|value| *value *= 2);
    ///
    /// assert_eq!(map.get_keys("poneyland", &Wrapper(10)), Some(&38));
    ///
    /// let _ = map
    ///     .entry_ref("bearland", &Wrapper(20))
    ///     .map(|ent| ent.or_insert_with_keys(|k1, k2| (k1.chars().count() + k2.0 * 3) as u64));
    /// assert_eq!(map.get_keys("bearland", &Wrapper(20)), Some(&68));
    /// ```
    #[cfg_attr(feature = "inline-more", inline)]
    pub fn or_insert_with_keys<F: FnOnce(&Q1, &Q2) -> V>(self, default: F) -> &'a mut V
    where
        K1: Hash + Borrow<Q1> + From<&'b Q1>,
        K2: Hash + Borrow<Q2> + From<&'b Q2>,
        S: BuildHasher,
    {
        match self {
            EntryRef::Occupied(entry) => entry.into_mut(),
            EntryRef::Vacant(entry) => {
                let value = default(entry.key1(), entry.key2());
                entry.insert(value)
            }
        }
    }

    /// Returns a reference to this entry's first `Q1` key.
    ///
    /// # Examples
    ///
    /// ```
    /// use double_map::DHashMap;
    ///
    /// #[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
    /// struct Wrapper<T>(T);
    ///
    /// impl<T: Copy> From<&Wrapper<T>> for Wrapper<T> {
    ///     fn from(id: &Wrapper<T>) -> Self {
    ///         Wrapper(id.0)
    ///     }
    /// }
    ///
    /// let mut map: DHashMap<String, Wrapper<usize>, u64> = DHashMap::new();
    ///
    /// // It is VacantEntryRef
    /// match map.entry_ref("poneyland", &Wrapper(0)) {
    ///     Ok(entry) => {
    ///         // key equal to provided one
    ///         assert_eq!(entry.key1(), "poneyland");
    ///         // we insert some value
    ///         entry.or_insert(25);
    ///     }
    ///     Err(_) => unreachable!(),
    /// }
    /// // As we can see, now this element exists
    /// assert_eq!(map.get_key1("poneyland"), Some(&25));
    ///
    /// // So now it is OccupiedEntryRef
    /// match map.entry_ref("poneyland", &Wrapper(0)) {
    ///     Ok(entry) => {
    ///         // And key equals to provided one too
    ///         assert_eq!(entry.key1(), "poneyland");
    ///         entry.or_insert(50);
    ///     }
    ///     Err(_) => unreachable!(),
    /// }
    /// // The value does not changed
    /// assert_eq!(map.get_key1("poneyland"), Some(&25));
    /// ```
    #[cfg_attr(feature = "inline-more", inline)]
    pub fn key1(&self) -> &Q1
    where
        K1: Borrow<Q1>,
    {
        match *self {
            EntryRef::Occupied(ref entry) => entry.key1(),
            EntryRef::Vacant(ref entry) => entry.key1(),
        }
    }

    /// Returns a reference to this entry's second `Q2` key.
    ///
    /// # Examples
    ///
    /// ```
    /// use double_map::DHashMap;
    ///
    /// #[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
    /// struct Wrapper<T>(T);
    ///
    /// impl<T: Copy> From<&Wrapper<T>> for Wrapper<T> {
    ///     fn from(id: &Wrapper<T>) -> Self {
    ///         Wrapper(id.0)
    ///     }
    /// }
    ///
    /// let mut map: DHashMap<String, Wrapper<usize>, u64> = DHashMap::new();
    ///
    /// // It is VacantEntryRef
    /// match map.entry_ref("poneyland", &Wrapper(10)) {
    ///     Ok(entry) => {
    ///         // key equal to provided one
    ///         assert_eq!(entry.key2(), &Wrapper(10));
    ///         // we insert some value
    ///         entry.or_insert(25);
    ///     }
    ///     Err(_) => unreachable!(),
    /// }
    /// // As we can see, now this element exists
    /// assert_eq!(map.get_key2(&Wrapper(10)), Some(&25));
    ///
    /// // So now it is OccupiedEntryRef
    /// match map.entry_ref("poneyland", &Wrapper(10)) {
    ///     Ok(entry) => {
    ///         // And key equals to provided one too
    ///         assert_eq!(entry.key2(), &Wrapper(10));
    ///         entry.or_insert(50);
    ///     }
    ///     Err(_) => unreachable!(),
    /// }
    /// // The value does not changed
    /// assert_eq!(map.get_key2(&Wrapper(10)), Some(&25));
    /// ```
    #[cfg_attr(feature = "inline-more", inline)]
    pub fn key2(&self) -> &Q2
    where
        K2: Borrow<Q2>,
    {
        match *self {
            EntryRef::Occupied(ref entry) => entry.key2(),
            EntryRef::Vacant(ref entry) => entry.key2(),
        }
    }

    /// Returns a reference to this entry's keys.
    /// Return tuple of type (&'a Q1, &'a Q2).
    ///
    /// # Examples
    ///
    /// ```
    /// use double_map::DHashMap;
    ///
    /// #[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
    /// struct Wrapper<T>(T);
    ///
    /// impl<T: Copy> From<&Wrapper<T>> for Wrapper<T> {
    ///     fn from(id: &Wrapper<T>) -> Self {
    ///         Wrapper(id.0)
    ///     }
    /// }
    ///
    /// let mut map: DHashMap<String, Wrapper<usize>, u64> = DHashMap::new();
    ///
    /// // It is VacantEntryRef
    /// match map.entry_ref("poneyland", &Wrapper(10)) {
    ///     Ok(entry) => {
    ///         // keys equal to provided one
    ///         assert_eq!(entry.keys(), ("poneyland", &Wrapper(10)));
    ///         // we insert some value
    ///         entry.or_insert(25);
    ///     }
    ///     Err(_) => unreachable!(),
    /// }
    /// // As we can see, now this element exists
    /// assert_eq!(map.get_keys("poneyland", &Wrapper(10)), Some(&25));
    ///
    /// // So now it is OccupiedEntryRef
    /// match map.entry_ref("poneyland", &Wrapper(10)) {
    ///     Ok(entry) => {
    ///         // And keys equal to provided one too
    ///         assert_eq!(entry.keys(), ("poneyland", &Wrapper(10)));
    ///         entry.or_insert(50);
    ///     }
    ///     Err(_) => unreachable!(),
    /// }
    /// // The value does not changed
    /// assert_eq!(map.get_keys("poneyland", &Wrapper(10)), Some(&25));
    /// ```
    #[cfg_attr(feature = "inline-more", inline)]
    pub fn keys(&self) -> (&Q1, &Q2)
    where
        K1: Borrow<Q1>,
        K2: Borrow<Q2>,
    {
        match *self {
            EntryRef::Occupied(ref entry) => entry.keys(),
            EntryRef::Vacant(ref entry) => entry.keys(),
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
    /// #[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
    /// struct Wrapper<T>(T);
    ///
    /// impl<T: Copy> From<&Wrapper<T>> for Wrapper<T> {
    ///     fn from(id: &Wrapper<T>) -> Self {
    ///         Wrapper(id.0)
    ///     }
    /// }
    ///
    /// let mut map: DHashMap<String, Wrapper<usize>, u64> = DHashMap::new();
    ///
    /// let _ = map
    ///     .entry_ref("poneyland", &Wrapper(1))
    ///     .map(|entry| entry.and_modify(|value| *value += 100).or_insert(42));
    /// assert_eq!(map.get_key1("poneyland"), Some(&42));
    ///
    /// let _ = map
    ///     .entry_ref("poneyland", &Wrapper(1))
    ///     .map(|entry| entry.and_modify(|value| *value += 100).or_insert(42));
    /// assert_eq!(map.get_key1("poneyland"), Some(&142));
    /// ```
    #[cfg_attr(feature = "inline-more", inline)]
    pub fn and_modify<F>(self, f: F) -> Self
    where
        F: FnOnce(&mut V),
    {
        match self {
            EntryRef::Occupied(mut entry) => {
                f(entry.get_mut());
                EntryRef::Occupied(entry)
            }
            EntryRef::Vacant(entry) => EntryRef::Vacant(entry),
        }
    }

    /// Provides shared access to the first `Q1` key and owned access to the
    /// value of an occupied entry and allows to replace or remove it based on the
    /// value of the returned option.
    ///
    /// # Examples
    ///
    /// ```
    /// use double_map::dhash_map::{DHashMap, EntryRef};
    ///
    /// #[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
    /// struct Wrapper<T>(T);
    ///
    /// impl<T: Copy> From<&Wrapper<T>> for Wrapper<T> {
    ///     fn from(id: &Wrapper<T>) -> Self {
    ///         Wrapper(id.0)
    ///     }
    /// }
    ///
    /// let mut map: DHashMap<String, Wrapper<usize>, String> = DHashMap::new();
    ///
    /// let entry = map
    ///     .entry_ref("poneyland", &Wrapper(1))
    ///     .unwrap()
    ///     .and_replace_entry_with_key1(|_k1, _v| panic!());
    ///
    /// match entry {
    ///     EntryRef::Vacant(e) => {
    ///         assert_eq!(e.key1(), "poneyland");
    ///         assert_eq!(e.key2(), &Wrapper(1));
    ///     }
    ///     EntryRef::Occupied(_) => panic!(),
    /// }
    ///
    /// map.insert("poneyland".to_owned(), Wrapper(1), "land".to_owned());
    ///
    /// let entry = map
    ///     .entry_ref("poneyland", &Wrapper(1))
    ///     .unwrap()
    ///     .and_replace_entry_with_key1(|k1, v| {
    ///         assert_eq!(k1, "poneyland");
    ///         assert_eq!(v.as_str(), "land");
    ///         Some("dream land".to_owned())
    ///     });
    ///
    /// match entry {
    ///     EntryRef::Occupied(e) => {
    ///         assert_eq!(e.key1(), "poneyland");
    ///         assert_eq!(e.key2(), &Wrapper(1));
    ///         assert_eq!(e.get(), "dream land");
    ///     }
    ///     EntryRef::Vacant(_) => panic!(),
    /// }
    ///
    /// assert_eq!(map["poneyland"], "dream land");
    ///
    /// let entry = map
    ///     .entry_ref("poneyland", &Wrapper(1))
    ///     .unwrap()
    ///     .and_replace_entry_with_key1(|_k1, _v| None);
    ///
    /// match entry {
    ///     EntryRef::Vacant(e) => {
    ///         assert_eq!(e.key1(), "poneyland");
    ///         assert_eq!(e.key2(), &Wrapper(1));
    ///     }
    ///     EntryRef::Occupied(_) => panic!(),
    /// }
    ///
    /// assert!(!map.contains_key1("poneyland"));
    /// assert!(map.is_empty());
    /// ```
    #[cfg_attr(feature = "inline-more", inline)]
    pub fn and_replace_entry_with_key1<F>(self, f: F) -> Self
    where
        F: FnOnce(&Q1, V) -> Option<V>,
        K1: Borrow<Q1>,
    {
        match self {
            EntryRef::Occupied(entry) => entry.replace_entry_with_key1(f),
            EntryRef::Vacant(_) => self,
        }
    }

    /// Provides shared access to the second `Q2` key and owned access to the
    /// value of an occupied entry and allows to replace or remove it based on the
    /// value of the returned option.
    ///
    /// # Examples
    ///
    /// ```
    /// use double_map::dhash_map::{DHashMap, EntryRef};
    ///
    /// #[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
    /// struct Wrapper<T>(T);
    ///
    /// impl<T: Copy> From<&Wrapper<T>> for Wrapper<T> {
    ///     fn from(id: &Wrapper<T>) -> Self {
    ///         Wrapper(id.0)
    ///     }
    /// }
    ///
    /// let mut map: DHashMap<String, Wrapper<usize>, String> = DHashMap::new();
    ///
    /// let entry = map
    ///     .entry_ref("poneyland", &Wrapper(1))
    ///     .unwrap()
    ///     .and_replace_entry_with_key2(|_k2, _v| panic!());
    ///
    /// match entry {
    ///     EntryRef::Vacant(e) => {
    ///         assert_eq!(e.key1(), "poneyland");
    ///         assert_eq!(e.key2(), &Wrapper(1));
    ///     }
    ///     EntryRef::Occupied(_) => panic!(),
    /// }
    ///
    /// map.insert("poneyland".to_owned(), Wrapper(1), "land".to_owned());
    ///
    /// let entry = map
    ///     .entry_ref("poneyland", &Wrapper(1))
    ///     .unwrap()
    ///     .and_replace_entry_with_key2(|k2, v| {
    ///         assert_eq!(k2, &Wrapper(1));
    ///         assert_eq!(v.as_str(), "land");
    ///         Some("dream land".to_owned())
    ///     });
    ///
    /// match entry {
    ///     EntryRef::Occupied(e) => {
    ///         assert_eq!(e.key1(), "poneyland");
    ///         assert_eq!(e.key2(), &Wrapper(1));
    ///         assert_eq!(e.get(), "dream land");
    ///     }
    ///     EntryRef::Vacant(_) => panic!(),
    /// }
    ///
    /// assert_eq!(map["poneyland"], "dream land");
    ///
    /// let entry = map
    ///     .entry_ref("poneyland", &Wrapper(1))
    ///     .unwrap()
    ///     .and_replace_entry_with_key2(|_k2, _v| None);
    ///
    /// match entry {
    ///     EntryRef::Vacant(e) => {
    ///         assert_eq!(e.key1(), "poneyland");
    ///         assert_eq!(e.key2(), &Wrapper(1));
    ///     }
    ///     EntryRef::Occupied(_) => panic!(),
    /// }
    ///
    /// assert!(!map.contains_key2(&Wrapper(1)));
    /// assert!(map.is_empty());
    /// ```
    #[cfg_attr(feature = "inline-more", inline)]
    pub fn and_replace_entry_with_key2<F>(self, f: F) -> Self
    where
        F: FnOnce(&Q2, V) -> Option<V>,
        K2: Borrow<Q2>,
    {
        match self {
            EntryRef::Occupied(entry) => entry.replace_entry_with_key2(f),
            EntryRef::Vacant(_) => self,
        }
    }

    /// Provides shared access to the `Q1` and `Q2` keys and owned access to the
    /// value of an occupied entry and allows to replace or remove it based on the
    /// value of the returned option.
    ///
    /// # Examples
    ///
    /// ```
    /// use double_map::dhash_map::{DHashMap, EntryRef};
    ///
    /// #[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
    /// struct Wrapper<T>(T);
    ///
    /// impl<T: Copy> From<&Wrapper<T>> for Wrapper<T> {
    ///     fn from(id: &Wrapper<T>) -> Self {
    ///         Wrapper(id.0)
    ///     }
    /// }
    ///
    /// let mut map: DHashMap<String, Wrapper<usize>, String> = DHashMap::new();
    ///
    /// let entry = map
    ///     .entry_ref("poneyland", &Wrapper(1))
    ///     .unwrap()
    ///     .and_replace_entry_with_keys(|_k1, _k2, _v| panic!());
    ///
    /// match entry {
    ///     EntryRef::Vacant(e) => {
    ///         assert_eq!(e.key1(), "poneyland");
    ///         assert_eq!(e.key2(), &Wrapper(1));
    ///     }
    ///     EntryRef::Occupied(_) => panic!(),
    /// }
    ///
    /// map.insert("poneyland".to_owned(), Wrapper(1), "land".to_owned());
    ///
    /// let entry = map
    ///     .entry_ref("poneyland", &Wrapper(1))
    ///     .unwrap()
    ///     .and_replace_entry_with_keys(|k1, k2, v| {
    ///         assert_eq!(k1, "poneyland");
    ///         assert_eq!(k2, &Wrapper(1));
    ///         assert_eq!(v.as_str(), "land");
    ///         Some("dream land".to_owned())
    ///     });
    ///
    /// match entry {
    ///     EntryRef::Occupied(e) => {
    ///         assert_eq!(e.key1(), "poneyland");
    ///         assert_eq!(e.key2(), &Wrapper(1));
    ///         assert_eq!(e.get(), "dream land");
    ///     }
    ///     EntryRef::Vacant(_) => panic!(),
    /// }
    ///
    /// assert_eq!(map["poneyland"], "dream land");
    ///
    /// let entry = map
    ///     .entry_ref("poneyland", &Wrapper(1))
    ///     .unwrap()
    ///     .and_replace_entry_with_keys(|_k1, _k2, _v| None);
    ///
    /// match entry {
    ///     EntryRef::Vacant(e) => {
    ///         assert_eq!(e.key1(), "poneyland");
    ///         assert_eq!(e.key2(), &Wrapper(1));
    ///     }
    ///     EntryRef::Occupied(_) => panic!(),
    /// }
    ///
    /// assert!(!map.contains_keys("poneyland", &Wrapper(1)));
    /// assert!(map.is_empty());
    /// ```
    #[cfg_attr(feature = "inline-more", inline)]
    pub fn and_replace_entry_with_keys<F>(self, f: F) -> Self
    where
        F: FnOnce(&Q1, &Q2, V) -> Option<V>,
        K1: Borrow<Q1>,
        K2: Borrow<Q2>,
    {
        match self {
            EntryRef::Occupied(entry) => entry.replace_entry_with_keys(f),
            EntryRef::Vacant(_) => self,
        }
    }
}

impl<'a, 'b, K1, Q1: ?Sized, K2, Q2: ?Sized, V: Default, S, A>
    EntryRef<'a, 'b, K1, Q1, K2, Q2, V, S, A>
where
    A: Allocator + Clone,
{
    /// Ensures a value is in the entry by inserting the default value if empty,
    /// and returns a mutable reference to the value in the entry.
    ///
    /// # Examples
    ///
    /// ```
    /// use double_map::DHashMap;
    ///
    /// #[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
    /// struct Wrapper<T>(T);
    ///
    /// impl<T: Copy> From<&Wrapper<T>> for Wrapper<T> {
    ///     fn from(id: &Wrapper<T>) -> Self {
    ///         Wrapper(id.0)
    ///     }
    /// }
    ///
    /// let mut map: DHashMap<String, Wrapper<usize>, Option<u32>> = DHashMap::new();
    ///
    /// // nonexistent key
    /// map.entry_ref("poneyland", &Wrapper(1))
    ///     .unwrap()
    ///     .or_default();
    /// assert_eq!(map["poneyland"], None);
    ///
    /// map.insert("horseland".to_owned(), Wrapper(2), Some(3));
    ///
    /// // existing key
    /// assert_eq!(
    ///     map.entry_ref("horseland", &Wrapper(2))
    ///         .unwrap()
    ///         .or_default(),
    ///     &mut Some(3)
    /// );
    /// ```
    #[cfg_attr(feature = "inline-more", inline)]
    pub fn or_default(self) -> &'a mut V
    where
        K1: Hash + From<&'b Q1>,
        K2: Hash + From<&'b Q2>,
        S: BuildHasher,
    {
        match self {
            EntryRef::Occupied(entry) => entry.into_mut(),
            EntryRef::Vacant(entry) => entry.insert(Default::default()),
        }
    }
}

#[derive(Debug)]
pub(super) enum KeyOrRef<'a, K, Q: ?Sized> {
    Borrowed(&'a Q),
    Owned(K),
}

impl<'a, K, Q: ?Sized> KeyOrRef<'a, K, Q> {
    fn into_owned(self) -> K
    where
        K: From<&'a Q>,
    {
        match self {
            Self::Borrowed(borrowed) => borrowed.into(),
            Self::Owned(owned) => owned,
        }
    }
}

impl<'a, K: Borrow<Q>, Q: ?Sized> AsRef<Q> for KeyOrRef<'a, K, Q> {
    fn as_ref(&self) -> &Q {
        match self {
            Self::Borrowed(borrowed) => borrowed,
            Self::Owned(owned) => owned.borrow(),
        }
    }
}

/// A view into an occupied entry in a `DHashMap`.
/// It is part of the [`EntryRef`] enum.
///
/// [`EntryRef`]: enum.EntryRef.html
///
/// # Examples
///
/// ```
/// use double_map::dhash_map::{DHashMap, EntryRef, OccupiedEntryRef};
///
/// #[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
/// struct Wrapper<T>(T);
///
/// impl<T: Copy> From<&Wrapper<T>> for Wrapper<T> {
///     fn from(id: &Wrapper<T>) -> Self {
///         Wrapper(id.0)
///     }
/// }
///
/// let mut map: DHashMap<Wrapper<usize>, String, i32> = DHashMap::new();
///
/// map.extend([
///     (Wrapper(1), "a".to_owned(), 10),
///     (Wrapper(2), "b".to_owned(), 20),
///     (Wrapper(3), "c".to_owned(), 30),
/// ]);
///
/// let _entry_o: OccupiedEntryRef<_, _, _, _, _, _> =
///     map.entry_ref(&Wrapper(1), "a").unwrap().insert(100);
/// assert_eq!(map.len(), 3);
///
/// // Existing key (insert and update)
/// match map.entry_ref(&Wrapper(1), "a") {
///     Ok(EntryRef::Occupied(mut view)) => {
///         assert_eq!(view.get(), &100);
///         let v = view.get_mut();
///         *v *= 10;
///         assert_eq!(view.insert(1111), 1000);
///     }
///     _ => panic!("Not existing key?"),
/// }
///
/// assert_eq!(map[&Wrapper(1)], 1111);
/// assert_eq!(map.len(), 3);
///
/// // Existing key (take)
/// match map.entry_ref(&Wrapper(3), "c") {
///     Ok(EntryRef::Occupied(view)) => {
///         assert_eq!(view.remove_entry(), (Wrapper(3), "c".to_owned(), 30));
///     }
///     _ => panic!("It should be existing key"),
/// }
/// assert_eq!(map.get_key2("c"), None);
/// assert_eq!(map.len(), 2);
/// ```
pub struct OccupiedEntryRef<'a, 'b, K1, Q1: ?Sized, K2, Q2: ?Sized, V, S, A = Global>
where
    A: Allocator + Clone,
{
    pub(super) hash1: u64,
    pub(super) key1: Option<KeyOrRef<'b, K1, Q1>>,
    pub(super) hash2: u64,
    pub(super) key2: Option<KeyOrRef<'b, K2, Q2>>,
    pub(super) data_bucket: DataBucket<(K1, K2, V)>,
    pub(super) pointer_bucket: PointerBucket<DataBucket<(K1, K2, V)>>,
    pub(super) table: &'a mut DHashMap<K1, K2, V, S, A>,
}

unsafe impl<'a, 'b, K1, Q1, K2, Q2, V, S, A> Send
    for OccupiedEntryRef<'a, 'b, K1, Q1, K2, Q2, V, S, A>
where
    K1: Send,
    Q1: Sync + ?Sized,
    K2: Send,
    Q2: Sync + ?Sized,
    V: Send,
    S: Send,
    A: Send + Allocator + Clone,
{
}

unsafe impl<'a, 'b, K1, Q1, K2, Q2, V, S, A> Sync
    for OccupiedEntryRef<'a, 'b, K1, Q1, K2, Q2, V, S, A>
where
    K1: Sync,
    Q1: Sync + ?Sized,
    K2: Sync,
    Q2: Sync + ?Sized,
    V: Sync,
    S: Sync,
    A: Sync + Allocator + Clone,
{
}

impl<K1, Q1, K2, Q2, V, S, A> Debug for OccupiedEntryRef<'_, '_, K1, Q1, K2, Q2, V, S, A>
where
    K1: Borrow<Q1>,
    Q1: ?Sized + Debug,
    K2: Borrow<Q2>,
    Q2: ?Sized + Debug,
    V: Debug,
    A: Allocator + Clone,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("OccupiedEntryRef")
            .field("key1", &self.key1())
            .field("key2", &self.key2())
            .field("value", self.get())
            .finish()
    }
}

impl<'a, 'b, K1, Q1: ?Sized, K2, Q2: ?Sized, V, S, A>
    OccupiedEntryRef<'a, 'b, K1, Q1, K2, Q2, V, S, A>
where
    A: Allocator + Clone,
{
    /// Gets a reference to the first `Q1` key in the entry.
    ///
    /// # Examples
    ///
    /// ```
    /// use double_map::dhash_map::{DHashMap, EntryRef};
    ///
    /// #[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
    /// struct Wrapper<T>(T);
    ///
    /// impl<T: Copy> From<&Wrapper<T>> for Wrapper<T> {
    ///     fn from(id: &Wrapper<T>) -> Self {
    ///         Wrapper(id.0)
    ///     }
    /// }
    ///
    /// let mut map: DHashMap<String, Wrapper<usize>, i32> = DHashMap::new();
    ///
    /// map.insert("poneyland".to_owned(), Wrapper(0), 12);
    ///
    /// match map.entry_ref("poneyland", &Wrapper(0)) {
    ///     Ok(EntryRef::Occupied(entry)) => {
    ///         assert_eq!(entry.key1(), "poneyland");
    ///     }
    ///     _ => panic!(),
    /// }
    /// ```
    #[cfg_attr(feature = "inline-more", inline)]
    pub fn key1(&self) -> &Q1
    where
        K1: Borrow<Q1>,
    {
        unsafe { &self.data_bucket.as_ref().0 }.borrow()
    }

    /// Gets a reference to the second `Q2` key in the entry.
    ///
    /// # Examples
    ///
    /// ```
    /// use double_map::dhash_map::{DHashMap, EntryRef};
    ///
    /// #[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
    /// struct Wrapper<T>(T);
    ///
    /// impl<T: Copy> From<&Wrapper<T>> for Wrapper<T> {
    ///     fn from(id: &Wrapper<T>) -> Self {
    ///         Wrapper(id.0)
    ///     }
    /// }
    ///
    /// let mut map: DHashMap<String, Wrapper<usize>, i32> = DHashMap::new();
    ///
    /// map.insert("poneyland".to_owned(), Wrapper(0), 12);
    ///
    /// match map.entry_ref("poneyland", &Wrapper(0)) {
    ///     Ok(EntryRef::Occupied(entry)) => {
    ///         assert_eq!(entry.key2(), &Wrapper(0));
    ///     }
    ///     _ => panic!(),
    /// }
    /// ```
    #[cfg_attr(feature = "inline-more", inline)]
    pub fn key2(&self) -> &Q2
    where
        K2: Borrow<Q2>,
    {
        unsafe { &self.data_bucket.as_ref().1 }.borrow()
    }

    /// Gets a reference to the `Q1` and `Q2` keys in the entry.
    /// Return tuple of type `(&'a Q1, &'a Q2)`.
    ///
    /// # Examples
    ///
    /// ```
    /// use double_map::dhash_map::{DHashMap, EntryRef};
    ///
    /// #[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
    /// struct Wrapper<T>(T);
    ///
    /// impl<T: Copy> From<&Wrapper<T>> for Wrapper<T> {
    ///     fn from(id: &Wrapper<T>) -> Self {
    ///         Wrapper(id.0)
    ///     }
    /// }
    ///
    /// let mut map: DHashMap<String, Wrapper<usize>, i32> = DHashMap::new();
    ///
    /// map.insert("poneyland".to_owned(), Wrapper(0), 12);
    ///
    /// match map.entry_ref("poneyland", &Wrapper(0)) {
    ///     Ok(EntryRef::Occupied(entry)) => {
    ///         assert_eq!(entry.keys(), ("poneyland", &Wrapper(0)));
    ///     }
    ///     _ => panic!(),
    /// }
    /// ```
    #[cfg_attr(feature = "inline-more", inline)]
    pub fn keys(&self) -> (&Q1, &Q2)
    where
        K1: Borrow<Q1>,
        K2: Borrow<Q2>,
    {
        let &(ref k1, ref k2, _) = unsafe { self.data_bucket.as_ref() };
        (k1.borrow(), k2.borrow())
    }

    /// Take the ownership of the keys and value from the map.
    /// Keeps the allocated memory for reuse.
    ///
    /// # Examples
    ///
    /// ```
    /// use double_map::dhash_map::{DHashMap, EntryRef};
    ///
    /// #[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
    /// struct Wrapper<T>(T);
    ///
    /// impl<T: Copy> From<&Wrapper<T>> for Wrapper<T> {
    ///     fn from(id: &Wrapper<T>) -> Self {
    ///         Wrapper(id.0)
    ///     }
    /// }
    ///
    /// let mut map: DHashMap<String, Wrapper<usize>, i32> = DHashMap::new();
    ///
    /// map.insert("poneyland".to_owned(), Wrapper(0), 10);
    /// map.insert("bearland".to_owned(), Wrapper(1), 11);
    ///
    /// assert!(map.get_key1("poneyland") == Some(&10) && map.get_key2(&Wrapper(0)) == Some(&10));
    /// match map.entry_ref("poneyland", &Wrapper(0)) {
    ///     Ok(EntryRef::Occupied(entry)) => {
    ///         // We delete the entry from the map.
    ///         let tuple = entry.remove_entry();
    ///         assert_eq!(tuple, ("poneyland".to_owned(), Wrapper(0), 10));
    ///     }
    ///     _ => panic!("poneyland"),
    /// }
    /// assert!(map.get_key1("poneyland") == None && map.get_key2(&Wrapper(0)) == None);
    ///
    /// assert!(map.get_key1("bearland") == Some(&11) && map.get_key2(&Wrapper(1)) == Some(&11));
    /// match map.entry_ref("bearland", &Wrapper(1)) {
    ///     Ok(EntryRef::Occupied(entry)) => {
    ///         // We delete the entry from the map.
    ///         let tuple = entry.remove_entry();
    ///         assert_eq!(tuple, ("bearland".to_owned(), Wrapper(1), 11));
    ///     }
    ///     _ => panic!("bearland"),
    /// }
    /// assert!(map.get_key1("bearland") == None && map.get_key2(&Wrapper(1)) == None);
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
    /// use double_map::dhash_map::{DHashMap, EntryRef};
    ///
    /// #[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
    /// struct Wrapper<T>(T);
    ///
    /// impl<T: Copy> From<&Wrapper<T>> for Wrapper<T> {
    ///     fn from(id: &Wrapper<T>) -> Self {
    ///         Wrapper(id.0)
    ///     }
    /// }
    ///
    /// let mut map: DHashMap<String, Wrapper<usize>, i32> = DHashMap::new();
    /// map.insert("poneyland".to_owned(), Wrapper(0), 12);
    ///
    /// match map.entry_ref("poneyland", &Wrapper(0)) {
    ///     Ok(EntryRef::Occupied(entry)) => {
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
    /// If you need a reference to the `OccupiedEntryRef` which
    /// may outlive the destruction of the `EntryRef` value,
    /// see [`into_mut`](`OccupiedEntryRef::into_mut`).
    ///
    /// # Examples
    ///
    /// ```
    /// use double_map::dhash_map::{DHashMap, EntryRef};
    ///
    /// #[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
    /// struct Wrapper<T>(T);
    ///
    /// impl<T: Copy> From<&Wrapper<T>> for Wrapper<T> {
    ///     fn from(id: &Wrapper<T>) -> Self {
    ///         Wrapper(id.0)
    ///     }
    /// }
    ///
    /// let mut map: DHashMap<String, Wrapper<usize>, i32> = DHashMap::new();
    /// map.insert("poneyland".to_owned(), Wrapper(0), 12);
    /// assert_eq!(map.get_key1("poneyland"), Some(&12));
    /// assert_eq!(map.get_key2(&Wrapper(0)), Some(&12));
    ///
    /// match map.entry_ref("poneyland", &Wrapper(0)) {
    ///     Ok(EntryRef::Occupied(mut entry)) => {
    ///         *entry.get_mut() += 10;
    ///         assert_eq!(entry.get(), &22);
    ///         // We can use the same Entry multiple times.
    ///         *entry.get_mut() += 2;
    ///     }
    ///     _ => panic!(),
    /// }
    /// assert_eq!(map.get_key1("poneyland"), Some(&24));
    /// assert_eq!(map.get_key2(&Wrapper(0)), Some(&24));
    /// ```
    #[cfg_attr(feature = "inline-more", inline)]
    pub fn get_mut(&mut self) -> &mut V {
        unsafe { &mut self.data_bucket.as_mut().2 }
    }

    /// Converts the `OccupiedEntryRef` into a mutable reference to
    /// the value in the entry with a lifetime bound to the map itself.
    ///
    /// If you need multiple references to the `OccupiedEntryRef`, see
    /// [`get_mut`].
    ///
    /// [`get_mut`]: #method.get_mut
    ///
    /// # Examples
    ///
    /// ```
    /// use double_map::dhash_map::{DHashMap, EntryRef};
    ///
    /// #[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
    /// struct Wrapper<T>(T);
    ///
    /// impl<T: Copy> From<&Wrapper<T>> for Wrapper<T> {
    ///     fn from(id: &Wrapper<T>) -> Self {
    ///         Wrapper(id.0)
    ///     }
    /// }
    ///
    /// let mut map: DHashMap<String, Wrapper<usize>, i32> = DHashMap::new();
    /// map.insert("poneyland".to_owned(), Wrapper(0), 12);
    /// assert_eq!(map.get_key1("poneyland"), Some(&12));
    /// assert_eq!(map.get_key2(&Wrapper(0)), Some(&12));
    ///
    /// // Let's create a variable that outlives the OccupiedEntryRef
    /// // (with some initial value)
    /// let mut value: &mut i32 = &mut 0;
    ///
    /// match map.entry_ref("poneyland", &Wrapper(0)) {
    ///     Ok(EntryRef::Occupied(entry)) => {
    ///         // So we can convert the OccupiedEntryRef into a mutable
    ///         // reference to the value.
    ///         value = entry.into_mut();
    ///         *value += 10;
    ///     }
    ///     _ => panic!(),
    /// }
    /// // We can use the same reference outside the created entry
    /// // (OccupiedEntryRef) scope.
    /// *value += 20;
    /// assert_eq!(map.get_key1("poneyland"), Some(&42));
    /// assert_eq!(map.get_key2(&Wrapper(0)), Some(&42));
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
    /// use double_map::dhash_map::{DHashMap, EntryRef};
    ///
    /// #[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
    /// struct Wrapper<T>(T);
    ///
    /// impl<T: Copy> From<&Wrapper<T>> for Wrapper<T> {
    ///     fn from(id: &Wrapper<T>) -> Self {
    ///         Wrapper(id.0)
    ///     }
    /// }
    ///
    /// let mut map: DHashMap<String, Wrapper<usize>, i32> = DHashMap::new();
    /// map.insert("poneyland".to_owned(), Wrapper(0), 12);
    /// assert_eq!(map.get_key1("poneyland"), Some(&12));
    /// assert_eq!(map.get_key2(&Wrapper(0)), Some(&12));
    ///
    /// // Let's create a variable that holds value
    /// let mut owner: i32 = 100;
    ///
    /// match map.entry_ref("poneyland", &Wrapper(0)) {
    ///     Ok(EntryRef::Occupied(mut entry)) => {
    ///         // So we can swap our created owner value with
    ///         // value inside the map.
    ///         owner = entry.insert(owner);
    ///     }
    ///     _ => panic!(),
    /// }
    /// assert_eq!(owner, 12);
    /// assert_eq!(map.get_key1("poneyland"), Some(&100));
    /// assert_eq!(map.get_key2(&Wrapper(0)), Some(&100));
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
    /// use double_map::dhash_map::{DHashMap, EntryRef};
    ///
    /// #[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
    /// struct Wrapper<T>(T);
    ///
    /// impl<T: Copy> From<&Wrapper<T>> for Wrapper<T> {
    ///     fn from(id: &Wrapper<T>) -> Self {
    ///         Wrapper(id.0)
    ///     }
    /// }
    ///
    /// let mut map: DHashMap<String, Wrapper<usize>, i32> = DHashMap::new();
    /// map.insert("poneyland".to_owned(), Wrapper(0), 10);
    /// map.insert("bearland".to_owned(), Wrapper(1), 11);
    ///
    /// assert!(map.get_key1("poneyland") == Some(&10) && map.get_key2(&Wrapper(0)) == Some(&10));
    ///
    /// match map.entry_ref("poneyland", &Wrapper(0)) {
    ///     Ok(EntryRef::Occupied(entry)) => {
    ///         // We remove the entry from the map.
    ///         let value = entry.remove();
    ///         assert_eq!(value, 10);
    ///     }
    ///     _ => panic!(),
    /// }
    /// assert!(map.get_key1("poneyland") == None && map.get_key2(&Wrapper(0)) == None);
    ///
    /// assert!(map.get_key1("bearland") == Some(&11) && map.get_key2(&Wrapper(1)) == Some(&11));
    /// match map.entry_ref("bearland", &Wrapper(1)) {
    ///     Ok(EntryRef::Occupied(entry)) => {
    ///         // We remove the entry from the map.
    ///         let value = entry.remove();
    ///         assert_eq!(value, 11);
    ///     }
    ///     _ => panic!(),
    /// }
    /// assert!(map.get_key1("bearland") == None && map.get_key2(&Wrapper(1)) == None);
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
    /// Will panic if this `OccupiedEntryRef` was created through
    /// [`EntryRef::insert`].
    ///
    /// # Examples
    ///
    /// ```
    /// use double_map::dhash_map::{DHashMap, EntryRef};
    /// use std::rc::Rc;
    ///
    /// let mut map: DHashMap<Rc<str>, Rc<str>, i32> = DHashMap::new();
    /// let key1: Rc<str> = Rc::from("First key");
    /// let key2: Rc<str> = Rc::from("Second key");
    ///
    /// map.insert(key1.clone(), key2.clone(), 15);
    /// assert_eq!(Rc::strong_count(&key1), 2);
    /// assert_eq!(Rc::strong_count(&key2), 2);
    ///
    /// match map.entry_ref("First key", "Second key") {
    ///     Ok(EntryRef::Occupied(entry)) => {
    ///         let (old_key1, old_key2, old_value): (Rc<str>, Rc<str>, i32) =
    ///             entry.replace_entry(16);
    ///         assert!(Rc::ptr_eq(&key1, &old_key1));
    ///         assert!(Rc::ptr_eq(&key2, &old_key2));
    ///         assert_eq!(old_value, 15);
    ///     }
    ///     _ => panic!(),
    /// }
    ///
    /// assert_eq!(Rc::strong_count(&key1), 1);
    /// assert_eq!(Rc::strong_count(&key2), 1);
    /// assert_eq!(map["First key"], 16);
    /// ```
    #[cfg_attr(feature = "inline-more", inline)]
    pub fn replace_entry(self, value: V) -> (K1, K2, V)
    where
        K1: From<&'b Q1> + Clone,
        K2: From<&'b Q2> + Clone,
    {
        let &mut (ref mut k1, ref mut k2, ref mut v) = unsafe { self.data_bucket.as_mut() };

        let old_key1 = mem::replace(k1, self.key1.unwrap().into_owned());
        let old_key2 = mem::replace(k2, self.key2.unwrap().into_owned());
        let old_value = mem::replace(v, value);
        (old_key1, old_key2, old_value)
    }

    /// Replaces the `K1` key in the hash map with the key used
    /// to create this entry.
    ///
    /// # Panics
    ///
    /// Will panic if this `OccupiedEntryRef` was created through
    /// [`EntryRef::insert`].
    ///
    /// # Examples
    ///
    /// ```
    /// use double_map::dhash_map::{DHashMap, EntryRef};
    /// use std::rc::Rc;
    ///
    /// let mut map: DHashMap<Rc<str>, usize, usize> = DHashMap::with_capacity(6);
    /// let mut keys: Vec<Rc<str>> = Vec::with_capacity(6);
    ///
    /// for (index, key1) in ["a", "b", "c", "d", "e", "f"].into_iter().enumerate() {
    ///     let rc_key: Rc<str> = Rc::from(key1);
    ///     keys.push(rc_key.clone());
    ///     map.insert(rc_key.clone(), index, index);
    /// }
    ///
    /// assert!(keys.iter().all(|key| Rc::strong_count(key) == 2));
    ///
    /// // It doesn't matter that we kind of use a vector with the same keys,
    /// // because all keys will be newly created from the references
    /// reclaim_memory(&mut map, &keys);
    ///
    /// assert!(keys.iter().all(|key| Rc::strong_count(key) == 1));
    ///
    /// fn reclaim_memory(map: &mut DHashMap<Rc<str>, usize, usize>, keys: &[Rc<str>]) {
    ///     for (index, key) in keys.iter().enumerate() {
    ///         if let Ok(EntryRef::Occupied(entry)) = map.entry_ref(key.as_ref(), &index) {
    ///             // Replaces the entry's key with newly created one
    ///             entry.replace_key1();
    ///         }
    ///     }
    /// }
    /// ```
    #[cfg_attr(feature = "inline-more", inline)]
    pub fn replace_key1(self) -> K1
    where
        K1: From<&'b Q1> + Clone,
    {
        let entry = unsafe { self.data_bucket.as_mut() };
        mem::replace(&mut entry.0, self.key1.unwrap().into_owned())
    }

    /// Replaces the `K2` key in the hash map with the key used
    /// to create this entry.
    ///
    /// # Panics
    ///
    /// Will panic if this `OccupiedEntryRef` was created through
    /// [`EntryRef::insert`].
    ///
    /// # Examples
    ///
    /// ```
    /// use double_map::dhash_map::{DHashMap, EntryRef};
    /// use std::rc::Rc;
    ///
    /// let mut map: DHashMap<usize, Rc<str>, usize> = DHashMap::with_capacity(6);
    /// let mut keys: Vec<Rc<str>> = Vec::with_capacity(6);
    ///
    /// for (index, key1) in ["a", "b", "c", "d", "e", "f"].into_iter().enumerate() {
    ///     let rc_key: Rc<str> = Rc::from(key1);
    ///     keys.push(rc_key.clone());
    ///     map.insert(index, rc_key.clone(), index);
    /// }
    ///
    /// assert!(keys.iter().all(|key| Rc::strong_count(key) == 2));
    ///
    /// // It doesn't matter that we kind of use a vector with the same keys,
    /// // because all keys will be newly created from the references
    /// reclaim_memory(&mut map, &keys);
    ///
    /// assert!(keys.iter().all(|key| Rc::strong_count(key) == 1));
    ///
    /// fn reclaim_memory(map: &mut DHashMap<usize, Rc<str>, usize>, keys: &[Rc<str>]) {
    ///     for (index, key) in keys.iter().enumerate() {
    ///         if let Ok(EntryRef::Occupied(entry)) = map.entry_ref(&index, key.as_ref()) {
    ///             // Replaces the entry's key with newly created one
    ///             entry.replace_key2();
    ///         }
    ///     }
    /// }
    /// ```
    #[cfg_attr(feature = "inline-more", inline)]
    pub fn replace_key2(self) -> K2
    where
        K2: From<&'b Q2> + Clone,
    {
        let entry = unsafe { self.data_bucket.as_mut() };
        mem::replace(&mut entry.1, self.key2.unwrap().into_owned())
    }

    /// Replaces the `K1` and `K2` keys in the hash map with the keys
    /// used to create this entry.
    ///
    /// # Panics
    ///
    /// Will panic if this `OccupiedEntryRef` was created through
    /// [`EntryRef::insert`].
    ///
    /// # Examples
    ///
    /// ```
    /// use double_map::dhash_map::{DHashMap, EntryRef};
    /// use std::rc::Rc;
    ///
    /// let mut map: DHashMap<Rc<str>, Rc<str>, usize> = DHashMap::with_capacity(6);
    /// let mut keys: Vec<Rc<str>> = Vec::with_capacity(6);
    ///
    /// for (index, key1) in ["a", "b", "c", "d", "e", "f"].into_iter().enumerate() {
    ///     let rc_key: Rc<str> = Rc::from(key1);
    ///     keys.push(rc_key.clone());
    ///     map.insert(rc_key.clone(), rc_key.clone(), index);
    /// }
    ///
    /// assert!(keys.iter().all(|key| Rc::strong_count(key) == 3));
    ///
    /// // It doesn't matter that we kind of use a vector with the same keys,
    /// // because all keys will be newly created from the references
    /// reclaim_memory(&mut map, &keys);
    ///
    /// assert!(keys.iter().all(|key| Rc::strong_count(key) == 1));
    ///
    /// fn reclaim_memory(map: &mut DHashMap<Rc<str>, Rc<str>, usize>, keys: &[Rc<str>]) {
    ///     for key in keys {
    ///         if let Ok(EntryRef::Occupied(entry)) = map.entry_ref(key.as_ref(), key.as_ref()) {
    ///             // Replaces the entry's keys with newly created
    ///             entry.replace_keys();
    ///         }
    ///     }
    /// }
    /// ```
    #[cfg_attr(feature = "inline-more", inline)]
    pub fn replace_keys(self) -> (K1, K2)
    where
        K1: From<&'b Q1> + Clone,
        K2: From<&'b Q2> + Clone,
    {
        let &mut (ref mut k1, ref mut k2, _) = unsafe { self.data_bucket.as_mut() };

        let old_key1 = mem::replace(k1, self.key1.unwrap().into_owned());
        let old_key2 = mem::replace(k2, self.key2.unwrap().into_owned());
        (old_key1, old_key2)
    }

    /// Provides shared access to the `Q1` key and owned access to the value of
    /// the entry and allows to replace or remove it based on the
    /// value of the returned option.
    ///
    /// # Examples
    ///
    /// ```
    /// use double_map::dhash_map::{DHashMap, EntryRef};
    ///
    /// #[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
    /// struct Wrapper<T>(T);
    ///
    /// impl<T: Copy> From<&Wrapper<T>> for Wrapper<T> {
    ///     fn from(id: &Wrapper<T>) -> Self {
    ///         Wrapper(id.0)
    ///     }
    /// }
    ///
    /// let mut map: DHashMap<Wrapper<usize>, String, i32> = DHashMap::new();
    ///
    /// map.insert(Wrapper(1), "poneyland".to_owned(), 42);
    ///
    /// let entry = match map.entry_ref(&Wrapper(1), "poneyland") {
    ///     Ok(EntryRef::Occupied(e)) => e.replace_entry_with_key1(|k1, v| {
    ///         assert_eq!(k1, &Wrapper(1));
    ///         assert_eq!(v, 42);
    ///         Some(v + 1)
    ///     }),
    ///     _ => panic!(),
    /// };
    ///
    /// match entry {
    ///     EntryRef::Occupied(e) => {
    ///         assert_eq!(e.key1(), &Wrapper(1));
    ///         assert_eq!(e.key2(), "poneyland");
    ///         assert_eq!(e.get(), &43);
    ///     }
    ///     EntryRef::Vacant(_) => panic!(),
    /// }
    ///
    /// assert_eq!(map[&Wrapper(1)], 43);
    ///
    /// let entry = match map.entry_ref(&Wrapper(1), "poneyland") {
    ///     Ok(EntryRef::Occupied(e)) => e.replace_entry_with_key1(|_k1, _v| None),
    ///     _ => panic!(),
    /// };
    ///
    /// match entry {
    ///     EntryRef::Vacant(e) => {
    ///         assert_eq!(e.key1(), &Wrapper(1));
    ///         assert_eq!(e.key2(), "poneyland");
    ///     }
    ///     EntryRef::Occupied(_) => panic!(),
    /// }
    ///
    /// assert!(!map.contains_key1(&Wrapper(1)));
    /// ```
    #[cfg_attr(feature = "inline-more", inline)]
    pub fn replace_entry_with_key1<F>(self, f: F) -> EntryRef<'a, 'b, K1, Q1, K2, Q2, V, S, A>
    where
        F: FnOnce(&Q1, V) -> Option<V>,
        K1: Borrow<Q1>,
    {
        unsafe {
            let mut spare_key = None;

            self.table.table.replace_data_with(
                self.pointer_bucket.clone(),
                |(key1, key2, value)| {
                    if let Some(new_value) = f(key1.borrow(), value) {
                        Some((key1, key2, new_value))
                    } else {
                        spare_key = Some((KeyOrRef::Owned(key1), KeyOrRef::Owned(key2)));
                        None
                    }
                },
            );

            if let Some((key1, key2)) = spare_key {
                EntryRef::Vacant(VacantEntryRef {
                    hash1: self.hash1,
                    key1,
                    hash2: self.hash2,
                    key2,
                    table: self.table,
                })
            } else {
                EntryRef::Occupied(self)
            }
        }
    }

    /// Provides shared access to the `Q2` key and owned access to the value of
    /// the entry and allows to replace or remove it based on the
    /// value of the returned option.
    ///
    /// # Examples
    ///
    /// ```
    /// use double_map::dhash_map::{DHashMap, EntryRef};
    ///
    /// #[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
    /// struct Wrapper<T>(T);
    ///
    /// impl<T: Copy> From<&Wrapper<T>> for Wrapper<T> {
    ///     fn from(id: &Wrapper<T>) -> Self {
    ///         Wrapper(id.0)
    ///     }
    /// }
    ///
    /// let mut map: DHashMap<Wrapper<usize>, String, i32> = DHashMap::new();
    ///
    /// map.insert(Wrapper(1), "poneyland".to_owned(), 42);
    ///
    /// let entry = match map.entry_ref(&Wrapper(1), "poneyland") {
    ///     Ok(EntryRef::Occupied(e)) => e.replace_entry_with_key2(|k2, v| {
    ///         assert_eq!(k2, "poneyland");
    ///         assert_eq!(v, 42);
    ///         Some(v + 1)
    ///     }),
    ///     _ => panic!(),
    /// };
    ///
    /// match entry {
    ///     EntryRef::Occupied(e) => {
    ///         assert_eq!(e.key1(), &Wrapper(1));
    ///         assert_eq!(e.key2(), "poneyland");
    ///         assert_eq!(e.get(), &43);
    ///     }
    ///     EntryRef::Vacant(_) => panic!(),
    /// }
    ///
    /// assert_eq!(map[&Wrapper(1)], 43);
    ///
    /// let entry = match map.entry_ref(&Wrapper(1), "poneyland") {
    ///     Ok(EntryRef::Occupied(e)) => e.replace_entry_with_key2(|_k2, _v| None),
    ///     _ => panic!(),
    /// };
    ///
    /// match entry {
    ///     EntryRef::Vacant(e) => {
    ///         assert_eq!(e.key1(), &Wrapper(1));
    ///         assert_eq!(e.key2(), "poneyland");
    ///     }
    ///     EntryRef::Occupied(_) => panic!(),
    /// }
    ///
    /// assert!(!map.contains_key2("poneyland"));
    /// ```
    #[cfg_attr(feature = "inline-more", inline)]
    pub fn replace_entry_with_key2<F>(self, f: F) -> EntryRef<'a, 'b, K1, Q1, K2, Q2, V, S, A>
    where
        F: FnOnce(&Q2, V) -> Option<V>,
        K2: Borrow<Q2>,
    {
        unsafe {
            let mut spare_key = None;

            self.table.table.replace_data_with(
                self.pointer_bucket.clone(),
                |(key1, key2, value)| {
                    if let Some(new_value) = f(key2.borrow(), value) {
                        Some((key1, key2, new_value))
                    } else {
                        spare_key = Some((KeyOrRef::Owned(key1), KeyOrRef::Owned(key2)));
                        None
                    }
                },
            );

            if let Some((key1, key2)) = spare_key {
                EntryRef::Vacant(VacantEntryRef {
                    hash1: self.hash1,
                    key1,
                    hash2: self.hash2,
                    key2,
                    table: self.table,
                })
            } else {
                EntryRef::Occupied(self)
            }
        }
    }

    /// Provides shared access to the `Q1` and `Q2` keys and owned
    /// access to the value of the entry and allows to replace or
    /// remove it based on the value of the returned option.
    ///
    /// # Examples
    ///
    /// ```
    /// use double_map::dhash_map::{DHashMap, EntryRef};
    ///
    /// #[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
    /// struct Wrapper<T>(T);
    ///
    /// impl<T: Copy> From<&Wrapper<T>> for Wrapper<T> {
    ///     fn from(id: &Wrapper<T>) -> Self {
    ///         Wrapper(id.0)
    ///     }
    /// }
    ///
    /// let mut map: DHashMap<Wrapper<usize>, String, i32> = DHashMap::new();
    ///
    /// map.insert(Wrapper(1), "poneyland".to_owned(), 42);
    ///
    /// let entry = match map.entry_ref(&Wrapper(1), "poneyland") {
    ///     Ok(EntryRef::Occupied(e)) => e.replace_entry_with_keys(|k1, k2, v| {
    ///         assert_eq!(k1, &Wrapper(1));
    ///         assert_eq!(k2, "poneyland");
    ///         assert_eq!(v, 42);
    ///         Some(v + 1)
    ///     }),
    ///     _ => panic!(),
    /// };
    ///
    /// match entry {
    ///     EntryRef::Occupied(e) => {
    ///         assert_eq!(e.key1(), &Wrapper(1));
    ///         assert_eq!(e.key2(), "poneyland");
    ///         assert_eq!(e.get(), &43);
    ///     }
    ///     EntryRef::Vacant(_) => panic!(),
    /// }
    ///
    /// assert_eq!(map[&Wrapper(1)], 43);
    ///
    /// let entry = match map.entry_ref(&Wrapper(1), "poneyland") {
    ///     Ok(EntryRef::Occupied(e)) => e.replace_entry_with_keys(|_k1, _k2, _v| None),
    ///     _ => panic!(),
    /// };
    ///
    /// match entry {
    ///     EntryRef::Vacant(e) => {
    ///         assert_eq!(e.key1(), &Wrapper(1));
    ///         assert_eq!(e.key2(), "poneyland");
    ///     }
    ///     EntryRef::Occupied(_) => panic!(),
    /// }
    ///
    /// assert!(!map.contains_keys(&Wrapper(1), "poneyland"));
    /// ```
    #[cfg_attr(feature = "inline-more", inline)]
    pub fn replace_entry_with_keys<F>(self, f: F) -> EntryRef<'a, 'b, K1, Q1, K2, Q2, V, S, A>
    where
        F: FnOnce(&Q1, &Q2, V) -> Option<V>,
        K1: Borrow<Q1>,
        K2: Borrow<Q2>,
    {
        unsafe {
            let mut spare_key = None;

            self.table.table.replace_data_with(
                self.pointer_bucket.clone(),
                |(key1, key2, value)| {
                    if let Some(new_value) = f(key1.borrow(), key2.borrow(), value) {
                        Some((key1, key2, new_value))
                    } else {
                        spare_key = Some((KeyOrRef::Owned(key1), KeyOrRef::Owned(key2)));
                        None
                    }
                },
            );

            if let Some((key1, key2)) = spare_key {
                EntryRef::Vacant(VacantEntryRef {
                    hash1: self.hash1,
                    key1,
                    hash2: self.hash2,
                    key2,
                    table: self.table,
                })
            } else {
                EntryRef::Occupied(self)
            }
        }
    }
}

/// A view into a vacant entry in a `DHashMap`.
/// It is part of the [`EntryRef`] enum.
///
/// [`EntryRef`]: enum.EntryRef.html
///
/// # Examples
///
/// ```
/// use double_map::dhash_map::{DHashMap, EntryRef, VacantEntryRef};
///
/// #[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
/// struct Wrapper<T>(T);
///
/// impl<T: Copy> From<&Wrapper<T>> for Wrapper<T> {
///     fn from(id: &Wrapper<T>) -> Self {
///         Wrapper(id.0)
///     }
/// }
///
/// let mut map: DHashMap<Wrapper<usize>, String, i32> = DHashMap::new();
///
/// let entry_v: VacantEntryRef<_, _, _, _, _, _> = match map.entry_ref(&Wrapper(1), "a").unwrap() {
///     EntryRef::Vacant(view) => view,
///     EntryRef::Occupied(_) => unreachable!(),
/// };
/// entry_v.insert(10);
/// assert!(map[&Wrapper(1)] == 10 && map.len() == 1);
///
/// // Nonexistent key (insert and update)
/// match map.entry_ref(&Wrapper(2), "b") {
///     Ok(EntryRef::Vacant(view)) => {
///         let value = view.insert(2);
///         assert_eq!(*value, 2);
///         *value = 20;
///     }
///     _ => panic!("It should be nonexistent key"),
/// }
/// assert!(map[&Wrapper(2)] == 20 && map.len() == 2);
/// ```
pub struct VacantEntryRef<'a, 'b, K1, Q1: ?Sized, K2, Q2: ?Sized, V, S, A = Global>
where
    A: Allocator + Clone,
{
    pub(super) hash1: u64,
    pub(super) key1: KeyOrRef<'b, K1, Q1>,
    pub(super) hash2: u64,
    pub(super) key2: KeyOrRef<'b, K2, Q2>,
    pub(super) table: &'a mut DHashMap<K1, K2, V, S, A>,
}

impl<K1, Q1, K2, Q2, V, S, A> Debug for VacantEntryRef<'_, '_, K1, Q1, K2, Q2, V, S, A>
where
    K1: Borrow<Q1>,
    Q1: ?Sized + Debug,
    K2: Borrow<Q2>,
    Q2: ?Sized + Debug,
    A: Allocator + Clone,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("VacantEntryRef")
            .field("key1", &self.key1())
            .field("key2", &self.key2())
            .finish()
    }
}

impl<'a, 'b, K1, Q1: ?Sized, K2, Q2: ?Sized, V, S, A>
    VacantEntryRef<'a, 'b, K1, Q1, K2, Q2, V, S, A>
where
    A: Allocator + Clone,
{
    /// Gets a reference to the `Q1` key that would be used
    /// when inserting a value through the `VacantEntryRef`.
    ///
    /// # Examples
    ///
    /// ```
    /// use double_map::dhash_map::{DHashMap, EntryRef};
    ///
    /// #[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
    /// struct Wrapper<T>(T);
    ///
    /// impl<T: Copy> From<&Wrapper<T>> for Wrapper<T> {
    ///     fn from(id: &Wrapper<T>) -> Self {
    ///         Wrapper(id.0)
    ///     }
    /// }
    ///
    /// let mut map: DHashMap<String, Wrapper<usize>, i32> = DHashMap::new();
    ///
    /// match map.entry_ref("poneyland", &Wrapper(0)) {
    ///     Ok(EntryRef::Vacant(vac_entry)) => assert_eq!(vac_entry.key1(), "poneyland"),
    ///     _ => panic!(),
    /// }
    /// ```
    #[cfg_attr(feature = "inline-more", inline)]
    pub fn key1(&self) -> &Q1
    where
        K1: Borrow<Q1>,
    {
        self.key1.as_ref()
    }

    /// Gets a reference to the `Q2` key that would be used
    /// when inserting a value through the `VacantEntryRef`.
    ///
    /// # Examples
    ///
    /// ```
    /// use double_map::dhash_map::{DHashMap, EntryRef};
    ///
    /// #[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
    /// struct Wrapper<T>(T);
    ///
    /// impl<T: Copy> From<&Wrapper<T>> for Wrapper<T> {
    ///     fn from(id: &Wrapper<T>) -> Self {
    ///         Wrapper(id.0)
    ///     }
    /// }
    ///
    /// let mut map: DHashMap<String, Wrapper<usize>, i32> = DHashMap::new();
    ///
    /// match map.entry_ref("poneyland", &Wrapper(0)) {
    ///     Ok(EntryRef::Vacant(vac_entry)) => assert_eq!(vac_entry.key2(), &Wrapper(0)),
    ///     _ => panic!(),
    /// }
    /// ```
    #[cfg_attr(feature = "inline-more", inline)]
    pub fn key2(&self) -> &Q2
    where
        K2: Borrow<Q2>,
    {
        self.key2.as_ref()
    }

    /// Gets a reference to the `Q1` and `Q2` keys that would be
    /// used when inserting a value through the `VacantEntryRef`.
    ///
    /// # Examples
    ///
    /// ```
    /// use double_map::dhash_map::{DHashMap, EntryRef};
    ///
    /// #[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
    /// struct Wrapper<T>(T);
    ///
    /// impl<T: Copy> From<&Wrapper<T>> for Wrapper<T> {
    ///     fn from(id: &Wrapper<T>) -> Self {
    ///         Wrapper(id.0)
    ///     }
    /// }
    ///
    /// let mut map: DHashMap<String, Wrapper<usize>, i32> = DHashMap::new();
    ///
    /// match map.entry_ref("poneyland", &Wrapper(0)) {
    ///     Ok(EntryRef::Vacant(vac_entry)) => assert_eq!(vac_entry.keys(), ("poneyland", &Wrapper(0))),
    ///     _ => panic!(),
    /// }
    /// ```
    #[cfg_attr(feature = "inline-more", inline)]
    pub fn keys(&self) -> (&Q1, &Q2)
    where
        K1: Borrow<Q1>,
        K2: Borrow<Q2>,
    {
        (self.key1.as_ref(), self.key2.as_ref())
    }

    /// Take ownership of the `K1` key.
    ///
    /// # Examples
    ///
    /// ```
    /// use double_map::dhash_map::{DHashMap, EntryRef};
    ///
    /// #[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
    /// struct Wrapper<T>(T);
    ///
    /// impl<T: Copy> From<&Wrapper<T>> for Wrapper<T> {
    ///     fn from(id: &Wrapper<T>) -> Self {
    ///         Wrapper(id.0)
    ///     }
    /// }
    ///
    /// let mut map: DHashMap<String, Wrapper<usize>, i32> = DHashMap::new();
    ///
    /// match map.entry_ref("poneyland", &Wrapper(0)) {
    ///     Ok(EntryRef::Vacant(v)) => assert_eq!(v.into_key1(), "poneyland".to_owned()),
    ///     _ => panic!(),
    /// }
    /// ```
    #[cfg_attr(feature = "inline-more", inline)]
    pub fn into_key1(self) -> K1
    where
        K1: From<&'b Q1>,
    {
        self.key1.into_owned()
    }

    /// Take ownership of the `K2` key.
    ///
    /// # Examples
    ///
    /// ```
    /// use double_map::dhash_map::{DHashMap, EntryRef};
    ///
    /// #[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
    /// struct Wrapper<T>(T);
    ///
    /// impl<T: Copy> From<&Wrapper<T>> for Wrapper<T> {
    ///     fn from(id: &Wrapper<T>) -> Self {
    ///         Wrapper(id.0)
    ///     }
    /// }
    ///
    /// let mut map: DHashMap<String, Wrapper<usize>, i32> = DHashMap::new();
    ///
    /// match map.entry_ref("poneyland", &Wrapper(0)) {
    ///     Ok(EntryRef::Vacant(v)) => assert_eq!(v.into_key2(), Wrapper(0)),
    ///     _ => panic!(),
    /// }
    /// ```
    #[cfg_attr(feature = "inline-more", inline)]
    pub fn into_key2(self) -> K2
    where
        K2: From<&'b Q2>,
    {
        self.key2.into_owned()
    }

    /// Take the ownership of the `K1` and `K2` keys.
    ///
    /// # Examples
    ///
    /// ```
    /// use double_map::dhash_map::{DHashMap, EntryRef};
    ///
    /// #[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
    /// struct Wrapper<T>(T);
    ///
    /// impl<T: Copy> From<&Wrapper<T>> for Wrapper<T> {
    ///     fn from(id: &Wrapper<T>) -> Self {
    ///         Wrapper(id.0)
    ///     }
    /// }
    ///
    /// let mut map: DHashMap<String, Wrapper<usize>, i32> = DHashMap::new();
    ///
    /// match map.entry_ref("poneyland", &Wrapper(0)) {
    ///     Ok(EntryRef::Vacant(v)) => assert_eq!(v.into_keys(), ("poneyland".to_owned(), Wrapper(0))),
    ///     _ => panic!(),
    /// }
    /// ```
    #[cfg_attr(feature = "inline-more", inline)]
    pub fn into_keys(self) -> (K1, K2)
    where
        K1: From<&'b Q1>,
        K2: From<&'b Q2>,
    {
        (self.key1.into_owned(), self.key2.into_owned())
    }

    /// Sets the value of the entry with the `VacantEntryRef`'s keys,
    /// and returns a mutable reference to it.
    ///
    /// # Examples
    ///
    /// ```
    /// use double_map::dhash_map::{DHashMap, EntryRef};
    ///
    /// #[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
    /// struct Wrapper<T>(T);
    ///
    /// impl<T: Copy> From<&Wrapper<T>> for Wrapper<T> {
    ///     fn from(id: &Wrapper<T>) -> Self {
    ///         Wrapper(id.0)
    ///     }
    /// }
    ///
    /// let mut map: DHashMap<String, Wrapper<usize>, i32> = DHashMap::new();
    ///
    /// match map.entry_ref("poneyland", &Wrapper(0)) {
    ///     Ok(EntryRef::Vacant(vac_entry)) => {
    ///         vac_entry.insert(37);
    ///     }
    ///     _ => panic!(),
    /// }
    /// assert_eq!(map.get_key1("poneyland"), Some(&37));
    /// ```
    #[cfg_attr(feature = "inline-more", inline)]
    pub fn insert(self, value: V) -> &'a mut V
    where
        K1: Hash + From<&'b Q1>,
        K2: Hash + From<&'b Q2>,
        S: BuildHasher,
    {
        let hash_builder = &self.table.hash_builder;
        let table = &mut self.table.table;

        let entry = table.insert_entry(
            self.hash1,
            self.hash2,
            (self.key1.into_owned(), self.key2.into_owned(), value),
            make_hasher_key1::<_, K2, V, S>(hash_builder),
            make_hasher_key2::<K1, _, V, S>(hash_builder),
        );
        &mut entry.2
    }

    #[cfg_attr(feature = "inline-more", inline)]
    fn insert_entry(self, value: V) -> OccupiedEntryRef<'a, 'b, K1, Q1, K2, Q2, V, S, A>
    where
        K1: Hash + From<&'b Q1>,
        K2: Hash + From<&'b Q2>,
        S: BuildHasher,
    {
        let hash_builder = &self.table.hash_builder;
        let (data_bucket, pointer_bucket) = self.table.table.insert(
            self.hash1,
            self.hash2,
            (self.key1.into_owned(), self.key2.into_owned(), value),
            make_hasher_key1::<_, K2, V, S>(hash_builder),
            make_hasher_key2::<K1, _, V, S>(hash_builder),
        );
        OccupiedEntryRef {
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
