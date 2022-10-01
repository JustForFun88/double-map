use super::*;

/// A builder for computing where in a [`DoubleMap`] a tuple of
/// keys and value `(K1, K2, V)` would be stored.
///
/// See the [`DoubleMap::raw_entry_mut`] docs for usage examples.
///
/// [`DoubleMap::raw_entry_mut`]: struct.DoubleMap.html#method.raw_entry_mut
///
/// # Examples
///
/// ```
/// use core::hash::{BuildHasher, Hash};
/// use double_map::shash_map::{RawEntryBuilderMut, RawEntryMut::Occupied, RawEntryMut::Vacant};
/// use double_map::DoubleMap;
///
/// let mut map = DoubleMap::new();
/// map.extend([
///     (1, 11, 51),
///     (2, 12, 52),
///     (3, 13, 53),
///     (4, 14, 54),
///     (5, 15, 55),
///     (6, 16, 56),
/// ]);
/// assert_eq!(map.len(), 6);
///
/// fn compute_hash<K: Hash + ?Sized, S: BuildHasher>(hash_builder: &S, key: &K) -> u64 {
///     use core::hash::Hasher;
///     let mut state = hash_builder.build_hasher();
///     key.hash(&mut state);
///     state.finish()
/// }
///
/// let builder: RawEntryBuilderMut<_, _, _, _> = map.raw_entry_mut();
///
/// // Existing key
/// match builder.from_keys(&6, &16) {
///     Ok(Occupied(view)) => assert_eq!(view.get(), &56),
///     _ => panic!(),
/// }
///
/// for (k1, k2) in (0..12).map(|i| (i, i + 10)) {
///     let hash1 = compute_hash(map.hasher(), &k1);
///     let hash2 = compute_hash(map.hasher(), &k2);
///     let value = map.get_key1(&k1).cloned();
///     let keys_value = value.as_ref().map(|v| (&k1, &k2, v));
///
///     println!("Key1: {}, key2: {} and value: {:?}", k1, k2, value);
///
///     match map.raw_entry_mut().from_keys(&k1, &k2) {
///         Ok(Occupied(mut o)) => assert_eq!(Some(o.get_keys_value()), keys_value),
///         Ok(Vacant(_)) => assert_eq!(value, None),
///         _ => panic!(),
///     }
///     match map
///         .raw_entry_mut()
///         .from_keys_hashed_nocheck(hash1, &k1, hash2, &k2)
///     {
///         Ok(Occupied(mut o)) => assert_eq!(Some(o.get_keys_value()), keys_value),
///         Ok(Vacant(_)) => assert_eq!(value, None),
///         _ => panic!(),
///     }
///     match map
///         .raw_entry_mut()
///         .from_hashes(hash1, |q| *q == k1, hash2, |q| *q == k2)
///     {
///         Ok(Occupied(mut o)) => assert_eq!(Some(o.get_keys_value()), keys_value),
///         Ok(Vacant(_)) => assert_eq!(value, None),
///         _ => panic!(),
///     }
/// }
///
/// assert_eq!(map.len(), 6);
/// ```
pub struct RawEntryBuilderMut<'a, K1, K2, V, S, A: Allocator + Clone = Global> {
    pub(super) map: &'a mut DoubleMap<K1, K2, V, S, A>,
}

impl<K1, K2, V, S, A: Allocator + Clone> Debug for RawEntryBuilderMut<'_, K1, K2, V, S, A> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("RawEntryBuilder").finish()
    }
}

impl<'a, K1, K2, V, S, A: Allocator + Clone> RawEntryBuilderMut<'a, K1, K2, V, S, A> {
    /// Creates a `RawEntryMut` from the given keys.
    ///
    /// Returns [`RawEntryMut`] enum if `all` of the following is `true`:
    /// - Both `K1` and `K2` keys are vacant.
    /// - If both `K1` and `K2` keys exist, they refer to the same value.
    ///
    /// When the above statements are `false`, `from_keys` method returns [`ErrorKind`]
    /// enum.
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
    /// use double_map::shash_map::{DoubleMap, ErrorKind, RawEntryMut};
    ///
    /// let mut map: DoubleMap<&str, u32, u32> = DoubleMap::new();
    /// let key1 = "a";
    /// let key2 = 1;
    /// let entry: RawEntryMut<&str, u32, u32, _> =
    ///     map.raw_entry_mut().from_keys(&key1, &key2).unwrap();
    /// entry.insert(key1, key2, 100);
    /// assert_eq!(map[&"a"], 100);
    ///
    /// map.insert("b", 2, 200);
    ///
    /// // Return `ErrorKind::OccupiedK1AndVacantK2` if `K1` key already
    /// // exists with some value, but `K2` key is vacant.
    /// let error_kind = map.raw_entry_mut().from_keys(&"a", &3).unwrap_err();
    /// assert_eq!(error_kind, ErrorKind::OccupiedK1AndVacantK2);
    ///
    /// // Return `ErrorKind::VacantK1AndOccupiedK2` if `K1` key is vacant,
    /// // but `K2` key already exists with some value.
    /// let error_kind = map.raw_entry_mut().from_keys(&"c", &1).unwrap_err();
    /// assert_eq!(error_kind, ErrorKind::VacantK1AndOccupiedK2);
    ///
    /// // Return `ErrorKind::KeysPointsToDiffEntries` if both
    /// // `K1` key and `K2` key already exist with some values,
    /// // but point to different entries (values).
    /// let error_kind = map.raw_entry_mut().from_keys(&"a", &2).unwrap_err();
    /// assert_eq!(error_kind, ErrorKind::KeysPointsToDiffEntries);
    ///
    /// let error_kind = map.raw_entry_mut().from_keys(&"b", &1).unwrap_err();
    /// assert_eq!(error_kind, ErrorKind::KeysPointsToDiffEntries);
    /// ```
    #[cfg_attr(feature = "inline-more", inline)]
    #[allow(clippy::wrong_self_convention)]
    pub fn from_keys<Q1, Q2>(
        self,
        k1: &Q1,
        k2: &Q2,
    ) -> Result<RawEntryMut<'a, K1, K2, V, S, A>, ErrorKind>
    where
        S: BuildHasher,
        Q1: ?Sized + Hash + Equivalent<K1>,
        Q2: ?Sized + Hash + Equivalent<K2>,
    {
        let hash1 = make_hash::<Q1, S>(&self.map.hash_builder, k1);
        let hash2 = make_hash::<Q2, S>(&self.map.hash_builder, k2);

        self.from_keys_hashed_nocheck(hash1, k1, hash2, k2)
    }

    /// Creates a `RawEntryMut` from the given keys and their hashes.
    ///
    /// Returns [`RawEntryMut`] enum if `all` of the following is `true`:
    /// - Both `K1` and `K2` keys are vacant.
    /// - If both `K1` and `K2` keys exist, they refer to the same value.
    ///
    /// When the above statements are `false`, `from_keys_hashed_nocheck`
    /// method returns [`ErrorKind`] enum.
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
    /// use core::hash::{BuildHasher, Hash};
    /// use double_map::shash_map::{DoubleMap, ErrorKind, RawEntryMut};
    ///
    /// fn compute_hash<K: Hash + ?Sized, S: BuildHasher>(hash_builder: &S, key: &K) -> u64 {
    ///     use core::hash::Hasher;
    ///     let mut state = hash_builder.build_hasher();
    ///     key.hash(&mut state);
    ///     state.finish()
    /// }
    ///
    /// let mut map: DoubleMap<&str, u32, u32> = DoubleMap::new();
    /// let key1 = "a";
    /// let hash1 = compute_hash(map.hasher(), &key1);
    /// let key2 = 1;
    /// let hash2 = compute_hash(map.hasher(), &key2);
    ///
    /// let entry: RawEntryMut<&str, u32, u32, _> = map
    ///     .raw_entry_mut()
    ///     .from_keys_hashed_nocheck(hash1, &key1, hash2, &key2)
    ///     .unwrap();
    /// entry.insert(key1, key2, 100);
    /// assert_eq!(map[&"a"], 100);
    ///
    /// map.insert("b", 2, 200);
    ///
    /// // Return `ErrorKind::OccupiedK1AndVacantK2` if `K1` key already
    /// // exists with some value, but `K2` key is vacant.
    /// let key1 = "a";
    /// let hash1 = compute_hash(map.hasher(), &key1);
    /// let key2 = 3;
    /// let hash2 = compute_hash(map.hasher(), &key2);
    /// let error_kind = map
    ///     .raw_entry_mut()
    ///     .from_keys_hashed_nocheck(hash1, &key1, hash2, &key2)
    ///     .unwrap_err();
    /// assert_eq!(error_kind, ErrorKind::OccupiedK1AndVacantK2);
    ///
    /// // Return `ErrorKind::VacantK1AndOccupiedK2` if `K1` key is vacant,
    /// // but `K2` key already exists with some value.
    /// let key1 = "c";
    /// let hash1 = compute_hash(map.hasher(), &key1);
    /// let key2 = 1;
    /// let hash2 = compute_hash(map.hasher(), &key2);
    /// let error_kind = map
    ///     .raw_entry_mut()
    ///     .from_keys_hashed_nocheck(hash1, &key1, hash2, &key2)
    ///     .unwrap_err();
    /// assert_eq!(error_kind, ErrorKind::VacantK1AndOccupiedK2);
    ///
    /// // Return `ErrorKind::KeysPointsToDiffEntries` if both
    /// // `K1` key and `K2` key already exist with some values,
    /// // but point to different entries (values).
    /// let key1 = "a";
    /// let hash1 = compute_hash(map.hasher(), &key1);
    /// let key2 = 2;
    /// let hash2 = compute_hash(map.hasher(), &key2);
    /// let error_kind = map
    ///     .raw_entry_mut()
    ///     .from_keys_hashed_nocheck(hash1, &key1, hash2, &key2)
    ///     .unwrap_err();
    /// assert_eq!(error_kind, ErrorKind::KeysPointsToDiffEntries);
    ///
    /// let key1 = "b";
    /// let hash1 = compute_hash(map.hasher(), &key1);
    /// let key2 = 1;
    /// let hash2 = compute_hash(map.hasher(), &key2);
    /// let error_kind = map
    ///     .raw_entry_mut()
    ///     .from_keys_hashed_nocheck(hash1, &key1, hash2, &key2)
    ///     .unwrap_err();
    /// assert_eq!(error_kind, ErrorKind::KeysPointsToDiffEntries);
    /// ```
    #[inline]
    #[allow(clippy::wrong_self_convention)]
    pub fn from_keys_hashed_nocheck<Q1, Q2>(
        self,
        hash1: u64,
        k1: &Q1,
        hash2: u64,
        k2: &Q2,
    ) -> Result<RawEntryMut<'a, K1, K2, V, S, A>, ErrorKind>
    where
        Q1: ?Sized + Equivalent<K1>,
        Q2: ?Sized + Equivalent<K2>,
    {
        self.from_hashes(hash1, equivalent(k1), hash2, equivalent(k2))
    }

    /// Creates a `RawEntryMut` from the given hashes and matching functions.
    ///
    /// Returns [`RawEntryMut`] enum if `all` of the following is `true`:
    /// - Both `K1` and `K2` keys are vacant (that is, no elements were
    /// found for the given hashes and matching functions).
    /// - If both `K1` and `K2` keys exist, they refer to the same value
    /// (that is, if elements were found for both given hashes and matching
    /// functions, so it is the same element)
    ///
    /// When the above statements are `false`, `from_hashes` method returns
    /// [`ErrorKind`] enum.
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
    /// use core::hash::{BuildHasher, Hash};
    /// use double_map::shash_map::{DoubleMap, ErrorKind, RawEntryMut};
    ///
    /// fn compute_hash<K: Hash + ?Sized, S: BuildHasher>(hash_builder: &S, key: &K) -> u64 {
    ///     use core::hash::Hasher;
    ///     let mut state = hash_builder.build_hasher();
    ///     key.hash(&mut state);
    ///     state.finish()
    /// }
    ///
    /// let mut map: DoubleMap<&str, u32, u32> = DoubleMap::new();
    /// let key1 = "a";
    /// let hash1 = compute_hash(map.hasher(), &key1);
    /// let key2 = 1;
    /// let hash2 = compute_hash(map.hasher(), &key2);
    ///
    /// let entry: RawEntryMut<&str, u32, u32, _> = map
    ///     .raw_entry_mut()
    ///     .from_hashes(hash1, |q| *q == key1, hash2, |q| *q == key2)
    ///     .unwrap();
    /// entry.insert(key1, key2, 100);
    /// assert_eq!(map[&"a"], 100);
    ///
    /// map.insert("b", 2, 200);
    ///
    /// // Return `ErrorKind::OccupiedK1AndVacantK2` if `K1` key already
    /// // exists with some value, but `K2` key is vacant.
    /// let key1 = "a";
    /// let hash1 = compute_hash(map.hasher(), &key1);
    /// let key2 = 3;
    /// let hash2 = compute_hash(map.hasher(), &key2);
    /// let error_kind = map
    ///     .raw_entry_mut()
    ///     .from_hashes(hash1, |q| *q == key1, hash2, |q| *q == key2)
    ///     .unwrap_err();
    /// assert_eq!(error_kind, ErrorKind::OccupiedK1AndVacantK2);
    ///
    /// // Return `ErrorKind::VacantK1AndOccupiedK2` if `K1` key is vacant,
    /// // but `K2` key already exists with some value.
    /// let key1 = "c";
    /// let hash1 = compute_hash(map.hasher(), &key1);
    /// let key2 = 1;
    /// let hash2 = compute_hash(map.hasher(), &key2);
    /// let error_kind = map
    ///     .raw_entry_mut()
    ///     .from_hashes(hash1, |q| *q == key1, hash2, |q| *q == key2)
    ///     .unwrap_err();
    /// assert_eq!(error_kind, ErrorKind::VacantK1AndOccupiedK2);
    ///
    /// // Return `ErrorKind::KeysPointsToDiffEntries` if both
    /// // `K1` key and `K2` key already exist with some values,
    /// // but point to different entries (values).
    /// let key1 = "a";
    /// let hash1 = compute_hash(map.hasher(), &key1);
    /// let key2 = 2;
    /// let hash2 = compute_hash(map.hasher(), &key2);
    /// let error_kind = map
    ///     .raw_entry_mut()
    ///     .from_hashes(hash1, |q| *q == key1, hash2, |q| *q == key2)
    ///     .unwrap_err();
    /// assert_eq!(error_kind, ErrorKind::KeysPointsToDiffEntries);
    ///
    /// let key1 = "b";
    /// let hash1 = compute_hash(map.hasher(), &key1);
    /// let key2 = 1;
    /// let hash2 = compute_hash(map.hasher(), &key2);
    /// let error_kind = map
    ///     .raw_entry_mut()
    ///     .from_hashes(hash1, |q| *q == key1, hash2, |q| *q == key2)
    ///     .unwrap_err();
    /// assert_eq!(error_kind, ErrorKind::KeysPointsToDiffEntries);
    /// ```
    #[cfg_attr(feature = "inline-more", inline)]
    #[allow(clippy::wrong_self_convention)]
    pub fn from_hashes<F1, F2>(
        self,
        hash1: u64,
        is_match1: F1,
        hash2: u64,
        is_match2: F2,
    ) -> Result<RawEntryMut<'a, K1, K2, V, S, A>, ErrorKind>
    where
        F1: FnMut(&K1) -> bool,
        F2: FnMut(&K2) -> bool,
    {
        self.search(hash1, is_match1, hash2, is_match2)
    }

    #[cfg_attr(feature = "inline-more", inline)]
    fn search<F1, F2>(
        self,
        hash1: u64,
        mut is_match1: F1,
        hash2: u64,
        mut is_match2: F2,
    ) -> Result<RawEntryMut<'a, K1, K2, V, S, A>, ErrorKind>
    where
        F1: FnMut(&K1) -> bool,
        F2: FnMut(&K2) -> bool,
    {
        match self.map.table.find_h1(hash1, |x| is_match1(&x.0)) {
            None => match self.map.table.find_h2(hash2, |x| is_match2(&x.1)) {
                None => Ok(RawEntryMut::Vacant(RawVacantEntryMut {
                    table: &mut self.map.table,
                    hash_builder: &self.map.hash_builder,
                })),
                Some(_) => Err(ErrorKind::VacantK1AndOccupiedK2),
            },
            Some(data_bucket) => match self.map.table.find_h2(hash2, |x| is_match2(&x.1)) {
                Some(pointer_bucket) => {
                    if unsafe { ptr::eq(data_bucket.as_ptr(), pointer_bucket.as_data_ptr()) } {
                        Ok(RawEntryMut::Occupied(RawOccupiedEntryMut {
                            data_bucket,
                            pointer_bucket,
                            table: &mut self.map.table,
                            hash_builder: &self.map.hash_builder,
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
}

/// A view into a vacant entry in a `DoubleMap`.
/// It is part of the [`RawEntryMut`] enum.
///
/// [`RawEntryMut`]: enum.RawEntryMut.html
///
/// # Examples
///
/// ```
/// use core::hash::{BuildHasher, Hash};
/// use double_map::shash_map::{DoubleMap, RawEntryMut, RawVacantEntryMut};
///
/// let mut map = DoubleMap::<&str, i32, i32>::new();
///
/// fn compute_hash<K: Hash + ?Sized, S: BuildHasher>(hash_builder: &S, key: &K) -> u64 {
///     use core::hash::Hasher;
///     let mut state = hash_builder.build_hasher();
///     key.hash(&mut state);
///     state.finish()
/// }
///
/// let raw_v: RawVacantEntryMut<_, _, _, _> = match map.raw_entry_mut().from_keys(&"a", &11) {
///     Ok(RawEntryMut::Vacant(view)) => view,
///     _ => panic!(),
/// };
/// raw_v.insert("a", 11, 111);
/// assert!(map[&"a"] == 111 && map.len() == 1);
///
/// // Nonexistent key (insert and update)
/// let hash1 = compute_hash(map.hasher(), &"b");
/// let hash2 = compute_hash(map.hasher(), &22);
/// match map
///     .raw_entry_mut()
///     .from_keys_hashed_nocheck(hash1, &"b", hash2, &22)
/// {
///     Ok(RawEntryMut::Vacant(view)) => {
///         let (k1, k2, value) = view.insert("b", 22, 200);
///         assert_eq!((*k1, *k2, *value), ("b", 22, 200));
///         *value = 222;
///     }
///     _ => panic!(),
/// }
/// assert!(map[&"b"] == 222 && map.len() == 2);
///
/// let hash1 = compute_hash(map.hasher(), &"c");
/// let hash2 = compute_hash(map.hasher(), &33);
/// match map
///     .raw_entry_mut()
///     .from_hashes(hash1, |q| *q == "c", hash2, |q| *q == 33)
/// {
///     Ok(RawEntryMut::Vacant(view)) => {
///         assert_eq!(view.insert("c", 33, 333), (&mut "c", &mut 33, &mut 333));
///     }
///     _ => panic!(),
/// }
/// assert!(map[&"c"] == 333 && map.len() == 3);
/// ```
pub struct RawVacantEntryMut<'a, K1, K2, V, S, A: Allocator + Clone = Global> {
    table: &'a mut RawTable<(K1, K2, V), A>,
    hash_builder: &'a S,
}

impl<K1, K2, V, S> Debug for RawVacantEntryMut<'_, K1, K2, V, S> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("RawVacantEntryMut").finish()
    }
}

impl<'a, K1, K2, V, S, A: Allocator + Clone> RawVacantEntryMut<'a, K1, K2, V, S, A> {
    /// Sets the value of the entry with the VacantEntry's keys,
    /// and returns a mutable reference to it.
    ///
    /// # Examples
    ///
    /// ```
    /// use double_map::shash_map::{DoubleMap, RawEntryMut};
    ///
    /// let mut map: DoubleMap<&str, u32, u32> = [("a", 10, 100), ("b", 20, 200)].into();
    ///
    /// match map.raw_entry_mut().from_keys(&"c", &30) {
    ///     Ok(RawEntryMut::Vacant(v)) => {
    ///         assert_eq!(v.insert("c", 30, 300), (&mut "c", &mut 30, &mut 300))
    ///     }
    ///     _ => panic!(),
    /// }
    ///
    /// assert_eq!(map[&"c"], 300);
    /// ```
    #[cfg_attr(feature = "inline-more", inline)]
    pub fn insert(self, k1: K1, k2: K2, value: V) -> (&'a mut K1, &'a mut K2, &'a mut V)
    where
        K1: Hash,
        K2: Hash,
        S: BuildHasher,
    {
        // let hash = make_insert_hash::<K, S>(self.hash_builder, &key);
        // self.insert_hashed_nocheck(hash, key, value)
        let hash_builder = self.hash_builder;
        let hash1 = make_insert_hash::<K1, S>(hash_builder, &k1);
        let hash2 = make_insert_hash::<K2, S>(hash_builder, &k2);

        self.insert_hashed_nocheck(hash1, k1, hash2, k2, value)
    }

    /// Sets the value of the entry with the VacantEntry's keys,
    /// and returns a mutable reference to it.
    ///
    /// # Examples
    ///
    /// ```
    /// use core::hash::{BuildHasher, Hash};
    /// use double_map::shash_map::{DoubleMap, RawEntryMut};
    ///
    /// fn compute_hash<K: Hash + ?Sized, S: BuildHasher>(hash_builder: &S, key: &K) -> u64 {
    ///     use core::hash::Hasher;
    ///     let mut state = hash_builder.build_hasher();
    ///     key.hash(&mut state);
    ///     state.finish()
    /// }
    ///
    /// let mut map: DoubleMap<&str, u32, u32> = [("a", 10, 100), ("b", 20, 200)].into();
    /// let key1 = "c";
    /// let hash1 = compute_hash(map.hasher(), &key1);
    /// let key2 = 30;
    /// let hash2 = compute_hash(map.hasher(), &key2);
    ///
    /// match map
    ///     .raw_entry_mut()
    ///     .from_keys_hashed_nocheck(hash1, &key1, hash2, &key2)
    /// {
    ///     Ok(RawEntryMut::Vacant(v)) => assert_eq!(
    ///         v.insert_hashed_nocheck(hash1, key1, hash2, key2, 300),
    ///         (&mut "c", &mut 30, &mut 300)
    ///     ),
    ///     _ => panic!(),
    /// }
    ///
    /// assert_eq!(map[&"c"], 300);
    /// ```
    #[cfg_attr(feature = "inline-more", inline)]
    #[allow(clippy::shadow_unrelated)]
    pub fn insert_hashed_nocheck(
        self,
        hash1: u64,
        k1: K1,
        hash2: u64,
        k2: K2,
        value: V,
    ) -> (&'a mut K1, &'a mut K2, &'a mut V)
    where
        K1: Hash,
        K2: Hash,
        S: BuildHasher,
    {
        let hash_builder = self.hash_builder;
        let &mut (ref mut k1, ref mut k2, ref mut v) = self.table.insert_entry(
            hash1,
            hash2,
            (k1, k2, value),
            make_hasher_key1::<_, K2, V, S>(hash_builder),
            make_hasher_key2::<K1, _, V, S>(hash_builder),
        );
        (k1, k2, v)
    }

    /// Set the value of an entry with custom hasher functions.
    ///
    /// # Examples
    ///
    /// ```
    /// use core::hash::{BuildHasher, Hash};
    /// use double_map::shash_map::{DoubleMap, RawEntryMut};
    ///
    /// fn make_hasher<K, S>(hash_builder: &S) -> impl Fn(&K) -> u64 + '_
    /// where
    ///     K: Hash + ?Sized,
    ///     S: BuildHasher,
    /// {
    ///     move |key: &K| {
    ///         use core::hash::Hasher;
    ///         let mut state = hash_builder.build_hasher();
    ///         key.hash(&mut state);
    ///         state.finish()
    ///     }
    /// }
    ///
    /// let mut map: DoubleMap<&str, u32, u32> = DoubleMap::new();
    /// let hash_builder = map.hasher().clone();
    ///
    /// for (mut k1, mut k2, mut v) in ["a", "b", "c", "d", "e", "f"]
    ///     .into_iter()
    ///     .zip(1..=6)
    ///     .map(|(k1, i)| (k1, i * 10, i * 100))
    /// {
    ///     let hash1 = make_hasher(&hash_builder)(&k1);
    ///     let hash2 = make_hasher(&hash_builder)(&k2);
    ///     match map
    ///         .raw_entry_mut()
    ///         .from_hashes(hash1, |q| *q == k1, hash2, |q| *q == k2)
    ///     {
    ///         Ok(RawEntryMut::Vacant(vacant)) => assert_eq!(
    ///             vacant.insert_with_hashers(
    ///                 hash1,
    ///                 k1,
    ///                 hash2,
    ///                 k2,
    ///                 v,
    ///                 make_hasher(&hash_builder),
    ///                 make_hasher(&hash_builder),
    ///             ),
    ///             (&mut k1, &mut k2, &mut v)
    ///         ),
    ///         _ => panic!(),
    ///     }
    /// }
    ///
    /// let mut vec: Vec<_> = map.into_iter().collect();
    /// // The `IntoIter` iterator produces tuples in arbitrary order, so
    /// // the tuples must be sorted to test them against a sorted array.
    /// vec.sort_unstable();
    /// assert_eq!(
    ///     vec,
    ///     [
    ///         ("a", 10, 100),
    ///         ("b", 20, 200),
    ///         ("c", 30, 300),
    ///         ("d", 40, 400),
    ///         ("e", 50, 500),
    ///         ("f", 60, 600)
    ///     ]
    /// )
    /// ```
    #[allow(clippy::too_many_arguments)]
    #[cfg_attr(feature = "inline-more", inline)]
    pub fn insert_with_hashers<H1, H2>(
        self,
        hash1: u64,
        k1: K1,
        hash2: u64,
        k2: K2,
        value: V,
        hasher1: H1,
        hasher2: H2,
    ) -> (&'a mut K1, &'a mut K2, &'a mut V)
    where
        H1: Fn(&K1) -> u64,
        H2: Fn(&K2) -> u64,
    {
        let &mut (ref mut k1, ref mut k2, ref mut v) = self.table.insert_entry(
            hash1,
            hash2,
            (k1, k2, value),
            |x| hasher1(&x.0),
            |x| hasher2(&x.1),
        );
        (k1, k2, v)
    }

    #[cfg_attr(feature = "inline-more", inline)]
    fn insert_entry(self, k1: K1, k2: K2, value: V) -> RawOccupiedEntryMut<'a, K1, K2, V, S, A>
    where
        K1: Hash,
        K2: Hash,
        S: BuildHasher,
    {
        let hash_builder = self.hash_builder;
        let hash1 = make_insert_hash::<K1, S>(hash_builder, &k1);
        let hash2 = make_insert_hash::<K2, S>(hash_builder, &k2);

        let (data_bucket, pointer_bucket) = self.table.insert(
            hash1,
            hash2,
            (k1, k2, value),
            make_hasher_key1::<_, K2, V, S>(hash_builder),
            make_hasher_key2::<K1, _, V, S>(hash_builder),
        );

        RawOccupiedEntryMut {
            data_bucket,
            pointer_bucket,
            table: self.table,
            hash_builder: self.hash_builder,
        }
    }
}

/// A view into an occupied entry in a `DoubleMap`.
/// It is part of the [`RawEntryMut`] enum.
///
/// [`RawEntryMut`]: enum.RawEntryMut.html
///
/// # Examples
///
/// ```
/// use core::hash::{BuildHasher, Hash};
/// use double_map::shash_map::{DoubleMap, RawEntryMut, RawOccupiedEntryMut};
///
/// let mut map = DoubleMap::new();
/// map.extend([("a", 10, 100), ("b", 20, 200), ("c", 30, 300)]);
///
/// fn compute_hash<K: Hash + ?Sized, S: BuildHasher>(hash_builder: &S, key: &K) -> u64 {
///     use core::hash::Hasher;
///     let mut state = hash_builder.build_hasher();
///     key.hash(&mut state);
///     state.finish()
/// }
///
/// let _raw_o: RawOccupiedEntryMut<_, _, _, _> = map
///     .raw_entry_mut()
///     .from_keys(&"a", &10)
///     .unwrap()
///     .insert("a", 10, 111);
/// assert_eq!(map.len(), 3);
///
/// // Existing key (insert and update)
/// match map.raw_entry_mut().from_keys(&"a", &10) {
///     Ok(RawEntryMut::Occupied(mut view)) => {
///         assert_eq!(view.get(), &111);
///         let v = view.get_mut();
///         let new_v = (*v) * 10;
///         *v = new_v;
///         assert_eq!(view.insert(121), 1110);
///     }
///     _ => panic!(),
/// }
///
/// assert_eq!(map[&"a"], 121);
/// assert_eq!(map.len(), 3);
///
/// // Existing key (take)
/// let hash1 = compute_hash(map.hasher(), "c");
/// let hash2 = compute_hash(map.hasher(), &30);
/// match map
///     .raw_entry_mut()
///     .from_keys_hashed_nocheck(hash1, &"c", hash2, &30)
/// {
///     Ok(RawEntryMut::Occupied(view)) => {
///         assert_eq!(view.remove_entry(), ("c", 30, 300));
///     }
///     _ => panic!(),
/// }
/// assert_eq!(map.raw_entry().from_keys(&"c", &30), None);
/// assert_eq!(map.len(), 2);
///
/// let hash1 = compute_hash(map.hasher(), "b");
/// let hash2 = compute_hash(map.hasher(), &20);
/// match map
///     .raw_entry_mut()
///     .from_hashes(hash1, |q| *q == "b", hash2, |q| *q == 20)
/// {
///     Ok(RawEntryMut::Occupied(view)) => {
///         assert_eq!(view.remove_entry(), ("b", 20, 200));
///     }
///     _ => panic!(),
/// }
/// assert_eq!(map.get_key1(&"b"), None);
/// assert_eq!(map.len(), 1);
/// ```
pub struct RawOccupiedEntryMut<'a, K1, K2, V, S, A: Allocator + Clone = Global> {
    data_bucket: DataBucket<(K1, K2, V)>,
    pointer_bucket: PointerBucket<DataBucket<(K1, K2, V)>>,
    table: &'a mut RawTable<(K1, K2, V), A>,
    hash_builder: &'a S,
}

unsafe impl<K1, K2, V, S, A> Send for RawOccupiedEntryMut<'_, K1, K2, V, S, A>
where
    K1: Send,
    K2: Send,
    V: Send,
    S: Send,
    A: Send + Allocator + Clone,
{
}

unsafe impl<K1, K2, V, S, A> Sync for RawOccupiedEntryMut<'_, K1, K2, V, S, A>
where
    K1: Sync,
    K2: Sync,
    V: Sync,
    S: Sync,
    A: Sync + Allocator + Clone,
{
}

impl<K1: Debug, K2: Debug, V: Debug, S, A> Debug for RawOccupiedEntryMut<'_, K1, K2, V, S, A>
where
    A: Allocator + Clone,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("RawOccupiedEntryMut")
            .field("key1", self.key1())
            .field("key2", self.key2())
            .field("value", self.get())
            .finish()
    }
}

impl<'a, K1, K2, V, S, A: Allocator + Clone> RawOccupiedEntryMut<'a, K1, K2, V, S, A> {
    /// Gets a reference to the `K1` key in the entry.
    ///
    /// # Examples
    ///
    /// ```
    /// use core::hash::{BuildHasher, Hash};
    /// use double_map::shash_map::{DoubleMap, RawEntryMut};
    ///
    /// fn compute_hash<K: Hash + ?Sized, S: BuildHasher>(hash_builder: &S, key: &K) -> u64 {
    ///     use core::hash::Hasher;
    ///     let mut state = hash_builder.build_hasher();
    ///     key.hash(&mut state);
    ///     state.finish()
    /// }
    ///
    /// let mut map: DoubleMap<&str, u32, u32> = [("a", 10, 100), ("b", 20, 200), ("c", 30, 300)].into();
    ///
    /// match map.raw_entry_mut().from_keys(&"a", &10) {
    ///     Ok(RawEntryMut::Occupied(o)) => assert_eq!(o.key1(), &"a"),
    ///     _ => panic!(),
    /// }
    ///
    /// let hash1 = compute_hash(map.hasher(), &"b");
    /// let hash2 = compute_hash(map.hasher(), &20);
    /// match map
    ///     .raw_entry_mut()
    ///     .from_keys_hashed_nocheck(hash1, &"b", hash2, &20)
    /// {
    ///     Ok(RawEntryMut::Occupied(o)) => assert_eq!(o.key1(), &"b"),
    ///     _ => panic!(),
    /// }
    ///
    /// let hash1 = compute_hash(map.hasher(), &"c");
    /// let hash2 = compute_hash(map.hasher(), &30);
    /// match map
    ///     .raw_entry_mut()
    ///     .from_hashes(hash1, |q| *q == "c", hash2, |q| *q == 30)
    /// {
    ///     Ok(RawEntryMut::Occupied(o)) => assert_eq!(o.key1(), &"c"),
    ///     _ => panic!(),
    /// }
    /// ```
    #[cfg_attr(feature = "inline-more", inline)]
    pub fn key1(&self) -> &K1 {
        unsafe { &self.data_bucket.as_ref().0 }
    }

    /// Gets a reference to the `K2` key in the entry.
    ///
    /// # Examples
    ///
    /// ```
    /// use core::hash::{BuildHasher, Hash};
    /// use double_map::shash_map::{DoubleMap, RawEntryMut};
    ///
    /// fn compute_hash<K: Hash + ?Sized, S: BuildHasher>(hash_builder: &S, key: &K) -> u64 {
    ///     use core::hash::Hasher;
    ///     let mut state = hash_builder.build_hasher();
    ///     key.hash(&mut state);
    ///     state.finish()
    /// }
    ///
    /// let mut map: DoubleMap<&str, u32, u32> = [("a", 10, 100), ("b", 20, 200), ("c", 30, 300)].into();
    ///
    /// match map.raw_entry_mut().from_keys(&"a", &10) {
    ///     Ok(RawEntryMut::Occupied(o)) => assert_eq!(o.key2(), &10),
    ///     _ => panic!(),
    /// }
    ///
    /// let hash1 = compute_hash(map.hasher(), &"b");
    /// let hash2 = compute_hash(map.hasher(), &20);
    /// match map
    ///     .raw_entry_mut()
    ///     .from_keys_hashed_nocheck(hash1, &"b", hash2, &20)
    /// {
    ///     Ok(RawEntryMut::Occupied(o)) => assert_eq!(o.key2(), &20),
    ///     _ => panic!(),
    /// }
    ///
    /// let hash1 = compute_hash(map.hasher(), &"c");
    /// let hash2 = compute_hash(map.hasher(), &30);
    /// match map
    ///     .raw_entry_mut()
    ///     .from_hashes(hash1, |q| *q == "c", hash2, |q| *q == 30)
    /// {
    ///     Ok(RawEntryMut::Occupied(o)) => assert_eq!(o.key2(), &30),
    ///     _ => panic!(),
    /// }
    /// ```
    #[cfg_attr(feature = "inline-more", inline)]
    pub fn key2(&self) -> &K2 {
        unsafe { &self.data_bucket.as_ref().1 }
    }

    /// Gets a reference to the `K1` and `K2` keys in the entry.
    ///
    /// # Examples
    ///
    /// ```
    /// use core::hash::{BuildHasher, Hash};
    /// use double_map::shash_map::{DoubleMap, RawEntryMut};
    ///
    /// fn compute_hash<K: Hash + ?Sized, S: BuildHasher>(hash_builder: &S, key: &K) -> u64 {
    ///     use core::hash::Hasher;
    ///     let mut state = hash_builder.build_hasher();
    ///     key.hash(&mut state);
    ///     state.finish()
    /// }
    ///
    /// let mut map: DoubleMap<&str, u32, u32> = [("a", 10, 100), ("b", 20, 200), ("c", 30, 300)].into();
    ///
    /// match map.raw_entry_mut().from_keys(&"a", &10) {
    ///     Ok(RawEntryMut::Occupied(o)) => assert_eq!(o.keys(), (&"a", &10)),
    ///     _ => panic!(),
    /// }
    ///
    /// let hash1 = compute_hash(map.hasher(), &"b");
    /// let hash2 = compute_hash(map.hasher(), &20);
    /// match map
    ///     .raw_entry_mut()
    ///     .from_keys_hashed_nocheck(hash1, &"b", hash2, &20)
    /// {
    ///     Ok(RawEntryMut::Occupied(o)) => assert_eq!(o.keys(), (&"b", &20)),
    ///     _ => panic!(),
    /// }
    ///
    /// let hash1 = compute_hash(map.hasher(), &"c");
    /// let hash2 = compute_hash(map.hasher(), &30);
    /// match map
    ///     .raw_entry_mut()
    ///     .from_hashes(hash1, |q| *q == "c", hash2, |q| *q == 30)
    /// {
    ///     Ok(RawEntryMut::Occupied(o)) => assert_eq!(o.keys(), (&"c", &30)),
    ///     _ => panic!(),
    /// }
    /// ```
    #[cfg_attr(feature = "inline-more", inline)]
    pub fn keys(&self) -> (&K1, &K2) {
        let &(ref k1, ref k2, _) = unsafe { self.data_bucket.as_ref() };
        (k1, k2)
    }

    /// Gets a mutable reference to the `K1` key in the entry.
    ///
    /// # Examples
    ///
    /// ```
    /// use core::hash::{BuildHasher, Hash};
    /// use double_map::shash_map::{DoubleMap, RawEntryMut};
    /// use std::rc::Rc;
    ///
    /// fn compute_hash<K: Hash + ?Sized, S: BuildHasher>(hash_builder: &S, key: &K) -> u64 {
    ///     use core::hash::Hasher;
    ///     let mut state = hash_builder.build_hasher();
    ///     key.hash(&mut state);
    ///     state.finish()
    /// }
    ///
    /// let mut map = DoubleMap::<Rc<&str>, usize, usize>::new();
    ///
    /// let array = ["a", "b", "c", "d", "e", "f", "g", "h", "i"];
    /// let keys_vec_one: Vec<_> = array.into_iter().map(|k1| Rc::new(k1)).collect();
    /// let keys_vec_two: Vec<_> = array.into_iter().map(|k1| Rc::new(k1)).collect();
    ///
    /// for (k1, k2, v) in keys_vec_one
    ///     .iter()
    ///     .enumerate()
    ///     .map(|(i, k1)| (k1, i * 127, i * 100))
    /// {
    ///     map.insert(k1.clone(), k2, v);
    /// }
    /// assert!(keys_vec_one.iter().all(|k1| Rc::strong_count(k1) == 2));
    /// assert!(keys_vec_two.iter().all(|k1| Rc::strong_count(k1) == 1));
    ///
    /// let iter = keys_vec_two.iter().enumerate().map(|(i, k1)| (k1, i * 127));
    ///
    /// for (k1, k2) in iter {
    ///     match k2 {
    ///         1..=3 => match map.raw_entry_mut().from_keys(k1, &k2) {
    ///             Ok(RawEntryMut::Occupied(mut o)) => *o.key1_mut() = k1.clone(),
    ///             _ => panic!(),
    ///         },
    ///         4..=6 => {
    ///             let hash1 = compute_hash(map.hasher(), k1);
    ///             let hash2 = compute_hash(map.hasher(), &k2);
    ///             match map
    ///                 .raw_entry_mut()
    ///                 .from_keys_hashed_nocheck(hash1, k1, hash2, &k2)
    ///             {
    ///                 Ok(RawEntryMut::Occupied(mut o)) => *o.key1_mut() = k1.clone(),
    ///                 _ => panic!(),
    ///             }
    ///         }
    ///         _ => {
    ///             let hash1 = compute_hash(map.hasher(), k1);
    ///             let hash2 = compute_hash(map.hasher(), &k2);
    ///             match map
    ///                 .raw_entry_mut()
    ///                 .from_hashes(hash1, |q| q == k1, hash2, |q| *q == k2)
    ///             {
    ///                 Ok(RawEntryMut::Occupied(mut o)) => *o.key1_mut() = k1.clone(),
    ///                 _ => panic!(),
    ///             }
    ///         }
    ///     }
    /// }
    /// assert!(keys_vec_one.iter().all(|k1| Rc::strong_count(k1) == 1));
    /// assert!(keys_vec_two.iter().all(|k1| Rc::strong_count(k1) == 2));
    /// ```
    #[cfg_attr(feature = "inline-more", inline)]
    pub fn key1_mut(&mut self) -> &mut K1 {
        unsafe { &mut self.data_bucket.as_mut().0 }
    }

    /// Gets a mutable reference to the `K2` key in the entry.
    ///
    /// # Examples
    ///
    /// ```
    /// use core::hash::{BuildHasher, Hash};
    /// use double_map::shash_map::{DoubleMap, RawEntryMut};
    /// use std::rc::Rc;
    ///
    /// fn compute_hash<K: Hash + ?Sized, S: BuildHasher>(hash_builder: &S, key: &K) -> u64 {
    ///     use core::hash::Hasher;
    ///     let mut state = hash_builder.build_hasher();
    ///     key.hash(&mut state);
    ///     state.finish()
    /// }
    ///
    /// let mut map = DoubleMap::<&str, Rc<i32>, usize>::new();
    ///
    /// let array = ["a", "b", "c", "d", "e", "f", "g", "h", "i"];
    /// let keys_vec_one: Vec<_> = (1..=9).into_iter().map(|k1| Rc::new(k1 * 127)).collect();
    /// let keys_vec_two: Vec<_> = (1..=9).into_iter().map(|k1| Rc::new(k1 * 127)).collect();
    ///
    /// for (k1, k2, v) in array
    ///     .iter()
    ///     .zip(&keys_vec_one)
    ///     .enumerate()
    ///     .map(|(i, (k1, k2))| (*k1, k2, i * 100))
    /// {
    ///     map.insert(k1, k2.clone(), v);
    /// }
    /// assert!(keys_vec_one.iter().all(|k1| Rc::strong_count(k1) == 2));
    /// assert!(keys_vec_two.iter().all(|k1| Rc::strong_count(k1) == 1));
    ///
    /// let iter = array.iter().zip(&keys_vec_two).map(|(k1, k2)| (*k1, k2));
    ///
    /// for (i, (k1, k2)) in iter.enumerate() {
    ///     match i {
    ///         1..=3 => match map.raw_entry_mut().from_keys(k1, k2) {
    ///             Ok(RawEntryMut::Occupied(mut o)) => *o.key2_mut() = k2.clone(),
    ///             _ => panic!(),
    ///         },
    ///         4..=6 => {
    ///             let hash1 = compute_hash(map.hasher(), k1);
    ///             let hash2 = compute_hash(map.hasher(), k2);
    ///             match map
    ///                 .raw_entry_mut()
    ///                 .from_keys_hashed_nocheck(hash1, k1, hash2, k2)
    ///             {
    ///                 Ok(RawEntryMut::Occupied(mut o)) => *o.key2_mut() = k2.clone(),
    ///                 _ => panic!(),
    ///             }
    ///         }
    ///         _ => {
    ///             let hash1 = compute_hash(map.hasher(), k1);
    ///             let hash2 = compute_hash(map.hasher(), k2);
    ///             match map
    ///                 .raw_entry_mut()
    ///                 .from_hashes(hash1, |q| *q == k1, hash2, |q| q == k2)
    ///             {
    ///                 Ok(RawEntryMut::Occupied(mut o)) => *o.key2_mut() = k2.clone(),
    ///                 _ => panic!(),
    ///             }
    ///         }
    ///     }
    /// }
    /// assert!(keys_vec_one.iter().all(|k1| Rc::strong_count(k1) == 1));
    /// assert!(keys_vec_two.iter().all(|k1| Rc::strong_count(k1) == 2));
    /// ```
    #[cfg_attr(feature = "inline-more", inline)]
    pub fn key2_mut(&mut self) -> &mut K2 {
        unsafe { &mut self.data_bucket.as_mut().1 }
    }

    /// Gets a mutable reference to the `K1` and `K2` keys in the entry.
    ///
    /// # Examples
    ///
    /// ```
    /// use core::hash::{BuildHasher, Hash};
    /// use double_map::shash_map::{DoubleMap, RawEntryMut};
    /// use std::rc::Rc;
    ///
    /// fn compute_hash<K: Hash + ?Sized, S: BuildHasher>(hash_builder: &S, key: &K) -> u64 {
    ///     use core::hash::Hasher;
    ///     let mut state = hash_builder.build_hasher();
    ///     key.hash(&mut state);
    ///     state.finish()
    /// }
    ///
    /// let mut map = DoubleMap::<Rc<&str>, Rc<i32>, usize>::new();
    ///
    /// let array = ["a", "b", "c", "d", "e", "f", "g", "h", "i"];
    /// let keys_vec_one: Vec<_> = array
    ///     .iter()
    ///     .zip(1..=9)
    ///     .into_iter()
    ///     .map(|(k1, k2)| (Rc::new(*k1), Rc::new(k2 * 127)))
    ///     .collect();
    /// let keys_vec_two: Vec<_> = array
    ///     .iter()
    ///     .zip(1..=9)
    ///     .into_iter()
    ///     .map(|(k1, k2)| (Rc::new(*k1), Rc::new(k2 * 127)))
    ///     .collect();
    ///
    /// for (k1, k2, v) in keys_vec_one
    ///     .iter()
    ///     .enumerate()
    ///     .map(|(i, (k1, k2))| (k1, k2, i * 100))
    /// {
    ///     map.insert(k1.clone(), k2.clone(), v);
    /// }
    /// assert!(keys_vec_one
    ///     .iter()
    ///     .all(|(k1, k2)| Rc::strong_count(k1) == 2 && Rc::strong_count(k2) == 2));
    /// assert!(keys_vec_two
    ///     .iter()
    ///     .all(|(k1, k2)| Rc::strong_count(k1) == 1 && Rc::strong_count(k2) == 1));
    ///
    /// for (i, (k1, k2)) in keys_vec_two.iter().enumerate() {
    ///     match i {
    ///         1..=3 => match map.raw_entry_mut().from_keys(k1, k2) {
    ///             Ok(RawEntryMut::Occupied(mut o)) => {
    ///                 let (k1_in, k2_in) = o.keys_mut();
    ///                 *k1_in = k1.clone();
    ///                 *k2_in = k2.clone();
    ///             }
    ///             _ => panic!(),
    ///         },
    ///         4..=6 => {
    ///             let hash1 = compute_hash(map.hasher(), k1);
    ///             let hash2 = compute_hash(map.hasher(), k2);
    ///             match map
    ///                 .raw_entry_mut()
    ///                 .from_keys_hashed_nocheck(hash1, k1, hash2, k2)
    ///             {
    ///                 Ok(RawEntryMut::Occupied(mut o)) => {
    ///                     let (k1_in, k2_in) = o.keys_mut();
    ///                     *k1_in = k1.clone();
    ///                     *k2_in = k2.clone();
    ///                 }
    ///                 _ => panic!(),
    ///             }
    ///         }
    ///         _ => {
    ///             let hash1 = compute_hash(map.hasher(), k1);
    ///             let hash2 = compute_hash(map.hasher(), k2);
    ///             match map
    ///                 .raw_entry_mut()
    ///                 .from_hashes(hash1, |q| q == k1, hash2, |q| q == k2)
    ///             {
    ///                 Ok(RawEntryMut::Occupied(mut o)) => {
    ///                     let (k1_in, k2_in) = o.keys_mut();
    ///                     *k1_in = k1.clone();
    ///                     *k2_in = k2.clone();
    ///                 }
    ///                 _ => panic!(),
    ///             }
    ///         }
    ///     }
    /// }
    /// assert!(keys_vec_one
    ///     .iter()
    ///     .all(|(k1, k2)| Rc::strong_count(k1) == 1 && Rc::strong_count(k2) == 1));
    /// assert!(keys_vec_two
    ///     .iter()
    ///     .all(|(k1, k2)| Rc::strong_count(k1) == 2 && Rc::strong_count(k2) == 2));
    /// ```
    #[cfg_attr(feature = "inline-more", inline)]
    pub fn keys_mut(&mut self) -> (&mut K1, &mut K2) {
        let &mut (ref mut k1, ref mut k2, _) = unsafe { self.data_bucket.as_mut() };
        (k1, k2)
    }

    /// Converts the entry into a mutable reference to the `K1` key in the entry
    /// with a lifetime bound to the map itself.
    ///
    /// # Examples
    ///
    /// ```
    /// use core::hash::{BuildHasher, Hash};
    /// use double_map::shash_map::{DoubleMap, RawEntryMut};
    /// use std::rc::Rc;
    ///
    /// fn compute_hash<K: Hash + ?Sized, S: BuildHasher>(hash_builder: &S, key: &K) -> u64 {
    ///     use core::hash::Hasher;
    ///     let mut state = hash_builder.build_hasher();
    ///     key.hash(&mut state);
    ///     state.finish()
    /// }
    ///
    /// let mut map = DoubleMap::<Rc<&str>, usize, usize>::new();
    ///
    /// let array = [
    ///     "one", "two", "three", "four", "five", "six", "seven", "eight", "nine",
    /// ];
    /// let keys_vec_one: Vec<_> = array.into_iter().map(|k1| Rc::new(k1)).collect();
    /// let keys_vec_two: Vec<_> = array.into_iter().map(|k1| Rc::new(k1)).collect();
    ///
    /// for (k1, k2, v) in keys_vec_one
    ///     .iter()
    ///     .enumerate()
    ///     .map(|(i, k1)| (k1, i * 127, i * 100))
    /// {
    ///     map.insert(k1.clone(), k2, v);
    /// }
    /// assert!(keys_vec_one.iter().all(|k1| Rc::strong_count(k1) == 2));
    /// assert!(keys_vec_two.iter().all(|k1| Rc::strong_count(k1) == 1));
    ///
    /// let iter = keys_vec_two.iter().enumerate().map(|(i, k1)| (k1, i * 127));
    ///
    /// for (k1, k2) in iter {
    ///     let inside_key: &mut Rc<&str>;
    ///     match k2 {
    ///         1..=3 => match map.raw_entry_mut().from_keys(k1, &k2) {
    ///             Ok(RawEntryMut::Occupied(o)) => inside_key = o.into_key1(),
    ///             _ => panic!(),
    ///         },
    ///         4..=6 => {
    ///             let hash1 = compute_hash(map.hasher(), k1);
    ///             let hash2 = compute_hash(map.hasher(), &k2);
    ///             match map
    ///                 .raw_entry_mut()
    ///                 .from_keys_hashed_nocheck(hash1, k1, hash2, &k2)
    ///             {
    ///                 Ok(RawEntryMut::Occupied(o)) => inside_key = o.into_key1(),
    ///                 _ => panic!(),
    ///             }
    ///         }
    ///         _ => {
    ///             let hash1 = compute_hash(map.hasher(), k1);
    ///             let hash2 = compute_hash(map.hasher(), &k2);
    ///             match map
    ///                 .raw_entry_mut()
    ///                 .from_hashes(hash1, |q| q == k1, hash2, |q| *q == k2)
    ///             {
    ///                 Ok(RawEntryMut::Occupied(o)) => inside_key = o.into_key1(),
    ///                 _ => panic!(),
    ///             }
    ///         }
    ///     }
    ///     *inside_key = k1.clone();
    /// }
    /// assert!(keys_vec_one.iter().all(|k1| Rc::strong_count(k1) == 1));
    /// assert!(keys_vec_two.iter().all(|k1| Rc::strong_count(k1) == 2));
    #[cfg_attr(feature = "inline-more", inline)]
    pub fn into_key1(self) -> &'a mut K1 {
        unsafe { &mut self.data_bucket.as_mut().0 }
    }

    /// Converts the entry into a mutable reference to the `K2` key in the entry
    /// with a lifetime bound to the map itself.
    ///
    /// # Examples
    ///
    /// ```
    /// use core::hash::{BuildHasher, Hash};
    /// use double_map::shash_map::{DoubleMap, RawEntryMut};
    /// use std::rc::Rc;
    ///
    /// fn compute_hash<K: Hash + ?Sized, S: BuildHasher>(hash_builder: &S, key: &K) -> u64 {
    ///     use core::hash::Hasher;
    ///     let mut state = hash_builder.build_hasher();
    ///     key.hash(&mut state);
    ///     state.finish()
    /// }
    ///
    /// let mut map = DoubleMap::<&str, Rc<i32>, usize>::new();
    ///
    /// let array = [
    ///     "one", "two", "three", "four", "five", "six", "seven", "eight", "nine",
    /// ];
    /// let keys_vec_one: Vec<_> = (1..=9).into_iter().map(|k1| Rc::new(k1 * 127)).collect();
    /// let keys_vec_two: Vec<_> = (1..=9).into_iter().map(|k1| Rc::new(k1 * 127)).collect();
    ///
    /// for (k1, k2, v) in array
    ///     .iter()
    ///     .zip(&keys_vec_one)
    ///     .enumerate()
    ///     .map(|(i, (k1, k2))| (*k1, k2, i * 100))
    /// {
    ///     map.insert(k1, k2.clone(), v);
    /// }
    /// assert!(keys_vec_one.iter().all(|k1| Rc::strong_count(k1) == 2));
    /// assert!(keys_vec_two.iter().all(|k1| Rc::strong_count(k1) == 1));
    ///
    /// let iter = array.iter().zip(&keys_vec_two).map(|(k1, k2)| (*k1, k2));
    ///
    /// for (i, (k1, k2)) in iter.enumerate() {
    ///     let inside_key: &mut Rc<i32>;
    ///     match i {
    ///         1..=3 => match map.raw_entry_mut().from_keys(k1, k2) {
    ///             Ok(RawEntryMut::Occupied(o)) => inside_key = o.into_key2(),
    ///             _ => panic!(),
    ///         },
    ///         4..=6 => {
    ///             let hash1 = compute_hash(map.hasher(), k1);
    ///             let hash2 = compute_hash(map.hasher(), k2);
    ///             match map
    ///                 .raw_entry_mut()
    ///                 .from_keys_hashed_nocheck(hash1, k1, hash2, k2)
    ///             {
    ///                 Ok(RawEntryMut::Occupied(o)) => inside_key = o.into_key2(),
    ///                 _ => panic!(),
    ///             }
    ///         }
    ///         _ => {
    ///             let hash1 = compute_hash(map.hasher(), k1);
    ///             let hash2 = compute_hash(map.hasher(), k2);
    ///             match map
    ///                 .raw_entry_mut()
    ///                 .from_hashes(hash1, |q| *q == k1, hash2, |q| q == k2)
    ///             {
    ///                 Ok(RawEntryMut::Occupied(o)) => inside_key = o.into_key2(),
    ///                 _ => panic!(),
    ///             }
    ///         }
    ///     }
    ///     *inside_key = k2.clone();
    /// }
    /// assert!(keys_vec_one.iter().all(|k1| Rc::strong_count(k1) == 1));
    /// assert!(keys_vec_two.iter().all(|k1| Rc::strong_count(k1) == 2));
    /// ```
    #[cfg_attr(feature = "inline-more", inline)]
    pub fn into_key2(self) -> &'a mut K2 {
        unsafe { &mut self.data_bucket.as_mut().1 }
    }

    /// Converts the entry into a mutable reference to the `K1` and `K2`
    /// keys in the entry with a lifetime bound to the map itself.
    ///
    /// # Examples
    ///
    /// ```
    /// use core::hash::{BuildHasher, Hash};
    /// use double_map::shash_map::{DoubleMap, RawEntryMut};
    /// use std::rc::Rc;
    ///
    /// fn compute_hash<K: Hash + ?Sized, S: BuildHasher>(hash_builder: &S, key: &K) -> u64 {
    ///     use core::hash::Hasher;
    ///     let mut state = hash_builder.build_hasher();
    ///     key.hash(&mut state);
    ///     state.finish()
    /// }
    ///
    /// let mut map = DoubleMap::<Rc<&str>, Rc<i32>, usize>::new();
    ///
    /// let array = [
    ///     "one", "two", "three", "four", "five", "six", "seven", "eight", "nine",
    /// ];
    /// let keys_vec_one: Vec<_> = array
    ///     .iter()
    ///     .zip(1..=9)
    ///     .into_iter()
    ///     .map(|(k1, k2)| (Rc::new(*k1), Rc::new(k2 * 127)))
    ///     .collect();
    /// let keys_vec_two: Vec<_> = array
    ///     .iter()
    ///     .zip(1..=9)
    ///     .into_iter()
    ///     .map(|(k1, k2)| (Rc::new(*k1), Rc::new(k2 * 127)))
    ///     .collect();
    ///
    /// for (k1, k2, v) in keys_vec_one
    ///     .iter()
    ///     .enumerate()
    ///     .map(|(i, (k1, k2))| (k1, k2, i * 100))
    /// {
    ///     map.insert(k1.clone(), k2.clone(), v);
    /// }
    /// assert!(keys_vec_one
    ///     .iter()
    ///     .all(|(k1, k2)| Rc::strong_count(k1) == 2 && Rc::strong_count(k2) == 2));
    /// assert!(keys_vec_two
    ///     .iter()
    ///     .all(|(k1, k2)| Rc::strong_count(k1) == 1 && Rc::strong_count(k2) == 1));
    ///
    /// for (i, (k1, k2)) in keys_vec_two.iter().enumerate() {
    ///     let inside_key1: &mut Rc<&str>;
    ///     let inside_key2: &mut Rc<i32>;
    ///     match i {
    ///         1..=3 => match map.raw_entry_mut().from_keys(k1, k2) {
    ///             Ok(RawEntryMut::Occupied(o)) => {
    ///                 let (in_key1, in_key2) = o.into_keys();
    ///                 inside_key1 = in_key1;
    ///                 inside_key2 = in_key2;
    ///             }
    ///             _ => panic!(),
    ///         },
    ///         4..=6 => {
    ///             let hash1 = compute_hash(map.hasher(), k1);
    ///             let hash2 = compute_hash(map.hasher(), k2);
    ///             match map
    ///                 .raw_entry_mut()
    ///                 .from_keys_hashed_nocheck(hash1, k1, hash2, k2)
    ///             {
    ///                 Ok(RawEntryMut::Occupied(o)) => {
    ///                     let (in_key1, in_key2) = o.into_keys();
    ///                     inside_key1 = in_key1;
    ///                     inside_key2 = in_key2;
    ///                 }
    ///                 _ => panic!(),
    ///             }
    ///         }
    ///         _ => {
    ///             let hash1 = compute_hash(map.hasher(), k1);
    ///             let hash2 = compute_hash(map.hasher(), k2);
    ///             match map
    ///                 .raw_entry_mut()
    ///                 .from_hashes(hash1, |q| q == k1, hash2, |q| q == k2)
    ///             {
    ///                 Ok(RawEntryMut::Occupied(o)) => {
    ///                     let (in_key1, in_key2) = o.into_keys();
    ///                     inside_key1 = in_key1;
    ///                     inside_key2 = in_key2;
    ///                 }
    ///                 _ => panic!(),
    ///             }
    ///         }
    ///     }
    ///     *inside_key1 = k1.clone();
    ///     *inside_key2 = k2.clone();
    /// }
    /// assert!(keys_vec_one
    ///     .iter()
    ///     .all(|(k1, k2)| Rc::strong_count(k1) == 1 && Rc::strong_count(k2) == 1));
    /// assert!(keys_vec_two
    ///     .iter()
    ///     .all(|(k1, k2)| Rc::strong_count(k1) == 2 && Rc::strong_count(k2) == 2));
    /// ```
    #[cfg_attr(feature = "inline-more", inline)]
    pub fn into_keys(self) -> (&'a mut K1, &'a mut K2) {
        let &mut (ref mut k1, ref mut k2, _) = unsafe { self.data_bucket.as_mut() };
        (k1, k2)
    }

    /// Gets a reference to the value in the entry.
    ///
    /// # Examples
    ///
    /// ```
    /// use core::hash::{BuildHasher, Hash};
    /// use double_map::shash_map::{DoubleMap, RawEntryMut};
    ///
    /// fn compute_hash<K: Hash + ?Sized, S: BuildHasher>(hash_builder: &S, key: &K) -> u64 {
    ///     use core::hash::Hasher;
    ///     let mut state = hash_builder.build_hasher();
    ///     key.hash(&mut state);
    ///     state.finish()
    /// }
    ///
    /// let mut map: DoubleMap<&str, u32, u32> =
    ///     [("first", 11, 100), ("second", 22, 200), ("third", 33, 300)].into();
    ///
    /// match map.raw_entry_mut().from_keys(&"first", &11) {
    ///     Ok(RawEntryMut::Occupied(o)) => assert_eq!(o.get(), &100),
    ///     _ => panic!(),
    /// }
    ///
    /// let hash1 = compute_hash(map.hasher(), &"second");
    /// let hash2 = compute_hash(map.hasher(), &22);
    /// match map
    ///     .raw_entry_mut()
    ///     .from_keys_hashed_nocheck(hash1, &"second", hash2, &22)
    /// {
    ///     Ok(RawEntryMut::Occupied(o)) => assert_eq!(o.get(), &200),
    ///     _ => panic!(),
    /// }
    ///
    /// let hash1 = compute_hash(map.hasher(), &"third");
    /// let hash2 = compute_hash(map.hasher(), &33);
    /// match map
    ///     .raw_entry_mut()
    ///     .from_hashes(hash1, |q| *q == "third", hash2, |q| *q == 33)
    /// {
    ///     Ok(RawEntryMut::Occupied(o)) => assert_eq!(o.get(), &300),
    ///     _ => panic!(),
    /// }
    /// ```
    #[cfg_attr(feature = "inline-more", inline)]
    pub fn get(&self) -> &V {
        unsafe { &self.data_bucket.as_ref().2 }
    }

    /// Converts the RawOccupiedEntryMut into a mutable reference
    /// to the value in the entry with a lifetime bound to the map
    /// itself.
    ///
    /// # Examples
    ///
    /// ```
    /// use double_map::shash_map::{DoubleMap, RawEntryMut};
    ///
    /// let mut map: DoubleMap<&str, u32, u32> = [("a", 10, 100), ("b", 20, 200)].into();
    ///
    /// let value: &mut u32;
    ///
    /// match map.raw_entry_mut().from_keys(&"a", &10) {
    ///     Ok(RawEntryMut::Occupied(o)) => value = o.into_mut(),
    ///     _ => panic!(),
    /// }
    /// *value += 900;
    /// assert_eq!(map[&"a"], 1000);
    /// ```
    #[cfg_attr(feature = "inline-more", inline)]
    pub fn into_mut(self) -> &'a mut V {
        unsafe { &mut self.data_bucket.as_mut().2 }
    }

    /// Gets a mutable reference to the value in the entry.
    ///
    /// # Examples
    ///
    /// ```
    /// use double_map::shash_map::{DoubleMap, RawEntryMut};
    ///
    /// let mut map: DoubleMap<&str, u32, u32> = [("a", 10, 100), ("b", 20, 200)].into();
    ///
    /// match map.raw_entry_mut().from_keys(&"a", &10) {
    ///     Ok(RawEntryMut::Occupied(mut o)) => *o.get_mut() += 900,
    ///     _ => panic!(),
    /// }
    /// assert_eq!(map[&"a"], 1000);
    /// ```
    #[cfg_attr(feature = "inline-more", inline)]
    pub fn get_mut(&mut self) -> &mut V {
        unsafe { &mut self.data_bucket.as_mut().2 }
    }

    /// Gets a reference to the keys and value in the entry.
    ///
    /// # Examples
    ///
    /// ```
    /// use double_map::shash_map::{DoubleMap, RawEntryMut};
    ///
    /// let mut map: DoubleMap<&str, u32, u32> = [("a", 10, 100), ("b", 20, 200)].into();
    ///
    /// match map.raw_entry_mut().from_keys(&"a", &10) {
    ///     Ok(RawEntryMut::Occupied(o)) => assert_eq!(o.get_keys_value(), (&"a", &10, &100)),
    ///     _ => panic!(),
    /// }
    /// assert_eq!(map[&"a"], 100);
    /// ```
    #[cfg_attr(feature = "inline-more", inline)]
    pub fn get_keys_value(&self) -> (&K1, &K2, &V) {
        unsafe {
            let &(ref key1, ref key2, ref value) = self.data_bucket.as_ref();
            (key1, key2, value)
        }
    }

    /// Gets a mutable reference to the keys and value in the entry.
    ///
    /// # Examples
    ///
    /// ```
    /// use core::hash::{BuildHasher, Hash};
    /// use double_map::shash_map::{DoubleMap, RawEntryMut};
    /// use std::rc::Rc;
    ///
    /// fn compute_hash<K: Hash + ?Sized, S: BuildHasher>(hash_builder: &S, key: &K) -> u64 {
    ///     use core::hash::Hasher;
    ///     let mut state = hash_builder.build_hasher();
    ///     key.hash(&mut state);
    ///     state.finish()
    /// }
    ///
    /// let mut map = DoubleMap::<Rc<&str>, Rc<i32>, usize>::new();
    ///
    /// let array = ["a1", "b2", "c3", "d4", "e5", "f6", "g7", "h8", "i9"];
    /// let keys_vec_one: Vec<_> = array
    ///     .iter()
    ///     .zip(1..=9)
    ///     .into_iter()
    ///     .map(|(k1, k2)| (Rc::new(*k1), Rc::new(k2 * 512)))
    ///     .collect();
    /// let keys_vec_two: Vec<_> = array
    ///     .iter()
    ///     .zip(1..=9)
    ///     .into_iter()
    ///     .map(|(k1, k2)| (Rc::new(*k1), Rc::new(k2 * 512)))
    ///     .collect();
    ///
    /// for (k1, k2, v) in keys_vec_one
    ///     .iter()
    ///     .enumerate()
    ///     .map(|(i, (k1, k2))| (k1, k2, (i + 1) * 100))
    /// {
    ///     map.insert(k1.clone(), k2.clone(), v);
    /// }
    /// assert!(keys_vec_one
    ///     .iter()
    ///     .all(|(k1, k2)| Rc::strong_count(k1) == 2 && Rc::strong_count(k2) == 2));
    /// assert!(keys_vec_two
    ///     .iter()
    ///     .all(|(k1, k2)| Rc::strong_count(k1) == 1 && Rc::strong_count(k2) == 1));
    ///
    /// for (i, (k1, k2)) in keys_vec_two.iter().enumerate() {
    ///     match i {
    ///         1..=3 => match map.raw_entry_mut().from_keys(k1, k2) {
    ///             Ok(RawEntryMut::Occupied(mut o)) => {
    ///                 let (k1_in, k2_in, v) = o.get_keys_value_mut();
    ///                 *k1_in = k1.clone();
    ///                 *k2_in = k2.clone();
    ///                 *v *= 10;
    ///             }
    ///             _ => panic!(),
    ///         },
    ///         4..=6 => {
    ///             let hash1 = compute_hash(map.hasher(), k1);
    ///             let hash2 = compute_hash(map.hasher(), k2);
    ///             match map
    ///                 .raw_entry_mut()
    ///                 .from_keys_hashed_nocheck(hash1, k1, hash2, k2)
    ///             {
    ///                 Ok(RawEntryMut::Occupied(mut o)) => {
    ///                     let (k1_in, k2_in, v) = o.get_keys_value_mut();
    ///                     *k1_in = k1.clone();
    ///                     *k2_in = k2.clone();
    ///                     *v *= 10;
    ///                 }
    ///                 _ => panic!(),
    ///             }
    ///         }
    ///         _ => {
    ///             let hash1 = compute_hash(map.hasher(), k1);
    ///             let hash2 = compute_hash(map.hasher(), k2);
    ///             match map
    ///                 .raw_entry_mut()
    ///                 .from_hashes(hash1, |q| q == k1, hash2, |q| q == k2)
    ///             {
    ///                 Ok(RawEntryMut::Occupied(mut o)) => {
    ///                     let (k1_in, k2_in, v) = o.get_keys_value_mut();
    ///                     *k1_in = k1.clone();
    ///                     *k2_in = k2.clone();
    ///                     *v *= 10;
    ///                 }
    ///                 _ => panic!(),
    ///             }
    ///         }
    ///     }
    /// }
    /// assert!(keys_vec_one
    ///     .iter()
    ///     .all(|(k1, k2)| Rc::strong_count(k1) == 1 && Rc::strong_count(k2) == 1));
    /// assert!(keys_vec_two
    ///     .iter()
    ///     .all(|(k1, k2)| Rc::strong_count(k1) == 2 && Rc::strong_count(k2) == 2));
    /// let mut vec: Vec<_> = map.into_values().collect();
    /// vec.sort_unstable();
    /// assert_eq!(vec, [1000, 2000, 3000, 4000, 5000, 6000, 7000, 8000, 9000])
    /// ```
    #[cfg_attr(feature = "inline-more", inline)]
    pub fn get_keys_value_mut(&mut self) -> (&mut K1, &mut K2, &mut V) {
        unsafe {
            let (key1, key2, value) = self.data_bucket.as_mut();
            (key1, key2, value)
        }
    }

    /// Converts the RawOccupiedEntryMut into a mutable reference to the keys
    /// and value in the entry with a lifetime bound to the map itself.
    ///
    /// # Examples
    ///
    /// ```
    /// use core::hash::{BuildHasher, Hash};
    /// use double_map::shash_map::{DoubleMap, RawEntryMut};
    /// use std::rc::Rc;
    ///
    /// fn compute_hash<K: Hash + ?Sized, S: BuildHasher>(hash_builder: &S, key: &K) -> u64 {
    ///     use core::hash::Hasher;
    ///     let mut state = hash_builder.build_hasher();
    ///     key.hash(&mut state);
    ///     state.finish()
    /// }
    ///
    /// let mut map = DoubleMap::<Rc<&str>, Rc<i32>, usize>::new();
    ///
    /// let array = [
    ///     "a11", "b22", "c33", "d44", "e55", "f66", "g77", "h88", "i99",
    /// ];
    /// let keys_vec_one: Vec<_> = array
    ///     .iter()
    ///     .zip(1..=9)
    ///     .into_iter()
    ///     .map(|(k1, k2)| (Rc::new(*k1), Rc::new(k2 * 512 / 7)))
    ///     .collect();
    /// let keys_vec_two: Vec<_> = array
    ///     .iter()
    ///     .zip(1..=9)
    ///     .into_iter()
    ///     .map(|(k1, k2)| (Rc::new(*k1), Rc::new(k2 * 512 / 7)))
    ///     .collect();
    ///
    /// for (k1, k2, v) in keys_vec_one
    ///     .iter()
    ///     .enumerate()
    ///     .map(|(i, (k1, k2))| (k1, k2, (i + 1) * 100))
    /// {
    ///     map.insert(k1.clone(), k2.clone(), v);
    /// }
    /// assert!(keys_vec_one
    ///     .iter()
    ///     .all(|(k1, k2)| Rc::strong_count(k1) == 2 && Rc::strong_count(k2) == 2));
    /// assert!(keys_vec_two
    ///     .iter()
    ///     .all(|(k1, k2)| Rc::strong_count(k1) == 1 && Rc::strong_count(k2) == 1));
    ///
    /// for (i, (k1, k2)) in keys_vec_two.iter().enumerate() {
    ///     let inside_key1: &mut Rc<&str>;
    ///     let inside_key2: &mut Rc<i32>;
    ///     let inside_value: &mut usize;
    ///     match i {
    ///         1..=3 => match map.raw_entry_mut().from_keys(k1, k2) {
    ///             Ok(RawEntryMut::Occupied(o)) => {
    ///                 let (in_key1, in_key2, in_value) = o.into_keys_value();
    ///                 inside_key1 = in_key1;
    ///                 inside_key2 = in_key2;
    ///                 inside_value = in_value;
    ///             }
    ///             _ => panic!(),
    ///         },
    ///         4..=6 => {
    ///             let hash1 = compute_hash(map.hasher(), k1);
    ///             let hash2 = compute_hash(map.hasher(), k2);
    ///             match map
    ///                 .raw_entry_mut()
    ///                 .from_keys_hashed_nocheck(hash1, k1, hash2, k2)
    ///             {
    ///                 Ok(RawEntryMut::Occupied(o)) => {
    ///                     let (in_key1, in_key2, in_value) = o.into_keys_value();
    ///                     inside_key1 = in_key1;
    ///                     inside_key2 = in_key2;
    ///                     inside_value = in_value;
    ///                 }
    ///                 _ => panic!(),
    ///             }
    ///         }
    ///         _ => {
    ///             let hash1 = compute_hash(map.hasher(), k1);
    ///             let hash2 = compute_hash(map.hasher(), k2);
    ///             match map
    ///                 .raw_entry_mut()
    ///                 .from_hashes(hash1, |q| q == k1, hash2, |q| q == k2)
    ///             {
    ///                 Ok(RawEntryMut::Occupied(o)) => {
    ///                     let (in_key1, in_key2, in_value) = o.into_keys_value();
    ///                     inside_key1 = in_key1;
    ///                     inside_key2 = in_key2;
    ///                     inside_value = in_value;
    ///                 }
    ///                 _ => panic!(),
    ///             }
    ///         }
    ///     }
    ///     *inside_key1 = k1.clone();
    ///     *inside_key2 = k2.clone();
    ///     *inside_value *= 10;
    /// }
    /// assert!(keys_vec_one
    ///     .iter()
    ///     .all(|(k1, k2)| Rc::strong_count(k1) == 1 && Rc::strong_count(k2) == 1));
    /// assert!(keys_vec_two
    ///     .iter()
    ///     .all(|(k1, k2)| Rc::strong_count(k1) == 2 && Rc::strong_count(k2) == 2));
    /// let mut vec: Vec<_> = map.into_values().collect();
    /// vec.sort_unstable();
    /// assert_eq!(vec, [1000, 2000, 3000, 4000, 5000, 6000, 7000, 8000, 9000])
    /// ```
    #[cfg_attr(feature = "inline-more", inline)]
    pub fn into_keys_value(self) -> (&'a mut K1, &'a mut K2, &'a mut V) {
        unsafe {
            let (key1, key2, value) = self.data_bucket.as_mut();
            (key1, key2, value)
        }
    }

    /// Sets the value of the entry, and returns the entry's old value.
    ///
    /// # Examples
    ///
    /// ```
    /// use core::hash::{BuildHasher, Hash};
    /// use double_map::shash_map::{DoubleMap, RawEntryMut};
    ///
    /// fn compute_hash<K: Hash + ?Sized, S: BuildHasher>(hash_builder: &S, key: &K) -> u64 {
    ///     use core::hash::Hasher;
    ///     let mut state = hash_builder.build_hasher();
    ///     key.hash(&mut state);
    ///     state.finish()
    /// }
    ///
    /// let mut map: DoubleMap<&str, u32, u32> =
    ///     [("a1", 51, 100), ("a2", 52, 200), ("a3", 53, 300)].into();
    ///
    /// match map.raw_entry_mut().from_keys(&"a1", &51) {
    ///     Ok(RawEntryMut::Occupied(mut o)) => assert_eq!(o.insert(10), 100),
    ///     _ => panic!(),
    /// }
    ///
    /// let hash1 = compute_hash(map.hasher(), &"a2");
    /// let hash2 = compute_hash(map.hasher(), &52);
    /// match map
    ///     .raw_entry_mut()
    ///     .from_keys_hashed_nocheck(hash1, &"a2", hash2, &52)
    /// {
    ///     Ok(RawEntryMut::Occupied(mut o)) => assert_eq!(o.insert(20), 200),
    ///     _ => panic!(),
    /// }
    ///
    /// let hash1 = compute_hash(map.hasher(), &"a3");
    /// let hash2 = compute_hash(map.hasher(), &53);
    /// match map
    ///     .raw_entry_mut()
    ///     .from_hashes(hash1, |q| *q == "a3", hash2, |q| *q == 53)
    /// {
    ///     Ok(RawEntryMut::Occupied(mut o)) => assert_eq!(o.insert(30), 300),
    ///     _ => panic!(),
    /// }
    /// assert_eq!(map.len(), 3);
    /// let mut vec: Vec<_> = map.into_values().collect();
    /// vec.sort_unstable();
    /// assert_eq!(vec, [10, 20, 30]);
    /// ```
    #[cfg_attr(feature = "inline-more", inline)]
    pub fn insert(&mut self, value: V) -> V {
        mem::replace(self.get_mut(), value)
    }

    /// Sets the `K1` of the entry, and returns the entry's old key.
    ///
    /// # Examples
    ///
    /// ```
    /// use double_map::shash_map::{DoubleMap, RawEntryMut};
    /// use std::rc::Rc;
    ///
    /// let key_one = Rc::new("a");
    /// let key_two = Rc::new("a");
    ///
    /// let mut map: DoubleMap<Rc<&str>, u32, u32> = DoubleMap::new();
    /// map.insert(key_one.clone(), 10, 100);
    ///
    /// assert_eq!(map[&key_one], 100);
    /// assert!(Rc::strong_count(&key_one) == 2 && Rc::strong_count(&key_two) == 1);
    ///
    /// match map.raw_entry_mut().from_keys(&key_one, &10) {
    ///     Ok(RawEntryMut::Occupied(mut o)) => {
    ///         let old_key = o.insert_key1(key_two.clone());
    ///         assert!(Rc::ptr_eq(&old_key, &key_one));
    ///     }
    ///     _ => panic!(),
    /// }
    /// assert_eq!(map[&key_two], 100);
    /// assert!(Rc::strong_count(&key_one) == 1 && Rc::strong_count(&key_two) == 2);
    /// ```
    #[cfg_attr(feature = "inline-more", inline)]
    pub fn insert_key1(&mut self, k1: K1) -> K1 {
        mem::replace(self.key1_mut(), k1)
    }

    /// Sets the `K2` of the entry, and returns the entry's old key.
    ///
    /// # Examples
    ///
    /// ```
    /// use double_map::shash_map::{DoubleMap, RawEntryMut};
    /// use std::rc::Rc;
    ///
    /// let key_one = Rc::new(10);
    /// let key_two = Rc::new(10);
    ///
    /// let mut map: DoubleMap<&str, Rc<u32>, u32> = DoubleMap::new();
    /// map.insert("a", key_one.clone(), 100);
    ///
    /// assert_eq!(map.get_key2(&key_one), Some(&100));
    /// assert!(Rc::strong_count(&key_one) == 2 && Rc::strong_count(&key_two) == 1);
    ///
    /// match map.raw_entry_mut().from_keys("a", &key_one) {
    ///     Ok(RawEntryMut::Occupied(mut o)) => {
    ///         let old_key = o.insert_key2(key_two.clone());
    ///         assert!(Rc::ptr_eq(&old_key, &key_one));
    ///     }
    ///     _ => panic!(),
    /// }
    /// assert_eq!(map.get_key2(&key_two), Some(&100));
    /// assert!(Rc::strong_count(&key_one) == 1 && Rc::strong_count(&key_two) == 2);
    /// ```
    #[cfg_attr(feature = "inline-more", inline)]
    pub fn insert_key2(&mut self, k2: K2) -> K2 {
        mem::replace(self.key2_mut(), k2)
    }

    /// Sets the `K1` and `K2` of the entry, and returns the entry's old keys.
    ///
    /// # Examples
    ///
    /// ```
    /// use double_map::shash_map::{DoubleMap, RawEntryMut};
    /// use std::rc::Rc;
    ///
    /// let key1_one = Rc::new("a");
    /// let key1_two = Rc::new("a");
    /// let key2_one = Rc::new(10);
    /// let key2_two = Rc::new(10);
    ///
    /// let mut map: DoubleMap<Rc<&str>, Rc<u32>, u32> = DoubleMap::new();
    /// map.insert(key1_one.clone(), key2_one.clone(), 100);
    ///
    /// assert_eq!(map[&key1_one], 100);
    /// assert!(Rc::strong_count(&key1_one) == 2 && Rc::strong_count(&key1_two) == 1);
    /// assert!(Rc::strong_count(&key2_one) == 2 && Rc::strong_count(&key2_two) == 1);
    ///
    /// match map.raw_entry_mut().from_keys(&key1_one, &key2_one) {
    ///     Ok(RawEntryMut::Occupied(mut o)) => {
    ///         let (old_key1, old_key2) = o.insert_keys(key1_two.clone(), key2_two.clone());
    ///         assert!(Rc::ptr_eq(&old_key1, &key1_one) && Rc::ptr_eq(&old_key2, &key2_one));
    ///     }
    ///     _ => panic!(),
    /// }
    /// assert_eq!(map[&key1_two], 100);
    /// assert!(Rc::strong_count(&key1_one) == 1 && Rc::strong_count(&key1_two) == 2);
    /// assert!(Rc::strong_count(&key2_one) == 1 && Rc::strong_count(&key2_two) == 2);
    /// ```
    #[cfg_attr(feature = "inline-more", inline)]
    pub fn insert_keys(&mut self, k1: K1, k2: K2) -> (K1, K2) {
        let (k1_dest, k2_dest, _) = unsafe { self.data_bucket.as_mut() };
        let key1_old = mem::replace(k1_dest, k1);
        let key2_old = mem::replace(k2_dest, k2);

        (key1_old, key2_old)
    }

    /// Takes the value out of the entry, and returns it.
    ///
    /// # Examples
    ///
    /// ```
    /// use double_map::shash_map::{DoubleMap, RawEntryMut};
    ///
    /// let mut map: DoubleMap<&str, u32, u32> = [("a", 10, 100), ("b", 20, 200)].into();
    ///
    /// match map.raw_entry_mut().from_keys(&"a", &10) {
    ///     Ok(RawEntryMut::Occupied(o)) => assert_eq!(o.remove(), 100),
    ///     _ => panic!(),
    /// }
    /// assert_eq!(map.get_key1(&"a"), None);
    /// ```
    #[cfg_attr(feature = "inline-more", inline)]
    pub fn remove(self) -> V {
        self.remove_entry().2
    }

    /// Take the ownership of the keys and value from the map.
    ///
    /// # Examples
    ///
    /// ```
    /// use double_map::shash_map::{DoubleMap, RawEntryMut};
    ///
    /// let mut map: DoubleMap<&str, u32, u32> = [("a", 10, 100), ("b", 20, 200)].into();
    ///
    /// match map.raw_entry_mut().from_keys(&"a", &10) {
    ///     Ok(RawEntryMut::Occupied(o)) => assert_eq!(o.remove_entry(), ("a", 10, 100)),
    ///     _ => panic!(),
    /// }
    /// assert_eq!(map.get_key1(&"a"), None);
    /// ```
    #[cfg_attr(feature = "inline-more", inline)]
    pub fn remove_entry(self) -> (K1, K2, V) {
        unsafe { self.table.remove(self.pointer_bucket) }
    }

    /// Provides shared access to the `K1` key and owned access to the value of
    /// the entry and allows to replace or remove it based on the
    /// value of the returned option.
    ///
    /// # Examples
    ///
    /// ```
    /// use double_map::shash_map::{DoubleMap, RawEntryMut};
    ///
    /// let mut map: DoubleMap<&str, u32, u32> = [("a", 10, 100), ("b", 20, 200)].into();
    ///
    /// let raw_entry = match map.raw_entry_mut().from_keys(&"a", &10) {
    ///     Ok(RawEntryMut::Occupied(o)) => o.replace_entry_with_key1(|k1, v| {
    ///         assert_eq!(k1, &"a");
    ///         assert_eq!(v, 100);
    ///         Some(v + 900)
    ///     }),
    ///     _ => panic!(),
    /// };
    /// let raw_entry = match raw_entry {
    ///     RawEntryMut::Occupied(o) => o.replace_entry_with_key1(|k1, v| {
    ///         assert_eq!(k1, &"a");
    ///         assert_eq!(v, 1000);
    ///         None
    ///     }),
    ///     _ => panic!(),
    /// };
    /// match raw_entry {
    ///     RawEntryMut::Vacant(_) => {}
    ///     RawEntryMut::Occupied(_) => panic!(),
    /// };
    /// assert_eq!(map.get_key1(&"a"), None);
    /// assert_eq!(map.get_key2(&10), None);
    /// assert_eq!(map.get_keys(&"a", &10), None);
    /// ```
    #[cfg_attr(feature = "inline-more", inline)]
    pub fn replace_entry_with_key1<F>(self, f: F) -> RawEntryMut<'a, K1, K2, V, S, A>
    where
        F: FnOnce(&K1, V) -> Option<V>,
    {
        unsafe {
            let still_occupied = self
                .table
                .replace_data_with(self.pointer_bucket.clone(), |(key1, key2, value)| {
                    f(&key1, value).map(|new_value| (key1, key2, new_value))
                });

            if still_occupied {
                RawEntryMut::Occupied(self)
            } else {
                RawEntryMut::Vacant(RawVacantEntryMut {
                    table: self.table,
                    hash_builder: self.hash_builder,
                })
            }
        }
    }

    /// Provides shared access to the `K2` key and owned access to the value of
    /// the entry and allows to replace or remove it based on the
    /// value of the returned option.
    ///
    /// # Examples
    ///
    /// ```
    /// use double_map::shash_map::{DoubleMap, RawEntryMut};
    ///
    /// let mut map: DoubleMap<&str, u32, u32> = [("one", 11, 100), ("two", 22, 200)].into();
    ///
    /// let raw_entry = match map.raw_entry_mut().from_keys(&"two", &22) {
    ///     Ok(RawEntryMut::Occupied(o)) => o.replace_entry_with_key2(|k2, v| {
    ///         assert_eq!(k2, &22);
    ///         assert_eq!(v, 200);
    ///         Some(v + 900)
    ///     }),
    ///     _ => panic!(),
    /// };
    /// let raw_entry = match raw_entry {
    ///     RawEntryMut::Occupied(o) => o.replace_entry_with_key2(|k2, v| {
    ///         assert_eq!(k2, &22);
    ///         assert_eq!(v, 1100);
    ///         None
    ///     }),
    ///     _ => panic!(),
    /// };
    /// match raw_entry {
    ///     RawEntryMut::Vacant(_) => {}
    ///     RawEntryMut::Occupied(_) => panic!(),
    /// };
    /// assert_eq!(map.get_key1(&"two"), None);
    /// assert_eq!(map.get_key2(&22), None);
    /// assert_eq!(map.get_keys(&"two", &22), None);
    /// ```
    #[cfg_attr(feature = "inline-more", inline)]
    pub fn replace_entry_with_key2<F>(self, f: F) -> RawEntryMut<'a, K1, K2, V, S, A>
    where
        F: FnOnce(&K2, V) -> Option<V>,
    {
        unsafe {
            let still_occupied = self
                .table
                .replace_data_with(self.pointer_bucket.clone(), |(key1, key2, value)| {
                    f(&key2, value).map(|new_value| (key1, key2, new_value))
                });

            if still_occupied {
                RawEntryMut::Occupied(self)
            } else {
                RawEntryMut::Vacant(RawVacantEntryMut {
                    table: self.table,
                    hash_builder: self.hash_builder,
                })
            }
        }
    }

    /// Provides shared access to the `K1` and `K2` keys and owned access
    /// to the value of the entry and allows to replace or remove it based
    /// on the value of the returned option.
    ///
    /// # Examples
    ///
    /// ```
    /// use double_map::shash_map::{DoubleMap, RawEntryMut};
    ///
    /// let mut map: DoubleMap<&str, u32, u32> = [("first", 17, 100), ("second", 27, 200)].into();
    ///
    /// let raw_entry = match map.raw_entry_mut().from_keys(&"first", &17) {
    ///     Ok(RawEntryMut::Occupied(o)) => o.replace_entry_with_keys(|k1, k2, v| {
    ///         assert_eq!(k1, &"first");
    ///         assert_eq!(k2, &17);
    ///         assert_eq!(v, 100);
    ///         Some(v + 900)
    ///     }),
    ///     _ => panic!(),
    /// };
    /// let raw_entry = match raw_entry {
    ///     RawEntryMut::Occupied(o) => o.replace_entry_with_keys(|k1, k2, v| {
    ///         assert_eq!(k1, &"first");
    ///         assert_eq!(k2, &17);
    ///         assert_eq!(v, 1000);
    ///         None
    ///     }),
    ///     _ => panic!(),
    /// };
    /// match raw_entry {
    ///     RawEntryMut::Vacant(_) => {}
    ///     RawEntryMut::Occupied(_) => panic!(),
    /// };
    /// assert_eq!(map.get_key1(&"first"), None);
    /// assert_eq!(map.get_key2(&17), None);
    /// assert_eq!(map.get_keys(&"first", &17), None);
    /// ```
    #[cfg_attr(feature = "inline-more", inline)]
    pub fn replace_entry_with_keys<F>(self, f: F) -> RawEntryMut<'a, K1, K2, V, S, A>
    where
        F: FnOnce(&K1, &K2, V) -> Option<V>,
    {
        unsafe {
            let still_occupied =
                self.table
                    .replace_data_with(self.pointer_bucket.clone(), |(key1, key2, value)| {
                        f(&key1, &key2, value).map(|new_value| (key1, key2, new_value))
                    });

            if still_occupied {
                RawEntryMut::Occupied(self)
            } else {
                RawEntryMut::Vacant(RawVacantEntryMut {
                    table: self.table,
                    hash_builder: self.hash_builder,
                })
            }
        }
    }
}

/// A view into a single entry in a map, which may either be vacant or occupied.
///
/// This is a lower-level version of [`Entry`].
///
/// This `enum` is constructed through the [`raw_entry_mut`] method on [`DoubleMap`],
/// then calling one of the methods of that [`RawEntryBuilderMut`].
///
/// [`DoubleMap`]: struct.DoubleMap.html
/// [`Entry`]: enum.Entry.html
/// [`raw_entry_mut`]: struct.DoubleMap.html#method.raw_entry_mut
/// [`RawEntryBuilderMut`]: struct.RawEntryBuilderMut.html
///
/// # Examples
///
/// ```
/// use core::hash::{BuildHasher, Hash};
/// use double_map::shash_map::{DoubleMap, RawEntryMut, RawOccupiedEntryMut};
///
/// let mut map = DoubleMap::new();
/// map.extend([('a', 1, 100), ('b', 2, 200), ('c', 3, 300)]);
/// assert_eq!(map.len(), 3);
///
/// fn compute_hash<K: Hash + ?Sized, S: BuildHasher>(hash_builder: &S, key: &K) -> u64 {
///     use core::hash::Hasher;
///     let mut state = hash_builder.build_hasher();
///     key.hash(&mut state);
///     state.finish()
/// }
///
/// // Existing key (insert)
/// let raw: RawEntryMut<_, _, _, _> = map.raw_entry_mut().from_keys(&'a', &1).unwrap();
/// let _raw_o: RawOccupiedEntryMut<_, _, _, _> = raw.insert('a', 1, 10);
/// assert_eq!(map.len(), 3);
///
/// // Nonexistent key (insert)
/// map.raw_entry_mut()
///     .from_keys(&'d', &4)
///     .unwrap()
///     .insert('d', 4, 40);
/// assert_eq!(map.len(), 4);
///
/// // Existing key (or_insert)
/// let hash1 = compute_hash(map.hasher(), &'b');
/// let hash2 = compute_hash(map.hasher(), &2);
/// let kv = map
///     .raw_entry_mut()
///     .from_keys_hashed_nocheck(hash1, &'b', hash2, &2)
///     .unwrap()
///     .or_insert('b', 2, 222);
/// assert_eq!(kv, (&mut 'b', &mut 2, &mut 200));
/// *kv.2 = 20;
/// assert_eq!(map.len(), 4);
///
/// // Nonexistent key (or_insert)
/// let hash1 = compute_hash(map.hasher(), &'e');
/// let hash2 = compute_hash(map.hasher(), &5);
/// let kv = map
///     .raw_entry_mut()
///     .from_keys_hashed_nocheck(hash1, &'e', hash2, &5)
///     .unwrap()
///     .or_insert('e', 5, 50);
/// assert_eq!(kv, (&mut 'e', &mut 5, &mut 50));
/// assert_eq!(map.len(), 5);
///
/// // Existing key (or_insert_with)
/// let hash1 = compute_hash(map.hasher(), &'c');
/// let hash2 = compute_hash(map.hasher(), &3);
/// let kv = map
///     .raw_entry_mut()
///     .from_hashes(hash1, |q| q == &'c', hash2, |q| *q == 3)
///     .unwrap()
///     .or_insert_with(|| ('c', 3, 333));
/// assert_eq!(kv, (&mut 'c', &mut 3, &mut 300));
/// *kv.2 = 30;
/// assert_eq!(map.len(), 5);
///
/// // Nonexistent key (or_insert_with)
/// let hash1 = compute_hash(map.hasher(), &'f');
/// let hash2 = compute_hash(map.hasher(), &6);
/// let kv = map
///     .raw_entry_mut()
///     .from_hashes(hash1, |q| q == &'f', hash2, |q| *q == 6)
///     .unwrap()
///     .or_insert_with(|| ('f', 6, 60));
/// assert_eq!(kv, (&mut 'f', &mut 6, &mut 60));
/// assert_eq!(map.len(), 6);
///
/// println!("Our DoubleMap: {:?}", map);
///
/// let mut vec: Vec<_> = map.into_iter().collect();
/// // The `Iter` iterator produces items in arbitrary order, so the
/// // items must be sorted to test them against a sorted array.
/// vec.sort_unstable();
/// assert_eq!(
///     vec,
///     [
///         ('a', 1, 10),
///         ('b', 2, 20),
///         ('c', 3, 30),
///         ('d', 4, 40),
///         ('e', 5, 50),
///         ('f', 6, 60)
///     ]
/// );
/// ```
pub enum RawEntryMut<'a, K1, K2, V, S, A: Allocator + Clone = Global> {
    /// An occupied entry.
    ///
    /// # Examples
    ///
    /// ```
    /// use double_map::shash_map::{DoubleMap, RawEntryMut};
    /// let mut map: DoubleMap<_, _, _> = [("a", 10, 100), ("b", 20, 200)].into();
    ///
    /// match map.raw_entry_mut().from_keys(&"a", &10) {
    ///     Ok(RawEntryMut::Occupied(_)) => {}
    ///     _ => panic!(),
    /// }
    /// ```
    Occupied(RawOccupiedEntryMut<'a, K1, K2, V, S, A>),

    /// A vacant entry.
    ///
    /// # Examples
    ///
    /// ```
    /// use double_map::shash_map::{DoubleMap, RawEntryMut};
    /// let mut map: DoubleMap<&str, i32, i32> = DoubleMap::new();
    ///
    /// match map.raw_entry_mut().from_keys(&"a", &10) {
    ///     Ok(RawEntryMut::Vacant(_)) => {}
    ///     _ => panic!(),
    /// }
    /// ```
    Vacant(RawVacantEntryMut<'a, K1, K2, V, S, A>),
}

impl<K1: Debug, K2: Debug, V: Debug, S> Debug for RawEntryMut<'_, K1, K2, V, S> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match *self {
            RawEntryMut::Vacant(ref v) => f.debug_tuple("RawEntry").field(v).finish(),
            RawEntryMut::Occupied(ref o) => f.debug_tuple("RawEntry").field(o).finish(),
        }
    }
}

impl<'a, K1, K2, V, S, A: Allocator + Clone> RawEntryMut<'a, K1, K2, V, S, A> {
    /// Sets the value of the entry, and returns a RawOccupiedEntryMut.
    ///
    /// # Examples
    ///
    /// ```
    /// use double_map::DoubleMap;
    ///
    /// let mut map: DoubleMap<&str, u32, u32> = DoubleMap::new();
    /// let entry = map
    ///     .raw_entry_mut()
    ///     .from_keys("horseyland", &1)
    ///     .unwrap()
    ///     .insert("horseyland", 1, 37);
    ///
    /// assert_eq!(entry.remove_entry(), ("horseyland", 1, 37));
    /// assert!(map.is_empty());
    /// ```
    #[cfg_attr(feature = "inline-more", inline)]
    pub fn insert(self, k1: K1, k2: K2, value: V) -> RawOccupiedEntryMut<'a, K1, K2, V, S, A>
    where
        K1: Hash,
        K2: Hash,
        S: BuildHasher,
    {
        match self {
            RawEntryMut::Occupied(mut entry) => {
                entry.insert(value);
                entry
            }
            RawEntryMut::Vacant(entry) => entry.insert_entry(k1, k2, value),
        }
    }

    /// Ensures a value is in the entry by inserting the default if empty, and returns
    /// mutable references to the keys and value in the entry.
    ///
    /// # Examples
    ///
    /// ```
    /// use double_map::DoubleMap;
    ///
    /// let mut map: DoubleMap<&str, u32, u32> = DoubleMap::new();
    ///
    /// map.raw_entry_mut()
    ///     .from_keys("poneyland", &11)
    ///     .unwrap()
    ///     .or_insert("poneyland", 11, 30);
    /// assert_eq!(map["poneyland"], 30);
    ///
    /// *map.raw_entry_mut()
    ///     .from_keys("poneyland", &11)
    ///     .unwrap()
    ///     .or_insert("poneyland", 11, 99)
    ///     .2 *= 2;
    /// assert_eq!(map["poneyland"], 60);
    /// ```
    #[cfg_attr(feature = "inline-more", inline)]
    pub fn or_insert(
        self,
        default_k1: K1,
        default_k2: K2,
        default_val: V,
    ) -> (&'a mut K1, &'a mut K2, &'a mut V)
    where
        K1: Hash,
        K2: Hash,
        S: BuildHasher,
    {
        match self {
            RawEntryMut::Occupied(entry) => entry.into_keys_value(),
            RawEntryMut::Vacant(entry) => entry.insert(default_k1, default_k2, default_val),
        }
    }

    /// Ensures a value is in the entry by inserting the result of the default function if empty,
    /// and returns mutable references to the keys and value in the entry.
    ///
    /// # Examples
    ///
    /// ```
    /// use double_map::DoubleMap;
    ///
    /// let mut map: DoubleMap<&str, i128, String> = DoubleMap::new();
    ///
    /// let (_, _, v) = map
    ///     .raw_entry_mut()
    ///     .from_keys("poneyland", &10)
    ///     .unwrap()
    ///     .or_insert_with(|| ("poneyland", 10, "hoho".to_string()));
    /// v.push_str("ho");
    ///
    /// assert_eq!(map["poneyland"], "hohoho".to_string());
    /// ```
    #[cfg_attr(feature = "inline-more", inline)]
    pub fn or_insert_with<F>(self, default: F) -> (&'a mut K1, &'a mut K2, &'a mut V)
    where
        F: FnOnce() -> (K1, K2, V),
        K1: Hash,
        K2: Hash,
        S: BuildHasher,
    {
        match self {
            RawEntryMut::Occupied(entry) => entry.into_keys_value(),
            RawEntryMut::Vacant(entry) => {
                let (k1, k2, value) = default();
                entry.insert(k1, k2, value)
            }
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
    /// let mut map: DoubleMap<&str, i64, i128> = DoubleMap::new();
    ///
    /// map.raw_entry_mut()
    ///     .from_keys("poneyland", &10)
    ///     .unwrap()
    ///     .and_modify(|k1, k2, v| *v += (k1.chars().count() as i64 + *k2) as i128)
    ///     .or_insert("poneyland", 10, 42);
    /// assert_eq!(map["poneyland"], 42);
    ///
    /// map.raw_entry_mut()
    ///     .from_keys("poneyland", &10)
    ///     .unwrap()
    ///     .and_modify(|k1, k2, v| *v += (k1.chars().count() as i64 + *k2) as i128)
    ///     .or_insert("poneyland", 10, 0);
    /// assert_eq!(map["poneyland"], 61);
    /// ```
    #[cfg_attr(feature = "inline-more", inline)]
    pub fn and_modify<F>(self, f: F) -> Self
    where
        F: FnOnce(&mut K1, &mut K2, &mut V),
    {
        match self {
            RawEntryMut::Occupied(mut entry) => {
                {
                    let (k1, k2, v) = entry.get_keys_value_mut();
                    f(k1, k2, v);
                }
                RawEntryMut::Occupied(entry)
            }
            RawEntryMut::Vacant(entry) => RawEntryMut::Vacant(entry),
        }
    }

    /// Provides shared access to the first `K1` key and owned access to
    /// the value of an occupied entry and allows to replace or remove it
    /// based on the value of the returned option.
    ///
    /// # Examples
    ///
    /// ```
    /// use double_map::shash_map::{DoubleMap, RawEntryMut};
    ///
    /// let mut map: DoubleMap<&str, u32, u32> = DoubleMap::new();
    ///
    /// let entry = map
    ///     .raw_entry_mut()
    ///     .from_keys("poneyland", &10)
    ///     .unwrap()
    ///     .and_replace_entry_with_key1(|_k1, _v| panic!());
    ///
    /// match entry {
    ///     RawEntryMut::Vacant(_) => {}
    ///     RawEntryMut::Occupied(_) => panic!(),
    /// }
    ///
    /// map.insert("poneyland", 10, 42);
    ///
    /// let entry = map
    ///     .raw_entry_mut()
    ///     .from_keys("poneyland", &10)
    ///     .unwrap()
    ///     .and_replace_entry_with_key1(|k1, v| {
    ///         assert_eq!(k1, &"poneyland");
    ///         assert_eq!(v, 42);
    ///         Some(v + 1)
    ///     });
    ///
    /// match entry {
    ///     RawEntryMut::Occupied(e) => {
    ///         assert_eq!(e.key1(), &"poneyland");
    ///         assert_eq!(e.key2(), &10);
    ///         assert_eq!(e.get(), &43);
    ///     }
    ///     RawEntryMut::Vacant(_) => panic!(),
    /// }
    ///
    /// assert_eq!(map["poneyland"], 43);
    ///
    /// let entry = map
    ///     .raw_entry_mut()
    ///     .from_keys("poneyland", &10)
    ///     .unwrap()
    ///     .and_replace_entry_with_key1(|_k1, _v| None);
    ///
    /// match entry {
    ///     RawEntryMut::Vacant(_) => {}
    ///     RawEntryMut::Occupied(_) => panic!(),
    /// }
    ///
    /// assert!(!map.contains_key1("poneyland"));
    /// ```
    #[cfg_attr(feature = "inline-more", inline)]
    pub fn and_replace_entry_with_key1<F>(self, f: F) -> Self
    where
        F: FnOnce(&K1, V) -> Option<V>,
    {
        match self {
            RawEntryMut::Occupied(entry) => entry.replace_entry_with_key1(f),
            RawEntryMut::Vacant(_) => self,
        }
    }

    /// Provides shared access to the second `K2` key and owned access to
    /// the value of an occupied entry and allows to replace or remove it
    /// based on the value of the returned option.
    ///
    /// # Examples
    ///
    /// ```
    /// use double_map::shash_map::{DoubleMap, RawEntryMut};
    ///
    /// let mut map: DoubleMap<&str, u32, u32> = DoubleMap::new();
    ///
    /// let entry = map
    ///     .raw_entry_mut()
    ///     .from_keys("poneyland", &10)
    ///     .unwrap()
    ///     .and_replace_entry_with_key2(|_k2, _v| panic!());
    ///
    /// match entry {
    ///     RawEntryMut::Vacant(_) => {}
    ///     RawEntryMut::Occupied(_) => panic!(),
    /// }
    ///
    /// map.insert("poneyland", 10, 42);
    ///
    /// let entry = map
    ///     .raw_entry_mut()
    ///     .from_keys("poneyland", &10)
    ///     .unwrap()
    ///     .and_replace_entry_with_key2(|k2, v| {
    ///         assert_eq!(k2, &10);
    ///         assert_eq!(v, 42);
    ///         Some(v + 1)
    ///     });
    ///
    /// match entry {
    ///     RawEntryMut::Occupied(e) => {
    ///         assert_eq!(e.key1(), &"poneyland");
    ///         assert_eq!(e.key2(), &10);
    ///         assert_eq!(e.get(), &43);
    ///     }
    ///     RawEntryMut::Vacant(_) => panic!(),
    /// }
    ///
    /// assert_eq!(map.get_key2(&10), Some(&43));
    ///
    /// let entry = map
    ///     .raw_entry_mut()
    ///     .from_keys("poneyland", &10)
    ///     .unwrap()
    ///     .and_replace_entry_with_key2(|_k2, _v| None);
    ///
    /// match entry {
    ///     RawEntryMut::Vacant(_) => {}
    ///     RawEntryMut::Occupied(_) => panic!(),
    /// }
    ///
    /// assert!(!map.contains_key2(&10));
    /// ```
    #[cfg_attr(feature = "inline-more", inline)]
    pub fn and_replace_entry_with_key2<F>(self, f: F) -> Self
    where
        F: FnOnce(&K2, V) -> Option<V>,
    {
        match self {
            RawEntryMut::Occupied(entry) => entry.replace_entry_with_key2(f),
            RawEntryMut::Vacant(_) => self,
        }
    }

    /// Provides shared access to the `K1` and `K2` key and owned access to
    /// the value of an occupied entry and allows to replace or remove it
    /// based on the value of the returned option.
    ///
    /// # Examples
    ///
    /// ```
    /// use double_map::shash_map::{DoubleMap, RawEntryMut};
    ///
    /// let mut map: DoubleMap<&str, u32, u32> = DoubleMap::new();
    ///
    /// let entry = map
    ///     .raw_entry_mut()
    ///     .from_keys("poneyland", &10)
    ///     .unwrap()
    ///     .and_replace_entry_with_keys(|_k1, _k2, _v| panic!());
    ///
    /// match entry {
    ///     RawEntryMut::Vacant(_) => {}
    ///     RawEntryMut::Occupied(_) => panic!(),
    /// }
    ///
    /// map.insert("poneyland", 10, 42);
    ///
    /// let entry = map
    ///     .raw_entry_mut()
    ///     .from_keys("poneyland", &10)
    ///     .unwrap()
    ///     .and_replace_entry_with_keys(|k1, k2, v| {
    ///         assert_eq!(*k1, "poneyland");
    ///         assert_eq!(*k2, 10);
    ///         assert_eq!(v, 42);
    ///         Some(v + 1)
    ///     });
    ///
    /// match entry {
    ///     RawEntryMut::Occupied(e) => {
    ///         assert_eq!(e.key1(), &"poneyland");
    ///         assert_eq!(e.key2(), &10);
    ///         assert_eq!(e.get(), &43);
    ///     }
    ///     RawEntryMut::Vacant(_) => panic!(),
    /// }
    ///
    /// assert_eq!(map.get_keys("poneyland", &10), Some(&43));
    ///
    /// let entry = map
    ///     .raw_entry_mut()
    ///     .from_keys("poneyland", &10)
    ///     .unwrap()
    ///     .and_replace_entry_with_keys(|_k1, _k2, _v| None);
    ///
    /// match entry {
    ///     RawEntryMut::Vacant(_) => {}
    ///     RawEntryMut::Occupied(_) => panic!(),
    /// }
    ///
    /// assert!(!map.contains_keys("poneyland", &10));
    /// ```
    #[cfg_attr(feature = "inline-more", inline)]
    pub fn and_replace_entry_with_keys<F>(self, f: F) -> Self
    where
        F: FnOnce(&K1, &K2, V) -> Option<V>,
    {
        match self {
            RawEntryMut::Occupied(entry) => entry.replace_entry_with_keys(f),
            RawEntryMut::Vacant(_) => self,
        }
    }
}
