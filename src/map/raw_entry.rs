use super::*;

/// A builder for computing where in a [`DHashMap`] a tuple of
/// keys and value `(K1, K2, V)` would be stored.
///
/// See the [`DHashMap::raw_entry`] docs for usage examples.
///
/// [`DHashMap::raw_entry`]: struct.DHashMap.html#method.raw_entry
///
/// # Examples
///
/// ```
/// use core::hash::{BuildHasher, Hash};
/// use double_map::dhash_map::{DHashMap, RawEntryBuilder};
///
/// let mut map = DHashMap::new();
/// map.extend([(1, 10, 100), (2, 20, 200), (3, 30, 300)]);
///
/// fn compute_hash<K: Hash + ?Sized, S: BuildHasher>(hash_builder: &S, key: &K) -> u64 {
///     use core::hash::Hasher;
///     let mut state = hash_builder.build_hasher();
///     key.hash(&mut state);
///     state.finish()
/// }
///
/// for (k1, k2) in (0..6).map(|i| (i, i * 10)) {
///     let hash1 = compute_hash(map.hasher(), &k1);
///     let hash2 = compute_hash(map.hasher(), &k2);
///     let v = map.get_key1(&k1).cloned();
///     let kv_tuple = v.as_ref().map(|v| (&k1, &k2, v));
///
///     println!("Key1: {}, key2: {} and value: {:?}", k1, k2, v);
///     let builder: RawEntryBuilder<_, _, _, _> = map.raw_entry();
///     assert_eq!(builder.from_keys(&k1, &k2), kv_tuple);
///     assert_eq!(
///         map.raw_entry()
///             .from_hashes(hash1, |q| *q == k1, hash2, |q| *q == k2),
///         kv_tuple
///     );
///     assert_eq!(
///         map.raw_entry()
///             .from_keys_hashed_nocheck(hash1, &k1, hash2, &k2),
///         kv_tuple
///     );
/// }
/// ```
pub struct RawEntryBuilder<'a, K1, K2, V, S, A: Allocator + Clone = Global> {
    pub(super) map: &'a DHashMap<K1, K2, V, S, A>,
}

impl<K1, K2, V, S, A> Debug for RawEntryBuilder<'_, K1, K2, V, S, A>
where
    A: Allocator + Clone,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("RawEntryBuilder").finish()
    }
}

impl<'a, K1, K2, V, S, A: Allocator + Clone> RawEntryBuilder<'a, K1, K2, V, S, A> {
    /// Access an immutable entry by keys.
    ///
    /// # Examples
    ///
    /// ```
    /// use double_map::DHashMap;
    ///
    /// let map: DHashMap<&str, u32, u32> = [("a", 10, 100), ("b", 20, 200)].into();
    /// assert_eq!(
    ///     map.raw_entry().from_keys(&"a", &10),
    ///     Some((&"a", &10, &100))
    /// );
    /// ```
    #[cfg_attr(feature = "inline-more", inline)]
    #[allow(clippy::wrong_self_convention)]
    pub fn from_keys<Q1, Q2>(self, k1: &Q1, k2: &Q2) -> Option<(&'a K1, &'a K2, &'a V)>
    where
        S: BuildHasher,
        Q1: ?Sized + Hash + Equivalent<K1>,
        Q2: ?Sized + Hash + Equivalent<K2>,
    {
        let hash_builder = &self.map.hash_builder;
        let hash1 = make_hash::<Q1, S>(hash_builder, k1);
        let hash2 = make_hash::<Q2, S>(hash_builder, k2);

        self.from_keys_hashed_nocheck(hash1, k1, hash2, k2)
    }

    /// Access an immutable entry by keys and their hashes.
    ///
    /// # Examples
    ///
    /// ```
    /// use core::hash::{BuildHasher, Hash};
    /// use double_map::DHashMap;
    ///
    /// fn compute_hash<K: Hash + ?Sized, S: BuildHasher>(hash_builder: &S, key: &K) -> u64 {
    ///     use core::hash::Hasher;
    ///     let mut state = hash_builder.build_hasher();
    ///     key.hash(&mut state);
    ///     state.finish()
    /// }
    ///
    /// let map: DHashMap<&str, u32, u32> = [("a", 10, 100), ("b", 20, 200)].into();
    /// let key1 = "a";
    /// let hash1 = compute_hash(map.hasher(), &key1);
    /// let key2 = 10;
    /// let hash2 = compute_hash(map.hasher(), &key2);
    /// assert_eq!(
    ///     map.raw_entry()
    ///         .from_keys_hashed_nocheck(hash1, &key1, hash2, &key2),
    ///     Some((&"a", &10, &100))
    /// );
    /// ```
    #[cfg_attr(feature = "inline-more", inline)]
    #[allow(clippy::wrong_self_convention)]
    pub fn from_keys_hashed_nocheck<Q1, Q2>(
        self,
        hash1: u64,
        k1: &Q1,
        hash2: u64,
        k2: &Q2,
    ) -> Option<(&'a K1, &'a K2, &'a V)>
    where
        Q1: ?Sized + Equivalent<K1>,
        Q2: ?Sized + Equivalent<K2>,
    {
        self.from_hashes(hash1, equivalent(k1), hash2, equivalent(k2))
    }

    /// Access an immutable entry by hashes and matching functions.
    ///
    /// # Examples
    ///
    /// ```
    /// use core::hash::{BuildHasher, Hash};
    /// use double_map::DHashMap;
    ///
    /// fn compute_hash<K: Hash + ?Sized, S: BuildHasher>(hash_builder: &S, key: &K) -> u64 {
    ///     use core::hash::Hasher;
    ///     let mut state = hash_builder.build_hasher();
    ///     key.hash(&mut state);
    ///     state.finish()
    /// }
    ///
    /// let map: DHashMap<&str, u32, u32> = [("a", 10, 100), ("b", 20, 200)].into();
    /// let key1 = "a";
    /// let hash1 = compute_hash(map.hasher(), &key1);
    /// let key2 = 10;
    /// let hash2 = compute_hash(map.hasher(), &key2);
    /// assert_eq!(
    ///     map.raw_entry()
    ///         .from_hashes(hash1, |k| *k == key1, hash2, |k| *k == key2),
    ///     Some((&"a", &10, &100))
    /// );
    /// ```
    #[cfg_attr(feature = "inline-more", inline)]
    #[allow(clippy::wrong_self_convention)]
    pub fn from_hashes<F1, F2>(
        self,
        hash1: u64,
        is_match1: F1,
        hash2: u64,
        is_match2: F2,
    ) -> Option<(&'a K1, &'a K2, &'a V)>
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
    ) -> Option<(&'a K1, &'a K2, &'a V)>
    where
        F1: FnMut(&K1) -> bool,
        F2: FnMut(&K2) -> bool,
    {
        match self
            .map
            .table
            .get(hash1, |x| is_match1(&x.0), hash2, |x| is_match2(&x.1))
        {
            Some(&(ref key1, ref key2, ref value)) => Some((key1, key2, value)),
            None => None,
        }
    }
}
