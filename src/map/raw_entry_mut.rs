use super::*;

pub struct RawEntryBuilderMut<'a, K1, K2, V, S, A: Allocator + Clone = Global> {
    pub(super) map: &'a mut DHashMap<K1, K2, V, S, A>,
}

impl<K1, K2, V, S, A: Allocator + Clone> Debug for RawEntryBuilderMut<'_, K1, K2, V, S, A> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("RawEntryBuilder").finish()
    }
}

impl<'a, K1, K2, V, S, A: Allocator + Clone> RawEntryBuilderMut<'a, K1, K2, V, S, A> {
    /// Creates a `RawEntryMut` from the given key.
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

    /// Creates a `RawEntryMut` from the given key and its hash.
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
        self.from_hash(hash1, equivalent(k1), hash2, equivalent(k2))
    }

    /// Creates a `RawEntryMut` from the given hash.
    #[cfg_attr(feature = "inline-more", inline)]
    #[allow(clippy::wrong_self_convention)]
    pub fn from_hash<F1, F2>(
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

    /// Set the value of an entry with a custom hasher function.
    #[cfg_attr(feature = "inline-more", inline)]
    pub fn insert_with_hasher<H1, H2>(
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
    /// Gets a reference to the key in the entry.
    #[cfg_attr(feature = "inline-more", inline)]
    pub fn key1(&self) -> &K1 {
        unsafe { &self.data_bucket.as_ref().0 }
    }

    #[cfg_attr(feature = "inline-more", inline)]
    pub fn key2(&self) -> &K2 {
        unsafe { &self.data_bucket.as_ref().1 }
    }

    #[cfg_attr(feature = "inline-more", inline)]
    pub fn keys(&self) -> (&K1, &K2) {
        let &(ref k1, ref k2, _) = unsafe { self.data_bucket.as_ref() };
        (k1, k2)
    }

    /// Gets a mutable reference to the key in the entry.
    #[cfg_attr(feature = "inline-more", inline)]
    pub fn key1_mut(&mut self) -> &mut K1 {
        unsafe { &mut self.data_bucket.as_mut().0 }
    }

    /// Gets a mutable reference to the key in the entry.
    #[cfg_attr(feature = "inline-more", inline)]
    pub fn key2_mut(&mut self) -> &mut K2 {
        unsafe { &mut self.data_bucket.as_mut().1 }
    }

    #[cfg_attr(feature = "inline-more", inline)]
    pub fn keys_mut(&mut self) -> (&mut K1, &mut K2) {
        let &mut (ref mut k1, ref mut k2, _) = unsafe { self.data_bucket.as_mut() };
        (k1, k2)
    }

    /// Gets a mutable reference to the key in the entry.
    #[cfg_attr(feature = "inline-more", inline)]
    pub fn into_key1(self) -> &'a mut K1 {
        unsafe { &mut self.data_bucket.as_mut().0 }
    }

    /// Gets a mutable reference to the key in the entry.
    #[cfg_attr(feature = "inline-more", inline)]
    pub fn into_key2(self) -> &'a mut K2 {
        unsafe { &mut self.data_bucket.as_mut().1 }
    }

    #[cfg_attr(feature = "inline-more", inline)]
    pub fn into_keys(self) -> (&'a mut K1, &'a mut K2) {
        let &mut (ref mut k1, ref mut k2, _) = unsafe { self.data_bucket.as_mut() };
        (k1, k2)
    }

    /// Gets a reference to the value in the entry.
    #[cfg_attr(feature = "inline-more", inline)]
    pub fn get(&self) -> &V {
        unsafe { &self.data_bucket.as_ref().2 }
    }

    /// Converts the OccupiedEntry into a mutable reference to the value in the entry
    /// with a lifetime bound to the map itself.
    #[cfg_attr(feature = "inline-more", inline)]
    pub fn into_mut(self) -> &'a mut V {
        unsafe { &mut self.data_bucket.as_mut().2 }
    }

    /// Gets a mutable reference to the value in the entry.
    #[cfg_attr(feature = "inline-more", inline)]
    pub fn get_mut(&mut self) -> &mut V {
        unsafe { &mut self.data_bucket.as_mut().2 }
    }

    /// Gets a reference to the key and value in the entry.
    #[cfg_attr(feature = "inline-more", inline)]
    pub fn get_keys_value(&mut self) -> (&K1, &K2, &V) {
        unsafe {
            let &(ref key1, ref key2, ref value) = self.data_bucket.as_ref();
            (key1, key2, value)
        }
    }

    /// Gets a mutable reference to the key and value in the entry.
    #[cfg_attr(feature = "inline-more", inline)]
    pub fn get_keys_value_mut(&mut self) -> (&mut K1, &mut K2, &mut V) {
        unsafe {
            let (key1, key2, value) = self.data_bucket.as_mut();
            (key1, key2, value)
        }
    }

    /// Converts the OccupiedEntry into a mutable reference to the key and value in the entry
    /// with a lifetime bound to the map itself.
    #[cfg_attr(feature = "inline-more", inline)]
    pub fn into_keys_value(self) -> (&'a mut K1, &'a mut K2, &'a mut V) {
        unsafe {
            let (key1, key2, value) = self.data_bucket.as_mut();
            (key1, key2, value)
        }
    }

    /// Sets the value of the entry, and returns the entry's old value.
    #[cfg_attr(feature = "inline-more", inline)]
    pub fn insert(&mut self, value: V) -> V {
        mem::replace(self.get_mut(), value)
    }

    /// Sets the value of the entry, and returns the entry's old value.
    #[cfg_attr(feature = "inline-more", inline)]
    pub fn insert_key1(&mut self, k1: K1) -> K1 {
        mem::replace(self.key1_mut(), k1)
    }

    /// Sets the value of the entry, and returns the entry's old value.
    #[cfg_attr(feature = "inline-more", inline)]
    pub fn insert_key2(&mut self, k2: K2) -> K2 {
        mem::replace(self.key2_mut(), k2)
    }

    /// Sets the value of the entry, and returns the entry's old value.
    #[cfg_attr(feature = "inline-more", inline)]
    pub fn insert_keys(&mut self, k1: K1, k2: K2) -> (K1, K2) {
        let (k1_dest, k2_dest, _) = unsafe { self.data_bucket.as_mut() };
        let key1_old = mem::replace(k1_dest, k1);
        let key2_old = mem::replace(k2_dest, k2);

        (key1_old, key2_old)
    }

    /// Take the ownership of the key and value from the map.
    #[cfg_attr(feature = "inline-more", inline)]
    pub fn remove(self) -> V {
        self.remove_entry().2
    }

    /// Take the ownership of the key and value from the map.
    #[cfg_attr(feature = "inline-more", inline)]
    pub fn remove_entry(self) -> (K1, K2, V) {
        unsafe { self.table.remove(self.pointer_bucket) }
    }

    /// Provides shared access to the key and owned access to the value of
    /// the entry and allows to replace or remove it based on the
    /// value of the returned option.
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

pub enum RawEntryMut<'a, K1, K2, V, S, A: Allocator + Clone = Global> {
    /// An occupied entry.
    Occupied(RawOccupiedEntryMut<'a, K1, K2, V, S, A>),
    /// A vacant entry.
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
