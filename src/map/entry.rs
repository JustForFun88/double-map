use super::*;

pub enum Entry<'a, K1, K2, V, S, A = Global>
where
    A: Allocator + Clone,
{
    /// An occupied entry.
    Occupied(OccupiedEntry<'a, K1, K2, V, S, A>),
    /// A vacant entry.
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

    #[cfg_attr(feature = "inline-more", inline)]
    pub fn key1(&self) -> &K1 {
        match *self {
            Entry::Occupied(ref entry) => entry.key1(),
            Entry::Vacant(ref entry) => entry.key1(),
        }
    }

    #[cfg_attr(feature = "inline-more", inline)]
    pub fn key2(&self) -> &K2 {
        match *self {
            Entry::Occupied(ref entry) => entry.key2(),
            Entry::Vacant(ref entry) => entry.key2(),
        }
    }

    #[cfg_attr(feature = "inline-more", inline)]
    pub fn keys(&self) -> (&K1, &K2) {
        match *self {
            Entry::Occupied(ref entry) => entry.keys(),
            Entry::Vacant(ref entry) => entry.keys(),
        }
    }

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

pub struct OccupiedEntry<'a, K1, K2, V, S, A: Allocator + Clone = Global> {
    pub(super) hash1: u64,
    pub(super) key1: Option<K1>,
    pub(super) hash2: u64,
    pub(super) key2: Option<K2>,
    pub(super) data_bucket: DataBucket<(K1, K2, V)>,
    pub(super) pointer_bucket: PointerBucket<DataBucket<(K1, K2, V)>>,
    pub(super) table: &'a mut DHashMap<K1, K2, V, S, A>,
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

    #[cfg_attr(feature = "inline-more", inline)]
    pub fn remove_entry(self) -> (K1, K2, V) {
        let (k1, k2, v) = unsafe { self.table.table.remove(self.pointer_bucket) };
        (k1, k2, v)
    }

    #[cfg_attr(feature = "inline-more", inline)]
    pub fn get(&self) -> &V {
        unsafe { &self.data_bucket.as_ref().2 }
    }

    #[cfg_attr(feature = "inline-more", inline)]
    pub fn get_mut(&mut self) -> &mut V {
        unsafe { &mut self.data_bucket.as_mut().2 }
    }

    #[cfg_attr(feature = "inline-more", inline)]
    pub fn into_mut(self) -> &'a mut V {
        unsafe { &mut self.data_bucket.as_mut().2 }
    }

    #[cfg_attr(feature = "inline-more", inline)]
    pub fn insert(&mut self, value: V) -> V {
        mem::replace(self.get_mut(), value)
    }

    #[cfg_attr(feature = "inline-more", inline)]
    pub fn remove(self) -> V {
        self.remove_entry().2
    }

    #[cfg_attr(feature = "inline-more", inline)]
    pub fn replace_entry(self, value: V) -> (K1, K2, V) {
        let &mut (ref mut k1, ref mut k2, ref mut v) = unsafe { self.data_bucket.as_mut() };

        let old_key1 = mem::replace(k1, self.key1.unwrap());
        let old_key2 = mem::replace(k2, self.key2.unwrap());
        let old_value = mem::replace(v, value);
        (old_key1, old_key2, old_value)
    }

    #[cfg_attr(feature = "inline-more", inline)]
    pub fn replace_key1(self) -> K1 {
        let entry = unsafe { self.data_bucket.as_mut() };
        mem::replace(&mut entry.0, self.key1.unwrap())
    }

    #[cfg_attr(feature = "inline-more", inline)]
    pub fn replace_key2(self) -> K2 {
        let entry = unsafe { self.data_bucket.as_mut() };
        mem::replace(&mut entry.1, self.key2.unwrap())
    }

    #[cfg_attr(feature = "inline-more", inline)]
    pub fn replace_keys(self) -> (K1, K2) {
        let &mut (ref mut k1, ref mut k2, _) = unsafe { self.data_bucket.as_mut() };

        let old_key1 = mem::replace(k1, self.key1.unwrap());
        let old_key2 = mem::replace(k2, self.key2.unwrap());
        (old_key1, old_key2)
    }

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

pub struct VacantEntry<'a, K1, K2, V, S, A: Allocator + Clone = Global> {
    pub(super) hash1: u64,
    pub(super) key1: K1,
    pub(super) hash2: u64,
    pub(super) key2: K2,
    pub(super) table: &'a mut DHashMap<K1, K2, V, S, A>,
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
    #[cfg_attr(feature = "inline-more", inline)]
    pub fn key1(&self) -> &K1 {
        &self.key1
    }

    #[cfg_attr(feature = "inline-more", inline)]
    pub fn key2(&self) -> &K2 {
        &self.key2
    }

    #[cfg_attr(feature = "inline-more", inline)]
    pub fn keys(&self) -> (&K1, &K2) {
        (&self.key1, &self.key2)
    }

    #[cfg_attr(feature = "inline-more", inline)]
    pub fn into_key1(self) -> K1 {
        self.key1
    }

    #[cfg_attr(feature = "inline-more", inline)]
    pub fn into_key2(self) -> K2 {
        self.key2
    }

    #[cfg_attr(feature = "inline-more", inline)]
    pub fn into_keys(self) -> (K1, K2) {
        (self.key1, self.key2)
    }

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
