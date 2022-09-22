use super::*;

pub enum EntryRef<'a, 'b, K1, Q1: ?Sized, K2, Q2: ?Sized, V, S, A = Global>
where
    A: Allocator + Clone,
{
    Occupied(OccupiedEntryRef<'a, 'b, K1, Q1, K2, Q2, V, S, A>),

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
    #[cfg_attr(feature = "inline-more", inline)]
    pub fn key1(&self) -> &Q1
    where
        K1: Borrow<Q1>,
    {
        unsafe { &self.data_bucket.as_ref().0 }.borrow()
    }

    #[cfg_attr(feature = "inline-more", inline)]
    pub fn key2(&self) -> &Q2
    where
        K2: Borrow<Q2>,
    {
        unsafe { &self.data_bucket.as_ref().1 }.borrow()
    }

    #[cfg_attr(feature = "inline-more", inline)]
    pub fn keys(&self) -> (&Q1, &Q2)
    where
        K1: Borrow<Q1>,
        K2: Borrow<Q2>,
    {
        let &(ref k1, ref k2, _) = unsafe { self.data_bucket.as_ref() };
        (k1.borrow(), k2.borrow())
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

    #[cfg_attr(feature = "inline-more", inline)]
    pub fn replace_key1(self) -> K1
    where
        K1: From<&'b Q1> + Clone,
    {
        let entry = unsafe { self.data_bucket.as_mut() };
        mem::replace(&mut entry.0, self.key1.unwrap().into_owned())
    }

    #[cfg_attr(feature = "inline-more", inline)]
    pub fn replace_key2(self) -> K2
    where
        K2: From<&'b Q2> + Clone,
    {
        let entry = unsafe { self.data_bucket.as_mut() };
        mem::replace(&mut entry.1, self.key2.unwrap().into_owned())
    }

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
    #[cfg_attr(feature = "inline-more", inline)]
    pub fn key1(&self) -> &Q1
    where
        K1: Borrow<Q1>,
    {
        self.key1.as_ref()
    }

    #[cfg_attr(feature = "inline-more", inline)]
    pub fn key2(&self) -> &Q2
    where
        K2: Borrow<Q2>,
    {
        self.key2.as_ref()
    }

    #[cfg_attr(feature = "inline-more", inline)]
    pub fn keys(&self) -> (&Q1, &Q2)
    where
        K1: Borrow<Q1>,
        K2: Borrow<Q2>,
    {
        (self.key1.as_ref(), self.key2.as_ref())
    }

    #[cfg_attr(feature = "inline-more", inline)]
    pub fn into_key1(self) -> K1
    where
        K1: From<&'b Q1>,
    {
        self.key1.into_owned()
    }

    #[cfg_attr(feature = "inline-more", inline)]
    pub fn into_key2(self) -> K2
    where
        K2: From<&'b Q2>,
    {
        self.key2.into_owned()
    }

    #[cfg_attr(feature = "inline-more", inline)]
    pub fn into_keys(self) -> (K1, K2)
    where
        K1: From<&'b Q1>,
        K2: From<&'b Q2>,
    {
        (self.key1.into_owned(), self.key2.into_owned())
    }

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
