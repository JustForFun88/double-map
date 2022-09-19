use super::*;

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
    /// Access an entry by key.
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

    /// Access an entry by a key and its hash.
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
        self.from_hash(hash1, equivalent(k1), hash2, equivalent(k2))
    }

    /// Access an entry by hash.
    #[cfg_attr(feature = "inline-more", inline)]
    #[allow(clippy::wrong_self_convention)]
    pub fn from_hash<F1, F2>(
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
