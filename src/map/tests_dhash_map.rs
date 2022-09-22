use super::*;
use alloc::string::{String, ToString};
use alloc::vec::Vec;
use core::cell::RefCell;
use rand::{thread_rng, Rng};
use std::borrow::ToOwned;

#[inline(always)]
fn insert_raw_entry_from_key<'a, 'b, Q1, Q2, K1, K2, V, S, A, I>(
    map: &mut DHashMap<K1, K2, V, S, A>,
    iter: I,
) -> bool
where
    Q1: ?Sized + Hash + Equivalent<K1> + 'a,
    Q2: ?Sized + Hash + Equivalent<K2> + 'b,
    for<'c> K1: Eq + Hash + From<&'c Q1>,
    for<'d> K2: Eq + Hash + From<&'d Q2>,
    S: BuildHasher,
    A: Allocator + Clone,
    I: IntoIterator<Item = (&'a Q1, &'b Q2, V)>,
{
    iter.into_iter().all(|(k1, k2, v)| {
        map.raw_entry_mut()
            .from_keys(k1, k2)
            .map(|e| e.or_insert(k1.into(), k2.into(), v))
            .is_ok()
    })
}

#[inline(always)]
fn insert_raw_entry_from_key_hashed_nocheck<'a, 'b, Q1, Q2, K1, K2, V, S, A, I>(
    map: &mut DHashMap<K1, K2, V, S, A>,
    iter: I,
) -> bool
where
    Q1: ?Sized + Hash + Equivalent<K1> + 'a,
    Q2: ?Sized + Hash + Equivalent<K2> + 'b,
    for<'c> K1: Eq + Hash + From<&'c Q1>,
    for<'d> K2: Eq + Hash + From<&'d Q2>,
    S: BuildHasher,
    A: Allocator + Clone,
    I: IntoIterator<Item = (&'a Q1, &'b Q2, V)>,
{
    iter.into_iter().all(|(k1, k2, v)| {
        let hash1 = make_hash::<Q1, S>(map.hasher(), k1);
        let hash2 = make_hash::<Q2, S>(map.hasher(), k2);
        map.raw_entry_mut()
            .from_keys_hashed_nocheck(hash1, k1, hash2, k2)
            .map(|e| e.or_insert(k1.into(), k2.into(), v))
            .is_ok()
    })
}

#[inline(always)]
fn insert_raw_entry_from_hash<'a, 'b, Q1, Q2, K1, K2, V, S, A, I>(
    map: &mut DHashMap<K1, K2, V, S, A>,
    iter: I,
) -> bool
where
    Q1: ?Sized + Hash + Equivalent<K1> + 'a,
    Q2: ?Sized + Hash + Equivalent<K2> + 'b,
    for<'c> K1: Eq + Hash + From<&'c Q1>,
    for<'d> K2: Eq + Hash + From<&'d Q2>,
    S: BuildHasher,
    A: Allocator + Clone,
    I: IntoIterator<Item = (&'a Q1, &'b Q2, V)>,
{
    iter.into_iter().all(|(k1, k2, v)| {
        let hash1 = make_hash::<Q1, S>(map.hasher(), k1);
        let hash2 = make_hash::<Q2, S>(map.hasher(), k2);
        map.raw_entry_mut()
            .from_hash(
                hash1,
                |key| k1.equivalent(key),
                hash2,
                |key| k2.equivalent(key),
            )
            .map(|e| e.or_insert(k1.into(), k2.into(), v))
            .is_ok()
    })
}

#[inline(always)]
fn match_entry_error<K1, K2, V, S, A>(
    map: &mut DHashMap<K1, K2, V, S, A>,
    (k1, k2): (&K1, &K2),
    err: ErrorKind,
) -> bool
where
    K1: Eq + Hash + Clone,
    K2: Eq + Hash + Clone,
    V: PartialEq + Clone,
    S: BuildHasher,
    A: Allocator + Clone,
{
    match map.entry(k1.clone(), k2.clone()) {
        Ok(_) => false,
        Err(EntryError {
            error,
            keys: (ret_k1, ret_k2),
        }) => matches!(error, in_err if in_err == err) && &ret_k1 == k1 && &ret_k2 == k2,
    }
}

#[inline(always)]
fn match_entry_ref_error<'a, 'b, Q1, Q2, K1, K2, V, S, A>(
    map: &mut DHashMap<K1, K2, V, S, A>,
    (k1, k2): (&Q1, &Q2),
    err: ErrorKind,
) -> bool
where
    Q1: ?Sized + Hash + Equivalent<K1> + 'a,
    Q2: ?Sized + Hash + Equivalent<K2> + 'b,
    for<'c> K1: Eq + Hash + From<&'c Q1>,
    for<'d> K2: Eq + Hash + From<&'d Q2>,
    S: BuildHasher,
    A: Allocator + Clone,
{
    match map.entry_ref(k1, k2) {
        Ok(_) => false,
        Err(error) => matches!(error, in_err if in_err == err),
    }
}

#[inline(always)]
fn match_insert_error<K1, K2, V, S, A>(
    map: &mut DHashMap<K1, K2, V, S, A>,
    (k1, k2): (&K1, &K2),
    val: &V,
    err: ErrorKind,
) -> bool
where
    K1: Eq + Hash + Clone,
    K2: Eq + Hash + Clone,
    V: PartialEq + Clone,
    S: BuildHasher,
    A: Allocator + Clone,
{
    match map.insert(k1.clone(), k2.clone(), val.clone()) {
        Some(result) => match result {
            Ok(_) => false,
            Err(InsertError {
                error,
                keys: (ret_k1, ret_k2),
                value,
            }) => {
                (matches! { error, in_err if in_err == err  }
                    && &ret_k1 == k1
                    && &ret_k2 == k2
                    && &value == val)
            }
        },
        None => false,
    }
}

#[inline(always)]
fn match_try_insert_error<K1, K2, V, S, A>(
    map: &mut DHashMap<K1, K2, V, S, A>,
    (k1, k2): (&K1, &K2),
    val: &V,
    err: Option<ErrorKind>,
) -> bool
where
    K1: Eq + Hash + Clone,
    K2: Eq + Hash + Clone,
    V: PartialEq + Clone,
    S: BuildHasher,
    A: Allocator + Clone,
{
    if let Some(err) = err {
        match map.try_insert(k1.clone(), k2.clone(), val.clone()) {
            Ok(_) => false,
            Err(error) => match error {
                TryInsertError::Occupied(_) => false,
                TryInsertError::Insert(InsertError {
                    error,
                    keys: (ret_k1, ret_k2),
                    value,
                }) => {
                    (matches! { error, in_err if in_err == err  }
                        && &ret_k1 == k1
                        && &ret_k2 == k2
                        && &value == val)
                }
            },
        }
    } else {
        match map.try_insert(k1.clone(), k2.clone(), val.clone()) {
            Ok(_) => false,
            Err(error) => match error {
                TryInsertError::Occupied(OccupiedError { entry, value }) => {
                    entry.key1() == k1 && entry.key2() == k2 && val == &value
                }
                TryInsertError::Insert(_) => false,
            },
        }
    }
}

#[inline(always)]
fn entry_keys_points_to_diff_entries<K1, K2, V, S, A>(
    map: &mut DHashMap<K1, K2, V, S, A>,
    keys: &[(K1, K2)],
) -> bool
where
    K1: Eq + Hash + Clone,
    K2: Eq + Hash + Clone,
    V: PartialEq + Clone,
    S: BuildHasher,
    A: Allocator + Clone,
{
    for (index, (k1, _)) in keys.iter().enumerate() {
        let (lsplit, rsplit) = keys.split_at(index);
        for (_, k2) in lsplit {
            if !match_entry_error(map, (k1, k2), ErrorKind::KeysPointsToDiffEntries) {
                return false;
            }
        }
        for (_, k2) in rsplit.iter().skip(1) {
            if !match_entry_error(map, (k1, k2), ErrorKind::KeysPointsToDiffEntries) {
                return false;
            }
        }
    }
    true
}

#[inline(always)]
fn entry_ref_keys_points_to_diff_entries<'a, 'b, Q1, Q2, K1, K2, V, S, A>(
    map: &mut DHashMap<K1, K2, V, S, A>,
    keys: &[(&Q1, &Q2)],
) -> bool
where
    Q1: ?Sized + Hash + Equivalent<K1> + 'a,
    Q2: ?Sized + Hash + Equivalent<K2> + 'b,
    for<'c> K1: Eq + Hash + From<&'c Q1>,
    for<'d> K2: Eq + Hash + From<&'d Q2>,
    S: BuildHasher,
    A: Allocator + Clone,
{
    for (index, (k1, _)) in keys.iter().enumerate() {
        let (lsplit, rsplit) = keys.split_at(index);
        for (_, k2) in lsplit {
            if !match_entry_ref_error(map, (*k1, *k2), ErrorKind::KeysPointsToDiffEntries) {
                return false;
            }
        }
        for (_, k2) in rsplit.iter().skip(1) {
            if !match_entry_ref_error(map, (*k1, *k2), ErrorKind::KeysPointsToDiffEntries) {
                return false;
            }
        }
    }
    true
}

#[inline(always)]
fn insert_keys_points_to_diff_entries<K1, K2, V, S, A>(
    map: &mut DHashMap<K1, K2, V, S, A>,
    keys: &[(K1, K2)],
    val: &V,
) -> bool
where
    K1: Eq + Hash + Clone,
    K2: Eq + Hash + Clone,
    V: PartialEq + Clone,
    S: BuildHasher,
    A: Allocator + Clone,
{
    for (index, (k1, _)) in keys.iter().enumerate() {
        let (lsplit, rsplit) = keys.split_at(index);
        for (_, k2) in lsplit {
            if !match_insert_error(map, (k1, k2), &val, ErrorKind::KeysPointsToDiffEntries) {
                return false;
            }
        }
        for (_, k2) in rsplit.iter().skip(1) {
            if !match_insert_error(map, (k1, k2), &val, ErrorKind::KeysPointsToDiffEntries) {
                return false;
            }
        }
    }
    true
}

#[inline(always)]
fn try_insert_keys_points_to_diff_entries<K1, K2, V, S, A>(
    map: &mut DHashMap<K1, K2, V, S, A>,
    keys: &[(K1, K2)],
    val: &V,
) -> bool
where
    K1: Eq + Hash + Clone,
    K2: Eq + Hash + Clone,
    V: PartialEq + Clone,
    S: BuildHasher,
    A: Allocator + Clone,
{
    for (index, (k1, _)) in keys.iter().enumerate() {
        let (lsplit, rsplit) = keys.split_at(index);
        for (_, k2) in lsplit {
            if !match_try_insert_error(
                map,
                (k1, k2),
                &val,
                Some(ErrorKind::KeysPointsToDiffEntries),
            ) {
                return false;
            }
        }
        for (_, k2) in rsplit.iter().skip(1) {
            if !match_try_insert_error(
                map,
                (k1, k2),
                &val,
                Some(ErrorKind::KeysPointsToDiffEntries),
            ) {
                return false;
            }
        }
    }
    true
}

#[test]
fn test_zero_capacities() {
    type HM = DHashMap<i32, i32, i32>;

    let m = HM::new();
    assert_eq!(m.capacity(), 0);

    let m = HM::default();
    assert_eq!(m.capacity(), 0);

    let m = HM::with_hasher(DefaultHashBuilder::default());
    assert_eq!(m.capacity(), 0);

    let m = HM::with_capacity(0);
    assert_eq!(m.capacity(), 0);

    let m = HM::with_capacity_and_hasher(0, DefaultHashBuilder::default());
    assert_eq!(m.capacity(), 0);

    // --------------------------------------------------------------------------------
    // test with `DHashMap::insert`
    // --------------------------------------------------------------------------------
    let mut m = HM::new();
    assert!((1..8).all(|i| m.insert(i, i * 10, i * 100).is_none()));
    assert!((1..8).all(|i| matches!( m.get_key1(&i), Some(num) if *num == i * 100 )));
    assert!((1..8).all(|i| m.remove_key1(&i).is_some()));
    m.shrink_to_fit();
    assert_eq!(m.capacity(), 0);

    let mut m = HM::new();
    assert!((1..8).all(|i| m.insert(i, i * 10, i * 100).is_none()));
    assert!((1..8).all(|i| matches!( m.get_key2(&(i * 10)), Some(num) if *num == i * 100 )));
    assert!((1..8).all(|i| m.remove_key2(&(i * 10)).is_some()));
    m.shrink_to_fit();
    assert_eq!(m.capacity(), 0);

    let mut m = HM::new();
    assert!((1..8).all(|i| m.insert(i, i * 10, i * 100).is_none()));
    assert!((1..8).all(|i| matches!( m.get_keys(&i, &(i * 10)), Some(num) if *num == i * 100 )));
    assert!((1..8).all(|i| m.remove_keys(&i, &(i * 10)).is_some()));
    m.shrink_to_fit();
    assert_eq!(m.capacity(), 0);

    // --------------------------------------------------------------------------------
    // test with `DHashMap::try_insert`
    // --------------------------------------------------------------------------------
    let mut m = HM::new();
    assert!((1..8).all(|i| m.try_insert(i, i * 10, i * 100).is_ok()));
    assert!((1..8).all(|i| matches!( m.get_key1(&i), Some(num) if *num == i * 100 )));
    assert!((1..8).all(|i| m.remove_key1(&i).is_some()));
    m.shrink_to_fit();
    assert_eq!(m.capacity(), 0);

    let mut m = HM::new();
    assert!((1..8).all(|i| m.try_insert(i, i * 10, i * 100).is_ok()));
    assert!((1..8).all(|i| matches!( m.get_key2(&(i * 10)), Some(num) if *num == i * 100 )));
    assert!((1..8).all(|i| m.remove_key2(&(i * 10)).is_some()));
    m.shrink_to_fit();
    assert_eq!(m.capacity(), 0);

    let mut m = HM::new();
    assert!((1..8).all(|i| m.try_insert(i, i * 10, i * 100).is_ok()));
    assert!((1..8).all(|i| matches!( m.get_keys(&i, &(i * 10)), Some(num) if *num == i * 100 )));
    assert!((1..8).all(|i| m.remove_keys(&i, &(i * 10)).is_some()));
    m.shrink_to_fit();
    assert_eq!(m.capacity(), 0);

    // --------------------------------------------------------------------------------
    // test with `DHashMap::insert_unique_unchecked`
    // --------------------------------------------------------------------------------
    let mut m = HM::new();
    assert!((1..8)
        .all(|i| m.insert_unique_unchecked(i, i * 10, i * 100) == (&i, &(i * 10), &mut (i * 100))));
    assert!((1..8).all(|i| matches!( m.get_key1(&i), Some(num) if *num == i * 100 )));
    assert!((1..8).all(|i| m.remove_key1(&i).is_some()));
    m.shrink_to_fit();
    assert_eq!(m.capacity(), 0);

    let mut m = HM::new();
    assert!((1..8)
        .all(|i| m.insert_unique_unchecked(i, i * 10, i * 100) == (&i, &(i * 10), &mut (i * 100))));
    assert!((1..8).all(|i| matches!( m.get_key2(&(i * 10)), Some(num) if *num == i * 100 )));
    assert!((1..8).all(|i| m.remove_key2(&(i * 10)).is_some()));
    m.shrink_to_fit();
    assert_eq!(m.capacity(), 0);

    let mut m = HM::new();
    assert!((1..8)
        .all(|i| m.insert_unique_unchecked(i, i * 10, i * 100) == (&i, &(i * 10), &mut (i * 100))));
    assert!((1..8).all(|i| matches!( m.get_keys(&i, &(i * 10)), Some(num) if *num == i * 100 )));
    assert!((1..8).all(|i| m.remove_keys(&i, &(i * 10)).is_some()));
    m.shrink_to_fit();
    assert_eq!(m.capacity(), 0);

    // --------------------------------------------------------------------------------
    // test with `DHashMap::entry`
    // --------------------------------------------------------------------------------
    let mut m = HM::new();
    assert!((1..8).all(|i| m.entry(i, i * 10).map(|e| e.or_insert(i * 100)).is_ok()));
    assert!((1..8).all(|i| matches!( m.get_key1(&i), Some(num) if *num == i * 100 )));
    assert!((1..8).all(|i| m.remove_key1(&i).is_some()));
    m.shrink_to_fit();
    assert_eq!(m.capacity(), 0);

    let mut m = HM::new();
    assert!((1..8).all(|i| m.entry(i, i * 10).map(|e| e.or_insert(i * 100)).is_ok()));
    assert!((1..8).all(|i| matches!( m.get_key2(&(i * 10)), Some(num) if *num == i * 100 )));
    assert!((1..8).all(|i| m.remove_key2(&(i * 10)).is_some()));
    m.shrink_to_fit();
    assert_eq!(m.capacity(), 0);

    let mut m = HM::new();
    assert!((1..8).all(|i| m.entry(i, i * 10).map(|e| e.or_insert(i * 100)).is_ok()));
    assert!((1..8).all(|i| matches!( m.get_keys(&i, &(i * 10)), Some(num) if *num == i * 100 )));
    assert!((1..8).all(|i| m.remove_keys(&i, &(i * 10)).is_some()));
    m.shrink_to_fit();
    assert_eq!(m.capacity(), 0);

    let vec: Vec<_> = (1..8)
        .map(|i| (i.to_string(), (i * 10).to_string(), i * 100))
        .collect();

    // --------------------------------------------------------------------------------
    // test with `DHashMap::entry_ref`
    // --------------------------------------------------------------------------------
    let mut m: DHashMap<String, String, i32> = DHashMap::new();
    assert!(vec
        .iter()
        .all(|(k1, k2, v)| m.entry_ref(k1, k2).map(|e| e.or_insert(*v)).is_ok()));
    assert!(vec
        .iter()
        .all(|(k1, _, v)| matches!(m.get_key1(k1), Some(num) if num == v)));
    assert!(vec.iter().all(|(k1, _, _)| m.remove_key1(k1).is_some()));
    m.shrink_to_fit();
    assert_eq!(m.capacity(), 0);

    let mut m: DHashMap<String, String, i32> = DHashMap::new();
    assert!(vec
        .iter()
        .all(|(k1, k2, v)| m.entry_ref(k1, k2).map(|e| e.or_insert(*v)).is_ok()));
    assert!(vec
        .iter()
        .all(|(_, k2, v)| matches!(m.get_key2(k2), Some(num) if num == v)));
    assert!(vec.iter().all(|(_, k2, _)| m.remove_key2(k2).is_some()));
    m.shrink_to_fit();
    assert_eq!(m.capacity(), 0);

    let mut m: DHashMap<String, String, i32> = DHashMap::new();
    assert!(vec
        .iter()
        .all(|(k1, k2, v)| m.entry_ref(k1, k2).map(|e| e.or_insert(*v)).is_ok()));
    assert!(vec
        .iter()
        .all(|(k1, k2, v)| matches!(m.get_keys(k1, k2), Some(num) if num == v)));
    assert!(vec
        .iter()
        .all(|(k1, k2, _)| m.remove_keys(k1, k2).is_some()));
    m.shrink_to_fit();
    assert_eq!(m.capacity(), 0);

    // --------------------------------------------------------------------------------
    // test with `RawEntryBuilderMut::from_keys`
    // --------------------------------------------------------------------------------
    let mut m: DHashMap<String, String, i32> = DHashMap::new();
    assert!(insert_raw_entry_from_key(
        &mut m,
        vec.iter().map(|(k1, k2, v)| (k1, k2, *v))
    ));
    assert!(vec
        .iter()
        .all(|(k1, _, v)| matches!(m.get_key1(k1), Some(num) if num == v)));
    assert!(vec.iter().all(|(k1, _, _)| m.remove_key1(k1).is_some()));
    m.shrink_to_fit();
    assert_eq!(m.capacity(), 0);

    let mut m: DHashMap<String, String, i32> = DHashMap::new();
    assert!(insert_raw_entry_from_key(
        &mut m,
        vec.iter().map(|(k1, k2, v)| (k1, k2, *v))
    ));
    assert!(vec
        .iter()
        .all(|(_, k2, v)| matches!(m.get_key2(k2), Some(num) if num == v)));
    assert!(vec.iter().all(|(_, k2, _)| m.remove_key2(k2).is_some()));
    m.shrink_to_fit();
    assert_eq!(m.capacity(), 0);

    let mut m: DHashMap<String, String, i32> = DHashMap::new();
    assert!(insert_raw_entry_from_key(
        &mut m,
        vec.iter().map(|(k1, k2, v)| (k1, k2, *v))
    ));
    assert!(vec
        .iter()
        .all(|(k1, k2, v)| matches!(m.get_keys(k1, k2), Some(num) if num == v)));
    assert!(vec
        .iter()
        .all(|(k1, k2, _)| m.remove_keys(k1, k2).is_some()));
    m.shrink_to_fit();
    assert_eq!(m.capacity(), 0);

    // --------------------------------------------------------------------------------
    // test with `RawEntryBuilderMut::from_keys_hashed_nocheck`
    // --------------------------------------------------------------------------------
    let mut m: DHashMap<String, String, i32> = DHashMap::new();
    assert!(insert_raw_entry_from_key_hashed_nocheck(
        &mut m,
        vec.iter().map(|(k1, k2, v)| (k1, k2, *v))
    ));
    assert!(vec
        .iter()
        .all(|(k1, _, v)| matches!(m.get_key1(k1), Some(num) if num == v)));
    assert!(vec.iter().all(|(k1, _, _)| m.remove_key1(k1).is_some()));
    m.shrink_to_fit();
    assert_eq!(m.capacity(), 0);

    let mut m: DHashMap<String, String, i32> = DHashMap::new();
    assert!(insert_raw_entry_from_key_hashed_nocheck(
        &mut m,
        vec.iter().map(|(k1, k2, v)| (k1, k2, *v))
    ));
    assert!(vec
        .iter()
        .all(|(_, k2, v)| matches!(m.get_key2(k2), Some(num) if num == v)));
    assert!(vec.iter().all(|(_, k2, _)| m.remove_key2(k2).is_some()));
    m.shrink_to_fit();
    assert_eq!(m.capacity(), 0);

    let mut m: DHashMap<String, String, i32> = DHashMap::new();
    assert!(insert_raw_entry_from_key_hashed_nocheck(
        &mut m,
        vec.iter().map(|(k1, k2, v)| (k1, k2, *v))
    ));
    assert!(vec
        .iter()
        .all(|(k1, k2, v)| matches!(m.get_keys(k1, k2), Some(num) if num == v)));
    assert!(vec
        .iter()
        .all(|(k1, k2, _)| m.remove_keys(k1, k2).is_some()));
    m.shrink_to_fit();
    assert_eq!(m.capacity(), 0);

    // --------------------------------------------------------------------------------
    // test with `RawEntryBuilderMut::from_hash`
    // --------------------------------------------------------------------------------
    let mut m: DHashMap<String, String, i32> = DHashMap::new();
    assert!(insert_raw_entry_from_hash(
        &mut m,
        vec.iter().map(|(k1, k2, v)| (k1, k2, *v))
    ));
    assert!(vec
        .iter()
        .all(|(k1, _, v)| matches!(m.get_key1(k1), Some(num) if num == v)));
    assert!(vec.iter().all(|(k1, _, _)| m.remove_key1(k1).is_some()));
    m.shrink_to_fit();
    assert_eq!(m.capacity(), 0);

    let mut m: DHashMap<String, String, i32> = DHashMap::new();
    assert!(insert_raw_entry_from_hash(
        &mut m,
        vec.iter().map(|(k1, k2, v)| (k1, k2, *v))
    ));
    assert!(vec
        .iter()
        .all(|(_, k2, v)| matches!(m.get_key2(k2), Some(num) if num == v)));
    assert!(vec.iter().all(|(_, k2, _)| m.remove_key2(k2).is_some()));
    m.shrink_to_fit();
    assert_eq!(m.capacity(), 0);

    let mut m: DHashMap<String, String, i32> = DHashMap::new();
    assert!(insert_raw_entry_from_hash(
        &mut m,
        vec.iter().map(|(k1, k2, v)| (k1, k2, *v))
    ));
    assert!(vec
        .iter()
        .all(|(k1, k2, v)| matches!(m.get_keys(k1, k2), Some(num) if num == v)));
    assert!(vec
        .iter()
        .all(|(k1, k2, _)| m.remove_keys(k1, k2).is_some()));
    m.shrink_to_fit();
    assert_eq!(m.capacity(), 0);

    let mut m = HM::new();
    m.reserve(0);
    assert_eq!(m.capacity(), 0);
}

#[test]
fn test_create_capacity_zero() {
    let mut m = DHashMap::with_capacity(0);

    assert_eq!(m.capacity(), 0);

    // --------------------------------------------------------------------------------
    // test with first allocation
    // --------------------------------------------------------------------------------
    assert!((1..=3).all(|i| m.insert(i, i * 10, i * 100).is_none()));

    assert!((1..=3).all(|i| matches!( m.get_key1(&i), Some(num) if *num == i * 100 )));
    assert!((1..=3).all(|i| matches!( m.get_key2(&(i * 10)), Some(num) if *num == i * 100 )));
    assert!((1..=3).all(|i| matches!( m.get_keys(&i, &(i * 10)), Some(num) if *num == i * 100 )));

    assert!((1..=3).all(|i| matches!(m.get_key1(&(i * 10)), None)));
    assert!((1..=3).all(|i| matches!(m.get_key2(&i), None)));
    assert!((1..=3).all(|i| matches!(m.get_keys(&(i * 10), &i), None)));

    assert!((1..=3).all(|i| m.contains_key1(&i)
        && m.contains_key2(&(i * 10))
        && m.contains_keys(&i, &(i * 10))));

    assert!((1..=3).all(|i| !m.contains_key1(&(i * 10))
        && !m.contains_key2(&i)
        && !m.contains_keys(&(i * 10), &i)));

    // --------------------------------------------------------------------------------
    // test with second allocation
    // --------------------------------------------------------------------------------
    assert!((4..=7).all(|i| m.insert(i, i * 10, i * 100).is_none()));

    assert!((1..=7).all(|i| matches!( m.get_key1(&i), Some(num) if *num == i * 100 )));
    assert!((1..=7).all(|i| matches!( m.get_key2(&(i * 10)), Some(num) if *num == i * 100 )));
    assert!((1..=7).all(|i| matches!( m.get_keys(&i, &(i * 10)), Some(num) if *num == i * 100 )));

    assert!((1..=7).all(|i| matches!(m.get_key1(&(i * 10)), None)));
    assert!((1..=7).all(|i| matches!(m.get_key2(&i), None)));
    assert!((1..=7).all(|i| matches!(m.get_keys(&(i * 10), &i), None)));

    assert!((1..=7).all(|i| m.contains_key1(&i)
        && m.contains_key2(&(i * 10))
        && m.contains_keys(&i, &(i * 10))));

    assert!((1..=7).all(|i| !m.contains_key1(&(i * 10))
        && !m.contains_key2(&i)
        && !m.contains_keys(&(i * 10), &i)));

    // --------------------------------------------------------------------------------
    // test with third allocation
    // --------------------------------------------------------------------------------
    assert!((8..=9).all(|i| m.insert(i, i * 10, i * 100).is_none()));

    assert!((1..=9).all(|i| matches!( m.get_key1(&i), Some(num) if *num == i * 100 )));
    assert!((1..=9).all(|i| matches!( m.get_key2(&(i * 10)), Some(num) if *num == i * 100 )));
    assert!((1..=9).all(|i| matches!( m.get_keys(&i, &(i * 10)), Some(num) if *num == i * 100 )));

    assert!((1..=9).all(|i| matches!(m.get_key1(&(i * 10)), None)));
    assert!((1..=9).all(|i| matches!(m.get_key2(&i), None)));
    assert!((1..=9).all(|i| matches!(m.get_keys(&(i * 10), &i), None)));

    assert!((1..=9).all(|i| m.contains_key1(&i)
        && m.contains_key2(&(i * 10))
        && m.contains_keys(&i, &(i * 10))));

    assert!((1..=9).all(|i| !m.contains_key1(&(i * 10))
        && !m.contains_key2(&i)
        && !m.contains_keys(&(i * 10), &i)));
}

#[test]
fn test_insert() {
    // --------------------------------------------------------------------------------
    // test with first allocation
    // --------------------------------------------------------------------------------
    let mut m = DHashMap::new();
    assert_eq!(m.len(), 0);
    assert_eq!(m.capacity(), 0);

    assert!(m.insert(1, 10, 100).is_none());
    assert_eq!(m.len(), 1);

    assert!(m.insert(2, 20, 200).is_none());
    assert_eq!(m.len(), 2);

    assert!(m.insert(3, 30, 300).is_none());
    assert_eq!(m.len(), 3);
    let old_capacity = m.capacity();

    assert!(
        (1..=3).all(|i| matches!( m.get_key1(&i), Some(num) if *num == i * 100 )
            && matches!( m.get_key2(&(i * 10)), Some(num) if *num == i * 100 )
            && matches!( m.get_keys(&i, &(i * 10)), Some(num) if *num == i * 100 ))
    );

    assert_eq!(m.is_empty(), false);
    assert!((1..=3).all(|i| m.contains_key1(&i)
        && m.contains_key2(&(i * 10))
        && m.contains_keys(&i, &(i * 10))));

    assert!(
        (1..=3).all(|i| matches!( m.insert(i, i * 10, i * 1000), Some(Ok(num)) if num == i * 100))
    );

    assert_eq!(m.capacity(), old_capacity);
    assert_eq!(m.len(), 3);

    assert!((1..=3).all(
        |i| matches!( m.get_key1(&i), Some(num) if *num == i * 1000 )
            && matches!( m.get_key2(&(i * 10)), Some(num) if *num == i * 1000 )
            && matches!( m.get_keys(&i, &(i * 10)), Some(num) if *num == i * 1000 )
    ));
    assert_eq!(m.is_empty(), false);
    assert!((1..=3).all(|i| m.contains_key1(&i)
        && m.contains_key2(&(i * 10))
        && m.contains_keys(&i, &(i * 10))));

    // test error insert
    assert!((1..=3).all(|i| match_insert_error(
        &mut m,
        (&i, &(i * 100)),
        &i,
        ErrorKind::OccupiedK1AndVacantK2
    )));
    assert!((1..=3).all(|i| match_insert_error(
        &mut m,
        (&(i * 100), &(i * 10)),
        &i,
        ErrorKind::VacantK1AndOccupiedK2
    )));
    assert!(insert_keys_points_to_diff_entries(
        &mut m,
        &[(1, 10), (2, 20), (3, 30)],
        &99999
    ));

    // to be sure that nothing changed
    assert_eq!(m.capacity(), old_capacity);
    assert_eq!(m.len(), 3);

    assert!((1..=3).all(
        |i| matches!( m.get_key1(&i), Some(num) if *num == i * 1000 )
            && matches!( m.get_key2(&(i * 10)), Some(num) if *num == i * 1000 )
            && matches!( m.get_keys(&i, &(i * 10)), Some(num) if *num == i * 1000 )
    ));
    assert_eq!(m.is_empty(), false);
    assert!((1..=3).all(|i| m.contains_key1(&i)
        && m.contains_key2(&(i * 10))
        && m.contains_keys(&i, &(i * 10))));

    // --------------------------------------------------------------------------------
    // test with second allocation
    // --------------------------------------------------------------------------------
    assert!(m.insert(4, 40, 4000).is_none());
    assert_eq!(m.len(), 4);

    assert!(m.insert(5, 50, 5000).is_none());
    assert_eq!(m.len(), 5);

    assert!(m.insert(6, 60, 6000).is_none());
    assert_eq!(m.len(), 6);
    let old_capacity = m.capacity();

    assert!((1..=6).all(
        |i| matches!( m.get_key1(&i), Some(num) if *num == i * 1000 )
            && matches!( m.get_key2(&(i * 10)), Some(num) if *num == i * 1000 )
            && matches!( m.get_keys(&i, &(i * 10)), Some(num) if *num == i * 1000 )
    ));
    assert_eq!(m.is_empty(), false);
    assert!((1..=6).all(|i| m.contains_key1(&i)
        && m.contains_key2(&(i * 10))
        && m.contains_keys(&i, &(i * 10))));

    assert!((1..=6)
        .all(|i| matches!( m.insert(i, i * 10, i * 10000), Some(Ok(num)) if num == i * 1000)));

    assert_eq!(m.capacity(), old_capacity);
    assert_eq!(m.len(), 6);

    assert!((1..=6).all(
        |i| matches!( m.get_key1(&i), Some(num) if *num == i * 10000 )
            && matches!( m.get_key2(&(i * 10)), Some(num) if *num == i * 10000 )
            && matches!( m.get_keys(&i, &(i * 10)), Some(num) if *num == i * 10000 )
    ));
    assert_eq!(m.is_empty(), false);
    assert!((1..=6).all(|i| m.contains_key1(&i)
        && m.contains_key2(&(i * 10))
        && m.contains_keys(&i, &(i * 10))));

    // test error insert
    assert!((1..=6).all(|i| match_insert_error(
        &mut m,
        (&i, &(i * 100)),
        &i,
        ErrorKind::OccupiedK1AndVacantK2
    )));
    assert!((1..=6).all(|i| match_insert_error(
        &mut m,
        (&(i * 100), &(i * 10)),
        &i,
        ErrorKind::VacantK1AndOccupiedK2
    )));
    assert!(insert_keys_points_to_diff_entries(
        &mut m,
        &[(1, 10), (2, 20), (3, 30), (4, 40), (5, 50), (6, 60)],
        &99999
    ));

    // to be sure that nothing changed
    assert_eq!(m.capacity(), old_capacity);
    assert_eq!(m.len(), 6);

    assert!((1..=6).all(
        |i| matches!( m.get_key1(&i), Some(num) if *num == i * 10000 )
            && matches!( m.get_key2(&(i * 10)), Some(num) if *num == i * 10000 )
            && matches!( m.get_keys(&i, &(i * 10)), Some(num) if *num == i * 10000 )
    ));
    assert_eq!(m.is_empty(), false);
    assert!((1..=6).all(|i| m.contains_key1(&i)
        && m.contains_key2(&(i * 10))
        && m.contains_keys(&i, &(i * 10))));

    // --------------------------------------------------------------------------------
    // test with third allocation
    // --------------------------------------------------------------------------------
    assert!(m.insert(7, 70, 70000).is_none());
    assert_eq!(m.len(), 7);

    assert!(m.insert(8, 80, 80000).is_none());
    assert_eq!(m.len(), 8);

    assert!(m.insert(9, 90, 90000).is_none());
    assert_eq!(m.len(), 9);
    let old_capacity = m.capacity();

    assert!((1..=9).all(
        |i| matches!( m.get_key1(&i), Some(num) if *num == i * 10000 )
            && matches!( m.get_key2(&(i * 10)), Some(num) if *num == i * 10000 )
            && matches!( m.get_keys(&i, &(i * 10)), Some(num) if *num == i * 10000 )
    ));
    assert_eq!(m.is_empty(), false);
    assert!((1..=9).all(|i| m.contains_key1(&i)
        && m.contains_key2(&(i * 10))
        && m.contains_keys(&i, &(i * 10))));

    assert!((1..=9)
        .all(|i| matches!( m.insert(i, i * 10, i * 100000), Some(Ok(num)) if num == i * 10000)));

    assert_eq!(m.capacity(), old_capacity);
    assert_eq!(m.len(), 9);

    assert!((1..=9).all(
        |i| matches!( m.get_key1(&i), Some(num) if *num == i * 100000 )
            && matches!( m.get_key2(&(i * 10)), Some(num) if *num == i * 100000 )
            && matches!( m.get_keys(&i, &(i * 10)), Some(num) if *num == i * 100000 )
    ));
    assert_eq!(m.is_empty(), false);
    assert!((1..=9).all(|i| m.contains_key1(&i)
        && m.contains_key2(&(i * 10))
        && m.contains_keys(&i, &(i * 10))));

    // test error insert
    assert!((1..=9).all(|i| match_insert_error(
        &mut m,
        (&i, &(i * 100)),
        &i,
        ErrorKind::OccupiedK1AndVacantK2
    )));
    assert!((1..=9).all(|i| match_insert_error(
        &mut m,
        (&(i * 100), &(i * 10)),
        &i,
        ErrorKind::VacantK1AndOccupiedK2
    )));
    assert!(insert_keys_points_to_diff_entries(
        &mut m,
        &[
            (1, 10),
            (2, 20),
            (3, 30),
            (4, 40),
            (5, 50),
            (6, 60),
            (7, 70),
            (8, 80),
            (9, 90)
        ],
        &99999
    ));

    // to be sure that nothing changed
    assert_eq!(m.capacity(), old_capacity);
    assert_eq!(m.len(), 9);

    assert!((1..=9).all(
        |i| matches!( m.get_key1(&i), Some(num) if *num == i * 100000 )
            && matches!( m.get_key2(&(i * 10)), Some(num) if *num == i * 100000 )
            && matches!( m.get_keys(&i, &(i * 10)), Some(num) if *num == i * 100000 )
    ));
    assert_eq!(m.is_empty(), false);
    assert!((1..=9).all(|i| m.contains_key1(&i)
        && m.contains_key2(&(i * 10))
        && m.contains_keys(&i, &(i * 10))));
}

#[test]
fn test_insert_unique_unchecked() {
    // --------------------------------------------------------------------------------
    // test with first allocation
    // --------------------------------------------------------------------------------
    let mut m = DHashMap::new();
    assert_eq!(m.len(), 0);
    assert_eq!(m.capacity(), 0);

    assert_eq!(m.insert_unique_unchecked(1, 10, 100), (&1, &10, &mut 100));
    assert_eq!(m.len(), 1);

    assert_eq!(m.insert_unique_unchecked(2, 20, 200), (&2, &20, &mut 200));
    assert_eq!(m.len(), 2);

    assert_eq!(m.insert_unique_unchecked(3, 30, 300), (&3, &30, &mut 300));
    assert_eq!(m.len(), 3);

    assert!(
        (1..=3).all(|i| matches!( m.get_key1(&i), Some(num) if *num == i * 100 )
            && matches!( m.get_key2(&(i * 10)), Some(num) if *num == i * 100 )
            && matches!( m.get_keys(&i, &(i * 10)), Some(num) if *num == i * 100 ))
    );

    assert_eq!(m.is_empty(), false);
    assert!((1..=3).all(|i| m.contains_key1(&i)
        && m.contains_key2(&(i * 10))
        && m.contains_keys(&i, &(i * 10))));

    // --------------------------------------------------------------------------------
    // test with second allocation
    // --------------------------------------------------------------------------------
    assert_eq!(m.insert_unique_unchecked(4, 40, 400), (&4, &40, &mut 400));
    assert_eq!(m.len(), 4);

    assert_eq!(m.insert_unique_unchecked(5, 50, 500), (&5, &50, &mut 500));
    assert_eq!(m.len(), 5);

    assert_eq!(m.insert_unique_unchecked(6, 60, 600), (&6, &60, &mut 600));
    assert_eq!(m.len(), 6);

    assert!(
        (1..=6).all(|i| matches!( m.get_key1(&i), Some(num) if *num == i * 100 )
            && matches!( m.get_key2(&(i * 10)), Some(num) if *num == i * 100 )
            && matches!( m.get_keys(&i, &(i * 10)), Some(num) if *num == i * 100 ))
    );
    assert_eq!(m.is_empty(), false);
    assert!((1..=6).all(|i| m.contains_key1(&i)
        && m.contains_key2(&(i * 10))
        && m.contains_keys(&i, &(i * 10))));

    // --------------------------------------------------------------------------------
    // test with third allocation
    // --------------------------------------------------------------------------------
    assert_eq!(m.insert_unique_unchecked(7, 70, 700), (&7, &70, &mut 700));
    assert_eq!(m.len(), 7);

    assert_eq!(m.insert_unique_unchecked(8, 80, 800), (&8, &80, &mut 800));
    assert_eq!(m.len(), 8);

    assert_eq!(m.insert_unique_unchecked(9, 90, 900), (&9, &90, &mut 900));
    assert_eq!(m.len(), 9);
    let old_capacity = m.capacity();

    assert!(
        (1..=9).all(|i| matches!( m.get_key1(&i), Some(num) if *num == i * 100 )
            && matches!( m.get_key2(&(i * 10)), Some(num) if *num == i * 100 )
            && matches!( m.get_keys(&i, &(i * 10)), Some(num) if *num == i * 100 ))
    );
    assert_eq!(m.is_empty(), false);
    assert!((1..=9).all(|i| m.contains_key1(&i)
        && m.contains_key2(&(i * 10))
        && m.contains_keys(&i, &(i * 10))));

    // --------------------------------------------------------------------------------
    // Additional test that we can use `insert` after `insert_unique_unchecked`
    // --------------------------------------------------------------------------------
    assert!((1..=9)
        .all(|i| matches!( m.insert(i, i * 10, i * 100000), Some(Ok(num)) if num == i * 100)));

    assert_eq!(m.capacity(), old_capacity);
    assert_eq!(m.len(), 9);

    assert!((1..=9).all(
        |i| matches!( m.get_key1(&i), Some(num) if *num == i * 100000 )
            && matches!( m.get_key2(&(i * 10)), Some(num) if *num == i * 100000 )
            && matches!( m.get_keys(&i, &(i * 10)), Some(num) if *num == i * 100000 )
    ));
    assert_eq!(m.is_empty(), false);
    assert!((1..=9).all(|i| m.contains_key1(&i)
        && m.contains_key2(&(i * 10))
        && m.contains_keys(&i, &(i * 10))));

    // test error insert
    assert!((1..=9).all(|i| match_insert_error(
        &mut m,
        (&i, &(i * 100)),
        &i,
        ErrorKind::OccupiedK1AndVacantK2
    )));
    assert!((1..=9).all(|i| match_insert_error(
        &mut m,
        (&(i * 100), &(i * 10)),
        &i,
        ErrorKind::VacantK1AndOccupiedK2
    )));
    assert!(insert_keys_points_to_diff_entries(
        &mut m,
        &[
            (1, 10),
            (2, 20),
            (3, 30),
            (4, 40),
            (5, 50),
            (6, 60),
            (7, 70),
            (8, 80),
            (9, 90)
        ],
        &99999
    ));

    // to be sure that nothing changed
    assert_eq!(m.capacity(), old_capacity);
    assert_eq!(m.len(), 9);

    assert!((1..=9).all(
        |i| matches!( m.get_key1(&i), Some(num) if *num == i * 100000 )
            && matches!( m.get_key2(&(i * 10)), Some(num) if *num == i * 100000 )
            && matches!( m.get_keys(&i, &(i * 10)), Some(num) if *num == i * 100000 )
    ));
    assert_eq!(m.is_empty(), false);
    assert!((1..=9).all(|i| m.contains_key1(&i)
        && m.contains_key2(&(i * 10))
        && m.contains_keys(&i, &(i * 10))));
}

#[test]
fn test_try_insert() {
    // --------------------------------------------------------------------------------
    // test with first allocation
    // --------------------------------------------------------------------------------
    let mut m = DHashMap::new();
    assert_eq!(m.len(), 0);
    assert_eq!(m.capacity(), 0);

    assert_eq!(m.try_insert(1, 10, 100).unwrap(), &mut 100);
    assert_eq!(m.len(), 1);

    assert_eq!(m.try_insert(2, 20, 200).unwrap(), &mut 200);
    assert_eq!(m.len(), 2);

    assert_eq!(m.try_insert(3, 30, 300).unwrap(), &mut 300);
    assert_eq!(m.len(), 3);
    let old_capacity = m.capacity();

    assert!(
        (1..=3).all(|i| matches!( m.get_key1(&i), Some(num) if *num == i * 100 )
            && matches!( m.get_key2(&(i * 10)), Some(num) if *num == i * 100 )
            && matches!( m.get_keys(&i, &(i * 10)), Some(num) if *num == i * 100 ))
    );
    assert_eq!(m.is_empty(), false);
    assert!((1..=3).all(|i| m.contains_key1(&i)
        && m.contains_key2(&(i * 10))
        && m.contains_keys(&i, &(i * 10))));

    // test error try_insert
    assert!((1..=3).all(|i| match_try_insert_error(&mut m, (&i, &(i * 10)), &i, None)));

    assert!((1..=3).all(|i| match_try_insert_error(
        &mut m,
        (&i, &(i * 100)),
        &i,
        Some(ErrorKind::OccupiedK1AndVacantK2)
    )));
    assert!((1..=3).all(|i| match_try_insert_error(
        &mut m,
        (&(i * 100), &(i * 10)),
        &i,
        Some(ErrorKind::VacantK1AndOccupiedK2)
    )));
    assert!(try_insert_keys_points_to_diff_entries(
        &mut m,
        &[(1, 10), (2, 20), (3, 30)],
        &99999
    ));

    // to be sure that nothing changed
    assert_eq!(m.capacity(), old_capacity);
    assert_eq!(m.len(), 3);

    assert!(
        (1..=3).all(|i| matches!( m.get_key1(&i), Some(num) if *num == i * 100 )
            && matches!( m.get_key2(&(i * 10)), Some(num) if *num == i * 100 )
            && matches!( m.get_keys(&i, &(i * 10)), Some(num) if *num == i * 100 ))
    );
    assert_eq!(m.is_empty(), false);
    assert!((1..=3).all(|i| m.contains_key1(&i)
        && m.contains_key2(&(i * 10))
        && m.contains_keys(&i, &(i * 10))));

    // --------------------------------------------------------------------------------
    // test with second allocation
    // --------------------------------------------------------------------------------
    assert_eq!(m.try_insert(4, 40, 400).unwrap(), &mut 400);
    assert_eq!(m.len(), 4);

    assert_eq!(m.try_insert(5, 50, 500).unwrap(), &mut 500);
    assert_eq!(m.len(), 5);

    assert_eq!(m.try_insert(6, 60, 600).unwrap(), &mut 600);
    assert_eq!(m.len(), 6);
    let old_capacity = m.capacity();

    assert!(
        (1..=6).all(|i| matches!( m.get_key1(&i), Some(num) if *num == i * 100 )
            && matches!( m.get_key2(&(i * 10)), Some(num) if *num == i * 100 )
            && matches!( m.get_keys(&i, &(i * 10)), Some(num) if *num == i * 100 ))
    );
    assert_eq!(m.is_empty(), false);
    assert!((1..=6).all(|i| m.contains_key1(&i)
        && m.contains_key2(&(i * 10))
        && m.contains_keys(&i, &(i * 10))));

    // test error insert
    assert!((1..=6).all(|i| match_try_insert_error(&mut m, (&i, &(i * 10)), &i, None)));

    assert!((1..=6).all(|i| match_try_insert_error(
        &mut m,
        (&i, &(i * 100)),
        &i,
        Some(ErrorKind::OccupiedK1AndVacantK2)
    )));
    assert!((1..=6).all(|i| match_try_insert_error(
        &mut m,
        (&(i * 100), &(i * 10)),
        &i,
        Some(ErrorKind::VacantK1AndOccupiedK2)
    )));
    assert!(try_insert_keys_points_to_diff_entries(
        &mut m,
        &[(1, 10), (2, 20), (3, 30), (4, 40), (5, 50), (6, 60)],
        &99999
    ));

    // to be sure that nothing changed
    assert_eq!(m.capacity(), old_capacity);
    assert_eq!(m.len(), 6);

    assert!(
        (1..=6).all(|i| matches!( m.get_key1(&i), Some(num) if *num == i * 100 )
            && matches!( m.get_key2(&(i * 10)), Some(num) if *num == i * 100 )
            && matches!( m.get_keys(&i, &(i * 10)), Some(num) if *num == i * 100 ))
    );
    assert_eq!(m.is_empty(), false);
    assert!((1..=6).all(|i| m.contains_key1(&i)
        && m.contains_key2(&(i * 10))
        && m.contains_keys(&i, &(i * 10))));

    // --------------------------------------------------------------------------------
    // test with third allocation
    // --------------------------------------------------------------------------------
    assert_eq!(m.try_insert(7, 70, 700).unwrap(), &mut 700);
    assert_eq!(m.len(), 7);

    assert_eq!(m.try_insert(8, 80, 800).unwrap(), &mut 800);
    assert_eq!(m.len(), 8);

    assert_eq!(m.try_insert(9, 90, 900).unwrap(), &mut 900);
    assert_eq!(m.len(), 9);
    let old_capacity = m.capacity();

    assert!(
        (1..=9).all(|i| matches!( m.get_key1(&i), Some(num) if *num == i * 100 )
            && matches!( m.get_key2(&(i * 10)), Some(num) if *num == i * 100 )
            && matches!( m.get_keys(&i, &(i * 10)), Some(num) if *num == i * 100 ))
    );
    assert_eq!(m.is_empty(), false);
    assert!((1..=9).all(|i| m.contains_key1(&i)
        && m.contains_key2(&(i * 10))
        && m.contains_keys(&i, &(i * 10))));

    // test error insert
    assert!((1..=9).all(|i| match_try_insert_error(&mut m, (&i, &(i * 10)), &i, None)));

    assert!((1..=9).all(|i| match_try_insert_error(
        &mut m,
        (&i, &(i * 100)),
        &i,
        Some(ErrorKind::OccupiedK1AndVacantK2)
    )));
    assert!((1..=9).all(|i| match_try_insert_error(
        &mut m,
        (&(i * 100), &(i * 10)),
        &i,
        Some(ErrorKind::VacantK1AndOccupiedK2)
    )));
    assert!(try_insert_keys_points_to_diff_entries(
        &mut m,
        &[
            (1, 10),
            (2, 20),
            (3, 30),
            (4, 40),
            (5, 50),
            (6, 60),
            (7, 70),
            (8, 80),
            (9, 90)
        ],
        &99999
    ));

    // to be sure that nothing changed
    assert_eq!(m.capacity(), old_capacity);
    assert_eq!(m.len(), 9);

    assert!(
        (1..=9).all(|i| matches!( m.get_key1(&i), Some(num) if *num == i * 100 )
            && matches!( m.get_key2(&(i * 10)), Some(num) if *num == i * 100 )
            && matches!( m.get_keys(&i, &(i * 10)), Some(num) if *num == i * 100 ))
    );
    assert_eq!(m.is_empty(), false);
    assert!((1..=9).all(|i| m.contains_key1(&i)
        && m.contains_key2(&(i * 10))
        && m.contains_keys(&i, &(i * 10))));
}

#[test]
fn test_clone_with_copy_type_simple() {
    // --------------------------------------------------------------------------------
    // test with one allocation
    // --------------------------------------------------------------------------------
    let mut map = DHashMap::new();
    assert_eq!(map.len(), 0);
    assert!((1..=3).all(|i| map.insert(i, i * 10, i * 100).is_none()));
    assert_eq!(map.len(), 3);

    let m2 = map.clone();

    // cloned map is the same length and contains the same keys and values
    assert_eq!(map.capacity(), m2.capacity());
    assert_eq!(m2.len(), 3);
    assert!((1..=3).all(|i| matches!( m2.get_key1(&i), Some(num) if *num == i * 100 )));
    assert!((1..=3).all(|i| matches!( m2.get_key2(&(i * 10)), Some(num) if *num == i * 100 )));
    assert!((1..=3).all(|i| matches!( m2.get_keys(&i, &(i * 10)), Some(num) if *num == i * 100 )));
    assert!((1..=3).all(|i| m2.contains_key1(&i)));
    assert!((1..=3).all(|i| m2.contains_key2(&(i * 10))));
    assert!((1..=3).all(|i| m2.contains_keys(&i, &(i * 10))));

    // sourse map is not changed
    assert_eq!(map.len(), 3);
    assert!((1..=3).all(|i| matches!( map.get_key1(&i), Some(num) if *num == i * 100 )));
    assert!((1..=3).all(|i| matches!( map.get_key2(&(i * 10)), Some(num) if *num == i * 100 )));
    assert!((1..=3).all(|i| matches!( map.get_keys(&i, &(i * 10)), Some(num) if *num == i * 100 )));
    assert!((1..=3).all(|i| map.contains_key1(&i)));
    assert!((1..=3).all(|i| map.contains_key2(&(i * 10))));
    assert!((1..=3).all(|i| map.contains_keys(&i, &(i * 10))));

    // --------------------------------------------------------------------------------
    // test with two allocation
    // --------------------------------------------------------------------------------
    let mut map = DHashMap::new();
    assert_eq!(map.len(), 0);
    assert!((1..=6).all(|i| map.insert(i, i * 10, i * 100).is_none()));
    assert_eq!(map.len(), 6);

    let m2 = map.clone();

    // cloned map is the same length and contains the same keys and values
    assert_eq!(map.capacity(), m2.capacity());
    assert_eq!(m2.len(), 6);
    assert!((1..=6).all(|i| matches!( m2.get_key1(&i), Some(num) if *num == i * 100 )));
    assert!((1..=6).all(|i| matches!( m2.get_key2(&(i * 10)), Some(num) if *num == i * 100 )));
    assert!((1..=6).all(|i| matches!( m2.get_keys(&i, &(i * 10)), Some(num) if *num == i * 100 )));
    assert!((1..=6).all(|i| m2.contains_key1(&i)));
    assert!((1..=6).all(|i| m2.contains_key2(&(i * 10))));
    assert!((1..=6).all(|i| m2.contains_keys(&i, &(i * 10))));

    // sourse map is not changed
    assert_eq!(map.len(), 6);
    assert!((1..=6).all(|i| matches!( map.get_key1(&i), Some(num) if *num == i * 100 )));
    assert!((1..=6).all(|i| matches!( map.get_key2(&(i * 10)), Some(num) if *num == i * 100 )));
    assert!((1..=6).all(|i| matches!( map.get_keys(&i, &(i * 10)), Some(num) if *num == i * 100 )));
    assert!((1..=6).all(|i| map.contains_key1(&i)));
    assert!((1..=6).all(|i| map.contains_key2(&(i * 10))));
    assert!((1..=6).all(|i| map.contains_keys(&i, &(i * 10))));

    // --------------------------------------------------------------------------------
    // test with three allocation
    // --------------------------------------------------------------------------------
    let mut map = DHashMap::new();
    assert_eq!(map.len(), 0);
    assert!((1..=9).all(|i| map.insert(i, i * 10, i * 100).is_none()));
    assert_eq!(map.len(), 9);

    let m2 = map.clone();

    // cloned map is the same length and contains the same keys and values
    assert_eq!(map.capacity(), m2.capacity());
    assert_eq!(m2.len(), 9);
    assert!((1..=9).all(|i| matches!( m2.get_key1(&i), Some(num) if *num == i * 100 )));
    assert!((1..=9).all(|i| matches!( m2.get_key2(&(i * 10)), Some(num) if *num == i * 100 )));
    assert!((1..=9).all(|i| matches!( m2.get_keys(&i, &(i * 10)), Some(num) if *num == i * 100 )));
    assert!((1..=9).all(|i| m2.contains_key1(&i)));
    assert!((1..=9).all(|i| m2.contains_key2(&(i * 10))));
    assert!((1..=9).all(|i| m2.contains_keys(&i, &(i * 10))));

    // sourse map is not changed
    assert_eq!(map.len(), 9);
    assert!((1..=9).all(|i| matches!( map.get_key1(&i), Some(num) if *num == i * 100 )));
    assert!((1..=9).all(|i| matches!( map.get_key2(&(i * 10)), Some(num) if *num == i * 100 )));
    assert!((1..=9).all(|i| matches!( map.get_keys(&i, &(i * 10)), Some(num) if *num == i * 100 )));
    assert!((1..=9).all(|i| map.contains_key1(&i)));
    assert!((1..=9).all(|i| map.contains_key2(&(i * 10))));
    assert!((1..=9).all(|i| map.contains_keys(&i, &(i * 10))));
}

#[test]
#[cfg_attr(miri, ignore)]
fn test_clone_with_copy_type_complex() {
    // --------------------------------------------------------------------------------
    // test with more allocation
    // --------------------------------------------------------------------------------
    let mut map = DHashMap::new();
    assert_eq!(map.len(), 0);
    assert!((1..=50).all(|i| map.insert(i, i * 10, i * 100).is_none()));
    assert_eq!(map.len(), 50);

    (1..=50).for_each(|i| {
        if i & 1 == 1 {
            map.remove_key1(&i);
        }
    });

    assert!((51..=100).all(|i| map.insert(i, i * 10, i * 100).is_none()));
    assert_eq!(map.len(), 75);

    (51..=100).for_each(|i| {
        if i & 1 == 1 {
            map.remove_key2(&(i * 10));
        }
    });

    assert!((101..=300).all(|i| map.insert(i, i * 10, i * 100).is_none()));
    assert_eq!(map.len(), 250);

    (101..=300).for_each(|i| {
        if i & 1 == 1 {
            map.remove_keys(&i, &(i * 10));
        }
    });

    let m2 = map.clone();

    // cloned map is the same length and contains the same keys and values
    assert_eq!(map.capacity(), m2.capacity());
    assert_eq!(m2.len(), 150);
    assert!((1..=300).all(|i| if i & 1 == 1 {
        !matches!( m2.get_key1(&i), Some(num) if *num == i * 100 )
    } else {
        matches!( m2.get_key1(&i), Some(num) if *num == i * 100 )
    }));
    assert!((1..=300).all(|i| if i & 1 == 1 {
        !matches!( m2.get_key2(&(i * 10)), Some(num) if *num == i * 100 )
    } else {
        matches!( m2.get_key2(&(i * 10)), Some(num) if *num == i * 100 )
    }));
    assert!((1..=300).all(|i| if i & 1 == 1 {
        !matches!( m2.get_keys(&i, &(i * 10)), Some(num) if *num == i * 100 )
    } else {
        matches!( m2.get_keys(&i, &(i * 10)), Some(num) if *num == i * 100 )
    }));

    assert!((1..=300).all(|i| if i & 1 == 1 {
        !m2.contains_key1(&i) && !m2.contains_key2(&(i * 10)) && !m2.contains_keys(&i, &(i * 10))
    } else {
        m2.contains_key1(&i) && m2.contains_key2(&(i * 10)) && m2.contains_keys(&i, &(i * 10))
    }));

    // sourse map is not changed
    assert_eq!(map.len(), 150);
    assert!((1..=300).all(|i| if i & 1 == 1 {
        !matches!( map.get_key1(&i), Some(num) if *num == i * 100 )
    } else {
        matches!( map.get_key1(&i), Some(num) if *num == i * 100 )
    }));
    assert!((1..=300).all(|i| if i & 1 == 1 {
        !matches!( map.get_key2(&(i * 10)), Some(num) if *num == i * 100 )
    } else {
        matches!( map.get_key2(&(i * 10)), Some(num) if *num == i * 100 )
    }));
    assert!((1..=300).all(|i| if i & 1 == 1 {
        !matches!( map.get_keys(&i, &(i * 10)), Some(num) if *num == i * 100 )
    } else {
        matches!( map.get_keys(&i, &(i * 10)), Some(num) if *num == i * 100 )
    }));
    assert!((1..=300).all(|i| if i & 1 == 1 {
        !map.contains_key1(&i) && !map.contains_key2(&(i * 10)) && !map.contains_keys(&i, &(i * 10))
    } else {
        map.contains_key1(&i) && map.contains_key2(&(i * 10)) && map.contains_keys(&i, &(i * 10))
    }));
}

#[test]
fn test_clone_with_non_copy_type_simple() {
    // --------------------------------------------------------------------------------
    // test with one allocation
    // --------------------------------------------------------------------------------
    let mut vec: Vec<_> = (1..=3)
        .map(|i| (i.to_string(), (i * 10).to_string(), (i * 100).to_string()))
        .collect();

    let mut map = DHashMap::new();
    assert_eq!(map.len(), 0);

    assert!(vec
        .iter()
        .all(|(k1, k2, v)| map.insert(k1.clone(), k2.clone(), v.clone()).is_none()));
    assert_eq!(map.len(), 3);

    let m2 = map.clone();

    // cloned map is the same length and contains the same keys and values
    assert_eq!(map.capacity(), m2.capacity());
    assert_eq!(m2.len(), 3);
    assert!(vec
        .iter()
        .all(|(k1, _, v)| matches!( m2.get_key1(k1), Some(value) if value == v )));
    assert!(vec
        .iter()
        .all(|(_, k2, v)| matches!( m2.get_key2(k2), Some(value) if value == v )));
    assert!(vec
        .iter()
        .all(|(k1, k2, v)| matches!( m2.get_keys(k1, k2), Some(value) if value == v )));
    assert!(vec.iter().all(|(k1, _, _)| m2.contains_key1(k1)));
    assert!(vec.iter().all(|(_, k2, _)| m2.contains_key2(k2)));
    assert!(vec.iter().all(|(k1, k2, _)| m2.contains_keys(k1, k2)));

    // sourse map is not changed
    assert_eq!(map.len(), 3);
    assert!(vec
        .iter()
        .all(|(k1, _, v)| matches!( map.get_key1(k1), Some(value) if value == v )));
    assert!(vec
        .iter()
        .all(|(_, k2, v)| matches!( map.get_key2(k2), Some(value) if value == v )));
    assert!(vec
        .iter()
        .all(|(k1, k2, v)| matches!( map.get_keys(k1, k2), Some(value) if value == v )));
    assert!(vec.iter().all(|(k1, _, _)| map.contains_key1(k1)));
    assert!(vec.iter().all(|(_, k2, _)| map.contains_key2(k2)));
    assert!(vec.iter().all(|(k1, k2, _)| map.contains_keys(k1, k2)));

    // --------------------------------------------------------------------------------
    // test with two allocation
    // --------------------------------------------------------------------------------
    vec.extend((4..=6).map(|i| (i.to_string(), (i * 10).to_string(), (i * 100).to_string())));

    let mut map = DHashMap::new();
    assert_eq!(map.len(), 0);

    assert!(vec
        .iter()
        .all(|(k1, k2, v)| map.insert(k1.clone(), k2.clone(), v.clone()).is_none()));
    assert_eq!(map.len(), 6);

    let m2 = map.clone();

    // cloned map is the same length and contains the same keys and values
    assert_eq!(map.capacity(), m2.capacity());
    assert_eq!(m2.len(), 6);
    assert!(vec
        .iter()
        .all(|(k1, _, v)| matches!( m2.get_key1(k1), Some(value) if value == v )));
    assert!(vec
        .iter()
        .all(|(_, k2, v)| matches!( m2.get_key2(k2), Some(value) if value == v )));
    assert!(vec
        .iter()
        .all(|(k1, k2, v)| matches!( m2.get_keys(k1, k2), Some(value) if value == v )));
    assert!(vec.iter().all(|(k1, _, _)| m2.contains_key1(k1)));
    assert!(vec.iter().all(|(_, k2, _)| m2.contains_key2(k2)));
    assert!(vec.iter().all(|(k1, k2, _)| m2.contains_keys(k1, k2)));

    // sourse map is not changed
    assert_eq!(map.len(), 6);
    assert!(vec
        .iter()
        .all(|(k1, _, v)| matches!( map.get_key1(k1), Some(value) if value == v )));
    assert!(vec
        .iter()
        .all(|(_, k2, v)| matches!( map.get_key2(k2), Some(value) if value == v )));
    assert!(vec
        .iter()
        .all(|(k1, k2, v)| matches!( map.get_keys(k1, k2), Some(value) if value == v )));
    assert!(vec.iter().all(|(k1, _, _)| map.contains_key1(k1)));
    assert!(vec.iter().all(|(_, k2, _)| map.contains_key2(k2)));
    assert!(vec.iter().all(|(k1, k2, _)| map.contains_keys(k1, k2)));

    // --------------------------------------------------------------------------------
    // test with three allocation
    // --------------------------------------------------------------------------------
    vec.extend((7..=9).map(|i| (i.to_string(), (i * 10).to_string(), (i * 100).to_string())));

    let mut map = DHashMap::new();
    assert_eq!(map.len(), 0);

    assert!(vec
        .iter()
        .all(|(k1, k2, v)| map.insert(k1.clone(), k2.clone(), v.clone()).is_none()));
    assert_eq!(map.len(), 9);

    let m2 = map.clone();

    // cloned map is the same length and contains the same keys and values
    assert_eq!(map.capacity(), m2.capacity());
    assert_eq!(m2.len(), 9);
    assert!(vec
        .iter()
        .all(|(k1, _, v)| matches!( m2.get_key1(k1), Some(value) if value == v )));
    assert!(vec
        .iter()
        .all(|(_, k2, v)| matches!( m2.get_key2(k2), Some(value) if value == v )));
    assert!(vec
        .iter()
        .all(|(k1, k2, v)| matches!( m2.get_keys(k1, k2), Some(value) if value == v )));
    assert!(vec.iter().all(|(k1, _, _)| m2.contains_key1(k1)));
    assert!(vec.iter().all(|(_, k2, _)| m2.contains_key2(k2)));
    assert!(vec.iter().all(|(k1, k2, _)| m2.contains_keys(k1, k2)));

    // sourse map is not changed
    assert_eq!(map.len(), 9);
    assert!(vec
        .iter()
        .all(|(k1, _, v)| matches!( map.get_key1(k1), Some(value) if value == v )));
    assert!(vec
        .iter()
        .all(|(_, k2, v)| matches!( map.get_key2(k2), Some(value) if value == v )));
    assert!(vec
        .iter()
        .all(|(k1, k2, v)| matches!( map.get_keys(k1, k2), Some(value) if value == v )));
    assert!(vec.iter().all(|(k1, _, _)| map.contains_key1(k1)));
    assert!(vec.iter().all(|(_, k2, _)| map.contains_key2(k2)));
    assert!(vec.iter().all(|(k1, k2, _)| map.contains_keys(k1, k2)));
}

#[test]
#[cfg_attr(miri, ignore)]
fn test_clone_with_non_copy_type_complex() {
    // --------------------------------------------------------------------------------
    // test with more allocation
    // --------------------------------------------------------------------------------
    let mut vec: Vec<(String, String, String)> = Vec::with_capacity(300);
    vec.extend((1..=300).map(|i| (i.to_string(), (i * 10).to_string(), (i * 100).to_string())));

    let mut map = DHashMap::new();
    assert_eq!(map.len(), 0);
    assert!(vec
        .iter()
        .take(50)
        .all(|(k1, k2, v)| map.insert(k1.clone(), k2.clone(), v.clone()).is_none()));
    assert_eq!(map.len(), 50);

    vec.iter().take(50).enumerate().for_each(|(i, (k1, _, _))| {
        if i & 1 == 1 {
            map.remove_key1(k1);
        }
    });

    assert!(vec
        .iter()
        .skip(50)
        .take(50)
        .all(|(k1, k2, v)| map.insert(k1.clone(), k2.clone(), v.clone()).is_none()));
    assert_eq!(map.len(), 75);

    vec.iter()
        .skip(50)
        .take(50)
        .enumerate()
        .for_each(|(i, (_, k2, _))| {
            if i & 1 == 1 {
                map.remove_key2(k2);
            }
        });

    assert!(vec
        .iter()
        .skip(100)
        .all(|(k1, k2, v)| map.insert(k1.clone(), k2.clone(), v.clone()).is_none()));
    assert_eq!(map.len(), 250);

    vec.iter()
        .skip(100)
        .enumerate()
        .for_each(|(i, (k1, k2, _))| {
            if i & 1 == 1 {
                map.remove_keys(k1, k2);
            }
        });

    let m2 = map.clone();

    // cloned map is the same length and contains the same keys and values
    assert_eq!(map.capacity(), m2.capacity());
    assert_eq!(m2.len(), 150);
    assert!(vec.iter().enumerate().all(|(i, (k1, _, v))| if i & 1 == 1 {
        !matches!( m2.get_key1(k1), Some(value) if value == v )
    } else {
        matches!( m2.get_key1(k1), Some(value) if value == v )
    }));
    assert!(vec.iter().enumerate().all(|(i, (_, k2, v))| if i & 1 == 1 {
        !matches!( m2.get_key2(k2), Some(value) if value == v )
    } else {
        matches!( m2.get_key2(k2), Some(value) if value == v )
    }));
    assert!(vec
        .iter()
        .enumerate()
        .all(|(i, (k1, k2, v))| if i & 1 == 1 {
            !matches!( m2.get_keys(k1, k2), Some(value) if value == v )
        } else {
            matches!( m2.get_keys(k1, k2), Some(value) if value == v )
        }));
    assert!(vec
        .iter()
        .enumerate()
        .all(|(i, (k1, k2, _))| if i & 1 == 1 {
            !m2.contains_key1(k1) && !m2.contains_key2(k2) && !m2.contains_keys(k1, k2)
        } else {
            m2.contains_key1(k1) && m2.contains_key2(k2) && m2.contains_keys(k1, k2)
        }));

    // sourse map is not changed
    assert_eq!(map.len(), 150);
    assert!(vec.iter().enumerate().all(|(i, (k1, _, v))| if i & 1 == 1 {
        !matches!( map.get_key1(k1), Some(value) if value == v )
    } else {
        matches!( map.get_key1(k1), Some(value) if value == v )
    }));
    assert!(vec.iter().enumerate().all(|(i, (_, k2, v))| if i & 1 == 1 {
        !matches!( map.get_key2(k2), Some(value) if value == v )
    } else {
        matches!( map.get_key2(k2), Some(value) if value == v )
    }));
    assert!(vec
        .iter()
        .enumerate()
        .all(|(i, (k1, k2, v))| if i & 1 == 1 {
            !matches!( map.get_keys(k1, k2), Some(value) if value == v )
        } else {
            matches!( map.get_keys(k1, k2), Some(value) if value == v )
        }));
    assert!(vec
        .iter()
        .enumerate()
        .all(|(i, (k1, k2, _))| if i & 1 == 1 {
            !map.contains_key1(k1) && !map.contains_key2(k2) && !map.contains_keys(k1, k2)
        } else {
            map.contains_key1(k1) && map.contains_key2(k2) && map.contains_keys(k1, k2)
        }));
}

#[test]
fn test_clone_from_with_copy_type_simple() {
    // --------------------------------------------------------------------------------
    // test with one allocation
    // --------------------------------------------------------------------------------
    let mut map = DHashMap::new();
    let mut m2 = DHashMap::new();

    assert_eq!(map.len(), 0);
    assert!((1..=3).all(|i| map.insert(i, i * 10, i * 100).is_none()));
    assert_eq!(map.len(), 3);

    m2.clone_from(&map);

    // cloned map is the same length and contains the same keys and values
    assert_eq!(map.capacity(), m2.capacity());
    assert_eq!(m2.len(), 3);
    assert!((1..=3).all(|i| matches!( m2.get_key1(&i), Some(num) if *num == i * 100 )));
    assert!((1..=3).all(|i| matches!( m2.get_key2(&(i * 10)), Some(num) if *num == i * 100 )));
    assert!((1..=3).all(|i| matches!( m2.get_keys(&i, &(i * 10)), Some(num) if *num == i * 100 )));
    assert!((1..=3).all(|i| m2.contains_key1(&i)));
    assert!((1..=3).all(|i| m2.contains_key2(&(i * 10))));
    assert!((1..=3).all(|i| m2.contains_keys(&i, &(i * 10))));

    // sourse map is not changed
    assert_eq!(map.len(), 3);
    assert!((1..=3).all(|i| matches!( map.get_key1(&i), Some(num) if *num == i * 100 )));
    assert!((1..=3).all(|i| matches!( map.get_key2(&(i * 10)), Some(num) if *num == i * 100 )));
    assert!((1..=3).all(|i| matches!( map.get_keys(&i, &(i * 10)), Some(num) if *num == i * 100 )));
    assert!((1..=3).all(|i| map.contains_key1(&i)));
    assert!((1..=3).all(|i| map.contains_key2(&(i * 10))));
    assert!((1..=3).all(|i| map.contains_keys(&i, &(i * 10))));

    // --------------------------------------------------------------------------------
    // test with two allocation
    // --------------------------------------------------------------------------------
    let mut map = DHashMap::new();
    let mut m2 = DHashMap::new();

    assert_eq!(map.len(), 0);
    assert!((1..=6).all(|i| map.insert(i, i * 10, i * 100).is_none()));
    assert_eq!(map.len(), 6);

    m2.clone_from(&map);

    // cloned map is the same length and contains the same keys and values
    assert_eq!(map.capacity(), m2.capacity());
    assert_eq!(m2.len(), 6);
    assert!((1..=6).all(|i| matches!( m2.get_key1(&i), Some(num) if *num == i * 100 )));
    assert!((1..=6).all(|i| matches!( m2.get_key2(&(i * 10)), Some(num) if *num == i * 100 )));
    assert!((1..=6).all(|i| matches!( m2.get_keys(&i, &(i * 10)), Some(num) if *num == i * 100 )));
    assert!((1..=6).all(|i| m2.contains_key1(&i)));
    assert!((1..=6).all(|i| m2.contains_key2(&(i * 10))));
    assert!((1..=6).all(|i| m2.contains_keys(&i, &(i * 10))));

    // sourse map is not changed
    assert_eq!(map.len(), 6);
    assert!((1..=6).all(|i| matches!( map.get_key1(&i), Some(num) if *num == i * 100 )));
    assert!((1..=6).all(|i| matches!( map.get_key2(&(i * 10)), Some(num) if *num == i * 100 )));
    assert!((1..=6).all(|i| matches!( map.get_keys(&i, &(i * 10)), Some(num) if *num == i * 100 )));
    assert!((1..=6).all(|i| map.contains_key1(&i)));
    assert!((1..=6).all(|i| map.contains_key2(&(i * 10))));
    assert!((1..=6).all(|i| map.contains_keys(&i, &(i * 10))));

    // --------------------------------------------------------------------------------
    // test with three allocation
    // --------------------------------------------------------------------------------
    let mut map = DHashMap::new();
    let mut m2 = DHashMap::new();

    assert_eq!(map.len(), 0);
    assert!((1..=9).all(|i| map.insert(i, i * 10, i * 100).is_none()));
    assert_eq!(map.len(), 9);

    m2.clone_from(&map);

    // cloned map is the same length and contains the same keys and values
    assert_eq!(map.capacity(), m2.capacity());
    assert_eq!(m2.len(), 9);
    assert!((1..=9).all(|i| matches!( m2.get_key1(&i), Some(num) if *num == i * 100 )));
    assert!((1..=9).all(|i| matches!( m2.get_key2(&(i * 10)), Some(num) if *num == i * 100 )));
    assert!((1..=9).all(|i| matches!( m2.get_keys(&i, &(i * 10)), Some(num) if *num == i * 100 )));
    assert!((1..=9).all(|i| m2.contains_key1(&i)));
    assert!((1..=9).all(|i| m2.contains_key2(&(i * 10))));
    assert!((1..=9).all(|i| m2.contains_keys(&i, &(i * 10))));

    // sourse map is not changed
    assert_eq!(map.len(), 9);
    assert!((1..=9).all(|i| matches!( map.get_key1(&i), Some(num) if *num == i * 100 )));
    assert!((1..=9).all(|i| matches!( map.get_key2(&(i * 10)), Some(num) if *num == i * 100 )));
    assert!((1..=9).all(|i| matches!( map.get_keys(&i, &(i * 10)), Some(num) if *num == i * 100 )));
    assert!((1..=9).all(|i| map.contains_key1(&i)));
    assert!((1..=9).all(|i| map.contains_key2(&(i * 10))));
    assert!((1..=9).all(|i| map.contains_keys(&i, &(i * 10))));
}

#[test]
#[cfg_attr(miri, ignore)]
fn test_clone_from_with_copy_type_complex() {
    // --------------------------------------------------------------------------------
    // test with more allocation
    // --------------------------------------------------------------------------------
    let mut map = DHashMap::new();
    let mut m2 = DHashMap::new();

    assert_eq!(map.len(), 0);
    assert!((1..=50).all(|i| map.insert(i, i * 10, i * 100).is_none()));
    assert_eq!(map.len(), 50);

    (1..=50).for_each(|i| {
        if i & 1 == 1 {
            map.remove_key1(&i);
        }
    });

    assert!((51..=100).all(|i| map.insert(i, i * 10, i * 100).is_none()));
    assert_eq!(map.len(), 75);

    (51..=100).for_each(|i| {
        if i & 1 == 1 {
            map.remove_key2(&(i * 10));
        }
    });

    assert!((101..=300).all(|i| map.insert(i, i * 10, i * 100).is_none()));
    assert_eq!(map.len(), 250);

    (101..=300).for_each(|i| {
        if i & 1 == 1 {
            map.remove_keys(&i, &(i * 10));
        }
    });

    m2.clone_from(&map);

    // cloned map is the same length and contains the same keys and values
    assert_eq!(map.capacity(), m2.capacity());
    assert_eq!(m2.len(), 150);
    assert!((1..=300).all(|i| if i & 1 == 1 {
        !matches!( m2.get_key1(&i), Some(num) if *num == i * 100 )
    } else {
        matches!( m2.get_key1(&i), Some(num) if *num == i * 100 )
    }));
    assert!((1..=300).all(|i| if i & 1 == 1 {
        !matches!( m2.get_key2(&(i * 10)), Some(num) if *num == i * 100 )
    } else {
        matches!( m2.get_key2(&(i * 10)), Some(num) if *num == i * 100 )
    }));
    assert!((1..=300).all(|i| if i & 1 == 1 {
        !matches!( m2.get_keys(&i, &(i * 10)), Some(num) if *num == i * 100 )
    } else {
        matches!( m2.get_keys(&i, &(i * 10)), Some(num) if *num == i * 100 )
    }));

    assert!((1..=300).all(|i| if i & 1 == 1 {
        !m2.contains_key1(&i) && !m2.contains_key2(&(i * 10)) && !m2.contains_keys(&i, &(i * 10))
    } else {
        m2.contains_key1(&i) && m2.contains_key2(&(i * 10)) && m2.contains_keys(&i, &(i * 10))
    }));

    // sourse map is not changed
    assert_eq!(map.len(), 150);
    assert!((1..=300).all(|i| if i & 1 == 1 {
        !matches!( map.get_key1(&i), Some(num) if *num == i * 100 )
    } else {
        matches!( map.get_key1(&i), Some(num) if *num == i * 100 )
    }));
    assert!((1..=300).all(|i| if i & 1 == 1 {
        !matches!( map.get_key2(&(i * 10)), Some(num) if *num == i * 100 )
    } else {
        matches!( map.get_key2(&(i * 10)), Some(num) if *num == i * 100 )
    }));
    assert!((1..=300).all(|i| if i & 1 == 1 {
        !matches!( map.get_keys(&i, &(i * 10)), Some(num) if *num == i * 100 )
    } else {
        matches!( map.get_keys(&i, &(i * 10)), Some(num) if *num == i * 100 )
    }));
    assert!((1..=300).all(|i| if i & 1 == 1 {
        !map.contains_key1(&i) && !map.contains_key2(&(i * 10)) && !map.contains_keys(&i, &(i * 10))
    } else {
        map.contains_key1(&i) && map.contains_key2(&(i * 10)) && map.contains_keys(&i, &(i * 10))
    }));
}

#[test]
fn test_clone_from_with_non_copy_type_simple() {
    // --------------------------------------------------------------------------------
    // test with one allocation
    // --------------------------------------------------------------------------------
    let mut vec: Vec<_> = (1..=3)
        .map(|i| (i.to_string(), (i * 10).to_string(), (i * 100).to_string()))
        .collect();

    let mut map = DHashMap::new();
    let mut m2 = DHashMap::new();

    assert_eq!(map.len(), 0);

    assert!(vec
        .iter()
        .all(|(k1, k2, v)| map.insert(k1.clone(), k2.clone(), v.clone()).is_none()));
    assert_eq!(map.len(), 3);

    m2.clone_from(&map);

    // cloned map is the same length and contains the same keys and values
    assert_eq!(map.capacity(), m2.capacity());
    assert_eq!(m2.len(), 3);
    assert!(vec
        .iter()
        .all(|(k1, _, v)| matches!( m2.get_key1(k1), Some(value) if value == v )));
    assert!(vec
        .iter()
        .all(|(_, k2, v)| matches!( m2.get_key2(k2), Some(value) if value == v )));
    assert!(vec
        .iter()
        .all(|(k1, k2, v)| matches!( m2.get_keys(k1, k2), Some(value) if value == v )));
    assert!(vec.iter().all(|(k1, _, _)| m2.contains_key1(k1)));
    assert!(vec.iter().all(|(_, k2, _)| m2.contains_key2(k2)));
    assert!(vec.iter().all(|(k1, k2, _)| m2.contains_keys(k1, k2)));

    // sourse map is not changed
    assert_eq!(map.len(), 3);
    assert!(vec
        .iter()
        .all(|(k1, _, v)| matches!( map.get_key1(k1), Some(value) if value == v )));
    assert!(vec
        .iter()
        .all(|(_, k2, v)| matches!( map.get_key2(k2), Some(value) if value == v )));
    assert!(vec
        .iter()
        .all(|(k1, k2, v)| matches!( map.get_keys(k1, k2), Some(value) if value == v )));
    assert!(vec.iter().all(|(k1, _, _)| map.contains_key1(k1)));
    assert!(vec.iter().all(|(_, k2, _)| map.contains_key2(k2)));
    assert!(vec.iter().all(|(k1, k2, _)| map.contains_keys(k1, k2)));

    // --------------------------------------------------------------------------------
    // test with two allocation
    // --------------------------------------------------------------------------------
    vec.extend((4..=6).map(|i| (i.to_string(), (i * 10).to_string(), (i * 100).to_string())));

    let mut map = DHashMap::new();
    let mut m2 = DHashMap::new();

    assert_eq!(map.len(), 0);

    assert!(vec
        .iter()
        .all(|(k1, k2, v)| map.insert(k1.clone(), k2.clone(), v.clone()).is_none()));
    assert_eq!(map.len(), 6);

    m2.clone_from(&map);

    // cloned map is the same length and contains the same keys and values
    assert_eq!(map.capacity(), m2.capacity());
    assert_eq!(m2.len(), 6);
    assert!(vec
        .iter()
        .all(|(k1, _, v)| matches!( m2.get_key1(k1), Some(value) if value == v )));
    assert!(vec
        .iter()
        .all(|(_, k2, v)| matches!( m2.get_key2(k2), Some(value) if value == v )));
    assert!(vec
        .iter()
        .all(|(k1, k2, v)| matches!( m2.get_keys(k1, k2), Some(value) if value == v )));
    assert!(vec.iter().all(|(k1, _, _)| m2.contains_key1(k1)));
    assert!(vec.iter().all(|(_, k2, _)| m2.contains_key2(k2)));
    assert!(vec.iter().all(|(k1, k2, _)| m2.contains_keys(k1, k2)));

    // sourse map is not changed
    assert_eq!(map.len(), 6);
    assert!(vec
        .iter()
        .all(|(k1, _, v)| matches!( map.get_key1(k1), Some(value) if value == v )));
    assert!(vec
        .iter()
        .all(|(_, k2, v)| matches!( map.get_key2(k2), Some(value) if value == v )));
    assert!(vec
        .iter()
        .all(|(k1, k2, v)| matches!( map.get_keys(k1, k2), Some(value) if value == v )));
    assert!(vec.iter().all(|(k1, _, _)| map.contains_key1(k1)));
    assert!(vec.iter().all(|(_, k2, _)| map.contains_key2(k2)));
    assert!(vec.iter().all(|(k1, k2, _)| map.contains_keys(k1, k2)));

    // --------------------------------------------------------------------------------
    // test with three allocation
    // --------------------------------------------------------------------------------
    vec.extend((7..=9).map(|i| (i.to_string(), (i * 10).to_string(), (i * 100).to_string())));

    let mut map = DHashMap::new();
    let mut m2 = DHashMap::new();

    assert_eq!(map.len(), 0);

    assert!(vec
        .iter()
        .all(|(k1, k2, v)| map.insert(k1.clone(), k2.clone(), v.clone()).is_none()));
    assert_eq!(map.len(), 9);

    m2.clone_from(&map);

    // cloned map is the same length and contains the same keys and values
    assert_eq!(map.capacity(), m2.capacity());
    assert_eq!(m2.len(), 9);
    assert!(vec
        .iter()
        .all(|(k1, _, v)| matches!( m2.get_key1(k1), Some(value) if value == v )));
    assert!(vec
        .iter()
        .all(|(_, k2, v)| matches!( m2.get_key2(k2), Some(value) if value == v )));
    assert!(vec
        .iter()
        .all(|(k1, k2, v)| matches!( m2.get_keys(k1, k2), Some(value) if value == v )));
    assert!(vec.iter().all(|(k1, _, _)| m2.contains_key1(k1)));
    assert!(vec.iter().all(|(_, k2, _)| m2.contains_key2(k2)));
    assert!(vec.iter().all(|(k1, k2, _)| m2.contains_keys(k1, k2)));

    // sourse map is not changed
    assert_eq!(map.len(), 9);
    assert!(vec
        .iter()
        .all(|(k1, _, v)| matches!( map.get_key1(k1), Some(value) if value == v )));
    assert!(vec
        .iter()
        .all(|(_, k2, v)| matches!( map.get_key2(k2), Some(value) if value == v )));
    assert!(vec
        .iter()
        .all(|(k1, k2, v)| matches!( map.get_keys(k1, k2), Some(value) if value == v )));
    assert!(vec.iter().all(|(k1, _, _)| map.contains_key1(k1)));
    assert!(vec.iter().all(|(_, k2, _)| map.contains_key2(k2)));
    assert!(vec.iter().all(|(k1, k2, _)| map.contains_keys(k1, k2)));
}

#[test]
#[cfg_attr(miri, ignore)]
fn test_clone_from_with_non_copy_type_complex() {
    // --------------------------------------------------------------------------------
    // test with more allocation
    // --------------------------------------------------------------------------------
    let mut vec: Vec<(String, String, String)> = Vec::with_capacity(300);
    vec.extend((1..=300).map(|i| (i.to_string(), (i * 10).to_string(), (i * 100).to_string())));

    let mut map = DHashMap::new();
    let mut m2 = DHashMap::new();

    assert_eq!(map.len(), 0);
    assert!(vec
        .iter()
        .take(50)
        .all(|(k1, k2, v)| map.insert(k1.clone(), k2.clone(), v.clone()).is_none()));
    assert_eq!(map.len(), 50);

    vec.iter().take(50).enumerate().for_each(|(i, (k1, _, _))| {
        if i & 1 == 1 {
            map.remove_key1(k1);
        }
    });

    assert!(vec
        .iter()
        .skip(50)
        .take(50)
        .all(|(k1, k2, v)| map.insert(k1.clone(), k2.clone(), v.clone()).is_none()));
    assert_eq!(map.len(), 75);

    vec.iter()
        .skip(50)
        .take(50)
        .enumerate()
        .for_each(|(i, (_, k2, _))| {
            if i & 1 == 1 {
                map.remove_key2(k2);
            }
        });

    assert!(vec
        .iter()
        .skip(100)
        .all(|(k1, k2, v)| map.insert(k1.clone(), k2.clone(), v.clone()).is_none()));
    assert_eq!(map.len(), 250);

    vec.iter()
        .skip(100)
        .enumerate()
        .for_each(|(i, (k1, k2, _))| {
            if i & 1 == 1 {
                map.remove_keys(k1, k2);
            }
        });

    m2.clone_from(&map);

    // cloned map is the same length and contains the same keys and values
    assert_eq!(map.capacity(), m2.capacity());
    assert_eq!(m2.len(), 150);
    assert!(vec.iter().enumerate().all(|(i, (k1, _, v))| if i & 1 == 1 {
        !matches!( m2.get_key1(k1), Some(value) if value == v )
    } else {
        matches!( m2.get_key1(k1), Some(value) if value == v )
    }));
    assert!(vec.iter().enumerate().all(|(i, (_, k2, v))| if i & 1 == 1 {
        !matches!( m2.get_key2(k2), Some(value) if value == v )
    } else {
        matches!( m2.get_key2(k2), Some(value) if value == v )
    }));
    assert!(vec
        .iter()
        .enumerate()
        .all(|(i, (k1, k2, v))| if i & 1 == 1 {
            !matches!( m2.get_keys(k1, k2), Some(value) if value == v )
        } else {
            matches!( m2.get_keys(k1, k2), Some(value) if value == v )
        }));
    assert!(vec
        .iter()
        .enumerate()
        .all(|(i, (k1, k2, _))| if i & 1 == 1 {
            !m2.contains_key1(k1) && !m2.contains_key2(k2) && !m2.contains_keys(k1, k2)
        } else {
            m2.contains_key1(k1) && m2.contains_key2(k2) && m2.contains_keys(k1, k2)
        }));

    // sourse map is not changed
    assert_eq!(map.len(), 150);
    assert!(vec.iter().enumerate().all(|(i, (k1, _, v))| if i & 1 == 1 {
        !matches!( map.get_key1(k1), Some(value) if value == v )
    } else {
        matches!( map.get_key1(k1), Some(value) if value == v )
    }));
    assert!(vec.iter().enumerate().all(|(i, (_, k2, v))| if i & 1 == 1 {
        !matches!( map.get_key2(k2), Some(value) if value == v )
    } else {
        matches!( map.get_key2(k2), Some(value) if value == v )
    }));
    assert!(vec
        .iter()
        .enumerate()
        .all(|(i, (k1, k2, v))| if i & 1 == 1 {
            !matches!( map.get_keys(k1, k2), Some(value) if value == v )
        } else {
            matches!( map.get_keys(k1, k2), Some(value) if value == v )
        }));
    assert!(vec
        .iter()
        .enumerate()
        .all(|(i, (k1, k2, _))| if i & 1 == 1 {
            !map.contains_key1(k1) && !map.contains_key2(k2) && !map.contains_keys(k1, k2)
        } else {
            map.contains_key1(k1) && map.contains_key2(k2) && map.contains_keys(k1, k2)
        }));
}

thread_local! { static DROP_VECTOR: RefCell<Vec<i32>> = RefCell::new(Vec::new()) }

#[derive(Hash, PartialEq, Eq)]
struct Droppable {
    k: usize,
}

impl Droppable {
    fn new(k: usize) -> Droppable {
        DROP_VECTOR.with(|slot| {
            slot.borrow_mut()[k] += 1;
        });

        Droppable { k }
    }
}

impl Drop for Droppable {
    fn drop(&mut self) {
        DROP_VECTOR.with(|slot| {
            slot.borrow_mut()[self.k] -= 1;
        });
    }
}

impl Clone for Droppable {
    fn clone(&self) -> Droppable {
        Droppable::new(self.k)
    }
}

#[test]
fn test_drops() {
    DROP_VECTOR.with(|slot| {
        *slot.borrow_mut() = vec![0; 200];
    });

    {
        let mut m = DHashMap::new();

        DROP_VECTOR.with(|v| {
            for i in 0..200 {
                assert_eq!(v.borrow()[i], 0);
            }
        });

        for i in 0..100 {
            let d1 = Droppable::new(i);
            let d2 = Droppable::new(i);
            let d3 = Droppable::new(i + 100);
            m.insert(d1, d2, d3);
        }

        DROP_VECTOR.with(|v| {
            for i in 0..100 {
                assert_eq!(v.borrow()[i], 2);
            }
            for i in 100..200 {
                assert_eq!(v.borrow()[i], 1);
            }
        });

        for i in 0..50 {
            let k = Droppable::new(i);
            let v = m.remove_key1(&k);

            assert!(v.is_some());

            DROP_VECTOR.with(|v| {
                assert_eq!(v.borrow()[i], 1);
                assert_eq!(v.borrow()[i + 100], 1);
            });
        }

        DROP_VECTOR.with(|v| {
            for i in 0..50 {
                assert_eq!(v.borrow()[i], 0);
                assert_eq!(v.borrow()[i + 100], 0);
            }

            for i in 50..100 {
                assert_eq!(v.borrow()[i], 2);
                assert_eq!(v.borrow()[i + 100], 1);
            }
        });

        for i in 0..50 {
            let d1 = Droppable::new(i);
            let d2 = Droppable::new(i);
            let d3 = Droppable::new(i + 100);
            m.insert(d1, d2, d3);
        }

        DROP_VECTOR.with(|v| {
            for i in 0..100 {
                assert_eq!(v.borrow()[i], 2);
            }
            for i in 100..200 {
                assert_eq!(v.borrow()[i], 1);
            }
        });

        for i in 0..50 {
            let k = Droppable::new(i);
            let v = m.remove_key2(&k);

            assert!(v.is_some());

            DROP_VECTOR.with(|v| {
                assert_eq!(v.borrow()[i], 1);
                assert_eq!(v.borrow()[i + 100], 1);
            });
        }

        DROP_VECTOR.with(|v| {
            for i in 0..50 {
                assert_eq!(v.borrow()[i], 0);
                assert_eq!(v.borrow()[i + 100], 0);
            }

            for i in 50..100 {
                assert_eq!(v.borrow()[i], 2);
                assert_eq!(v.borrow()[i + 100], 1);
            }
        });

        for i in 0..50 {
            let d1 = Droppable::new(i);
            let d2 = Droppable::new(i);
            let d3 = Droppable::new(i + 100);
            m.insert(d1, d2, d3);
        }

        DROP_VECTOR.with(|v| {
            for i in 0..100 {
                assert_eq!(v.borrow()[i], 2);
            }
            for i in 100..200 {
                assert_eq!(v.borrow()[i], 1);
            }
        });

        for i in 0..50 {
            let k = Droppable::new(i);
            let v = m.remove_keys(&k, &k);

            assert!(v.is_some());

            DROP_VECTOR.with(|v| {
                assert_eq!(v.borrow()[i], 1);
                assert_eq!(v.borrow()[i + 100], 1);
            });
        }

        DROP_VECTOR.with(|v| {
            for i in 0..50 {
                assert_eq!(v.borrow()[i], 0);
                assert_eq!(v.borrow()[i + 100], 0);
            }

            for i in 50..100 {
                assert_eq!(v.borrow()[i], 2);
                assert_eq!(v.borrow()[i + 100], 1);
            }
        });
    }

    DROP_VECTOR.with(|v| {
        for i in 0..200 {
            assert_eq!(v.borrow()[i], 0);
        }
    });
}

#[test]
fn test_into_iter_drops() {
    DROP_VECTOR.with(|v| {
        *v.borrow_mut() = vec![0; 200];
    });

    let hm = {
        let mut hm = DHashMap::new();

        DROP_VECTOR.with(|v| {
            for i in 0..200 {
                assert_eq!(v.borrow()[i], 0);
            }
        });

        for i in 0..100 {
            let d1 = Droppable::new(i);
            let d2 = Droppable::new(i);
            let d3 = Droppable::new(i + 100);
            hm.insert(d1, d2, d3);
        }

        DROP_VECTOR.with(|v| {
            for i in 0..100 {
                assert_eq!(v.borrow()[i], 2);
                assert_eq!(v.borrow()[i + 100], 1);
            }
        });

        hm
    };

    // By the way, ensure that cloning doesn't screw up the dropping.
    drop(hm.clone());

    {
        let mut half = hm.into_iter().take(50);

        DROP_VECTOR.with(|v| {
            for i in 0..100 {
                assert_eq!(v.borrow()[i], 2);
                assert_eq!(v.borrow()[i + 100], 1);
            }
        });

        for _ in half.by_ref() {}

        DROP_VECTOR.with(|v| {
            let nk = (0..100).filter(|&i| v.borrow()[i] == 2).count();

            let nv = (0..100).filter(|&i| v.borrow()[i + 100] == 1).count();

            assert_eq!(nk, 50);
            assert_eq!(nv, 50);
        });
    };

    DROP_VECTOR.with(|v| {
        for i in 0..200 {
            assert_eq!(v.borrow()[i], 0);
        }
    });
}

#[cfg(feature = "raw")]
#[test]
fn test_into_pointer_iter_drops() {
    use crate::raw::RawIntoPointerIter;

    DROP_VECTOR.with(|v| {
        *v.borrow_mut() = vec![0; 200];
    });

    let hm = {
        let mut hm = DHashMap::new();

        DROP_VECTOR.with(|v| {
            for i in 0..200 {
                assert_eq!(v.borrow()[i], 0);
            }
        });

        for i in 0..100 {
            let d1 = Droppable::new(i);
            let d2 = Droppable::new(i);
            let d3 = Droppable::new(i + 100);
            hm.insert(d1, d2, d3);
        }

        DROP_VECTOR.with(|v| {
            for i in 0..100 {
                assert_eq!(v.borrow()[i], 2);
                assert_eq!(v.borrow()[i + 100], 1);
            }
        });

        hm
    };

    // By the way, ensure that cloning doesn't screw up the dropping.
    drop(hm.clone());

    {
        fn into_pointer_iter<K1, K2, V, S, A: Allocator + Clone>(
            map: DHashMap<K1, K2, V, S, A>,
        ) -> RawIntoPointerIter<(K1, K2, V), A> {
            let DHashMap { table, .. } = map;
            table.into_pointer_iter()
        }

        let mut half = into_pointer_iter(hm).take(50);

        DROP_VECTOR.with(|v| {
            for i in 0..100 {
                assert_eq!(v.borrow()[i], 2);
                assert_eq!(v.borrow()[i + 100], 1);
            }
        });

        for _ in half.by_ref() {}

        DROP_VECTOR.with(|v| {
            let nk = (0..100).filter(|&i| v.borrow()[i] == 2).count();

            let nv = (0..100).filter(|&i| v.borrow()[i + 100] == 1).count();

            assert_eq!(nk, 50);
            assert_eq!(nv, 50);
        });
    };

    DROP_VECTOR.with(|v| {
        for i in 0..200 {
            assert_eq!(v.borrow()[i], 0);
        }
    });
}

#[test]
fn test_empty_remove() {
    let mut m: DHashMap<i32, i32, bool> = DHashMap::new();

    assert_eq!(m.remove_key1(&0), None);
    assert_eq!(m.remove_key2(&0), None);
    assert_eq!(m.remove_keys(&0, &0), None);

    assert_eq!(m.remove_key1(&0), None);
    assert_eq!(m.remove_key2(&0), None);
    assert_eq!(m.remove_keys(&0, &0), None);

    assert_eq!(m.capacity(), 0);
    assert_eq!(m.get_key1(&0), None);
    assert_eq!(m.get_key2(&0), None);
    assert_eq!(m.get_keys(&0, &0), None);
    assert_eq!(m.len(), 0);
    assert!(!m.contains_key1(&0));
    assert!(!m.contains_key2(&0));
    assert!(!m.contains_keys(&0, &0));
}

#[test]
fn test_empty_entry() {
    // --------------------------------------------------------------------------------
    // test with first allocation
    // --------------------------------------------------------------------------------
    let mut m = DHashMap::new();
    assert_eq!(m.len(), 0);
    assert_eq!(m.capacity(), 0);
    let all_vacant = (1..=3).all(|i| match m.entry(i, i * 10) {
        Ok(entry) => match entry {
            Entry::Occupied(_) => false,
            Entry::Vacant(_) => true,
        },
        Err(_) => false,
    });
    assert!(all_vacant);
    assert_eq!(m.len(), 0);
    assert_eq!(m.capacity(), 0);

    let all_vacant = (1..=3).all(|i| match m.entry(i, i * 10) {
        Ok(entry) => match entry {
            Entry::Occupied(_) => false,
            Entry::Vacant(entry) => {
                entry.insert(i * 100);
                true
            }
        },
        Err(_) => false,
    });
    assert!(all_vacant);
    assert_eq!(m.len(), 3);
    let old_capacity = m.capacity();

    assert!(
        (1..=3).all(|i| matches!( m.get_key1(&i), Some(num) if *num == i * 100 )
            && matches!( m.get_key2(&(i * 10)), Some(num) if *num == i * 100 )
            && matches!( m.get_keys(&i, &(i * 10)), Some(num) if *num == i * 100 ))
    );
    assert_eq!(m.is_empty(), false);
    assert!((1..=3).all(|i| m.contains_key1(&i)
        && m.contains_key2(&(i * 10))
        && m.contains_keys(&i, &(i * 10))));

    // test occupied entry
    let all_occuped = (1..3).all(|i| match m.entry(i, i * 10) {
        Ok(entry) => match entry {
            Entry::Occupied(_) => true,
            Entry::Vacant(_) => false,
        },
        Err(_) => false,
    });
    assert!(all_occuped);

    assert!((1..=3).all(|i| match_entry_error(
        &mut m,
        (&i, &(i * 100)),
        ErrorKind::OccupiedK1AndVacantK2
    )));
    assert!((1..=3).all(|i| match_entry_error(
        &mut m,
        (&(i * 100), &(i * 10)),
        ErrorKind::VacantK1AndOccupiedK2
    )));
    assert!(entry_keys_points_to_diff_entries(
        &mut m,
        &[(1, 10), (2, 20), (3, 30)],
    ));

    // to be sure that nothing changed
    assert_eq!(m.capacity(), old_capacity);
    assert_eq!(m.len(), 3);

    assert!(
        (1..=3).all(|i| matches!( m.get_key1(&i), Some(num) if *num == i * 100 )
            && matches!( m.get_key2(&(i * 10)), Some(num) if *num == i * 100 )
            && matches!( m.get_keys(&i, &(i * 10)), Some(num) if *num == i * 100 ))
    );
    assert_eq!(m.is_empty(), false);
    assert!((1..=3).all(|i| m.contains_key1(&i)
        && m.contains_key2(&(i * 10))
        && m.contains_keys(&i, &(i * 10))));

    // --------------------------------------------------------------------------------
    // test with second allocation
    // --------------------------------------------------------------------------------
    let all_vacant = (4..=6).all(|i| match m.entry(i, i * 10) {
        Ok(entry) => match entry {
            Entry::Occupied(_) => false,
            Entry::Vacant(_) => true,
        },
        Err(_) => false,
    });
    assert!(all_vacant);
    assert_eq!(m.len(), 3);
    assert_eq!(m.capacity(), old_capacity);

    let all_vacant = (4..=6).all(|i| match m.entry(i, i * 10) {
        Ok(entry) => match entry {
            Entry::Occupied(_) => false,
            Entry::Vacant(entry) => {
                entry.insert(i * 100);
                true
            }
        },
        Err(_) => false,
    });
    assert!(all_vacant);
    assert_eq!(m.len(), 6);
    let old_capacity = m.capacity();

    assert!(
        (1..=6).all(|i| matches!( m.get_key1(&i), Some(num) if *num == i * 100 )
            && matches!( m.get_key2(&(i * 10)), Some(num) if *num == i * 100 )
            && matches!( m.get_keys(&i, &(i * 10)), Some(num) if *num == i * 100 ))
    );
    assert_eq!(m.is_empty(), false);
    assert!((1..=6).all(|i| m.contains_key1(&i)
        && m.contains_key2(&(i * 10))
        && m.contains_keys(&i, &(i * 10))));

    // test occupied entry
    let all_occuped = (1..6).all(|i| match m.entry(i, i * 10) {
        Ok(entry) => match entry {
            Entry::Occupied(_) => true,
            Entry::Vacant(_) => false,
        },
        Err(_) => false,
    });
    assert!(all_occuped);

    assert!((1..=6).all(|i| match_entry_error(
        &mut m,
        (&i, &(i * 100)),
        ErrorKind::OccupiedK1AndVacantK2
    )));
    assert!((1..=6).all(|i| match_entry_error(
        &mut m,
        (&(i * 100), &(i * 10)),
        ErrorKind::VacantK1AndOccupiedK2
    )));
    assert!(entry_keys_points_to_diff_entries(
        &mut m,
        &[(1, 10), (2, 20), (3, 30), (4, 40), (5, 50), (6, 60)],
    ));

    // to be sure that nothing changed
    assert_eq!(m.capacity(), old_capacity);
    assert_eq!(m.len(), 6);

    assert!(
        (1..=6).all(|i| matches!( m.get_key1(&i), Some(num) if *num == i * 100 )
            && matches!( m.get_key2(&(i * 10)), Some(num) if *num == i * 100 )
            && matches!( m.get_keys(&i, &(i * 10)), Some(num) if *num == i * 100 ))
    );
    assert_eq!(m.is_empty(), false);
    assert!((1..=6).all(|i| m.contains_key1(&i)
        && m.contains_key2(&(i * 10))
        && m.contains_keys(&i, &(i * 10))));

    // --------------------------------------------------------------------------------
    // test with third allocation
    // --------------------------------------------------------------------------------
    let all_vacant = (7..=9).all(|i| match m.entry(i, i * 10) {
        Ok(entry) => match entry {
            Entry::Occupied(_) => false,
            Entry::Vacant(_) => true,
        },
        Err(_) => false,
    });
    assert!(all_vacant);
    assert_eq!(m.len(), 6);
    assert_eq!(m.capacity(), old_capacity);

    let all_vacant = (7..=9).all(|i| match m.entry(i, i * 10) {
        Ok(entry) => match entry {
            Entry::Occupied(_) => false,
            Entry::Vacant(entry) => {
                entry.insert(i * 100);
                true
            }
        },
        Err(_) => false,
    });
    assert!(all_vacant);
    assert_eq!(m.len(), 9);
    let old_capacity = m.capacity();

    assert!(
        (1..=9).all(|i| matches!( m.get_key1(&i), Some(num) if *num == i * 100 )
            && matches!( m.get_key2(&(i * 10)), Some(num) if *num == i * 100 )
            && matches!( m.get_keys(&i, &(i * 10)), Some(num) if *num == i * 100 ))
    );
    assert_eq!(m.is_empty(), false);
    assert!((1..=9).all(|i| m.contains_key1(&i)
        && m.contains_key2(&(i * 10))
        && m.contains_keys(&i, &(i * 10))));

    // test occupied entry
    let all_occuped = (1..9).all(|i| match m.entry(i, i * 10) {
        Ok(entry) => match entry {
            Entry::Occupied(_) => true,
            Entry::Vacant(_) => false,
        },
        Err(_) => false,
    });
    assert!(all_occuped);

    assert!((1..=9).all(|i| match_entry_error(
        &mut m,
        (&i, &(i * 100)),
        ErrorKind::OccupiedK1AndVacantK2
    )));
    assert!((1..=9).all(|i| match_entry_error(
        &mut m,
        (&(i * 100), &(i * 10)),
        ErrorKind::VacantK1AndOccupiedK2
    )));
    assert!(entry_keys_points_to_diff_entries(
        &mut m,
        &[
            (1, 10),
            (2, 20),
            (3, 30),
            (4, 40),
            (5, 50),
            (6, 60),
            (7, 70),
            (8, 80),
            (9, 90)
        ],
    ));

    // to be sure that nothing changed
    assert_eq!(m.capacity(), old_capacity);
    assert_eq!(m.len(), 9);

    assert!(
        (1..=9).all(|i| matches!( m.get_key1(&i), Some(num) if *num == i * 100 )
            && matches!( m.get_key2(&(i * 10)), Some(num) if *num == i * 100 )
            && matches!( m.get_keys(&i, &(i * 10)), Some(num) if *num == i * 100 ))
    );
    assert_eq!(m.is_empty(), false);
    assert!((1..=9).all(|i| m.contains_key1(&i)
        && m.contains_key2(&(i * 10))
        && m.contains_keys(&i, &(i * 10))));
}

#[test]
fn test_empty_entry_ref() {
    // --------------------------------------------------------------------------------
    // test with first allocation
    // --------------------------------------------------------------------------------
    let vec: Vec<_> = (1..=9)
        .map(|i| (i.to_string(), (i * 10).to_string(), (i * 100)))
        .collect();

    let mut m: DHashMap<String, String, i32> = DHashMap::new();
    assert_eq!(m.len(), 0);
    assert_eq!(m.capacity(), 0);
    let all_vacant = vec
        .iter()
        .take(3)
        .all(|(k1, k2, _)| match m.entry_ref(k1, k2) {
            Ok(entry) => match entry {
                EntryRef::Occupied(_) => false,
                EntryRef::Vacant(_) => true,
            },
            Err(_) => false,
        });
    assert!(all_vacant);
    assert_eq!(m.len(), 0);
    assert_eq!(m.capacity(), 0);

    let all_vacant = vec
        .iter()
        .take(3)
        .all(|(k1, k2, v)| match m.entry_ref(k1, k2) {
            Ok(entry) => match entry {
                EntryRef::Occupied(_) => false,
                EntryRef::Vacant(entry) => {
                    entry.insert(*v);
                    true
                }
            },
            Err(_) => false,
        });
    assert!(all_vacant);
    assert_eq!(m.len(), 3);
    let old_capacity = m.capacity();

    assert!(vec.iter().take(3).all(
        |(k1, k2, v)| matches!( m.get_key1(k1), Some(num) if num == v )
            && matches!( m.get_key2(k2), Some(num) if num == v )
            && matches!( m.get_keys(k1, k2), Some(num) if num == v )
    ));
    assert_eq!(m.is_empty(), false);
    assert!(vec
        .iter()
        .take(3)
        .all(|(k1, k2, _)| m.contains_key1(k1) && m.contains_key2(k2) && m.contains_keys(k1, k2)));

    // test occupied entry
    let all_occuped = vec
        .iter()
        .take(3)
        .all(|(k1, k2, _)| match m.entry_ref(k1, k2) {
            Ok(entry) => match entry {
                EntryRef::Occupied(_) => true,
                EntryRef::Vacant(_) => false,
            },
            Err(_) => false,
        });
    assert!(all_occuped);

    assert!(vec.iter().take(3).all(|(k1, _, _)| match_entry_ref_error(
        &mut m,
        (k1, "some key"),
        ErrorKind::OccupiedK1AndVacantK2
    )));
    assert!(vec.iter().take(3).all(|(_, k2, _)| match_entry_ref_error(
        &mut m,
        ("some key", k2),
        ErrorKind::VacantK1AndOccupiedK2
    )));
    assert!(entry_ref_keys_points_to_diff_entries(
        &mut m,
        &[("1", "10"), ("2", "20"), ("3", "30")],
    ));

    // to be sure that nothing changed
    assert_eq!(m.capacity(), old_capacity);
    assert_eq!(m.len(), 3);

    assert!(vec.iter().take(3).all(
        |(k1, k2, v)| matches!( m.get_key1(k1), Some(num) if num == v )
            && matches!( m.get_key2(k2), Some(num) if num == v )
            && matches!( m.get_keys(k1, k2), Some(num) if num == v )
    ));
    assert_eq!(m.is_empty(), false);
    assert!(vec
        .iter()
        .take(3)
        .all(|(k1, k2, _)| m.contains_key1(k1) && m.contains_key2(k2) && m.contains_keys(k1, k2)));

    // --------------------------------------------------------------------------------
    // test with second allocation
    // --------------------------------------------------------------------------------
    let all_vacant = vec
        .iter()
        .skip(3)
        .take(3)
        .all(|(k1, k2, _)| match m.entry_ref(k1, k2) {
            Ok(entry) => match entry {
                EntryRef::Occupied(_) => false,
                EntryRef::Vacant(_) => true,
            },
            Err(_) => false,
        });
    assert!(all_vacant);
    assert_eq!(m.len(), 3);
    assert_eq!(m.capacity(), old_capacity);

    let all_vacant = vec
        .iter()
        .skip(3)
        .take(3)
        .all(|(k1, k2, v)| match m.entry_ref(k1, k2) {
            Ok(entry) => match entry {
                EntryRef::Occupied(_) => false,
                EntryRef::Vacant(entry) => {
                    entry.insert(*v);
                    true
                }
            },
            Err(_) => false,
        });
    assert!(all_vacant);
    assert_eq!(m.len(), 6);
    let old_capacity = m.capacity();

    assert!(vec.iter().take(6).all(
        |(k1, k2, v)| matches!( m.get_key1(k1), Some(num) if num == v )
            && matches!( m.get_key2(k2), Some(num) if num == v )
            && matches!( m.get_keys(k1, k2), Some(num) if num == v )
    ));
    assert_eq!(m.is_empty(), false);
    assert!(vec
        .iter()
        .take(6)
        .all(|(k1, k2, _)| m.contains_key1(k1) && m.contains_key2(k2) && m.contains_keys(k1, k2)));

    // test occupied entry
    let all_occuped = vec
        .iter()
        .take(6)
        .all(|(k1, k2, _)| match m.entry_ref(k1, k2) {
            Ok(entry) => match entry {
                EntryRef::Occupied(_) => true,
                EntryRef::Vacant(_) => false,
            },
            Err(_) => false,
        });
    assert!(all_occuped);

    assert!(vec.iter().take(6).all(|(k1, _, _)| match_entry_ref_error(
        &mut m,
        (k1, "some key"),
        ErrorKind::OccupiedK1AndVacantK2
    )));
    assert!(vec.iter().take(6).all(|(_, k2, _)| match_entry_ref_error(
        &mut m,
        ("some key", k2),
        ErrorKind::VacantK1AndOccupiedK2
    )));
    assert!(entry_ref_keys_points_to_diff_entries(
        &mut m,
        &[
            ("1", "10"),
            ("2", "20"),
            ("3", "30"),
            ("4", "40"),
            ("5", "50"),
            ("6", "60")
        ],
    ));

    // to be sure that nothing changed
    assert_eq!(m.capacity(), old_capacity);
    assert_eq!(m.len(), 6);

    assert!(vec.iter().take(6).all(
        |(k1, k2, v)| matches!( m.get_key1(k1), Some(num) if num == v )
            && matches!( m.get_key2(k2), Some(num) if num == v )
            && matches!( m.get_keys(k1, k2), Some(num) if num == v )
    ));
    assert_eq!(m.is_empty(), false);
    assert!(vec
        .iter()
        .take(6)
        .all(|(k1, k2, _)| m.contains_key1(k1) && m.contains_key2(k2) && m.contains_keys(k1, k2)));

    // --------------------------------------------------------------------------------
    // test with third allocation
    // --------------------------------------------------------------------------------
    let all_vacant = vec
        .iter()
        .skip(6)
        .all(|(k1, k2, _)| match m.entry_ref(k1, k2) {
            Ok(entry) => match entry {
                EntryRef::Occupied(_) => false,
                EntryRef::Vacant(_) => true,
            },
            Err(_) => false,
        });
    assert!(all_vacant);
    assert_eq!(m.len(), 6);
    assert_eq!(m.capacity(), old_capacity);

    let all_vacant = vec
        .iter()
        .skip(6)
        .all(|(k1, k2, v)| match m.entry_ref(k1, k2) {
            Ok(entry) => match entry {
                EntryRef::Occupied(_) => false,
                EntryRef::Vacant(entry) => {
                    entry.insert(*v);
                    true
                }
            },
            Err(_) => false,
        });
    assert!(all_vacant);
    assert_eq!(m.len(), 9);
    let old_capacity = m.capacity();

    assert!(vec.iter().all(
        |(k1, k2, v)| matches!( m.get_key1(k1), Some(num) if num == v )
            && matches!( m.get_key2(k2), Some(num) if num == v )
            && matches!( m.get_keys(k1, k2), Some(num) if num == v )
    ));
    assert_eq!(m.is_empty(), false);
    assert!(vec
        .iter()
        .all(|(k1, k2, _)| m.contains_key1(k1) && m.contains_key2(k2) && m.contains_keys(k1, k2)));

    // test occupied entry
    let all_occuped = vec.iter().all(|(k1, k2, _)| match m.entry_ref(k1, k2) {
        Ok(entry) => match entry {
            EntryRef::Occupied(_) => true,
            EntryRef::Vacant(_) => false,
        },
        Err(_) => false,
    });
    assert!(all_occuped);

    assert!(vec.iter().all(|(k1, _, _)| match_entry_ref_error(
        &mut m,
        (k1, "some key"),
        ErrorKind::OccupiedK1AndVacantK2
    )));
    assert!(vec.iter().all(|(_, k2, _)| match_entry_ref_error(
        &mut m,
        ("some key", k2),
        ErrorKind::VacantK1AndOccupiedK2
    )));
    assert!(entry_ref_keys_points_to_diff_entries(
        &mut m,
        &[
            ("1", "10"),
            ("2", "20"),
            ("3", "30"),
            ("4", "40"),
            ("5", "50"),
            ("6", "60"),
            ("7", "70"),
            ("8", "80"),
            ("9", "90")
        ],
    ));

    // to be sure that nothing changed
    assert_eq!(m.capacity(), old_capacity);
    assert_eq!(m.len(), 9);

    assert!(vec.iter().all(
        |(k1, k2, v)| matches!( m.get_key1(k1), Some(num) if num == v )
            && matches!( m.get_key2(k2), Some(num) if num == v )
            && matches!( m.get_keys(k1, k2), Some(num) if num == v )
    ));
    assert_eq!(m.is_empty(), false);
    assert!(vec
        .iter()
        .all(|(k1, k2, _)| m.contains_key1(k1) && m.contains_key2(k2) && m.contains_keys(k1, k2)));
}

#[test]
fn test_empty_iter() {
    let mut m: DHashMap<i32, i32, bool> = DHashMap::new();
    assert_eq!(m.drain().next(), None);
    assert_eq!(m.drain_filter(|_k1, _k2, _v| true).next(), None);
    assert_eq!(m.keys().next(), None);
    assert_eq!(m.values().next(), None);
    assert_eq!(m.values_mut().next(), None);
    assert_eq!(m.iter().next(), None);
    assert_eq!(m.iter_mut().next(), None);

    assert_eq!(m.len(), 0);
    assert_eq!(m.capacity(), 0);

    assert!(m.is_empty());
    assert_eq!(m.into_iter().next(), None);

    let mut m: DHashMap<i32, i32, bool> = DHashMap::with_capacity(100);
    assert_eq!(m.drain().next(), None);
    assert_eq!(m.drain_filter(|_k1, _k2, _v| true).next(), None);
    assert_eq!(m.keys().next(), None);
    assert_eq!(m.values().next(), None);
    assert_eq!(m.values_mut().next(), None);
    assert_eq!(m.iter().next(), None);
    assert_eq!(m.iter_mut().next(), None);

    assert_eq!(m.len(), 0);
    assert!(m.capacity() >= 100);

    assert!(m.is_empty());
    assert_eq!(m.into_iter().next(), None);
}

#[cfg(feature = "raw")]
#[test]
fn test_empty_into_pointer_iter() {
    use crate::raw::RawIntoPointerIter;

    fn into_pointer_iter<K1, K2, V, S, A: Allocator + Clone>(
        map: DHashMap<K1, K2, V, S, A>,
    ) -> RawIntoPointerIter<(K1, K2, V), A> {
        let DHashMap { table, .. } = map;
        table.into_pointer_iter()
    }
    let m: DHashMap<i32, i32, bool> = DHashMap::new();
    assert_eq!(into_pointer_iter(m).next(), None);

    let m: DHashMap<i32, i32, bool> = DHashMap::with_capacity(100);
    assert_eq!(m.len(), 0);
    assert!(m.capacity() >= 100);
    assert_eq!(into_pointer_iter(m).next(), None);
}

// #[test]
// #[cfg_attr(miri, ignore)]
// fn test_lots_of_insertions() {
//     let mut m = DHashMap::new();

//     // Try this a few times to make sure we never screw up the hashmap's
//     // internal state.
//     for _ in 0..10 {
//         assert!(m.is_empty());

//         for i in 1..1001 {
//             assert!(m.insert(i, i, i).is_none());

//             for j in 1..=i {
//                 let r = m.get_key1(&j);
//                 assert_eq!(r, Some(&j));
//             }

//             for j in 1..=i {
//                 let r = m.get_key2(&j);
//                 assert_eq!(r, Some(&j));
//             }

//             for j in 1..=i {
//                 let r = m.get_keys(&j, &j);
//                 assert_eq!(r, Some(&j));
//             }

//             for j in i + 1..1001 {
//                 let r = m.get_key1(&j);
//                 assert_eq!(r, None);
//             }

//             for j in i + 1..1001 {
//                 let r = m.get_key2(&j);
//                 assert_eq!(r, None);
//             }

//             for j in i + 1..1001 {
//                 let r = m.get_keys(&j, &j);
//                 assert_eq!(r, None);
//             }
//         }

//         for i in 1001..2001 {
//             assert!(!m.contains_key1(&i));
//         }

//         for i in 1001..2001 {
//             assert!(!m.contains_key2(&i));
//         }

//         for i in 1001..2001 {
//             assert!(!m.contains_keys(&i, &i));
//         }

//         // remove forwards with key #1
//         for i in 1..1001 {
//             assert!(m.remove_key1(&i).is_some());

//             for j in 1..=i {
//                 assert!(!m.contains_key1(&j));
//             }

//             for j in i + 1..1001 {
//                 assert!(m.contains_key1(&j));
//             }
//         }

//         for i in 1..1001 {
//             assert!(m.insert(i, i, i).is_none());
//         }

//         // remove forwards with key #2
//         for i in 1..1001 {
//             assert!(m.remove_key2(&i).is_some());

//             for j in 1..=i {
//                 assert!(!m.contains_key2(&j));
//             }

//             for j in i + 1..1001 {
//                 assert!(m.contains_key2(&j));
//             }
//         }

//         for i in 1..1001 {
//             assert!(m.insert(i, i, i).is_none());
//         }

//         // remove forwards with both keys
//         for i in 1..1001 {
//             assert!(m.remove_keys(&i, &i).is_some());

//             for j in 1..=i {
//                 assert!(!m.contains_keys(&j, &j));
//             }

//             for j in i + 1..1001 {
//                 assert!(m.contains_keys(&j, &j));
//             }
//         }
//         for i in 1..1001 {
//             assert!(!m.contains_key1(&i));
//             assert!(!m.contains_key2(&i));
//             assert!(!m.contains_keys(&i, &i));
//         }

//         for i in 1..1001 {
//             assert!(m.insert(i, i, i).is_none());
//         }

//         // remove backwards with key #1
//         for i in (1..1001).rev() {
//             assert!(m.remove_key1(&i).is_some());

//             for j in i..1001 {
//                 assert!(!m.contains_key1(&j));
//             }

//             for j in 1..i {
//                 assert!(m.contains_key1(&j));
//             }
//         }

//         for i in 1..1001 {
//             assert!(m.insert(i, i, i).is_none());
//         }

//         // remove backwards with key #2
//         for i in (1..1001).rev() {
//             assert!(m.remove_key2(&i).is_some());

//             for j in i..1001 {
//                 assert!(!m.contains_key2(&j));
//             }

//             for j in 1..i {
//                 assert!(m.contains_key2(&j));
//             }
//         }

//         for i in 1..1001 {
//             assert!(m.insert(i, i, i).is_none());
//         }

//         // remove backwards with both keys
//         for i in (1..1001).rev() {
//             assert!(m.remove_keys(&i, &i).is_some());

//             for j in i..1001 {
//                 assert!(!m.contains_keys(&j, &j));
//             }

//             for j in 1..i {
//                 assert!(m.contains_keys(&j, &j));
//             }
//         }
//     }
// }

#[test]
fn test_find_mut() {
    let mut m = DHashMap::new();
    assert!(m.insert(1, 10, 100).is_none());
    assert!(m.insert(2, 20, 200).is_none());
    assert!(m.insert(5, 50, 500).is_none());

    let old_cap = m.capacity();
    assert_eq!(m.len(), 3);

    let new = 100;
    match m.get_mut_key1(&5) {
        None => panic!(),
        Some(x) => *x = new,
    }
    assert_eq!(m.get_key1(&5), Some(&new));
    assert_eq!(m.get_key2(&50), Some(&new));
    assert_eq!(m.get_keys(&5, &50), Some(&new));

    let new = 321;
    match m.get_mut_key2(&50) {
        None => panic!(),
        Some(x) => *x = new,
    }
    assert_eq!(m.get_key1(&5), Some(&new));
    assert_eq!(m.get_key2(&50), Some(&new));
    assert_eq!(m.get_keys(&5, &50), Some(&new));

    let new = 123;
    match m.get_mut_keys(&5, &50) {
        None => panic!(),
        Some(x) => *x = new,
    }
    assert_eq!(m.get_key1(&5), Some(&new));
    assert_eq!(m.get_key2(&50), Some(&new));
    assert_eq!(m.get_keys(&5, &50), Some(&new));

    match m.get_mut_key1(&100) {
        None => {}
        Some(_) => panic!(),
    }
    match m.get_mut_key2(&100) {
        None => {}
        Some(_) => panic!(),
    }
    match m.get_mut_keys(&5, &100) {
        None => {}
        Some(_) => panic!(),
    }
    match m.get_mut_keys(&100, &50) {
        None => {}
        Some(_) => panic!(),
    }
    match m.get_mut_keys(&1, &20) {
        None => {}
        Some(_) => panic!(),
    }

    assert_eq!(m.capacity(), old_cap);
    assert_eq!(m.len(), 3);
}

#[test]
fn test_insert_overwrite() {
    let mut m = DHashMap::new();
    assert!(m.insert(1, 10, 100).is_none());
    assert_eq!(*m.get_key1(&1).unwrap(), 100);
    assert_eq!(*m.get_key2(&10).unwrap(), 100);
    assert_eq!(*m.get_keys(&1, &10).unwrap(), 100);

    assert!(!m.insert(1, 10, 200).is_none());
    assert_eq!(*m.get_key1(&1).unwrap(), 200);
    assert_eq!(*m.get_key2(&10).unwrap(), 200);
    assert_eq!(*m.get_keys(&1, &10).unwrap(), 200);

    assert_eq!(m.len(), 1);
}

#[test]
fn test_entry_insert_overwrite() {
    let mut m = DHashMap::new();

    match m.entry(1, 10).map(|e| e.insert(100)) {
        Ok(_entry) => {}
        Err(_) => panic!(),
    }
    assert_eq!(*m.get_key1(&1).unwrap(), 100);
    assert_eq!(*m.get_key2(&10).unwrap(), 100);
    assert_eq!(*m.get_keys(&1, &10).unwrap(), 100);

    match m.entry(1, 10).map(|e| e.insert(200)) {
        Ok(_entry) => {}
        Err(_) => panic!(),
    }
    assert_eq!(*m.get_key1(&1).unwrap(), 200);
    assert_eq!(*m.get_key2(&10).unwrap(), 200);
    assert_eq!(*m.get_keys(&1, &10).unwrap(), 200);

    assert_eq!(m.len(), 1);
}

#[test]
fn test_raw_entry_insert_overwrite() {
    let mut m = DHashMap::new();

    match m
        .raw_entry_mut()
        .from_keys(&1, &10)
        .map(|e| e.insert(1, 10, 100))
    {
        Ok(_entry) => {}
        Err(_) => panic!(),
    }
    assert_eq!(*m.get_key1(&1).unwrap(), 100);
    assert_eq!(*m.get_key2(&10).unwrap(), 100);
    assert_eq!(*m.get_keys(&1, &10).unwrap(), 100);

    match m
        .raw_entry_mut()
        .from_keys(&1, &10)
        .map(|e| e.insert(1, 10, 200))
    {
        Ok(_entry) => {}
        Err(_) => panic!(),
    }
    assert_eq!(*m.get_key1(&1).unwrap(), 200);
    assert_eq!(*m.get_key2(&10).unwrap(), 200);
    assert_eq!(*m.get_keys(&1, &10).unwrap(), 200);

    assert_eq!(m.len(), 1);
}

#[test]
fn test_insert_conflicts() {
    let mut m = DHashMap::with_capacity(4);
    assert!(m.insert(1, 1, 2).is_none());
    assert!(m.insert(5, 5, 3).is_none());
    assert!(m.insert(9, 9, 4).is_none());

    assert_eq!(*m.get_key1(&9).unwrap(), 4);
    assert_eq!(*m.get_key1(&5).unwrap(), 3);
    assert_eq!(*m.get_key1(&1).unwrap(), 2);

    assert_eq!(*m.get_key2(&9).unwrap(), 4);
    assert_eq!(*m.get_key2(&5).unwrap(), 3);
    assert_eq!(*m.get_key2(&1).unwrap(), 2);

    assert_eq!(*m.get_keys(&9, &9).unwrap(), 4);
    assert_eq!(*m.get_keys(&5, &5).unwrap(), 3);
    assert_eq!(*m.get_keys(&1, &1).unwrap(), 2);

    assert_eq!(m.len(), 3);

    m.clear();

    assert!(m.insert(1, 10, 2).is_none());
    assert!(m.insert(5, 50, 3).is_none());
    assert!(m.insert(9, 90, 4).is_none());

    assert_eq!(*m.get_key1(&9).unwrap(), 4);
    assert_eq!(*m.get_key1(&5).unwrap(), 3);
    assert_eq!(*m.get_key1(&1).unwrap(), 2);

    assert_eq!(*m.get_key2(&90).unwrap(), 4);
    assert_eq!(*m.get_key2(&50).unwrap(), 3);
    assert_eq!(*m.get_key2(&10).unwrap(), 2);

    assert_eq!(*m.get_keys(&9, &90).unwrap(), 4);
    assert_eq!(*m.get_keys(&5, &50).unwrap(), 3);
    assert_eq!(*m.get_keys(&1, &10).unwrap(), 2);

    assert_eq!(m.len(), 3);

    m.clear();

    assert!(m.insert(10, 1, 2).is_none());
    assert!(m.insert(50, 5, 3).is_none());
    assert!(m.insert(90, 9, 4).is_none());

    assert_eq!(*m.get_key1(&90).unwrap(), 4);
    assert_eq!(*m.get_key1(&50).unwrap(), 3);
    assert_eq!(*m.get_key1(&10).unwrap(), 2);

    assert_eq!(*m.get_key2(&9).unwrap(), 4);
    assert_eq!(*m.get_key2(&5).unwrap(), 3);
    assert_eq!(*m.get_key2(&1).unwrap(), 2);

    assert_eq!(*m.get_keys(&90, &9).unwrap(), 4);
    assert_eq!(*m.get_keys(&50, &5).unwrap(), 3);
    assert_eq!(*m.get_keys(&10, &1).unwrap(), 2);

    assert_eq!(m.len(), 3);
}

#[test]
fn test_insert_unique_unchecked_conflicts() {
    let mut m = DHashMap::with_capacity(4);
    assert_eq!(m.insert_unique_unchecked(1, 1, 2), (&1, &1, &mut 2));
    assert_eq!(m.insert_unique_unchecked(5, 5, 3), (&5, &5, &mut 3));
    assert_eq!(m.insert_unique_unchecked(9, 9, 4), (&9, &9, &mut 4));

    assert_eq!(*m.get_key1(&9).unwrap(), 4);
    assert_eq!(*m.get_key1(&5).unwrap(), 3);
    assert_eq!(*m.get_key1(&1).unwrap(), 2);

    assert_eq!(*m.get_key2(&9).unwrap(), 4);
    assert_eq!(*m.get_key2(&5).unwrap(), 3);
    assert_eq!(*m.get_key2(&1).unwrap(), 2);

    assert_eq!(*m.get_keys(&9, &9).unwrap(), 4);
    assert_eq!(*m.get_keys(&5, &5).unwrap(), 3);
    assert_eq!(*m.get_keys(&1, &1).unwrap(), 2);

    assert_eq!(m.len(), 3);

    m.clear();

    assert_eq!(m.insert_unique_unchecked(1, 10, 2), (&1, &10, &mut 2));
    assert_eq!(m.insert_unique_unchecked(5, 50, 3), (&5, &50, &mut 3));
    assert_eq!(m.insert_unique_unchecked(9, 90, 4), (&9, &90, &mut 4));

    assert_eq!(*m.get_key1(&9).unwrap(), 4);
    assert_eq!(*m.get_key1(&5).unwrap(), 3);
    assert_eq!(*m.get_key1(&1).unwrap(), 2);

    assert_eq!(*m.get_key2(&90).unwrap(), 4);
    assert_eq!(*m.get_key2(&50).unwrap(), 3);
    assert_eq!(*m.get_key2(&10).unwrap(), 2);

    assert_eq!(*m.get_keys(&9, &90).unwrap(), 4);
    assert_eq!(*m.get_keys(&5, &50).unwrap(), 3);
    assert_eq!(*m.get_keys(&1, &10).unwrap(), 2);

    assert_eq!(m.len(), 3);

    m.clear();

    assert_eq!(m.insert_unique_unchecked(10, 1, 2), (&10, &1, &mut 2));
    assert_eq!(m.insert_unique_unchecked(50, 5, 3), (&50, &5, &mut 3));
    assert_eq!(m.insert_unique_unchecked(90, 9, 4), (&90, &9, &mut 4));

    assert_eq!(*m.get_key1(&90).unwrap(), 4);
    assert_eq!(*m.get_key1(&50).unwrap(), 3);
    assert_eq!(*m.get_key1(&10).unwrap(), 2);

    assert_eq!(*m.get_key2(&9).unwrap(), 4);
    assert_eq!(*m.get_key2(&5).unwrap(), 3);
    assert_eq!(*m.get_key2(&1).unwrap(), 2);

    assert_eq!(*m.get_keys(&90, &9).unwrap(), 4);
    assert_eq!(*m.get_keys(&50, &5).unwrap(), 3);
    assert_eq!(*m.get_keys(&10, &1).unwrap(), 2);

    assert_eq!(m.len(), 3);
}

#[test]
fn test_entry_insert_conflicts_and_overwrite() {
    let mut m = DHashMap::with_capacity(4);

    match m.entry(1, 1).map(|e| e.insert(2)) {
        Ok(_entry) => {}
        Err(_) => panic!(),
    }
    match m.entry(5, 5).map(|e| e.insert(3)) {
        Ok(_entry) => {}
        Err(_) => panic!(),
    }
    match m.entry(9, 9).map(|e| e.insert(4)) {
        Ok(_entry) => {}
        Err(_) => panic!(),
    }

    assert_eq!(*m.get_key1(&9).unwrap(), 4);
    assert_eq!(*m.get_key1(&5).unwrap(), 3);
    assert_eq!(*m.get_key1(&1).unwrap(), 2);

    assert_eq!(*m.get_key2(&9).unwrap(), 4);
    assert_eq!(*m.get_key2(&5).unwrap(), 3);
    assert_eq!(*m.get_key2(&1).unwrap(), 2);

    assert_eq!(*m.get_keys(&9, &9).unwrap(), 4);
    assert_eq!(*m.get_keys(&5, &5).unwrap(), 3);
    assert_eq!(*m.get_keys(&1, &1).unwrap(), 2);

    assert_eq!(m.len(), 3);

    match m.entry(1, 1).map(|e| e.insert(20)) {
        Ok(_entry) => {}
        Err(_) => panic!(),
    }
    match m.entry(5, 5).map(|e| e.insert(30)) {
        Ok(_entry) => {}
        Err(_) => panic!(),
    }
    match m.entry(9, 9).map(|e| e.insert(40)) {
        Ok(_entry) => {}
        Err(_) => panic!(),
    }

    assert_eq!(*m.get_key1(&9).unwrap(), 40);
    assert_eq!(*m.get_key1(&5).unwrap(), 30);
    assert_eq!(*m.get_key1(&1).unwrap(), 20);

    assert_eq!(*m.get_key2(&9).unwrap(), 40);
    assert_eq!(*m.get_key2(&5).unwrap(), 30);
    assert_eq!(*m.get_key2(&1).unwrap(), 20);

    assert_eq!(*m.get_keys(&9, &9).unwrap(), 40);
    assert_eq!(*m.get_keys(&5, &5).unwrap(), 30);
    assert_eq!(*m.get_keys(&1, &1).unwrap(), 20);

    assert_eq!(m.len(), 3);

    m.clear();

    match m.entry(1, 10).map(|e| e.insert(2)) {
        Ok(_entry) => {}
        Err(_) => panic!(),
    }
    match m.entry(5, 50).map(|e| e.insert(3)) {
        Ok(_entry) => {}
        Err(_) => panic!(),
    }
    match m.entry(9, 90).map(|e| e.insert(4)) {
        Ok(_entry) => {}
        Err(_) => panic!(),
    }

    assert_eq!(*m.get_key1(&9).unwrap(), 4);
    assert_eq!(*m.get_key1(&5).unwrap(), 3);
    assert_eq!(*m.get_key1(&1).unwrap(), 2);

    assert_eq!(*m.get_key2(&90).unwrap(), 4);
    assert_eq!(*m.get_key2(&50).unwrap(), 3);
    assert_eq!(*m.get_key2(&10).unwrap(), 2);

    assert_eq!(*m.get_keys(&9, &90).unwrap(), 4);
    assert_eq!(*m.get_keys(&5, &50).unwrap(), 3);
    assert_eq!(*m.get_keys(&1, &10).unwrap(), 2);

    assert_eq!(m.len(), 3);

    match m.entry(1, 10).map(|e| e.insert(20)) {
        Ok(_entry) => {}
        Err(_) => panic!(),
    }
    match m.entry(5, 50).map(|e| e.insert(30)) {
        Ok(_entry) => {}
        Err(_) => panic!(),
    }
    match m.entry(9, 90).map(|e| e.insert(40)) {
        Ok(_entry) => {}
        Err(_) => panic!(),
    }

    assert_eq!(*m.get_key1(&9).unwrap(), 40);
    assert_eq!(*m.get_key1(&5).unwrap(), 30);
    assert_eq!(*m.get_key1(&1).unwrap(), 20);

    assert_eq!(*m.get_key2(&90).unwrap(), 40);
    assert_eq!(*m.get_key2(&50).unwrap(), 30);
    assert_eq!(*m.get_key2(&10).unwrap(), 20);

    assert_eq!(*m.get_keys(&9, &90).unwrap(), 40);
    assert_eq!(*m.get_keys(&5, &50).unwrap(), 30);
    assert_eq!(*m.get_keys(&1, &10).unwrap(), 20);

    assert_eq!(m.len(), 3);

    m.clear();

    match m.entry(10, 1).map(|e| e.insert(2)) {
        Ok(_entry) => {}
        Err(_) => panic!(),
    }
    match m.entry(50, 5).map(|e| e.insert(3)) {
        Ok(_entry) => {}
        Err(_) => panic!(),
    }
    match m.entry(90, 9).map(|e| e.insert(4)) {
        Ok(_entry) => {}
        Err(_) => panic!(),
    }

    assert_eq!(*m.get_key1(&90).unwrap(), 4);
    assert_eq!(*m.get_key1(&50).unwrap(), 3);
    assert_eq!(*m.get_key1(&10).unwrap(), 2);

    assert_eq!(*m.get_key2(&9).unwrap(), 4);
    assert_eq!(*m.get_key2(&5).unwrap(), 3);
    assert_eq!(*m.get_key2(&1).unwrap(), 2);

    assert_eq!(*m.get_keys(&90, &9).unwrap(), 4);
    assert_eq!(*m.get_keys(&50, &5).unwrap(), 3);
    assert_eq!(*m.get_keys(&10, &1).unwrap(), 2);

    assert_eq!(m.len(), 3);

    match m.entry(10, 1).map(|e| e.insert(20)) {
        Ok(_entry) => {}
        Err(_) => panic!(),
    }
    match m.entry(50, 5).map(|e| e.insert(30)) {
        Ok(_entry) => {}
        Err(_) => panic!(),
    }
    match m.entry(90, 9).map(|e| e.insert(40)) {
        Ok(_entry) => {}
        Err(_) => panic!(),
    }

    assert_eq!(*m.get_key1(&90).unwrap(), 40);
    assert_eq!(*m.get_key1(&50).unwrap(), 30);
    assert_eq!(*m.get_key1(&10).unwrap(), 20);

    assert_eq!(*m.get_key2(&9).unwrap(), 40);
    assert_eq!(*m.get_key2(&5).unwrap(), 30);
    assert_eq!(*m.get_key2(&1).unwrap(), 20);

    assert_eq!(*m.get_keys(&90, &9).unwrap(), 40);
    assert_eq!(*m.get_keys(&50, &5).unwrap(), 30);
    assert_eq!(*m.get_keys(&10, &1).unwrap(), 20);

    assert_eq!(m.len(), 3);
}

#[test]
fn test_raw_entry_insert_conflicts_and_overwrite() {
    let mut m = DHashMap::with_capacity(4);

    match m
        .raw_entry_mut()
        .from_keys(&1, &1)
        .map(|e| e.insert(1, 1, 2))
    {
        Ok(_entry) => {}
        Err(_) => panic!(),
    }
    match m
        .raw_entry_mut()
        .from_keys(&5, &5)
        .map(|e| e.insert(5, 5, 3))
    {
        Ok(_entry) => {}
        Err(_) => panic!(),
    }
    match m
        .raw_entry_mut()
        .from_keys(&9, &9)
        .map(|e| e.insert(9, 9, 4))
    {
        Ok(_entry) => {}
        Err(_) => panic!(),
    }

    assert_eq!(*m.get_key1(&9).unwrap(), 4);
    assert_eq!(*m.get_key1(&5).unwrap(), 3);
    assert_eq!(*m.get_key1(&1).unwrap(), 2);

    assert_eq!(*m.get_key2(&9).unwrap(), 4);
    assert_eq!(*m.get_key2(&5).unwrap(), 3);
    assert_eq!(*m.get_key2(&1).unwrap(), 2);

    assert_eq!(*m.get_keys(&9, &9).unwrap(), 4);
    assert_eq!(*m.get_keys(&5, &5).unwrap(), 3);
    assert_eq!(*m.get_keys(&1, &1).unwrap(), 2);

    assert_eq!(m.len(), 3);

    match m
        .raw_entry_mut()
        .from_keys(&1, &1)
        .map(|e| e.insert(1, 1, 20))
    {
        Ok(_entry) => {}
        Err(_) => panic!(),
    }
    match m
        .raw_entry_mut()
        .from_keys(&5, &5)
        .map(|e| e.insert(5, 5, 30))
    {
        Ok(_entry) => {}
        Err(_) => panic!(),
    }
    match m
        .raw_entry_mut()
        .from_keys(&9, &9)
        .map(|e| e.insert(9, 9, 40))
    {
        Ok(_entry) => {}
        Err(_) => panic!(),
    }

    assert_eq!(*m.get_key1(&9).unwrap(), 40);
    assert_eq!(*m.get_key1(&5).unwrap(), 30);
    assert_eq!(*m.get_key1(&1).unwrap(), 20);

    assert_eq!(*m.get_key2(&9).unwrap(), 40);
    assert_eq!(*m.get_key2(&5).unwrap(), 30);
    assert_eq!(*m.get_key2(&1).unwrap(), 20);

    assert_eq!(*m.get_keys(&9, &9).unwrap(), 40);
    assert_eq!(*m.get_keys(&5, &5).unwrap(), 30);
    assert_eq!(*m.get_keys(&1, &1).unwrap(), 20);

    assert_eq!(m.len(), 3);

    m.clear();

    match m
        .raw_entry_mut()
        .from_keys(&1, &10)
        .map(|e| e.insert(1, 10, 2))
    {
        Ok(_entry) => {}
        Err(_) => panic!(),
    }
    match m
        .raw_entry_mut()
        .from_keys(&5, &50)
        .map(|e| e.insert(5, 50, 3))
    {
        Ok(_entry) => {}
        Err(_) => panic!(),
    }
    match m
        .raw_entry_mut()
        .from_keys(&9, &90)
        .map(|e| e.insert(9, 90, 4))
    {
        Ok(_entry) => {}
        Err(_) => panic!(),
    }

    assert_eq!(*m.get_key1(&9).unwrap(), 4);
    assert_eq!(*m.get_key1(&5).unwrap(), 3);
    assert_eq!(*m.get_key1(&1).unwrap(), 2);

    assert_eq!(*m.get_key2(&90).unwrap(), 4);
    assert_eq!(*m.get_key2(&50).unwrap(), 3);
    assert_eq!(*m.get_key2(&10).unwrap(), 2);

    assert_eq!(*m.get_keys(&9, &90).unwrap(), 4);
    assert_eq!(*m.get_keys(&5, &50).unwrap(), 3);
    assert_eq!(*m.get_keys(&1, &10).unwrap(), 2);

    assert_eq!(m.len(), 3);

    match m
        .raw_entry_mut()
        .from_keys(&1, &10)
        .map(|e| e.insert(1, 10, 20))
    {
        Ok(_entry) => {}
        Err(_) => panic!(),
    }
    match m
        .raw_entry_mut()
        .from_keys(&5, &50)
        .map(|e| e.insert(5, 50, 30))
    {
        Ok(_entry) => {}
        Err(_) => panic!(),
    }
    match m
        .raw_entry_mut()
        .from_keys(&9, &90)
        .map(|e| e.insert(9, 90, 40))
    {
        Ok(_entry) => {}
        Err(_) => panic!(),
    }

    assert_eq!(*m.get_key1(&9).unwrap(), 40);
    assert_eq!(*m.get_key1(&5).unwrap(), 30);
    assert_eq!(*m.get_key1(&1).unwrap(), 20);

    assert_eq!(*m.get_key2(&90).unwrap(), 40);
    assert_eq!(*m.get_key2(&50).unwrap(), 30);
    assert_eq!(*m.get_key2(&10).unwrap(), 20);

    assert_eq!(*m.get_keys(&9, &90).unwrap(), 40);
    assert_eq!(*m.get_keys(&5, &50).unwrap(), 30);
    assert_eq!(*m.get_keys(&1, &10).unwrap(), 20);

    assert_eq!(m.len(), 3);

    m.clear();

    match m
        .raw_entry_mut()
        .from_keys(&10, &1)
        .map(|e| e.insert(10, 1, 2))
    {
        Ok(_entry) => {}
        Err(_) => panic!(),
    }
    match m
        .raw_entry_mut()
        .from_keys(&50, &5)
        .map(|e| e.insert(50, 5, 3))
    {
        Ok(_entry) => {}
        Err(_) => panic!(),
    }
    match m
        .raw_entry_mut()
        .from_keys(&90, &9)
        .map(|e| e.insert(90, 9, 4))
    {
        Ok(_entry) => {}
        Err(_) => panic!(),
    }

    assert_eq!(*m.get_key1(&90).unwrap(), 4);
    assert_eq!(*m.get_key1(&50).unwrap(), 3);
    assert_eq!(*m.get_key1(&10).unwrap(), 2);

    assert_eq!(*m.get_key2(&9).unwrap(), 4);
    assert_eq!(*m.get_key2(&5).unwrap(), 3);
    assert_eq!(*m.get_key2(&1).unwrap(), 2);

    assert_eq!(*m.get_keys(&90, &9).unwrap(), 4);
    assert_eq!(*m.get_keys(&50, &5).unwrap(), 3);
    assert_eq!(*m.get_keys(&10, &1).unwrap(), 2);

    assert_eq!(m.len(), 3);

    match m
        .raw_entry_mut()
        .from_keys(&10, &1)
        .map(|e| e.insert(10, 1, 20))
    {
        Ok(_entry) => {}
        Err(_) => panic!(),
    }
    match m
        .raw_entry_mut()
        .from_keys(&50, &5)
        .map(|e| e.insert(50, 5, 30))
    {
        Ok(_entry) => {}
        Err(_) => panic!(),
    }
    match m
        .raw_entry_mut()
        .from_keys(&90, &9)
        .map(|e| e.insert(90, 9, 40))
    {
        Ok(_entry) => {}
        Err(_) => panic!(),
    }

    assert_eq!(*m.get_key1(&90).unwrap(), 40);
    assert_eq!(*m.get_key1(&50).unwrap(), 30);
    assert_eq!(*m.get_key1(&10).unwrap(), 20);

    assert_eq!(*m.get_key2(&9).unwrap(), 40);
    assert_eq!(*m.get_key2(&5).unwrap(), 30);
    assert_eq!(*m.get_key2(&1).unwrap(), 20);

    assert_eq!(*m.get_keys(&90, &9).unwrap(), 40);
    assert_eq!(*m.get_keys(&50, &5).unwrap(), 30);
    assert_eq!(*m.get_keys(&10, &1).unwrap(), 20);

    assert_eq!(m.len(), 3);
}

#[test]
fn test_conflict_remove() {
    let mut m = DHashMap::with_capacity(4);
    assert!(m.insert(1, 1, 2).is_none());

    assert_eq!(*m.get_key1(&1).unwrap(), 2);
    assert_eq!(*m.get_key2(&1).unwrap(), 2);
    assert_eq!(*m.get_keys(&1, &1).unwrap(), 2);

    assert!(m.insert(5, 5, 3).is_none());
    assert_eq!(*m.get_key1(&1).unwrap(), 2);
    assert_eq!(*m.get_key1(&5).unwrap(), 3);
    assert_eq!(*m.get_key2(&1).unwrap(), 2);
    assert_eq!(*m.get_key2(&5).unwrap(), 3);
    assert_eq!(*m.get_keys(&1, &1).unwrap(), 2);
    assert_eq!(*m.get_keys(&5, &5).unwrap(), 3);

    assert!(m.insert(9, 9, 4).is_none());
    assert_eq!(*m.get_key1(&1).unwrap(), 2);
    assert_eq!(*m.get_key1(&5).unwrap(), 3);
    assert_eq!(*m.get_key1(&9).unwrap(), 4);
    assert_eq!(*m.get_key2(&1).unwrap(), 2);
    assert_eq!(*m.get_key2(&5).unwrap(), 3);
    assert_eq!(*m.get_key2(&9).unwrap(), 4);
    assert_eq!(*m.get_keys(&1, &1).unwrap(), 2);
    assert_eq!(*m.get_keys(&5, &5).unwrap(), 3);
    assert_eq!(*m.get_keys(&9, &9).unwrap(), 4);

    assert_eq!(m.len(), 3);

    assert!(m.remove_key1(&1).is_some());
    assert_eq!(m.get_key1(&1), None);
    assert_eq!(*m.get_key1(&5).unwrap(), 3);
    assert_eq!(*m.get_key1(&9).unwrap(), 4);
    assert_eq!(m.get_key2(&1), None);
    assert_eq!(*m.get_key2(&5).unwrap(), 3);
    assert_eq!(*m.get_key2(&9).unwrap(), 4);
    assert_eq!(m.get_keys(&1, &1), None);
    assert_eq!(*m.get_keys(&5, &5).unwrap(), 3);
    assert_eq!(*m.get_keys(&9, &9).unwrap(), 4);

    assert!(m.insert(1, 1, 2).is_none());

    assert_eq!(*m.get_key1(&1).unwrap(), 2);
    assert_eq!(*m.get_key2(&1).unwrap(), 2);
    assert_eq!(*m.get_keys(&1, &1).unwrap(), 2);

    assert!(m.remove_key2(&1).is_some());
    assert_eq!(m.get_key1(&1), None);
    assert_eq!(*m.get_key1(&5).unwrap(), 3);
    assert_eq!(*m.get_key1(&9).unwrap(), 4);
    assert_eq!(m.get_key2(&1), None);
    assert_eq!(*m.get_key2(&5).unwrap(), 3);
    assert_eq!(*m.get_key2(&9).unwrap(), 4);
    assert_eq!(m.get_keys(&1, &1), None);
    assert_eq!(*m.get_keys(&5, &5).unwrap(), 3);
    assert_eq!(*m.get_keys(&9, &9).unwrap(), 4);

    assert!(m.insert(1, 1, 2).is_none());

    assert_eq!(*m.get_key1(&1).unwrap(), 2);
    assert_eq!(*m.get_key2(&1).unwrap(), 2);
    assert_eq!(*m.get_keys(&1, &1).unwrap(), 2);

    assert!(m.remove_keys(&1, &1).is_some());
    assert_eq!(m.get_key1(&1), None);
    assert_eq!(*m.get_key1(&5).unwrap(), 3);
    assert_eq!(*m.get_key1(&9).unwrap(), 4);
    assert_eq!(m.get_key2(&1), None);
    assert_eq!(*m.get_key2(&5).unwrap(), 3);
    assert_eq!(*m.get_key2(&9).unwrap(), 4);
    assert_eq!(m.get_keys(&1, &1), None);
    assert_eq!(*m.get_keys(&5, &5).unwrap(), 3);
    assert_eq!(*m.get_keys(&9, &9).unwrap(), 4);

    assert_eq!(m.len(), 2);
}

#[test]
fn test_occupied_entry_conflict_remove() {
    let mut m = DHashMap::with_capacity(4);

    match m.entry(1, 1) {
        Ok(entry) => match entry {
            Entry::Occupied(_) => panic!(),
            Entry::Vacant(e) => e.insert(2),
        },
        Err(_) => panic!(),
    };

    assert_eq!(*m.get_key1(&1).unwrap(), 2);
    assert_eq!(*m.get_key2(&1).unwrap(), 2);
    assert_eq!(*m.get_keys(&1, &1).unwrap(), 2);

    match m.entry(5, 5) {
        Ok(entry) => match entry {
            Entry::Occupied(_) => panic!(),
            Entry::Vacant(e) => e.insert(3),
        },
        Err(_) => panic!(),
    };

    assert_eq!(*m.get_key1(&1).unwrap(), 2);
    assert_eq!(*m.get_key1(&5).unwrap(), 3);
    assert_eq!(*m.get_key2(&1).unwrap(), 2);
    assert_eq!(*m.get_key2(&5).unwrap(), 3);
    assert_eq!(*m.get_keys(&1, &1).unwrap(), 2);
    assert_eq!(*m.get_keys(&5, &5).unwrap(), 3);

    match m.entry(9, 9) {
        Ok(entry) => match entry {
            Entry::Occupied(_) => panic!(),
            Entry::Vacant(e) => e.insert(4),
        },
        Err(_) => panic!(),
    };

    assert_eq!(*m.get_key1(&1).unwrap(), 2);
    assert_eq!(*m.get_key1(&5).unwrap(), 3);
    assert_eq!(*m.get_key1(&9).unwrap(), 4);
    assert_eq!(*m.get_key2(&1).unwrap(), 2);
    assert_eq!(*m.get_key2(&5).unwrap(), 3);
    assert_eq!(*m.get_key2(&9).unwrap(), 4);
    assert_eq!(*m.get_keys(&1, &1).unwrap(), 2);
    assert_eq!(*m.get_keys(&5, &5).unwrap(), 3);
    assert_eq!(*m.get_keys(&9, &9).unwrap(), 4);

    assert_eq!(m.len(), 3);

    match m.entry(1, 1) {
        Ok(entry) => match entry {
            Entry::Occupied(e) => e.remove(),
            Entry::Vacant(_) => panic!(),
        },
        Err(_) => panic!(),
    };

    assert_eq!(m.get_key1(&1), None);
    assert_eq!(*m.get_key1(&5).unwrap(), 3);
    assert_eq!(*m.get_key1(&9).unwrap(), 4);
    assert_eq!(m.get_key2(&1), None);
    assert_eq!(*m.get_key2(&5).unwrap(), 3);
    assert_eq!(*m.get_key2(&9).unwrap(), 4);
    assert_eq!(m.get_keys(&1, &1), None);
    assert_eq!(*m.get_keys(&5, &5).unwrap(), 3);
    assert_eq!(*m.get_keys(&9, &9).unwrap(), 4);

    assert_eq!(m.len(), 2);

    match m.entry(5, 5) {
        Ok(entry) => match entry {
            Entry::Occupied(e) => e.remove(),
            Entry::Vacant(_) => panic!(),
        },
        Err(_) => panic!(),
    };

    assert_eq!(m.get_key1(&1), None);
    assert_eq!(m.get_key1(&5), None);
    assert_eq!(*m.get_key1(&9).unwrap(), 4);
    assert_eq!(m.get_key2(&1), None);
    assert_eq!(m.get_key2(&5), None);
    assert_eq!(*m.get_key2(&9).unwrap(), 4);
    assert_eq!(m.get_keys(&1, &1), None);
    assert_eq!(m.get_keys(&5, &5), None);
    assert_eq!(*m.get_keys(&9, &9).unwrap(), 4);

    assert_eq!(m.len(), 1);
    assert!(!m.contains_key1(&1) && !m.contains_key2(&1) && !m.contains_keys(&1, &1));
    assert!(!m.contains_key1(&5) && !m.contains_key2(&5) && !m.contains_keys(&5, &5));
    assert!(m.contains_key1(&9) && m.contains_key2(&9) && m.contains_keys(&9, &9));
}

#[test]
fn test_raw_occupied_entry_conflict_remove() {
    let mut m = DHashMap::with_capacity(4);

    match m.raw_entry_mut().from_keys(&1, &1) {
        Ok(entry) => match entry {
            RawEntryMut::Occupied(_) => panic!(),
            RawEntryMut::Vacant(e) => e.insert(1, 1, 2),
        },
        Err(_) => panic!(),
    };

    assert_eq!(*m.get_key1(&1).unwrap(), 2);
    assert_eq!(*m.get_key2(&1).unwrap(), 2);
    assert_eq!(*m.get_keys(&1, &1).unwrap(), 2);

    match m.raw_entry_mut().from_keys(&5, &5) {
        Ok(entry) => match entry {
            RawEntryMut::Occupied(_) => panic!(),
            RawEntryMut::Vacant(e) => e.insert(5, 5, 3),
        },
        Err(_) => panic!(),
    };

    assert_eq!(*m.get_key1(&1).unwrap(), 2);
    assert_eq!(*m.get_key1(&5).unwrap(), 3);
    assert_eq!(*m.get_key2(&1).unwrap(), 2);
    assert_eq!(*m.get_key2(&5).unwrap(), 3);
    assert_eq!(*m.get_keys(&1, &1).unwrap(), 2);
    assert_eq!(*m.get_keys(&5, &5).unwrap(), 3);

    match m.raw_entry_mut().from_keys(&9, &9) {
        Ok(entry) => match entry {
            RawEntryMut::Occupied(_) => panic!(),
            RawEntryMut::Vacant(e) => e.insert(9, 9, 4),
        },
        Err(_) => panic!(),
    };

    assert_eq!(*m.get_key1(&1).unwrap(), 2);
    assert_eq!(*m.get_key1(&5).unwrap(), 3);
    assert_eq!(*m.get_key1(&9).unwrap(), 4);
    assert_eq!(*m.get_key2(&1).unwrap(), 2);
    assert_eq!(*m.get_key2(&5).unwrap(), 3);
    assert_eq!(*m.get_key2(&9).unwrap(), 4);
    assert_eq!(*m.get_keys(&1, &1).unwrap(), 2);
    assert_eq!(*m.get_keys(&5, &5).unwrap(), 3);
    assert_eq!(*m.get_keys(&9, &9).unwrap(), 4);

    assert_eq!(m.len(), 3);

    match m.raw_entry_mut().from_keys(&1, &1) {
        Ok(entry) => match entry {
            RawEntryMut::Occupied(e) => e.remove_entry(),
            RawEntryMut::Vacant(_) => panic!(),
        },
        Err(_) => panic!(),
    };

    assert_eq!(m.get_key1(&1), None);
    assert_eq!(*m.get_key1(&5).unwrap(), 3);
    assert_eq!(*m.get_key1(&9).unwrap(), 4);
    assert_eq!(m.get_key2(&1), None);
    assert_eq!(*m.get_key2(&5).unwrap(), 3);
    assert_eq!(*m.get_key2(&9).unwrap(), 4);
    assert_eq!(m.get_keys(&1, &1), None);
    assert_eq!(*m.get_keys(&5, &5).unwrap(), 3);
    assert_eq!(*m.get_keys(&9, &9).unwrap(), 4);

    assert_eq!(m.len(), 2);

    match m.raw_entry_mut().from_keys(&5, &5) {
        Ok(entry) => match entry {
            RawEntryMut::Occupied(e) => e.remove_entry(),
            RawEntryMut::Vacant(_) => panic!(),
        },
        Err(_) => panic!(),
    };

    assert_eq!(m.get_key1(&1), None);
    assert_eq!(m.get_key1(&5), None);
    assert_eq!(*m.get_key1(&9).unwrap(), 4);
    assert_eq!(m.get_key2(&1), None);
    assert_eq!(m.get_key2(&5), None);
    assert_eq!(*m.get_key2(&9).unwrap(), 4);
    assert_eq!(m.get_keys(&1, &1), None);
    assert_eq!(m.get_keys(&5, &5), None);
    assert_eq!(*m.get_keys(&9, &9).unwrap(), 4);

    assert_eq!(m.len(), 1);
    assert!(!m.contains_key1(&1) && !m.contains_key2(&1) && !m.contains_keys(&1, &1));
    assert!(!m.contains_key1(&5) && !m.contains_key2(&5) && !m.contains_keys(&5, &5));
    assert!(m.contains_key1(&9) && m.contains_key2(&9) && m.contains_keys(&9, &9));
}

#[test]
fn test_is_empty() {
    let mut m = DHashMap::with_capacity(4);
    assert!(m.insert(1, 2, 3).is_none());
    assert!(!m.is_empty());
    assert!(m.remove_key1(&1).is_some());
    assert!(m.is_empty());

    assert!(m.insert(1, 2, 3).is_none());
    assert!(!m.is_empty());
    assert!(m.remove_key2(&2).is_some());
    assert!(m.is_empty());

    assert!(m.insert(1, 2, 3).is_none());
    assert!(!m.is_empty());
    assert!(m.remove_keys(&1, &2).is_some());
    assert!(m.is_empty());

    assert!(m.insert(1, 2, 3).is_none());
    assert!(!m.is_empty());

    match m.entry(1, 2) {
        Ok(entry) => match entry {
            Entry::Occupied(e) => assert_eq!(e.remove_entry(), (1, 2, 3)),
            Entry::Vacant(_) => panic!(),
        },
        Err(_) => panic!(),
    };

    assert!(m.is_empty());

    assert!(m.insert(1, 2, 3).is_none());
    assert!(!m.is_empty());

    match m.raw_entry_mut().from_keys(&1, &2) {
        Ok(entry) => match entry {
            RawEntryMut::Occupied(e) => assert_eq!(e.remove_entry(), (1, 2, 3)),
            RawEntryMut::Vacant(_) => panic!(),
        },
        Err(_) => panic!(),
    };

    assert!(m.is_empty());
}

#[test]
fn test_remove() {
    let mut m = DHashMap::new();
    m.insert(1, 2, 3);
    assert_eq!(m.remove_key1(&1), Some(3));
    assert_eq!(m.remove_key1(&1), None);
    assert!(m.is_empty());

    m.insert(1, 2, 3);
    assert_eq!(m.remove_key2(&2), Some(3));
    assert_eq!(m.remove_key2(&2), None);
    assert!(m.is_empty());

    m.insert(1, 2, 3);
    m.insert(9, 5, 6);

    assert_eq!(m.remove_keys(&1, &5), None);
    assert_eq!(m.remove_keys(&9, &2), None);
    assert_eq!(m.remove_keys(&1, &10), None);
    assert_eq!(m.remove_keys(&9, &10), None);
    assert_eq!(m.remove_keys(&10, &2), None);
    assert_eq!(m.remove_keys(&10, &5), None);

    assert_eq!(m.remove_keys(&1, &2), Some(3));
    assert_eq!(m.remove_keys(&1, &2), None);
    assert!(!m.is_empty());
    assert_eq!(m.len(), 1);

    assert_eq!(m.remove_keys(&9, &5), Some(6));
    assert_eq!(m.remove_keys(&9, &5), None);
    assert!(m.is_empty());

    m.insert(1, 2, 3);
    match m.entry(1, 2) {
        Ok(entry) => match entry {
            Entry::Occupied(e) => assert_eq!(e.remove_entry(), (1, 2, 3)),
            Entry::Vacant(_) => panic!(),
        },
        Err(_) => panic!(),
    };

    assert!(m.is_empty());

    m.insert(1, 2, 3);
    match m.raw_entry_mut().from_keys(&1, &2) {
        Ok(entry) => match entry {
            RawEntryMut::Occupied(e) => assert_eq!(e.remove_entry(), (1, 2, 3)),
            RawEntryMut::Vacant(_) => panic!(),
        },
        Err(_) => panic!(),
    };

    assert!(m.is_empty());
}

#[test]
fn test_remove_entry() {
    let mut m = DHashMap::new();
    m.insert(1, 2, 3);
    assert_eq!(m.remove_entry_key1(&1), Some((1, 2, 3)));
    assert_eq!(m.remove_entry_key1(&1), None);
    assert!(m.is_empty());

    m.insert(1, 2, 3);
    assert_eq!(m.remove_entry_key2(&2), Some((1, 2, 3)));
    assert_eq!(m.remove_entry_key2(&2), None);
    assert!(m.is_empty());

    m.insert(1, 2, 3);
    m.insert(9, 5, 6);

    assert_eq!(m.remove_entry_keys(&1, &5), None);
    assert_eq!(m.remove_entry_keys(&9, &2), None);
    assert_eq!(m.remove_entry_keys(&1, &10), None);
    assert_eq!(m.remove_entry_keys(&9, &10), None);
    assert_eq!(m.remove_entry_keys(&10, &2), None);
    assert_eq!(m.remove_entry_keys(&10, &5), None);

    assert_eq!(m.remove_entry_keys(&1, &2), Some((1, 2, 3)));
    assert_eq!(m.remove_entry_keys(&1, &2), None);
    assert!(!m.is_empty());
    assert_eq!(m.len(), 1);

    assert_eq!(m.remove_entry_keys(&9, &5), Some((9, 5, 6)));
    assert_eq!(m.remove_entry_keys(&9, &5), None);
    assert!(m.is_empty());
}

#[test]
fn test_iterate() {
    let mut m = DHashMap::with_capacity(4);
    for i in 0..32 {
        assert!(m.insert(i, i, i * 2).is_none());
    }
    assert_eq!(m.len(), 32);

    let mut observed: u32 = 0;

    for (k1, k2, v) in &m {
        assert_eq!(*k1, *k2);
        assert_eq!(*v, *k1 * 2);
        observed |= 1 << *k1;
    }
    assert_eq!(observed, 0xFFFF_FFFF);
}

#[test]
fn test_iter() {
    let vec = vec![(1, 'a', "One"), (2, 'b', "Two"), (3, 'c', "Three")];
    let map: DHashMap<_, _, _> = vec.into_iter().collect();

    let mut data: Vec<(i32, char, &str)> = map.iter().map(|(k1, k2, v)| (*k1, *k2, *v)).collect();
    data.sort_unstable();
    assert_eq!(data, [(1, 'a', "One"), (2, 'b', "Two"), (3, 'c', "Three")]);
}

#[test]
fn test_keys() {
    let vec = vec![(1, 'a', "One"), (2, 'b', "Two"), (3, 'c', "Three")];
    let map: DHashMap<_, _, _> = vec.into_iter().collect();

    let mut keys: Vec<_> = map.keys().map(|(&k1, &k2)| (k1, k2)).collect();
    keys.sort_unstable();
    assert_eq!(keys, [(1, 'a'), (2, 'b'), (3, 'c')]);
}

#[test]
fn test_values() {
    let vec = vec![(1, 'a', "One"), (2, 'b', "Two"), (3, 'c', "Three")];
    let map: DHashMap<_, _, _> = vec.into_iter().collect();

    let values: Vec<_> = map.values().cloned().collect();
    assert_eq!(values.len(), 3);
    assert!(values.contains(&"One"));
    assert!(values.contains(&"Two"));
    assert!(values.contains(&"Three"));
}

#[test]
fn test_values_mut() {
    let vec = vec![(1, 1, 1), (2, 2, 2), (3, 3, 3)];
    let mut map: DHashMap<_, _, _> = vec.into_iter().collect();
    for value in map.values_mut() {
        *value = (*value) * 2
    }
    let values: Vec<_> = map.values().cloned().collect();
    assert_eq!(values.len(), 3);
    assert!(values.contains(&2));
    assert!(values.contains(&4));
    assert!(values.contains(&6));
}

#[test]
fn test_into_iter() {
    let vec = vec![(1, 'a', "One"), (2, 'b', "Two"), (3, 'c', "Three")];
    let map: DHashMap<_, _, _> = vec.into_iter().collect();
    let mut data: Vec<_> = map.into_iter().collect();

    data.sort_unstable();
    assert_eq!(data, [(1, 'a', "One"), (2, 'b', "Two"), (3, 'c', "Three")]);
}

#[test]
fn test_into_keys() {
    let vec = vec![(1, 'a', "One"), (2, 'b', "Two"), (3, 'c', "Three")];
    let map: DHashMap<_, _, _> = vec.into_iter().collect();
    let mut keys: Vec<_> = map.into_keys().collect();

    keys.sort_unstable();
    assert_eq!(keys, [(1, 'a'), (2, 'b'), (3, 'c')]);
}

#[test]
fn test_into_values() {
    let vec = vec![(1, 'a', "One"), (2, 'b', "Two"), (3, 'c', "Three")];
    let map: DHashMap<_, _, _> = vec.into_iter().collect();
    let values: Vec<_> = map.into_values().collect();

    assert_eq!(values.len(), 3);
    assert!(values.contains(&"One"));
    assert!(values.contains(&"Two"));
    assert!(values.contains(&"Three"));
}

#[cfg(feature = "raw")]
#[test]
fn test_into_pointer_iter() {
    use crate::raw::RawIntoPointerIter;

    fn into_pointer_iter<K1, K2, V, S, A: Allocator + Clone>(
        map: DHashMap<K1, K2, V, S, A>,
    ) -> RawIntoPointerIter<(K1, K2, V), A> {
        let DHashMap { table, .. } = map;
        table.into_pointer_iter()
    }

    let vec = vec![(1, 'a', "One"), (2, 'b', "Two"), (3, 'c', "Three")];
    let map: DHashMap<_, _, _> = vec.into_iter().collect();
    let mut data: Vec<_> = into_pointer_iter(map).collect();

    data.sort_unstable();
    assert_eq!(data, [(1, 'a', "One"), (2, 'b', "Two"), (3, 'c', "Three")]);
}

#[test]
fn test_find() {
    let mut m = DHashMap::new();
    assert!(m.get_key1(&1).is_none());
    assert!(m.get_key2(&2).is_none());
    assert!(m.get_keys(&1, &2).is_none());

    m.insert(1, 2, 3);

    match m.get_key1(&1) {
        None => panic!(),
        Some(v) => assert_eq!(*v, 3),
    }

    match m.get_key2(&2) {
        None => panic!(),
        Some(v) => assert_eq!(*v, 3),
    }

    match m.get_keys(&1, &2) {
        None => panic!(),
        Some(v) => assert_eq!(*v, 3),
    }

    m.insert(4, 5, 6);

    match m.get_key1(&4) {
        None => panic!(),
        Some(v) => assert_eq!(*v, 6),
    }

    match m.get_key2(&5) {
        None => panic!(),
        Some(v) => assert_eq!(*v, 6),
    }

    match m.get_keys(&1, &10) {
        None => {}
        Some(_) => panic!(),
    }

    match m.get_keys(&4, &10) {
        None => {}
        Some(_) => panic!(),
    }

    match m.get_keys(&10, &2) {
        None => {}
        Some(_) => panic!(),
    }

    match m.get_keys(&10, &5) {
        None => {}
        Some(_) => panic!(),
    }

    match m.get_keys(&1, &5) {
        None => {}
        Some(_) => panic!(),
    }

    match m.get_keys(&4, &2) {
        None => {}
        Some(_) => panic!(),
    }

    match m.get_keys(&1, &2) {
        None => panic!(),
        Some(v) => assert_eq!(*v, 3),
    }

    match m.get_keys(&4, &5) {
        None => panic!(),
        Some(v) => assert_eq!(*v, 6),
    }
}

#[test]
fn test_eq() {
    let mut m1 = DHashMap::new();
    m1.insert(1, 2, 3);
    m1.insert(2, 3, 4);
    m1.insert(3, 4, 5);

    let mut m2 = DHashMap::new();
    m2.insert(1, 2, 3);
    m2.insert(2, 3, 4);

    assert!(m1 != m2);

    m2.insert(3, 4, 5);

    assert_eq!(m1, m2);

    assert_eq!(m1.len(), m2.len());
    assert_eq!(m1.capacity(), m2.capacity());

    m2.reserve(10);

    assert_eq!(m1, m2);

    assert_eq!(m1.len(), m2.len());
    assert!(m1.capacity() < m2.capacity());
}

#[test]
fn test_show() {
    let mut map = DHashMap::new();
    let empty: DHashMap<i32, i32, i32> = DHashMap::new();

    map.insert(1, 2, 3);
    map.insert(3, 4, 5);

    let map_str = format!("{:?}", map);

    assert!(map_str == "{(1, 2): 3, (3, 4): 5}" || map_str == "{(1, 2): 3, (3, 4): 5}");
    assert_eq!(format!("{:?}", empty), "{}");
}

#[test]
fn test_expand() {
    let mut m = DHashMap::new();

    assert_eq!(m.len(), 0);
    assert!(m.is_empty());

    let mut i = 0;
    let old_raw_tab_cap = m.raw_capacity();

    while old_raw_tab_cap == m.raw_capacity() {
        m.insert(i, i, i);
        i += 1;
    }

    assert_eq!(m.len(), i);
    assert!(!m.is_empty());
}

#[test]
fn test_behavior_resize_policy() {
    let mut m = DHashMap::new();

    assert_eq!(m.len(), 0);
    assert_eq!(m.raw_capacity(), 1);
    assert!(m.is_empty());

    m.insert(0, 0, 0);
    m.remove_key1(&0);
    assert!(m.is_empty());
    let initial_raw_cap = m.raw_capacity();
    m.reserve(initial_raw_cap);

    let raw_cap = m.raw_capacity();

    assert_eq!(raw_cap, initial_raw_cap * 2);

    let mut i = 0;
    for _ in 0..raw_cap * 3 / 4 {
        m.insert(i, i, i);
        i += 1;
    }
    // three quarters full

    assert_eq!(m.len(), i);
    assert_eq!(m.raw_capacity(), raw_cap);

    for _ in 0..raw_cap / 4 {
        m.insert(i, i, i);
        i += 1;
    }
    // half full

    let new_raw_cap = m.raw_capacity();
    assert_eq!(new_raw_cap, raw_cap * 2);

    for _ in 0..raw_cap / 2 - 1 {
        i -= 1;
        m.remove_key1(&i);
        assert_eq!(m.raw_capacity(), new_raw_cap);
    }

    for _ in 0..raw_cap / 2 - 1 {
        m.insert(i, i, i);
        i += 1;
    }
    assert_eq!(m.raw_capacity(), new_raw_cap);

    for _ in 0..raw_cap / 2 - 1 {
        i -= 1;
        m.remove_key2(&i);
        assert_eq!(m.raw_capacity(), new_raw_cap);
    }

    for _ in 0..raw_cap / 2 - 1 {
        m.insert(i, i, i);
        i += 1;
    }
    assert_eq!(m.raw_capacity(), new_raw_cap);

    for _ in 0..raw_cap / 2 - 1 {
        i -= 1;
        m.remove_keys(&i, &i);
        assert_eq!(m.raw_capacity(), new_raw_cap);
    }

    // A little more than one quarter full.
    m.shrink_to_fit();
    assert_eq!(m.raw_capacity(), raw_cap);
    // again, a little more than half full
    for _ in 0..raw_cap / 2 {
        i -= 1;
        m.remove_key1(&i);
    }
    m.shrink_to_fit();

    assert_eq!(m.len(), i);
    assert!(!m.is_empty());
    assert_eq!(m.raw_capacity(), initial_raw_cap);
}

#[test]
fn test_reserve_shrink_to_fit() {
    let mut m = DHashMap::new();
    m.insert(0, 0, 0);
    m.remove_key1(&0);

    assert!(m.capacity() >= m.len());

    for i in 0..128 {
        m.insert(i, i, i);
    }
    m.reserve(256);

    let usable_cap = m.capacity();
    for i in 128..(128 + 256) {
        m.insert(i, i, i);
        assert_eq!(m.capacity(), usable_cap);
    }

    for i in 100..(128 + 256) {
        assert_eq!(m.remove_key1(&i), Some(i));
    }
    m.shrink_to_fit();

    assert_eq!(m.len(), 100);
    assert!(!m.is_empty());
    assert!(m.capacity() >= m.len());

    for i in 0..100 {
        assert_eq!(m.remove_key1(&i), Some(i));
    }
    m.shrink_to_fit();
    m.insert(0, 0, 0);

    assert_eq!(m.len(), 1);
    assert!(m.capacity() >= m.len());
    assert_eq!(m.remove_key1(&0), Some(0));
    assert!(m.is_empty());

    m.insert(0, 0, 0);
    m.remove_key2(&0);

    assert!(m.capacity() >= m.len());

    for i in 0..128 {
        m.insert(i, i, i);
    }
    m.reserve(256);

    let usable_cap = m.capacity();
    for i in 128..(128 + 256) {
        m.insert(i, i, i);
        assert_eq!(m.capacity(), usable_cap);
    }

    for i in 100..(128 + 256) {
        assert_eq!(m.remove_key2(&i), Some(i));
    }
    m.shrink_to_fit();

    assert_eq!(m.len(), 100);
    assert!(!m.is_empty());
    assert!(m.capacity() >= m.len());

    for i in 0..100 {
        assert_eq!(m.remove_key2(&i), Some(i));
    }
    m.shrink_to_fit();
    m.insert(0, 0, 0);

    assert_eq!(m.len(), 1);
    assert!(m.capacity() >= m.len());
    assert_eq!(m.remove_key2(&0), Some(0));
    assert!(m.is_empty());

    m.insert(0, 0, 0);
    m.remove_keys(&0, &0);

    assert!(m.capacity() >= m.len());

    for i in 0..128 {
        m.insert(i, i, i);
    }
    m.reserve(256);

    let usable_cap = m.capacity();
    for i in 128..(128 + 256) {
        m.insert(i, i, i);
        assert_eq!(m.capacity(), usable_cap);
    }

    for i in 100..(128 + 256) {
        assert_eq!(m.remove_keys(&i, &i), Some(i));
    }
    m.shrink_to_fit();

    assert_eq!(m.len(), 100);
    assert!(!m.is_empty());
    assert!(m.capacity() >= m.len());

    for i in 0..100 {
        assert_eq!(m.remove_keys(&i, &i), Some(i));
    }
    m.shrink_to_fit();
    m.insert(0, 0, 0);

    assert_eq!(m.len(), 1);
    assert!(m.capacity() >= m.len());
    assert_eq!(m.remove_keys(&0, &0), Some(0));
    assert!(m.is_empty());
}

#[test]
fn test_from_iter() {
    let xs = [
        (1, 1, 1),
        (2, 2, 2),
        (2, 2, 2),
        (3, 3, 3),
        (4, 4, 4),
        (5, 5, 5),
        (6, 6, 6),
    ];

    let map: DHashMap<_, _, _> = xs.iter().cloned().collect();

    for &(k1, k2, v) in &xs {
        assert_eq!(map.get_key1(&k1), Some(&v));
        assert_eq!(map.get_key2(&k2), Some(&v));
        assert_eq!(map.get_keys(&k1, &k2), Some(&v));
    }

    assert_eq!(map.iter().len(), xs.len() - 1);
}

#[test]
fn test_size_hint() {
    let xs = [
        (1, 1, 1),
        (2, 2, 2),
        (3, 3, 3),
        (4, 4, 4),
        (5, 5, 5),
        (6, 6, 6),
    ];

    let map: DHashMap<_, _, _> = xs.iter().cloned().collect();

    let mut iter = map.iter();

    for _ in iter.by_ref().take(3) {}

    assert_eq!(iter.size_hint(), (3, Some(3)));
}

#[test]
fn test_iter_len() {
    let xs = [
        (1, 1, 1),
        (2, 2, 2),
        (3, 3, 3),
        (4, 4, 4),
        (5, 5, 5),
        (6, 6, 6),
    ];

    let map: DHashMap<_, _, _> = xs.iter().cloned().collect();

    let mut iter = map.iter();

    for _ in iter.by_ref().take(3) {}

    assert_eq!(iter.len(), 3);
}

#[test]
fn test_mut_size_hint() {
    let xs = [
        (1, 1, 1),
        (2, 2, 2),
        (3, 3, 3),
        (4, 4, 4),
        (5, 5, 5),
        (6, 6, 6),
    ];

    let mut map: DHashMap<_, _, _> = xs.iter().cloned().collect();

    let mut iter = map.iter_mut();

    for _ in iter.by_ref().take(3) {}

    assert_eq!(iter.size_hint(), (3, Some(3)));
}

#[test]
fn test_iter_mut_len() {
    let xs = [
        (1, 1, 1),
        (2, 2, 2),
        (3, 3, 3),
        (4, 4, 4),
        (5, 5, 5),
        (6, 6, 6),
    ];

    let mut map: DHashMap<_, _, _> = xs.iter().cloned().collect();

    let mut iter = map.iter_mut();

    for _ in iter.by_ref().take(3) {}

    assert_eq!(iter.len(), 3);
}

#[test]
fn test_index() {
    let mut map = DHashMap::new();

    map.insert(1, 2, 3);
    map.insert(2, 1, 4);
    map.insert(3, 4, 5);

    assert_eq!(map[&1], 3);
    assert_eq!(map[&2], 4);
    assert_eq!(map[&3], 5);
}

#[test]
#[should_panic]
fn test_index_nonexistent() {
    let mut map = DHashMap::new();

    map.insert(1, 2, 3);
    map.insert(2, 1, 4);
    map.insert(3, 4, 5);

    #[allow(clippy::no_effect)] // false positive lint
    map[&4];
}

#[allow(unused_must_use)]
#[test]
fn test_entry() {
    // Test with two entries

    let mut m: DHashMap<i32, i32, i32> = DHashMap::new();
    assert_eq!(m.len(), 0);
    assert_eq!(m.capacity(), 0);

    match m.entry(1, 10) {
        Ok(entry) => match entry {
            Entry::Vacant(_vacant) => {
                assert_eq!(m.capacity(), 0);
            }
            _ => panic!(),
        },
        _ => panic!(),
    }

    assert_eq!(m.len(), 0);
    assert_eq!(m.capacity(), 0);

    match m.entry(1, 10) {
        Ok(entry) => match entry {
            Entry::Vacant(vacant) => {
                assert_eq!(vacant.insert(100), &mut 100);
            }
            _ => panic!(),
        },
        _ => panic!(),
    }

    match m.entry(2, 20) {
        Ok(entry) => match entry {
            Entry::Vacant(vacant) => {
                assert_eq!(vacant.insert(200), &mut 200);
            }
            _ => panic!(),
        },
        _ => panic!(),
    }

    assert_eq!(*m.get_key1(&1).unwrap(), 100);
    assert_eq!(*m.get_key1(&2).unwrap(), 200);

    assert_eq!(*m.get_key2(&10).unwrap(), 100);
    assert_eq!(*m.get_key2(&20).unwrap(), 200);
    assert_eq!(m.is_empty(), false);
    assert_eq!(m.len(), 2);
    let old_cap = m.capacity();
    assert!(old_cap >= 2);

    match m.entry(1, 10) {
        Ok(entry) => match entry {
            Entry::Occupied(_occupied) => {
                assert_eq!(old_cap, m.capacity());
            }
            _ => panic!(),
        },
        _ => panic!(),
    }

    match m.entry(1, 10) {
        Ok(entry) => match entry {
            Entry::Occupied(mut occupied) => {
                assert_eq!(occupied.insert(1000), 100);
            }
            _ => panic!(),
        },
        _ => panic!(),
    }

    match m.entry(2, 20) {
        Ok(entry) => match entry {
            Entry::Occupied(mut occupied) => {
                assert_eq!(occupied.insert(2000), 200);
            }
            _ => panic!(),
        },
        _ => panic!(),
    }

    assert_eq!(*m.get_key1(&1).unwrap(), 1000);
    assert_eq!(*m.get_key1(&2).unwrap(), 2000);

    assert_eq!(*m.get_key2(&10).unwrap(), 1000);
    assert_eq!(*m.get_key2(&20).unwrap(), 2000);
    assert_eq!(m.len(), 2);
    assert_eq!(old_cap, m.capacity());

    match m.entry(1, 30) {
        Err(EntryError { error, keys }) => {
            assert_eq!(error, ErrorKind::OccupiedK1AndVacantK2);
            assert_eq!(keys, (1, 30));
            assert_eq!(old_cap, m.capacity());
        }
        _ => panic!(),
    }

    match m.entry(2, 40) {
        Err(EntryError { error, keys }) => {
            assert_eq!(error, ErrorKind::OccupiedK1AndVacantK2);
            assert_eq!(keys, (2, 40));
        }
        _ => panic!(),
    }

    match m.entry(3, 10) {
        Err(EntryError { error, keys }) => {
            assert_eq!(error, ErrorKind::VacantK1AndOccupiedK2);
            assert_eq!(keys, (3, 10));
        }
        _ => panic!(),
    }

    match m.entry(4, 20) {
        Err(EntryError { error, keys }) => {
            assert_eq!(error, ErrorKind::VacantK1AndOccupiedK2);
            assert_eq!(keys, (4, 20));
        }
        _ => panic!(),
    }

    match m.entry(1, 20) {
        Err(EntryError { error, keys }) => {
            assert_eq!(error, ErrorKind::KeysPointsToDiffEntries);
            assert_eq!(keys, (1, 20));
            assert_eq!(old_cap, m.capacity());
        }
        _ => panic!(),
    }

    match m.entry(2, 10) {
        Err(EntryError { error, keys }) => {
            assert_eq!(error, ErrorKind::KeysPointsToDiffEntries);
            assert_eq!(keys, (2, 10));
        }
        _ => panic!(),
    }

    assert_eq!(*m.get_key1(&1).unwrap(), 1000);
    assert_eq!(*m.get_key1(&2).unwrap(), 2000);

    assert_eq!(*m.get_key2(&10).unwrap(), 1000);
    assert_eq!(*m.get_key2(&20).unwrap(), 2000);
    assert_eq!(m.len(), 2);
    assert_eq!(old_cap, m.capacity());

    // Test with more than two entries

    let xs = [
        (1, 10, 100),
        (2, 20, 200),
        (3, 30, 300),
        (4, 40, 400),
        (5, 50, 500),
        (6, 60, 600),
    ];

    let mut map: DHashMap<_, _, _> = xs.iter().cloned().collect();

    // Existing key (insert)
    match map.entry(1, 10) {
        Ok(entry) => match entry {
            Entry::Occupied(mut view) => {
                assert_eq!(view.get(), &100);
                assert_eq!(view.insert(1000), 100);
            }
            _ => panic!(),
        },
        _ => panic!(),
    }
    assert_eq!(map.get_key1(&1).unwrap(), &1000);
    assert_eq!(map.len(), 6);

    // Existing key (update)
    match map.entry(2, 20) {
        Ok(entry) => match entry {
            Entry::Occupied(mut view) => {
                let v = view.get_mut();
                let new_v = (*v) * 10;
                *v = new_v;
            }
            _ => panic!(),
        },
        _ => panic!(),
    }
    assert_eq!(map.get_key1(&2).unwrap(), &2000);
    assert_eq!(map.len(), 6);

    // Existing key (take)
    match map.entry(3, 30) {
        Ok(entry) => match entry {
            Entry::Occupied(view) => {
                assert_eq!(view.remove(), 300);
            }
            _ => panic!(),
        },
        _ => panic!(),
    }
    assert_eq!(map.get_key1(&3), None);
    assert_eq!(map.len(), 5);

    // Inexistent key (insert)
    match map.entry(10, 100) {
        Ok(entry) => match entry {
            Entry::Vacant(view) => {
                assert_eq!(*view.insert(10000), 10000);
            }
            _ => panic!(),
        },
        _ => panic!(),
    }
    assert_eq!(map.get_key1(&10).unwrap(), &10000);
    assert_eq!(map.len(), 6);

    let old_cap = map.capacity();

    match map.entry(1, 70) {
        Err(EntryError { error, keys }) => {
            assert_eq!(error, ErrorKind::OccupiedK1AndVacantK2);
            assert_eq!(keys, (1, 70));
            assert_eq!(old_cap, map.capacity());
        }
        _ => panic!(),
    }

    match map.entry(7, 10) {
        Err(EntryError { error, keys }) => {
            assert_eq!(error, ErrorKind::VacantK1AndOccupiedK2);
            assert_eq!(keys, (7, 10));
        }
        _ => panic!(),
    }

    match map.entry(6, 50) {
        Err(EntryError { error, keys }) => {
            assert_eq!(error, ErrorKind::KeysPointsToDiffEntries);
            assert_eq!(keys, (6, 50));
            assert_eq!(old_cap, map.capacity());
        }
        _ => panic!(),
    }

    let mut map = DHashMap::new();
    map.entry(1, 10).map(|e| e.insert(100));
    map.entry(2, 20).map(|e| e.insert(200));
    map.entry(3, 30).map(|e| e.insert(300));
    map.entry(4, 40).map(|e| e.insert(400));
    map.entry(5, 50).map(|e| e.insert(500));
    map.entry(6, 60).map(|e| e.insert(600));
    map.entry(7, 70).map(|e| e.insert(700));
    map.entry(8, 80).map(|e| e.insert(800));

    assert_eq!(map.len(), 8);

    let cap = map.capacity();

    assert!(cap >= 8);

    assert_eq!(map.get_key1(&1).unwrap(), &100);
    assert_eq!(map.get_key1(&2).unwrap(), &200);
    assert_eq!(map.get_key1(&3).unwrap(), &300);
    assert_eq!(map.get_key1(&4).unwrap(), &400);
    assert_eq!(map.get_key1(&5).unwrap(), &500);
    assert_eq!(map.get_key1(&6).unwrap(), &600);
    assert_eq!(map.get_key1(&7).unwrap(), &700);
    assert_eq!(map.get_key1(&8).unwrap(), &800);
    assert_eq!(map.get_key1(&9), None);

    assert_eq!(map.get_key2(&10).unwrap(), &100);
    assert_eq!(map.get_key2(&20).unwrap(), &200);
    assert_eq!(map.get_key2(&30).unwrap(), &300);
    assert_eq!(map.get_key2(&40).unwrap(), &400);
    assert_eq!(map.get_key2(&50).unwrap(), &500);
    assert_eq!(map.get_key2(&60).unwrap(), &600);
    assert_eq!(map.get_key2(&70).unwrap(), &700);
    assert_eq!(map.get_key2(&80).unwrap(), &800);
    assert_eq!(map.get_key2(&90), None);

    assert_eq!(map.get_keys(&1, &10).unwrap(), &100);
    assert_eq!(map.get_keys(&2, &20).unwrap(), &200);
    assert_eq!(map.get_keys(&3, &30).unwrap(), &300);
    assert_eq!(map.get_keys(&4, &40).unwrap(), &400);
    assert_eq!(map.get_keys(&5, &50).unwrap(), &500);
    assert_eq!(map.get_keys(&6, &60).unwrap(), &600);
    assert_eq!(map.get_keys(&7, &70).unwrap(), &700);
    assert_eq!(map.get_keys(&8, &80).unwrap(), &800);
    assert_eq!(map.get_keys(&9, &90), None);

    match map.entry(8, 90) {
        Err(EntryError { error, keys }) => {
            assert_eq!(error, ErrorKind::OccupiedK1AndVacantK2);
            assert_eq!(keys, (8, 90));
        }
        _ => panic!(),
    }

    match map.entry(9, 80) {
        Err(EntryError { error, keys }) => {
            assert_eq!(error, ErrorKind::VacantK1AndOccupiedK2);
            assert_eq!(keys, (9, 80));
        }
        _ => panic!(),
    }

    match map.entry(7, 80) {
        Err(EntryError { error, keys }) => {
            assert_eq!(error, ErrorKind::KeysPointsToDiffEntries);
            assert_eq!(keys, (7, 80));
        }
        _ => panic!(),
    }

    assert_eq!(map.len(), 8);
    assert_eq!(map.capacity(), cap);
}

#[allow(unused_must_use)]
#[test]
fn test_entry_ref() {
    // Test with two entries

    let mut m: DHashMap<String, String, i32> = DHashMap::new();
    assert_eq!(m.len(), 0);
    assert_eq!(m.capacity(), 0);

    match m.entry_ref("One", "Second One") {
        Ok(entry) => match entry {
            EntryRef::Vacant(_vacant) => {
                assert_eq!(m.capacity(), 0);
            }
            _ => panic!(),
        },
        _ => panic!(),
    }

    assert_eq!(m.len(), 0);
    assert_eq!(m.capacity(), 0);

    match m.entry_ref("One", "Second One") {
        Ok(entry) => match entry {
            EntryRef::Vacant(vacant) => {
                assert_eq!(vacant.insert(100), &mut 100);
            }
            _ => panic!(),
        },
        _ => panic!(),
    }

    match m.entry_ref("Two", "Second Two") {
        Ok(entry) => match entry {
            EntryRef::Vacant(vacant) => {
                assert_eq!(vacant.insert(200), &mut 200);
            }
            _ => panic!(),
        },
        _ => panic!(),
    }

    assert_eq!(*m.get_key1("One").unwrap(), 100);
    assert_eq!(*m.get_key1("Two").unwrap(), 200);

    assert_eq!(*m.get_key2("Second One").unwrap(), 100);
    assert_eq!(*m.get_key2("Second Two").unwrap(), 200);
    assert_eq!(m.is_empty(), false);
    assert_eq!(m.len(), 2);
    let old_cap = m.capacity();
    assert!(old_cap >= 2);

    match m.entry_ref("One", "Second One") {
        Ok(entry) => match entry {
            EntryRef::Occupied(_occupied) => {
                assert_eq!(old_cap, m.capacity());
            }
            _ => panic!(),
        },
        _ => panic!(),
    }

    match m.entry_ref("One", "Second One") {
        Ok(entry) => match entry {
            EntryRef::Occupied(mut occupied) => {
                assert_eq!(occupied.insert(1000), 100);
            }
            _ => panic!(),
        },
        _ => panic!(),
    }

    match m.entry_ref("Two", "Second Two") {
        Ok(entry) => match entry {
            EntryRef::Occupied(mut occupied) => {
                assert_eq!(occupied.insert(2000), 200);
            }
            _ => panic!(),
        },
        _ => panic!(),
    }

    assert_eq!(*m.get_key1("One").unwrap(), 1000);
    assert_eq!(*m.get_key1("Two").unwrap(), 2000);

    assert_eq!(*m.get_key2("Second One").unwrap(), 1000);
    assert_eq!(*m.get_key2("Second Two").unwrap(), 2000);
    assert_eq!(m.len(), 2);
    assert_eq!(old_cap, m.capacity());

    match m.entry_ref("One", "Second Three") {
        Err(error) => {
            assert_eq!(error, ErrorKind::OccupiedK1AndVacantK2);
            assert_eq!(old_cap, m.capacity());
        }
        _ => panic!(),
    }

    match m.entry_ref("Two", "Second Four") {
        Err(error) => {
            assert_eq!(error, ErrorKind::OccupiedK1AndVacantK2);
        }
        _ => panic!(),
    }

    match m.entry_ref("Three", "Second One") {
        Err(error) => {
            assert_eq!(error, ErrorKind::VacantK1AndOccupiedK2);
        }
        _ => panic!(),
    }

    match m.entry_ref("Four", "Second Two") {
        Err(error) => {
            assert_eq!(error, ErrorKind::VacantK1AndOccupiedK2);
        }
        _ => panic!(),
    }

    match m.entry_ref("One", "Second Two") {
        Err(error) => {
            assert_eq!(error, ErrorKind::KeysPointsToDiffEntries);
            assert_eq!(old_cap, m.capacity());
        }
        _ => panic!(),
    }

    match m.entry_ref("Two", "Second One") {
        Err(error) => {
            assert_eq!(error, ErrorKind::KeysPointsToDiffEntries);
        }
        _ => panic!(),
    }

    assert_eq!(*m.get_key1("One").unwrap(), 1000);
    assert_eq!(*m.get_key1("Two").unwrap(), 2000);

    assert_eq!(*m.get_key2("Second One").unwrap(), 1000);
    assert_eq!(*m.get_key2("Second Two").unwrap(), 2000);
    assert_eq!(m.len(), 2);
    assert_eq!(old_cap, m.capacity());

    // Test with more than two entries

    let xs = [
        ("One".to_owned(), "10".to_owned(), 100),
        ("Two".to_owned(), "20".to_owned(), 200),
        ("Three".to_owned(), "30".to_owned(), 300),
        ("Four".to_owned(), "40".to_owned(), 400),
        ("Five".to_owned(), "50".to_owned(), 500),
        ("Six".to_owned(), "60".to_owned(), 600),
    ];

    let mut map: DHashMap<_, _, _> = xs.iter().cloned().collect();

    // Existing key (insert)
    match map.entry_ref("One", "10") {
        Ok(entry) => match entry {
            EntryRef::Occupied(mut view) => {
                assert_eq!(view.get(), &100);
                assert_eq!(view.insert(1000), 100);
            }
            _ => panic!(),
        },
        _ => panic!(),
    }
    assert_eq!(map.get_key1("One").unwrap(), &1000);
    assert_eq!(map.len(), 6);

    // Existing key (update)
    match map.entry_ref("Two", "20") {
        Ok(entry) => match entry {
            EntryRef::Occupied(mut view) => {
                let v = view.get_mut();
                let new_v = (*v) * 10;
                *v = new_v;
            }
            _ => panic!(),
        },
        _ => panic!(),
    }
    assert_eq!(map.get_key1("Two").unwrap(), &2000);
    assert_eq!(map.len(), 6);

    // Existing key (take)
    match map.entry_ref("Three", "30") {
        Ok(entry) => match entry {
            EntryRef::Occupied(view) => {
                assert_eq!(view.remove(), 300);
            }
            _ => panic!(),
        },
        _ => panic!(),
    }
    assert_eq!(map.get_key1("Three"), None);
    assert_eq!(map.len(), 5);

    // Inexistent key (insert)
    match map.entry_ref("Ten", "100") {
        Ok(entry) => match entry {
            EntryRef::Vacant(view) => {
                assert_eq!(*view.insert(10000), 10000);
            }
            _ => panic!(),
        },
        _ => panic!(),
    }
    assert_eq!(map.get_key1("Ten").unwrap(), &10000);
    assert_eq!(map.len(), 6);

    let old_cap = map.capacity();

    match map.entry_ref("One", "70") {
        Err(error) => {
            assert_eq!(error, ErrorKind::OccupiedK1AndVacantK2);
            assert_eq!(old_cap, map.capacity());
        }
        _ => panic!(),
    }

    match map.entry_ref("Seven", "10") {
        Err(error) => {
            assert_eq!(error, ErrorKind::VacantK1AndOccupiedK2);
        }
        _ => panic!(),
    }

    match map.entry_ref("Six", "50") {
        Err(error) => {
            assert_eq!(error, ErrorKind::KeysPointsToDiffEntries);
            assert_eq!(old_cap, map.capacity());
        }
        _ => panic!(),
    }

    let mut map: DHashMap<String, String, i32> = DHashMap::new();
    map.entry_ref("1", "10").map(|e| e.insert(100));
    map.entry_ref("2", "20").map(|e| e.insert(200));
    map.entry_ref("3", "30").map(|e| e.insert(300));
    map.entry_ref("4", "40").map(|e| e.insert(400));
    map.entry_ref("5", "50").map(|e| e.insert(500));
    map.entry_ref("6", "60").map(|e| e.insert(600));
    map.entry_ref("7", "70").map(|e| e.insert(700));
    map.entry_ref("8", "80").map(|e| e.insert(800));

    assert_eq!(map.len(), 8);

    let cap = map.capacity();

    assert!(cap >= 8);

    assert_eq!(map.get_key1("1").unwrap(), &100);
    assert_eq!(map.get_key1("2").unwrap(), &200);
    assert_eq!(map.get_key1("3").unwrap(), &300);
    assert_eq!(map.get_key1("4").unwrap(), &400);
    assert_eq!(map.get_key1("5").unwrap(), &500);
    assert_eq!(map.get_key1("6").unwrap(), &600);
    assert_eq!(map.get_key1("7").unwrap(), &700);
    assert_eq!(map.get_key1("8").unwrap(), &800);
    assert_eq!(map.get_key1("9"), None);

    assert_eq!(map.get_key2("10").unwrap(), &100);
    assert_eq!(map.get_key2("20").unwrap(), &200);
    assert_eq!(map.get_key2("30").unwrap(), &300);
    assert_eq!(map.get_key2("40").unwrap(), &400);
    assert_eq!(map.get_key2("50").unwrap(), &500);
    assert_eq!(map.get_key2("60").unwrap(), &600);
    assert_eq!(map.get_key2("70").unwrap(), &700);
    assert_eq!(map.get_key2("80").unwrap(), &800);
    assert_eq!(map.get_key2("90"), None);

    assert_eq!(map.get_keys("1", "10").unwrap(), &100);
    assert_eq!(map.get_keys("2", "20").unwrap(), &200);
    assert_eq!(map.get_keys("3", "30").unwrap(), &300);
    assert_eq!(map.get_keys("4", "40").unwrap(), &400);
    assert_eq!(map.get_keys("5", "50").unwrap(), &500);
    assert_eq!(map.get_keys("6", "60").unwrap(), &600);
    assert_eq!(map.get_keys("7", "70").unwrap(), &700);
    assert_eq!(map.get_keys("8", "80").unwrap(), &800);
    assert_eq!(map.get_keys("9", "90"), None);

    match map.entry_ref("8", "90") {
        Err(error) => {
            assert_eq!(error, ErrorKind::OccupiedK1AndVacantK2);
        }
        _ => panic!(),
    }

    match map.entry_ref("9", "80") {
        Err(error) => {
            assert_eq!(error, ErrorKind::VacantK1AndOccupiedK2);
        }
        _ => panic!(),
    }

    match map.entry_ref("7", "80") {
        Err(error) => {
            assert_eq!(error, ErrorKind::KeysPointsToDiffEntries);
        }
        _ => panic!(),
    }

    assert_eq!(map.len(), 8);
    assert_eq!(map.capacity(), cap);
}

#[test]
fn test_entry_take_doesnt_corrupt() {
    #![allow(deprecated)] //rand
                          // Test for #19292
    fn check<T>(m: &DHashMap<T, T, ()>)
    where
        T: std::cmp::Eq + std::hash::Hash,
    {
        for (k1, k2) in m.keys() {
            assert!(m.contains_key1(k1));
            assert!(m.contains_key2(k2));
            assert!(m.contains_keys(k1, k2));
        }
    }

    let mut m = DHashMap::new();
    let mut rng = thread_rng();

    // Populate the map with some items.
    for _ in 0..50 {
        let x = rng.gen_range(-10..10);
        m.insert(x, x, ());
    }

    for _ in 0..1000 {
        let x = rng.gen_range(-10..10);
        match m.entry(x, x) {
            Ok(entry) => match entry {
                Entry::Vacant(_) => {}
                Entry::Occupied(e) => e.remove(),
            },
            _ => panic!(),
        }

        check(&m);
    }
}

#[test]
fn test_entry_ref_take_doesnt_corrupt() {
    #![allow(deprecated)] //rand
                          // Test for #19292
    fn check<T>(m: &DHashMap<T, T, ()>)
    where
        T: std::cmp::Eq + std::hash::Hash,
    {
        for (k1, k2) in m.keys() {
            assert!(m.contains_key1(k1));
            assert!(m.contains_key2(k2));
            assert!(m.contains_keys(k1, k2));
        }
    }

    let mut m = DHashMap::new();
    let mut rng = thread_rng();

    // Populate the map with some items.
    for _ in 0..50 {
        let mut x = std::string::String::with_capacity(1);
        x.push(rng.gen_range('a'..='z'));
        m.insert(x.clone(), x, ());
    }

    for _ in 0..1000 {
        let mut x = std::string::String::with_capacity(1);
        x.push(rng.gen_range('a'..='z'));
        match m.entry_ref(x.as_str(), x.as_str()) {
            Ok(entry) => match entry {
                EntryRef::Vacant(_) => {}
                EntryRef::Occupied(e) => e.remove(),
            },
            _ => panic!(),
        }

        check(&m);
    }
}

#[test]
fn test_extend_ref_keys_ref_value() {
    use std::ops::AddAssign;
    let mut a = DHashMap::new();
    a.insert(1, "one", "one");
    let mut b = DHashMap::new();
    b.insert(2, "two", "two");
    b.insert(3, "three", "three");

    a.extend(&b);

    assert_eq!(b.len(), 2);

    assert_eq!(a.len(), 3);
    assert_eq!(a[&1], "one");
    assert_eq!(a[&2], "two");
    assert_eq!(a[&3], "three");

    let mut a = DHashMap::new();
    a.insert(0, 0, 0);

    fn create_arr<T: AddAssign<T> + Copy, const N: usize>(start: T, step: T) -> [(T, T, T); N] {
        let mut outs: [(T, T, T); N] = [(start, start, start); N];
        let mut element = step;
        outs.iter_mut().skip(1).for_each(|(k1, k2, v)| {
            *k1 += element;
            *k2 += element;
            *v += element;
            element += step;
        });
        outs
    }

    let vec: Vec<_> = (0..100).map(|i| (i, i, i)).collect();
    let arr = create_arr::<i32, 100>(100, 1);

    let iter_vec = vec.iter().map(|(k1, k2, v)| (k1, k2, v));
    let iter_arr = arr.iter().map(|(k1, k2, v)| (k1, k2, v));

    a.extend(iter_vec);
    a.extend(iter_arr);

    assert_eq!(vec.len(), 100);
    assert_eq!(arr.len(), 100);
    assert_eq!(a.len(), 200);

    for item in 0..200 {
        assert_eq!(a[&item], item);
    }
}

#[test]
fn test_extend_ref_kv_tuple() {
    use std::ops::AddAssign;
    let mut a = DHashMap::new();
    a.insert(0, 0, 0);

    fn create_arr<T: AddAssign<T> + Copy, const N: usize>(start: T, step: T) -> [(T, T, T); N] {
        let mut outs: [(T, T, T); N] = [(start, start, start); N];
        let mut element = step;
        outs.iter_mut().skip(1).for_each(|(k1, k2, v)| {
            *k1 += element;
            *k2 += element;
            *v += element;
            element += step;
        });
        outs
    }

    let for_iter: Vec<_> = (0..100).map(|i| (i, i, i)).collect();
    let iter = for_iter.iter();
    let vec: Vec<_> = (100..200).map(|i| (i, i, i)).collect();
    let arr = create_arr::<i32, 100>(200, 1);
    a.extend(iter);
    a.extend(&vec);
    a.extend(&arr);

    assert_eq!(for_iter.len(), 100);
    assert_eq!(vec.len(), 100);
    assert_eq!(arr.len(), 100);

    assert_eq!(a.len(), 300);

    for item in 0..300 {
        assert_eq!(a[&item], item);
    }
}

#[test]
fn test_capacity_not_less_than_len() {
    let mut a = DHashMap::new();
    let mut item = 0;

    for _ in 0..116 {
        a.insert(item, item, 0);
        item += 1;
    }

    assert!(a.capacity() > a.len());

    let free = a.capacity() - a.len();
    for _ in 0..free {
        a.insert(item, item, 0);
        item += 1;
    }

    assert_eq!(a.len(), a.capacity());

    // Insert at capacity should cause allocation.
    a.insert(item, item, 0);
    assert!(a.capacity() > a.len());
}

#[test]
fn test_occupied_entry_key() {
    let mut a = DHashMap::new();
    let key1 = "Key 1";
    let key2 = "Key 2";
    let value = "Value";

    assert!(a.is_empty());
    a.insert(key1, key2, value);

    assert_eq!(a.get_key1(&key1), Some(&value));
    assert_eq!(a.get_key2(&key2), Some(&value));
    assert_eq!(a.get_keys(&key1, &key2), Some(&value));
    assert!(a.contains_key1(&key1));
    assert!(a.contains_key2(&key2));
    assert!(a.contains_keys(&key1, &key2));

    assert_eq!(a.len(), 1);

    assert_eq!(a[key1], value);

    match a.entry(key1, key2) {
        Ok(entry) => match entry {
            Entry::Vacant(_) => panic!(),
            Entry::Occupied(e) => {
                assert_eq!(key1, *e.key1());
                assert_eq!(key2, *e.key2());
                assert_eq!((&key1, &key2), e.keys());
                assert_eq!(&value, e.get());
            }
        },
        _ => panic!(),
    }

    assert_eq!(a.get_key1(&key1), Some(&value));
    assert_eq!(a.get_key2(&key2), Some(&value));
    assert_eq!(a.get_keys(&key1, &key2), Some(&value));
    assert!(a.contains_key1(&key1));
    assert!(a.contains_key2(&key2));
    assert!(a.contains_keys(&key1, &key2));

    assert_eq!(a.len(), 1);

    assert_eq!(a[key1], value);
}

#[test]
fn test_occupied_entry_ref_key() {
    let mut a = DHashMap::new();
    let key1 = "Key 1";
    let key2 = "Key 2";
    let value = "Value";

    assert!(a.is_empty());
    a.insert(key1.to_owned(), key2.to_owned(), value);

    assert_eq!(a.get_key1(key1), Some(&value));
    assert_eq!(a.get_key2(key2), Some(&value));
    assert_eq!(a.get_keys(key1, key2), Some(&value));
    assert!(a.contains_key1(key1));
    assert!(a.contains_key2(key2));
    assert!(a.contains_keys(key1, key2));

    assert_eq!(a.len(), 1);

    assert_eq!(a[key1], value);

    match a.entry_ref(key1, key2) {
        Ok(entry) => match entry {
            EntryRef::Vacant(_) => panic!(),
            EntryRef::Occupied(e) => {
                assert_eq!(key1, e.key1());
                assert_eq!(key2, e.key2());
                assert_eq!((key1, key2), e.keys());
                assert_eq!(&value, e.get());
            }
        },
        _ => panic!(),
    }

    assert_eq!(a.get_key1(key1), Some(&value));
    assert_eq!(a.get_key2(key2), Some(&value));
    assert_eq!(a.get_keys(key1, key2), Some(&value));
    assert!(a.contains_key1(key1));
    assert!(a.contains_key2(key2));
    assert!(a.contains_keys(key1, key2));

    assert_eq!(a.len(), 1);

    assert_eq!(a[key1], value);
}

#[test]
fn test_vacant_entry_key() {
    let mut a = DHashMap::new();
    let key1 = "Key 1";
    let key2 = "Key 2";
    let value = "Value";

    assert!(a.is_empty());
    match a.entry(key1, key2) {
        Ok(entry) => match entry {
            Entry::Occupied(_) => panic!(),
            Entry::Vacant(e) => {
                assert_eq!(key1, *e.key1());
                assert_eq!(key2, *e.key2());
                assert_eq!((&key1, &key2), e.keys());
                e.insert(value);
            }
        },
        _ => panic!(),
    }

    assert_eq!(a.get_key1(&key1), Some(&value));
    assert_eq!(a.get_key2(&key2), Some(&value));
    assert_eq!(a.get_keys(&key1, &key2), Some(&value));
    assert!(a.contains_key1(&key1));
    assert!(a.contains_key2(&key2));
    assert!(a.contains_keys(&key1, &key2));

    assert_eq!(a.len(), 1);

    assert_eq!(a[key1], value);
}

#[test]
fn test_vacant_entry_ref_key() {
    let mut a: DHashMap<String, String, &str> = DHashMap::new();
    let key1 = "Key 1";
    let key2 = "Key 2";
    let value = "Value";

    assert!(a.is_empty());
    match a.entry_ref(key1, key2) {
        Ok(entry) => match entry {
            EntryRef::Occupied(_) => panic!(),
            EntryRef::Vacant(e) => {
                assert_eq!(key1, e.key1());
                assert_eq!(key2, e.key2());
                assert_eq!((key1, key2), e.keys());
                e.insert(value);
            }
        },
        _ => panic!(),
    }

    assert_eq!(a.get_key1(key1), Some(&value));
    assert_eq!(a.get_key2(key2), Some(&value));
    assert_eq!(a.get_keys(key1, key2), Some(&value));
    assert!(a.contains_key1(key1));
    assert!(a.contains_key2(key2));
    assert!(a.contains_keys(key1, key2));

    assert_eq!(a.len(), 1);

    assert_eq!(a[key1], value);
}

#[test]
fn test_occupied_entry_replace_entry_with() {
    let mut a: DHashMap<&str, &str, &str> = DHashMap::new();

    let key1 = "a key 1";
    let key2 = "a key 2";
    let value = "an initial value";
    let new_value = "a new value";

    let result = a.entry(key1, key2).map(|entry| {
        entry.insert(value).replace_entry_with_keys(|k1, k2, v| {
            assert_eq!(k1, &key1);
            assert_eq!(k2, &key2);
            assert_eq!(v, value);
            Some(new_value)
        })
    });

    match result {
        Ok(entry) => match entry {
            Entry::Occupied(e) => {
                assert_eq!(e.key1(), &key1);
                assert_eq!(e.key2(), &key2);
                assert_eq!(e.get(), &new_value);
            }
            Entry::Vacant(_) => panic!(),
        },
        Err(_) => panic!(),
    }

    assert_eq!(a.get_key1(key1), Some(&new_value));
    assert_eq!(a.get_key2(key2), Some(&new_value));
    assert_eq!(a.get_keys(key1, key2), Some(&new_value));
    assert!(a.contains_key1(key1));
    assert!(a.contains_key2(key2));
    assert!(a.contains_keys(key1, key2));

    assert_eq!(a.len(), 1);

    assert_eq!(a[key1], new_value);

    let entry = match a.entry(key1, key2) {
        Ok(entry) => match entry {
            Entry::Occupied(e) => e.replace_entry_with_keys(|k1, k2, v| {
                assert_eq!(k1, &key1);
                assert_eq!(k2, &key2);
                assert_eq!(v, new_value);
                None
            }),
            Entry::Vacant(_) => panic!(),
        },
        Err(_) => panic!(),
    };

    match entry {
        Entry::Vacant(e) => {
            assert_eq!(e.key1(), &key1);
            assert_eq!(e.key2(), &key2);
        }
        Entry::Occupied(_) => panic!(),
    }

    assert_eq!(a.get_key1(key1), None);
    assert_eq!(a.get_key2(key2), None);
    assert_eq!(a.get_keys(key1, key2), None);
    assert!(!a.contains_key1(key1));
    assert!(!a.contains_key2(key2));
    assert!(!a.contains_keys(key1, key2));

    assert_eq!(a.len(), 0);

    let result = a.entry(key1, key2).map(|entry| {
        entry.insert(value).replace_entry_with_key1(|k1, v| {
            assert_eq!(k1, &key1);
            assert_eq!(v, value);
            Some(new_value)
        })
    });

    match result {
        Ok(entry) => match entry {
            Entry::Occupied(e) => {
                assert_eq!(e.key1(), &key1);
                assert_eq!(e.key2(), &key2);
                assert_eq!(e.get(), &new_value);
            }
            Entry::Vacant(_) => panic!(),
        },
        Err(_) => panic!(),
    }

    assert_eq!(a.get_key1(key1), Some(&new_value));
    assert_eq!(a.get_key2(key2), Some(&new_value));
    assert_eq!(a.get_keys(key1, key2), Some(&new_value));
    assert!(a.contains_key1(key1));
    assert!(a.contains_key2(key2));
    assert!(a.contains_keys(key1, key2));

    assert_eq!(a.len(), 1);

    assert_eq!(a[key1], new_value);

    let entry = match a.entry(key1, key2) {
        Ok(entry) => match entry {
            Entry::Occupied(e) => e.replace_entry_with_key1(|k1, v| {
                assert_eq!(k1, &key1);
                assert_eq!(v, new_value);
                None
            }),
            Entry::Vacant(_) => panic!(),
        },
        Err(_) => panic!(),
    };

    match entry {
        Entry::Vacant(e) => {
            assert_eq!(e.key1(), &key1);
            assert_eq!(e.key2(), &key2);
        }
        Entry::Occupied(_) => panic!(),
    }

    assert_eq!(a.get_key1(key1), None);
    assert_eq!(a.get_key2(key2), None);
    assert_eq!(a.get_keys(key1, key2), None);
    assert!(!a.contains_key1(key1));
    assert!(!a.contains_key2(key2));
    assert!(!a.contains_keys(key1, key2));

    assert_eq!(a.len(), 0);

    let result = a.entry(key1, key2).map(|entry| {
        entry.insert(value).replace_entry_with_key2(|k2, v| {
            assert_eq!(k2, &key2);
            assert_eq!(v, value);
            Some(new_value)
        })
    });

    match result {
        Ok(entry) => match entry {
            Entry::Occupied(e) => {
                assert_eq!(e.key1(), &key1);
                assert_eq!(e.key2(), &key2);
                assert_eq!(e.get(), &new_value);
            }
            Entry::Vacant(_) => panic!(),
        },
        Err(_) => panic!(),
    }

    assert_eq!(a.get_key1(key1), Some(&new_value));
    assert_eq!(a.get_key2(key2), Some(&new_value));
    assert_eq!(a.get_keys(key1, key2), Some(&new_value));
    assert!(a.contains_key1(key1));
    assert!(a.contains_key2(key2));
    assert!(a.contains_keys(key1, key2));

    assert_eq!(a.len(), 1);

    assert_eq!(a[key1], new_value);

    let entry = match a.entry(key1, key2) {
        Ok(entry) => match entry {
            Entry::Occupied(e) => e.replace_entry_with_key2(|k2, v| {
                assert_eq!(k2, &key2);
                assert_eq!(v, new_value);
                None
            }),
            Entry::Vacant(_) => panic!(),
        },
        Err(_) => panic!(),
    };

    match entry {
        Entry::Vacant(e) => {
            assert_eq!(e.key1(), &key1);
            assert_eq!(e.key2(), &key2);
        }
        Entry::Occupied(_) => panic!(),
    }

    assert_eq!(a.get_key1(key1), None);
    assert_eq!(a.get_key2(key2), None);
    assert_eq!(a.get_keys(key1, key2), None);
    assert!(!a.contains_key1(key1));
    assert!(!a.contains_key2(key2));
    assert!(!a.contains_keys(key1, key2));

    assert_eq!(a.len(), 0);
}

#[test]
fn test_occupied_entry_ref_replace_entry_with() {
    let mut a: DHashMap<String, String, &str> = DHashMap::new();

    let key1 = "a key 1";
    let key2 = "a key 2";
    let value = "an initial value";
    let new_value = "a new value";

    let result = a.entry_ref(key1, key2).map(|entry| {
        entry.insert(value).replace_entry_with_keys(|k1, k2, v| {
            assert_eq!(k1, key1);
            assert_eq!(k2, key2);
            assert_eq!(v, value);
            Some(new_value)
        })
    });

    match result {
        Ok(entry) => match entry {
            EntryRef::Occupied(e) => {
                assert_eq!(e.key1(), key1);
                assert_eq!(e.key2(), key2);
                assert_eq!(e.get(), &new_value);
            }
            EntryRef::Vacant(_) => panic!(),
        },
        Err(_) => panic!(),
    }

    assert_eq!(a.get_key1(key1), Some(&new_value));
    assert_eq!(a.get_key2(key2), Some(&new_value));
    assert_eq!(a.get_keys(key1, key2), Some(&new_value));
    assert!(a.contains_key1(key1));
    assert!(a.contains_key2(key2));
    assert!(a.contains_keys(key1, key2));

    assert_eq!(a.len(), 1);

    assert_eq!(a[key1], new_value);

    let entry = match a.entry_ref(key1, key2) {
        Ok(entry) => match entry {
            EntryRef::Occupied(e) => e.replace_entry_with_keys(|k1, k2, v| {
                assert_eq!(k1, key1);
                assert_eq!(k2, key2);
                assert_eq!(v, new_value);
                None
            }),
            EntryRef::Vacant(_) => panic!(),
        },
        Err(_) => panic!(),
    };

    match entry {
        EntryRef::Vacant(e) => {
            assert_eq!(e.key1(), key1);
            assert_eq!(e.key2(), key2);
        }
        EntryRef::Occupied(_) => panic!(),
    }

    assert_eq!(a.get_key1(key1), None);
    assert_eq!(a.get_key2(key2), None);
    assert_eq!(a.get_keys(key1, key2), None);
    assert!(!a.contains_key1(key1));
    assert!(!a.contains_key2(key2));
    assert!(!a.contains_keys(key1, key2));

    assert_eq!(a.len(), 0);

    let result = a.entry_ref(key1, key2).map(|entry| {
        entry.insert(value).replace_entry_with_key1(|k1, v| {
            assert_eq!(k1, key1);
            assert_eq!(v, value);
            Some(new_value)
        })
    });

    match result {
        Ok(entry) => match entry {
            EntryRef::Occupied(e) => {
                assert_eq!(e.key1(), key1);
                assert_eq!(e.key2(), key2);
                assert_eq!(e.get(), &new_value);
            }
            EntryRef::Vacant(_) => panic!(),
        },
        Err(_) => panic!(),
    }

    assert_eq!(a.get_key1(key1), Some(&new_value));
    assert_eq!(a.get_key2(key2), Some(&new_value));
    assert_eq!(a.get_keys(key1, key2), Some(&new_value));
    assert!(a.contains_key1(key1));
    assert!(a.contains_key2(key2));
    assert!(a.contains_keys(key1, key2));

    assert_eq!(a.len(), 1);

    assert_eq!(a[key1], new_value);

    let entry = match a.entry_ref(key1, key2) {
        Ok(entry) => match entry {
            EntryRef::Occupied(e) => e.replace_entry_with_key1(|k1, v| {
                assert_eq!(k1, key1);
                assert_eq!(v, new_value);
                None
            }),
            EntryRef::Vacant(_) => panic!(),
        },
        Err(_) => panic!(),
    };

    match entry {
        EntryRef::Vacant(e) => {
            assert_eq!(e.key1(), key1);
            assert_eq!(e.key2(), key2);
        }
        EntryRef::Occupied(_) => panic!(),
    }

    assert_eq!(a.get_key1(key1), None);
    assert_eq!(a.get_key2(key2), None);
    assert_eq!(a.get_keys(key1, key2), None);
    assert!(!a.contains_key1(key1));
    assert!(!a.contains_key2(key2));
    assert!(!a.contains_keys(key1, key2));

    assert_eq!(a.len(), 0);

    let result = a.entry_ref(key1, key2).map(|entry| {
        entry.insert(value).replace_entry_with_key2(|k2, v| {
            assert_eq!(k2, key2);
            assert_eq!(v, value);
            Some(new_value)
        })
    });

    match result {
        Ok(entry) => match entry {
            EntryRef::Occupied(e) => {
                assert_eq!(e.key1(), key1);
                assert_eq!(e.key2(), key2);
                assert_eq!(e.get(), &new_value);
            }
            EntryRef::Vacant(_) => panic!(),
        },
        Err(_) => panic!(),
    }

    assert_eq!(a.get_key1(key1), Some(&new_value));
    assert_eq!(a.get_key2(key2), Some(&new_value));
    assert_eq!(a.get_keys(key1, key2), Some(&new_value));
    assert!(a.contains_key1(key1));
    assert!(a.contains_key2(key2));
    assert!(a.contains_keys(key1, key2));

    assert_eq!(a.len(), 1);

    assert_eq!(a[key1], new_value);

    let entry = match a.entry_ref(key1, key2) {
        Ok(entry) => match entry {
            EntryRef::Occupied(e) => e.replace_entry_with_key2(|k2, v| {
                assert_eq!(k2, key2);
                assert_eq!(v, new_value);
                None
            }),
            EntryRef::Vacant(_) => panic!(),
        },
        Err(_) => panic!(),
    };

    match entry {
        EntryRef::Vacant(e) => {
            assert_eq!(e.key1(), key1);
            assert_eq!(e.key2(), key2);
        }
        EntryRef::Occupied(_) => panic!(),
    }

    assert_eq!(a.get_key1(key1), None);
    assert_eq!(a.get_key2(key2), None);
    assert_eq!(a.get_keys(key1, key2), None);
    assert!(!a.contains_key1(key1));
    assert!(!a.contains_key2(key2));
    assert!(!a.contains_keys(key1, key2));

    assert_eq!(a.len(), 0);
}

#[test]
fn test_entry_and_replace_entry_with() {
    let mut a: DHashMap<&str, &str, &str> = DHashMap::new();

    let key1 = "a key 1";
    let key2 = "a key 2";
    let value = "an initial value";
    let new_value = "a new value";

    let entry = match a.entry(key1, key2) {
        Ok(entry) => entry.and_replace_entry_with_keys(|_, _, _| panic!()),
        Err(_) => panic!(),
    };

    match entry {
        Entry::Occupied(_) => panic!(),
        Entry::Vacant(e) => {
            assert_eq!(e.key1(), &key1);
            assert_eq!(e.key2(), &key2);
        }
    }

    let entry = match a.entry(key1, key2) {
        Ok(entry) => entry.and_replace_entry_with_key1(|_, _| panic!()),
        Err(_) => panic!(),
    };

    match entry {
        Entry::Occupied(_) => panic!(),
        Entry::Vacant(e) => {
            assert_eq!(e.key1(), &key1);
            assert_eq!(e.key2(), &key2);
        }
    }

    let entry = match a.entry(key1, key2) {
        Ok(entry) => entry.and_replace_entry_with_key2(|_, _| panic!()),
        Err(_) => panic!(),
    };

    match entry {
        Entry::Occupied(_) => panic!(),
        Entry::Vacant(e) => {
            assert_eq!(e.key1(), &key1);
            assert_eq!(e.key2(), &key2);
        }
    }

    a.insert(key1, key2, value);

    let entry = match a.entry(key1, key2) {
        Ok(entry) => entry.and_replace_entry_with_keys(|k1, k2, v| {
            assert_eq!(k1, &key1);
            assert_eq!(k2, &key2);
            assert_eq!(v, value);
            Some(new_value)
        }),
        Err(_) => panic!(),
    };

    match entry {
        Entry::Occupied(e) => {
            assert_eq!(e.key1(), &key1);
            assert_eq!(e.key2(), &key2);
            assert_eq!(e.get(), &new_value);
        }
        Entry::Vacant(_) => panic!(),
    }

    assert_eq!(a.get_key1(key1), Some(&new_value));
    assert_eq!(a.get_key2(key2), Some(&new_value));
    assert_eq!(a.get_keys(key1, key2), Some(&new_value));
    assert!(a.contains_key1(key1));
    assert!(a.contains_key2(key2));
    assert!(a.contains_keys(key1, key2));

    assert_eq!(a.len(), 1);

    assert_eq!(a[key1], new_value);

    let entry = match a.entry(key1, key2) {
        Ok(entry) => entry.and_replace_entry_with_keys(|k1, k2, v| {
            assert_eq!(k1, &key1);
            assert_eq!(k2, &key2);
            assert_eq!(v, new_value);
            None
        }),
        Err(_) => panic!(),
    };

    match entry {
        Entry::Vacant(e) => {
            assert_eq!(e.key1(), &key1);
            assert_eq!(e.key2(), &key2);
        }
        Entry::Occupied(_) => panic!(),
    }

    assert_eq!(a.get_key1(key1), None);
    assert_eq!(a.get_key2(key2), None);
    assert_eq!(a.get_keys(key1, key2), None);
    assert!(!a.contains_key1(key1));
    assert!(!a.contains_key2(key2));
    assert!(!a.contains_keys(key1, key2));

    assert_eq!(a.len(), 0);

    a.insert(key1, key2, value);

    let entry = match a.entry(key1, key2) {
        Ok(entry) => entry.and_replace_entry_with_key1(|k1, v| {
            assert_eq!(k1, &key1);
            assert_eq!(v, value);
            Some(new_value)
        }),
        Err(_) => panic!(),
    };

    match entry {
        Entry::Occupied(e) => {
            assert_eq!(e.key1(), &key1);
            assert_eq!(e.key2(), &key2);
            assert_eq!(e.get(), &new_value);
        }
        Entry::Vacant(_) => panic!(),
    }

    assert_eq!(a.get_key1(key1), Some(&new_value));
    assert_eq!(a.get_key2(key2), Some(&new_value));
    assert_eq!(a.get_keys(key1, key2), Some(&new_value));
    assert!(a.contains_key1(key1));
    assert!(a.contains_key2(key2));
    assert!(a.contains_keys(key1, key2));

    assert_eq!(a.len(), 1);

    assert_eq!(a[key1], new_value);

    let entry = match a.entry(key1, key2) {
        Ok(entry) => entry.and_replace_entry_with_key1(|k1, v| {
            assert_eq!(k1, &key1);
            assert_eq!(v, new_value);
            None
        }),
        Err(_) => panic!(),
    };

    match entry {
        Entry::Vacant(e) => {
            assert_eq!(e.key1(), &key1);
            assert_eq!(e.key2(), &key2);
        }
        Entry::Occupied(_) => panic!(),
    }

    assert_eq!(a.get_key1(key1), None);
    assert_eq!(a.get_key2(key2), None);
    assert_eq!(a.get_keys(key1, key2), None);
    assert!(!a.contains_key1(key1));
    assert!(!a.contains_key2(key2));
    assert!(!a.contains_keys(key1, key2));

    assert_eq!(a.len(), 0);

    a.insert(key1, key2, value);

    let entry = match a.entry(key1, key2) {
        Ok(entry) => entry.and_replace_entry_with_key2(|k2, v| {
            assert_eq!(k2, &key2);
            assert_eq!(v, value);
            Some(new_value)
        }),
        Err(_) => panic!(),
    };

    match entry {
        Entry::Occupied(e) => {
            assert_eq!(e.key1(), &key1);
            assert_eq!(e.key2(), &key2);
            assert_eq!(e.get(), &new_value);
        }
        Entry::Vacant(_) => panic!(),
    }

    assert_eq!(a.get_key1(key1), Some(&new_value));
    assert_eq!(a.get_key2(key2), Some(&new_value));
    assert_eq!(a.get_keys(key1, key2), Some(&new_value));
    assert!(a.contains_key1(key1));
    assert!(a.contains_key2(key2));
    assert!(a.contains_keys(key1, key2));

    assert_eq!(a.len(), 1);

    assert_eq!(a[key1], new_value);

    let entry = match a.entry(key1, key2) {
        Ok(entry) => entry.and_replace_entry_with_key2(|k2, v| {
            assert_eq!(k2, &key2);
            assert_eq!(v, new_value);
            None
        }),
        Err(_) => panic!(),
    };

    match entry {
        Entry::Vacant(e) => {
            assert_eq!(e.key1(), &key1);
            assert_eq!(e.key2(), &key2);
        }
        Entry::Occupied(_) => panic!(),
    }

    assert_eq!(a.get_key1(key1), None);
    assert_eq!(a.get_key2(key2), None);
    assert_eq!(a.get_keys(key1, key2), None);
    assert!(!a.contains_key1(key1));
    assert!(!a.contains_key2(key2));
    assert!(!a.contains_keys(key1, key2));

    assert_eq!(a.len(), 0);
}

#[test]
fn test_entry_ref_and_replace_entry_with() {
    let mut a: DHashMap<String, String, &str> = DHashMap::new();

    let key1 = "a key 1";
    let key2 = "a key 2";
    let value = "an initial value";
    let new_value = "a new value";

    let entry = match a.entry_ref(key1, key2) {
        Ok(entry) => entry.and_replace_entry_with_keys(|_, _, _| panic!()),
        Err(_) => panic!(),
    };

    match entry {
        EntryRef::Occupied(_) => panic!(),
        EntryRef::Vacant(e) => {
            assert_eq!(e.key1(), key1);
            assert_eq!(e.key2(), key2);
        }
    }

    let entry = match a.entry_ref(key1, key2) {
        Ok(entry) => entry.and_replace_entry_with_key1(|_, _| panic!()),
        Err(_) => panic!(),
    };

    match entry {
        EntryRef::Occupied(_) => panic!(),
        EntryRef::Vacant(e) => {
            assert_eq!(e.key1(), key1);
            assert_eq!(e.key2(), key2);
        }
    }

    let entry = match a.entry_ref(key1, key2) {
        Ok(entry) => entry.and_replace_entry_with_key2(|_, _| panic!()),
        Err(_) => panic!(),
    };

    match entry {
        EntryRef::Occupied(_) => panic!(),
        EntryRef::Vacant(e) => {
            assert_eq!(e.key1(), key1);
            assert_eq!(e.key2(), key2);
        }
    }

    a.insert(key1.to_owned(), key2.to_owned(), value);

    let entry = match a.entry_ref(key1, key2) {
        Ok(entry) => entry.and_replace_entry_with_keys(|k1, k2, v| {
            assert_eq!(k1, key1);
            assert_eq!(k2, key2);
            assert_eq!(v, value);
            Some(new_value)
        }),
        Err(_) => panic!(),
    };

    match entry {
        EntryRef::Occupied(e) => {
            assert_eq!(e.key1(), key1);
            assert_eq!(e.key2(), key2);
            assert_eq!(e.get(), &new_value);
        }
        EntryRef::Vacant(_) => panic!(),
    }

    assert_eq!(a.get_key1(key1), Some(&new_value));
    assert_eq!(a.get_key2(key2), Some(&new_value));
    assert_eq!(a.get_keys(key1, key2), Some(&new_value));
    assert!(a.contains_key1(key1));
    assert!(a.contains_key2(key2));
    assert!(a.contains_keys(key1, key2));

    assert_eq!(a.len(), 1);

    assert_eq!(a[key1], new_value);

    let entry = match a.entry_ref(key1, key2) {
        Ok(entry) => entry.and_replace_entry_with_keys(|k1, k2, v| {
            assert_eq!(k1, key1);
            assert_eq!(k2, key2);
            assert_eq!(v, new_value);
            None
        }),
        Err(_) => panic!(),
    };

    match entry {
        EntryRef::Vacant(e) => {
            assert_eq!(e.key1(), key1);
            assert_eq!(e.key2(), key2);
        }
        EntryRef::Occupied(_) => panic!(),
    }

    assert_eq!(a.get_key1(key1), None);
    assert_eq!(a.get_key2(key2), None);
    assert_eq!(a.get_keys(key1, key2), None);
    assert!(!a.contains_key1(key1));
    assert!(!a.contains_key2(key2));
    assert!(!a.contains_keys(key1, key2));

    assert_eq!(a.len(), 0);

    a.insert(key1.to_owned(), key2.to_owned(), value);

    let entry = match a.entry_ref(key1, key2) {
        Ok(entry) => entry.and_replace_entry_with_key1(|k1, v| {
            assert_eq!(k1, key1);
            assert_eq!(v, value);
            Some(new_value)
        }),
        Err(_) => panic!(),
    };

    match entry {
        EntryRef::Occupied(e) => {
            assert_eq!(e.key1(), key1);
            assert_eq!(e.key2(), key2);
            assert_eq!(e.get(), &new_value);
        }
        EntryRef::Vacant(_) => panic!(),
    }

    assert_eq!(a.get_key1(key1), Some(&new_value));
    assert_eq!(a.get_key2(key2), Some(&new_value));
    assert_eq!(a.get_keys(key1, key2), Some(&new_value));
    assert!(a.contains_key1(key1));
    assert!(a.contains_key2(key2));
    assert!(a.contains_keys(key1, key2));

    assert_eq!(a.len(), 1);

    assert_eq!(a[key1], new_value);

    let entry = match a.entry_ref(key1, key2) {
        Ok(entry) => entry.and_replace_entry_with_key1(|k1, v| {
            assert_eq!(k1, key1);
            assert_eq!(v, new_value);
            None
        }),
        Err(_) => panic!(),
    };

    match entry {
        EntryRef::Vacant(e) => {
            assert_eq!(e.key1(), key1);
            assert_eq!(e.key2(), key2);
        }
        EntryRef::Occupied(_) => panic!(),
    }

    assert_eq!(a.get_key1(key1), None);
    assert_eq!(a.get_key2(key2), None);
    assert_eq!(a.get_keys(key1, key2), None);
    assert!(!a.contains_key1(key1));
    assert!(!a.contains_key2(key2));
    assert!(!a.contains_keys(key1, key2));

    assert_eq!(a.len(), 0);

    a.insert(key1.to_owned(), key2.to_owned(), value);

    let entry = match a.entry_ref(key1, key2) {
        Ok(entry) => entry.and_replace_entry_with_key2(|k2, v| {
            assert_eq!(k2, key2);
            assert_eq!(v, value);
            Some(new_value)
        }),
        Err(_) => panic!(),
    };

    match entry {
        EntryRef::Occupied(e) => {
            assert_eq!(e.key1(), key1);
            assert_eq!(e.key2(), key2);
            assert_eq!(e.get(), &new_value);
        }
        EntryRef::Vacant(_) => panic!(),
    }

    assert_eq!(a.get_key1(key1), Some(&new_value));
    assert_eq!(a.get_key2(key2), Some(&new_value));
    assert_eq!(a.get_keys(key1, key2), Some(&new_value));
    assert!(a.contains_key1(key1));
    assert!(a.contains_key2(key2));
    assert!(a.contains_keys(key1, key2));

    assert_eq!(a.len(), 1);

    assert_eq!(a[key1], new_value);

    let entry = match a.entry_ref(key1, key2) {
        Ok(entry) => entry.and_replace_entry_with_key2(|k2, v| {
            assert_eq!(k2, key2);
            assert_eq!(v, new_value);
            None
        }),
        Err(_) => panic!(),
    };

    match entry {
        EntryRef::Vacant(e) => {
            assert_eq!(e.key1(), key1);
            assert_eq!(e.key2(), key2);
        }
        EntryRef::Occupied(_) => panic!(),
    }

    assert_eq!(a.get_key1(key1), None);
    assert_eq!(a.get_key2(key2), None);
    assert_eq!(a.get_keys(key1, key2), None);
    assert!(!a.contains_key1(key1));
    assert!(!a.contains_key2(key2));
    assert!(!a.contains_keys(key1, key2));

    assert_eq!(a.len(), 0);
}

#[test]
fn test_raw_occupied_entry_replace_entry_with() {
    let mut a = DHashMap::new();

    let key1 = "a key 1";
    let key2 = "a key 2";
    let value = "an initial value";
    let new_value = "a new value";

    let entry = a.raw_entry_mut().from_keys(&key1, &key2).map(|entry| {
        entry
            .insert(key1, key2, value)
            .replace_entry_with_keys(|k1, k2, v| {
                assert_eq!(k1, &key1);
                assert_eq!(k2, &key2);
                assert_eq!(v, value);
                Some(new_value)
            })
    });

    match entry {
        Ok(entry) => match entry {
            RawEntryMut::Occupied(e) => {
                assert_eq!(e.key1(), &key1);
                assert_eq!(e.key2(), &key2);
                assert_eq!(e.get(), &new_value);
            }
            RawEntryMut::Vacant(_) => panic!(),
        },
        Err(_) => panic!(),
    }

    assert_eq!(a.get_key1(key1), Some(&new_value));
    assert_eq!(a.get_key2(key2), Some(&new_value));
    assert_eq!(a.get_keys(key1, key2), Some(&new_value));
    assert!(a.contains_key1(key1));
    assert!(a.contains_key2(key2));
    assert!(a.contains_keys(key1, key2));

    assert_eq!(a.len(), 1);

    assert_eq!(a[key1], new_value);

    let entry = match a.raw_entry_mut().from_keys(&key1, &key2) {
        Ok(entry) => match entry {
            RawEntryMut::Occupied(e) => e.replace_entry_with_keys(|k1, k2, v| {
                assert_eq!(k1, &key1);
                assert_eq!(k2, &key2);
                assert_eq!(v, new_value);
                None
            }),
            RawEntryMut::Vacant(_) => panic!(),
        },
        Err(_) => panic!(),
    };

    match entry {
        RawEntryMut::Vacant(_) => {}
        RawEntryMut::Occupied(_) => panic!(),
    }

    assert_eq!(a.get_key1(&key1), None);
    assert_eq!(a.get_key2(&key2), None);
    assert_eq!(a.get_keys(&key1, &key2), None);
    assert!(!a.contains_key1(&key1));
    assert!(!a.contains_key2(&key2));
    assert!(!a.contains_keys(&key1, &key2));

    assert_eq!(a.len(), 0);

    let entry = a.raw_entry_mut().from_keys(&key1, &key2).map(|entry| {
        entry
            .insert(key1, key2, value)
            .replace_entry_with_key1(|k1, v| {
                assert_eq!(k1, &key1);
                assert_eq!(v, value);
                Some(new_value)
            })
    });

    match entry {
        Ok(entry) => match entry {
            RawEntryMut::Occupied(e) => {
                assert_eq!(e.key1(), &key1);
                assert_eq!(e.key2(), &key2);
                assert_eq!(e.get(), &new_value);
            }
            RawEntryMut::Vacant(_) => panic!(),
        },
        Err(_) => panic!(),
    }

    assert_eq!(a.get_key1(key1), Some(&new_value));
    assert_eq!(a.get_key2(key2), Some(&new_value));
    assert_eq!(a.get_keys(key1, key2), Some(&new_value));
    assert!(a.contains_key1(key1));
    assert!(a.contains_key2(key2));
    assert!(a.contains_keys(key1, key2));

    assert_eq!(a.len(), 1);

    assert_eq!(a[key1], new_value);

    let entry = match a.raw_entry_mut().from_keys(&key1, &key2) {
        Ok(entry) => match entry {
            RawEntryMut::Occupied(e) => e.replace_entry_with_key1(|k1, v| {
                assert_eq!(k1, &key1);
                assert_eq!(v, new_value);
                None
            }),
            RawEntryMut::Vacant(_) => panic!(),
        },
        Err(_) => panic!(),
    };

    match entry {
        RawEntryMut::Vacant(_) => {}
        RawEntryMut::Occupied(_) => panic!(),
    }

    assert_eq!(a.get_key1(&key1), None);
    assert_eq!(a.get_key2(&key2), None);
    assert_eq!(a.get_keys(&key1, &key2), None);
    assert!(!a.contains_key1(&key1));
    assert!(!a.contains_key2(&key2));
    assert!(!a.contains_keys(&key1, &key2));

    assert_eq!(a.len(), 0);

    let entry = a.raw_entry_mut().from_keys(&key1, &key2).map(|entry| {
        entry
            .insert(key1, key2, value)
            .replace_entry_with_key2(|k2, v| {
                assert_eq!(k2, &key2);
                assert_eq!(v, value);
                Some(new_value)
            })
    });

    match entry {
        Ok(entry) => match entry {
            RawEntryMut::Occupied(e) => {
                assert_eq!(e.key1(), &key1);
                assert_eq!(e.key2(), &key2);
                assert_eq!(e.get(), &new_value);
            }
            RawEntryMut::Vacant(_) => panic!(),
        },
        Err(_) => panic!(),
    }

    assert_eq!(a.get_key1(key1), Some(&new_value));
    assert_eq!(a.get_key2(key2), Some(&new_value));
    assert_eq!(a.get_keys(key1, key2), Some(&new_value));
    assert!(a.contains_key1(key1));
    assert!(a.contains_key2(key2));
    assert!(a.contains_keys(key1, key2));

    assert_eq!(a.len(), 1);

    assert_eq!(a[key1], new_value);

    let entry = match a.raw_entry_mut().from_keys(&key1, &key2) {
        Ok(entry) => match entry {
            RawEntryMut::Occupied(e) => e.replace_entry_with_key2(|k2, v| {
                assert_eq!(k2, &key2);
                assert_eq!(v, new_value);
                None
            }),
            RawEntryMut::Vacant(_) => panic!(),
        },
        Err(_) => panic!(),
    };

    match entry {
        RawEntryMut::Vacant(_) => {}
        RawEntryMut::Occupied(_) => panic!(),
    }

    assert_eq!(a.get_key1(&key1), None);
    assert_eq!(a.get_key2(&key2), None);
    assert_eq!(a.get_keys(&key1, &key2), None);
    assert!(!a.contains_key1(&key1));
    assert!(!a.contains_key2(&key2));
    assert!(!a.contains_keys(&key1, &key2));

    assert_eq!(a.len(), 0);
}

#[test]
fn test_raw_entry_and_replace_entry_with() {
    let mut a: DHashMap<&str, &str, &str> = DHashMap::new();

    let key1 = "a key 1";
    let key2 = "a key 2";
    let value = "an initial value";
    let new_value = "a new value";

    let entry = match a.raw_entry_mut().from_keys(key1, key2) {
        Ok(entry) => entry.and_replace_entry_with_keys(|_, _, _| panic!()),
        Err(_) => panic!(),
    };

    match entry {
        RawEntryMut::Occupied(_) => panic!(),
        RawEntryMut::Vacant(_) => {}
    }

    let entry = match a.raw_entry_mut().from_keys(key1, key2) {
        Ok(entry) => entry.and_replace_entry_with_key1(|_, _| panic!()),
        Err(_) => panic!(),
    };

    match entry {
        RawEntryMut::Occupied(_) => panic!(),
        RawEntryMut::Vacant(_) => {}
    }

    let entry = match a.raw_entry_mut().from_keys(key1, key2) {
        Ok(entry) => entry.and_replace_entry_with_key2(|_, _| panic!()),
        Err(_) => panic!(),
    };

    match entry {
        RawEntryMut::Occupied(_) => panic!(),
        RawEntryMut::Vacant(_) => {}
    }

    assert_eq!(a.get_key1(&key1), None);
    assert_eq!(a.get_key2(&key2), None);
    assert_eq!(a.get_keys(&key1, &key2), None);
    assert!(!a.contains_key1(&key1));
    assert!(!a.contains_key2(&key2));
    assert!(!a.contains_keys(&key1, &key2));

    assert_eq!(a.len(), 0);

    a.insert(key1, key2, value);

    let entry = match a.raw_entry_mut().from_keys(key1, key2) {
        Ok(entry) => entry.and_replace_entry_with_keys(|k1, k2, v| {
            assert_eq!(k1, &key1);
            assert_eq!(k2, &key2);
            assert_eq!(v, value);
            Some(new_value)
        }),
        Err(_) => panic!(),
    };

    match entry {
        RawEntryMut::Occupied(e) => {
            assert_eq!(e.key1(), &key1);
            assert_eq!(e.key2(), &key2);
            assert_eq!(e.get(), &new_value);
        }
        RawEntryMut::Vacant(_) => panic!(),
    }

    assert_eq!(a.get_key1(key1), Some(&new_value));
    assert_eq!(a.get_key2(key2), Some(&new_value));
    assert_eq!(a.get_keys(key1, key2), Some(&new_value));
    assert!(a.contains_key1(key1));
    assert!(a.contains_key2(key2));
    assert!(a.contains_keys(key1, key2));

    assert_eq!(a.len(), 1);

    assert_eq!(a[key1], new_value);

    let entry = match a.raw_entry_mut().from_keys(key1, key2) {
        Ok(entry) => entry.and_replace_entry_with_keys(|k1, k2, v| {
            assert_eq!(k1, &key1);
            assert_eq!(k2, &key2);
            assert_eq!(v, new_value);
            None
        }),
        Err(_) => panic!(),
    };

    match entry {
        RawEntryMut::Vacant(_) => {}
        RawEntryMut::Occupied(_) => panic!(),
    }

    assert_eq!(a.get_key1(key1), None);
    assert_eq!(a.get_key2(key2), None);
    assert_eq!(a.get_keys(key1, key2), None);
    assert!(!a.contains_key1(key1));
    assert!(!a.contains_key2(key2));
    assert!(!a.contains_keys(key1, key2));

    assert_eq!(a.len(), 0);

    a.insert(key1, key2, value);

    let entry = match a.raw_entry_mut().from_keys(key1, key2) {
        Ok(entry) => entry.and_replace_entry_with_key1(|k1, v| {
            assert_eq!(k1, &key1);
            assert_eq!(v, value);
            Some(new_value)
        }),
        Err(_) => panic!(),
    };

    match entry {
        RawEntryMut::Occupied(e) => {
            assert_eq!(e.key1(), &key1);
            assert_eq!(e.key2(), &key2);
            assert_eq!(e.get(), &new_value);
        }
        RawEntryMut::Vacant(_) => panic!(),
    }

    assert_eq!(a.get_key1(key1), Some(&new_value));
    assert_eq!(a.get_key2(key2), Some(&new_value));
    assert_eq!(a.get_keys(key1, key2), Some(&new_value));
    assert!(a.contains_key1(key1));
    assert!(a.contains_key2(key2));
    assert!(a.contains_keys(key1, key2));

    assert_eq!(a.len(), 1);

    assert_eq!(a[key1], new_value);

    let entry = match a.raw_entry_mut().from_keys(key1, key2) {
        Ok(entry) => entry.and_replace_entry_with_key1(|k1, v| {
            assert_eq!(k1, &key1);
            assert_eq!(v, new_value);
            None
        }),
        Err(_) => panic!(),
    };

    match entry {
        RawEntryMut::Vacant(_) => {}
        RawEntryMut::Occupied(_) => panic!(),
    }

    assert_eq!(a.get_key1(key1), None);
    assert_eq!(a.get_key2(key2), None);
    assert_eq!(a.get_keys(key1, key2), None);
    assert!(!a.contains_key1(key1));
    assert!(!a.contains_key2(key2));
    assert!(!a.contains_keys(key1, key2));

    assert_eq!(a.len(), 0);

    a.insert(key1, key2, value);

    let entry = match a.raw_entry_mut().from_keys(key1, key2) {
        Ok(entry) => entry.and_replace_entry_with_key2(|k2, v| {
            assert_eq!(k2, &key2);
            assert_eq!(v, value);
            Some(new_value)
        }),
        Err(_) => panic!(),
    };

    match entry {
        RawEntryMut::Occupied(e) => {
            assert_eq!(e.key1(), &key1);
            assert_eq!(e.key2(), &key2);
            assert_eq!(e.get(), &new_value);
        }
        RawEntryMut::Vacant(_) => panic!(),
    }

    assert_eq!(a.get_key1(key1), Some(&new_value));
    assert_eq!(a.get_key2(key2), Some(&new_value));
    assert_eq!(a.get_keys(key1, key2), Some(&new_value));
    assert!(a.contains_key1(key1));
    assert!(a.contains_key2(key2));
    assert!(a.contains_keys(key1, key2));

    assert_eq!(a.len(), 1);

    assert_eq!(a[key1], new_value);

    let entry = match a.raw_entry_mut().from_keys(key1, key2) {
        Ok(entry) => entry.and_replace_entry_with_key2(|k2, v| {
            assert_eq!(k2, &key2);
            assert_eq!(v, new_value);
            None
        }),
        Err(_) => panic!(),
    };

    match entry {
        RawEntryMut::Vacant(_) => {}
        RawEntryMut::Occupied(_) => panic!(),
    }

    assert_eq!(a.get_key1(key1), None);
    assert_eq!(a.get_key2(key2), None);
    assert_eq!(a.get_keys(key1, key2), None);
    assert!(!a.contains_key1(key1));
    assert!(!a.contains_key2(key2));
    assert!(!a.contains_keys(key1, key2));

    assert_eq!(a.len(), 0);
}

#[test]
fn test_replace_entry_with_doesnt_corrupt() {
    #![allow(deprecated)] //rand
                          // Test for #19292
    fn check<T>(m: &DHashMap<T, T, ()>)
    where
        T: std::cmp::Eq + std::hash::Hash,
    {
        for (k1, k2) in m.keys() {
            assert!(m.contains_key1(k1));
            assert!(m.contains_key2(k2));
            assert!(m.contains_keys(k1, k2));
        }
    }

    let mut m = DHashMap::new();
    let mut rng = thread_rng();

    // Populate the map with some items.
    for _ in 0..50 {
        let x = rng.gen_range(-10..10);
        m.insert(x, x, ());
    }

    assert!(m.len() > 0);

    for _ in 0..1000 {
        let x = rng.gen_range(-10..10);
        match m.entry(x, x) {
            Ok(entry) => {
                entry.and_replace_entry_with_keys(|_, _, _| None);
            }

            _ => panic!(),
        }
        check(&m);
    }

    m.clear();

    // Populate the map with some items.
    for _ in 0..50 {
        let x = rng.gen_range(-10..10);
        m.insert(x, x, ());
    }

    assert!(m.len() > 0);

    for _ in 0..1000 {
        let x = rng.gen_range(-10..10);
        match m.entry(x, x) {
            Ok(entry) => {
                entry.and_replace_entry_with_key1(|_, _| None);
            }

            _ => panic!(),
        }
        check(&m);
    }

    m.clear();

    // Populate the map with some items.
    for _ in 0..50 {
        let x = rng.gen_range(-10..10);
        m.insert(x, x, ());
    }

    assert!(m.len() > 0);

    for _ in 0..1000 {
        let x = rng.gen_range(-10..10);
        match m.entry(x, x) {
            Ok(entry) => {
                entry.and_replace_entry_with_key2(|_, _| None);
            }

            _ => panic!(),
        }
        check(&m);
    }
}

#[test]
fn test_replace_entry_ref_with_doesnt_corrupt() {
    #![allow(deprecated)] //rand
                          // Test for #19292
    fn check<T>(m: &DHashMap<T, T, ()>)
    where
        T: std::cmp::Eq + std::hash::Hash,
    {
        for (k1, k2) in m.keys() {
            assert!(m.contains_key1(k1));
            assert!(m.contains_key2(k2));
            assert!(m.contains_keys(k1, k2));
        }
    }

    let mut m = DHashMap::new();
    let mut rng = thread_rng();

    // Populate the map with some items.
    for _ in 0..50 {
        let mut x = std::string::String::with_capacity(1);
        x.push(rng.gen_range('a'..='z'));
        m.insert(x.clone(), x, ());
    }

    assert!(m.len() > 0);

    for _ in 0..1000 {
        let mut x = std::string::String::with_capacity(1);
        x.push(rng.gen_range('a'..='z'));
        match m.entry_ref(x.as_str(), x.as_str()) {
            Ok(entry) => {
                entry.and_replace_entry_with_keys(|_, _, _| None);
            }
            _ => panic!(),
        }
        check(&m);
    }

    m.clear();

    // Populate the map with some items.
    for _ in 0..50 {
        let mut x = std::string::String::with_capacity(1);
        x.push(rng.gen_range('a'..='z'));
        m.insert(x.clone(), x, ());
    }

    assert!(m.len() > 0);

    for _ in 0..1000 {
        let mut x = std::string::String::with_capacity(1);
        x.push(rng.gen_range('a'..='z'));
        match m.entry_ref(x.as_str(), x.as_str()) {
            Ok(entry) => {
                entry.and_replace_entry_with_key1(|_, _| None);
            }
            _ => panic!(),
        }
        check(&m);
    }

    m.clear();

    // Populate the map with some items.
    for _ in 0..50 {
        let mut x = std::string::String::with_capacity(1);
        x.push(rng.gen_range('a'..='z'));
        m.insert(x.clone(), x, ());
    }

    assert!(m.len() > 0);

    for _ in 0..1000 {
        let mut x = std::string::String::with_capacity(1);
        x.push(rng.gen_range('a'..='z'));
        match m.entry_ref(x.as_str(), x.as_str()) {
            Ok(entry) => {
                entry.and_replace_entry_with_key2(|_, _| None);
            }
            _ => panic!(),
        }
        check(&m);
    }
}

#[test]
fn test_replace_raw_entry_with_doesnt_corrupt() {
    #![allow(deprecated)] //rand
                          // Test for #19292
    fn check<T>(m: &DHashMap<T, T, ()>)
    where
        T: std::cmp::Eq + std::hash::Hash,
    {
        for (k1, k2) in m.keys() {
            assert!(m.contains_key1(k1));
            assert!(m.contains_key2(k2));
            assert!(m.contains_keys(k1, k2));
        }
    }

    let mut m = DHashMap::new();
    let mut rng = thread_rng();

    // Populate the map with some items.
    for _ in 0..50 {
        let x = rng.gen_range(-10..10);
        m.insert(x, x, ());
    }

    assert!(m.len() > 0);

    for _ in 0..1000 {
        let x = rng.gen_range(-10..10);
        match m.raw_entry_mut().from_keys(&x, &x) {
            Ok(entry) => {
                entry.and_replace_entry_with_keys(|_, _, _| None);
            }
            _ => panic!(),
        }
        check(&m);
    }

    m.clear();

    // Populate the map with some items.
    for _ in 0..50 {
        let x = rng.gen_range(-10..10);
        m.insert(x, x, ());
    }

    assert!(m.len() > 0);

    for _ in 0..1000 {
        let x = rng.gen_range(-10..10);
        match m.raw_entry_mut().from_keys(&x, &x) {
            Ok(entry) => {
                entry.and_replace_entry_with_key1(|_, _| None);
            }
            _ => panic!(),
        }
        check(&m);
    }

    m.clear();

    // Populate the map with some items.
    for _ in 0..50 {
        let x = rng.gen_range(-10..10);
        m.insert(x, x, ());
    }

    assert!(m.len() > 0);

    for _ in 0..1000 {
        let x = rng.gen_range(-10..10);
        match m.raw_entry_mut().from_keys(&x, &x) {
            Ok(entry) => {
                entry.and_replace_entry_with_key2(|_, _| None);
            }
            _ => panic!(),
        }
        check(&m);
    }
}

#[test]
fn test_retain() {
    let mut map: DHashMap<i32, i32, i32> = (0..100).map(|x| (x, x, x * 100)).collect();

    map.retain_key1(|&k, _| k % 2 == 0);

    assert_eq!(map.len(), 50);
    for key in 0..50 {
        assert_eq!(map[&(key * 2)], key * 2 * 100);
    }

    let mut map: DHashMap<i32, i32, i32> = (0..100).map(|x| (x, x, x * 100)).collect();

    map.retain_key2(|&k, _| k % 2 == 0);

    assert_eq!(map.len(), 50);
    for key in 0..50 {
        assert_eq!(map[&(key * 2)], key * 2 * 100);
    }

    let mut map: DHashMap<i32, i32, i32> = (0..100).map(|x| (x, x * 10, x * 100)).collect();

    map.retain_keys(|&k1, &k2, _| k1 % 2 == 0 && k2 % 2 == 0);

    assert_eq!(map.len(), 50);
    for key in 0..50 {
        assert_eq!(map[&(key * 2)], key * 2 * 100);
    }
}

#[test]
#[cfg_attr(miri, ignore)] // FIXME: no OOM signalling (https://github.com/rust-lang/miri/issues/613)
fn test_try_reserve() {
    use crate::TryReserveError::{AllocError, CapacityOverflow};

    const MAX_ISIZE: usize = isize::MAX as usize;

    let mut empty_bytes: DHashMap<u8, u8, u8> = DHashMap::new();

    if let Err(CapacityOverflow) = empty_bytes.try_reserve(usize::MAX) {
    } else {
        panic!("usize::MAX should trigger an overflow!");
    }

    if let Err(CapacityOverflow) = empty_bytes.try_reserve(MAX_ISIZE) {
    } else {
        panic!("isize::MAX should trigger an overflow!");
    }

    if let Err(AllocError { .. }) = empty_bytes.try_reserve(MAX_ISIZE / 19) {
    } else {
        // This may succeed if there is enough free memory. Attempt to
        // allocate a few more hashmaps to ensure the allocation will fail.
        let mut empty_bytes2: DHashMap<u8, u8, u8> = DHashMap::new();
        let _ = empty_bytes2.try_reserve(MAX_ISIZE / 19);
        let mut empty_bytes3: DHashMap<u8, u8, u8> = DHashMap::new();
        let _ = empty_bytes3.try_reserve(MAX_ISIZE / 19);
        let mut empty_bytes4: DHashMap<u8, u8, u8> = DHashMap::new();
        if let Err(AllocError { .. }) = empty_bytes4.try_reserve(MAX_ISIZE / 19) {
        } else {
            panic!("isize::MAX / 19 should trigger an OOM!");
        }
    }
}

#[test]
fn test_raw_entry() {
    use super::RawEntryMut::{Occupied, Vacant};

    let xs = [
        (1, 10, 100),
        (2, 20, 200),
        (3, 30, 300),
        (4, 40, 400),
        (5, 50, 500),
        (6, 60, 600),
    ];

    let mut map: DHashMap<_, _, _> = xs.iter().cloned().collect();

    let compute_hash = |map: &DHashMap<i32, i32, i32>, k: i32| -> u64 {
        use core::hash::{BuildHasher, Hash, Hasher};

        let mut hasher = map.hasher().build_hasher();
        k.hash(&mut hasher);
        hasher.finish()
    };

    // Existing key (insert)
    match map.raw_entry_mut().from_keys(&1, &10) {
        Ok(raw_entry) => match raw_entry {
            Vacant(_) => panic!(),
            Occupied(mut view) => {
                assert_eq!(view.get(), &100);
                assert_eq!(view.insert(1000), 100);
            }
        },
        Err(_) => panic!(),
    }
    let hash1 = compute_hash(&map, 1);
    let hash2 = compute_hash(&map, 10);
    assert_eq!(
        map.raw_entry().from_keys(&1, &10).unwrap(),
        (&1, &10, &1000)
    );
    assert_eq!(
        map.raw_entry()
            .from_hash(hash1, |k| *k == 1, hash2, |k| *k == 10)
            .unwrap(),
        (&1, &10, &1000)
    );
    assert_eq!(
        map.raw_entry()
            .from_keys_hashed_nocheck(hash1, &1, hash2, &10)
            .unwrap(),
        (&1, &10, &1000)
    );
    assert_eq!(map.len(), 6);

    // Existing key (update)
    match map.raw_entry_mut().from_keys(&2, &20) {
        Ok(raw_entry) => match raw_entry {
            Vacant(_) => panic!(),
            Occupied(mut view) => {
                let v = view.get_mut();
                let new_v = (*v) * 10;
                *v = new_v;
            }
        },
        Err(_) => panic!(),
    }
    let hash1 = compute_hash(&map, 2);
    let hash2 = compute_hash(&map, 20);
    assert_eq!(
        map.raw_entry().from_keys(&2, &20).unwrap(),
        (&2, &20, &2000)
    );
    assert_eq!(
        map.raw_entry()
            .from_hash(hash1, |k| *k == 2, hash2, |k| *k == 20)
            .unwrap(),
        (&2, &20, &2000)
    );
    assert_eq!(
        map.raw_entry()
            .from_keys_hashed_nocheck(hash1, &2, hash2, &20)
            .unwrap(),
        (&2, &20, &2000)
    );
    assert_eq!(map.len(), 6);

    // Existing key (take)
    let hash1 = compute_hash(&map, 3);
    let hash2 = compute_hash(&map, 30);
    match map
        .raw_entry_mut()
        .from_keys_hashed_nocheck(hash1, &3, hash2, &30)
    {
        Ok(raw_entry) => match raw_entry {
            Vacant(_) => panic!(),
            Occupied(view) => {
                assert_eq!(view.remove_entry(), (3, 30, 300));
            }
        },
        Err(_) => panic!(),
    }
    assert_eq!(map.raw_entry().from_keys(&3, &30), None);
    assert_eq!(
        map.raw_entry()
            .from_hash(hash1, |k| *k == 3, hash2, |k| *k == 30),
        None
    );
    assert_eq!(
        map.raw_entry()
            .from_keys_hashed_nocheck(hash1, &3, hash2, &30),
        None
    );
    assert_eq!(map.len(), 5);

    // Nonexistent key (insert)
    match map.raw_entry_mut().from_keys(&10, &100) {
        Ok(raw_entry) => match raw_entry {
            Occupied(_) => panic!(),
            Vacant(view) => {
                assert_eq!(view.insert(10, 100, 10000), (&mut 10, &mut 100, &mut 10000));
            }
        },
        Err(_) => panic!(),
    }
    let hash1 = compute_hash(&map, 10);
    let hash2 = compute_hash(&map, 100);
    assert_eq!(
        map.raw_entry().from_keys(&10, &100).unwrap(),
        (&10, &100, &10000)
    );
    assert_eq!(
        map.raw_entry()
            .from_hash(hash1, |k| *k == 10, hash2, |k| *k == 100)
            .unwrap(),
        (&10, &100, &10000)
    );
    assert_eq!(
        map.raw_entry()
            .from_keys_hashed_nocheck(hash1, &10, hash2, &100)
            .unwrap(),
        (&10, &100, &10000)
    );
    assert_eq!(map.len(), 6);

    // Ensure all lookup methods produce equivalent results.
    for (k1, k2) in (0..12).zip((0..12).map(|x| x * 10)) {
        let hash1 = compute_hash(&map, k1);
        let hash2 = compute_hash(&map, k2);
        let v = map.get_key1(&k1).cloned();
        let kv = v.as_ref().map(|v| (&k1, &k2, v));

        assert_eq!(map.raw_entry().from_keys(&k1, &k2), kv);
        assert_eq!(
            map.raw_entry()
                .from_hash(hash1, |k| *k == k1, hash2, |k| *k == k2),
            kv
        );
        assert_eq!(
            map.raw_entry()
                .from_keys_hashed_nocheck(hash1, &k1, hash2, &k2),
            kv
        );

        match map.raw_entry_mut().from_keys(&k1, &k2) {
            Ok(raw_entry) => match raw_entry {
                Occupied(mut o) => assert_eq!(o.get_keys_value(), kv.unwrap()),
                Vacant(_) => assert_eq!(v, None),
            },
            Err(_) => panic!(),
        }
        match map
            .raw_entry_mut()
            .from_keys_hashed_nocheck(hash1, &k1, hash2, &k2)
        {
            Ok(raw_entry) => match raw_entry {
                Occupied(mut o) => assert_eq!(o.get_keys_value(), kv.unwrap()),
                Vacant(_) => assert_eq!(v, None),
            },
            Err(_) => panic!(),
        }
        match map
            .raw_entry_mut()
            .from_hash(hash1, |k| *k == k1, hash2, |k| *k == k2)
        {
            Ok(raw_entry) => match raw_entry {
                Occupied(mut o) => assert_eq!(o.get_keys_value(), kv.unwrap()),
                Vacant(_) => assert_eq!(v, None),
            },
            Err(_) => panic!(),
        }
    }

    let mut map = DHashMap::from([
        (1, 10, 100),
        (2, 20, 200),
        (3, 30, 300),
        (4, 40, 400),
        (5, 50, 500),
        (6, 60, 600),
    ]);

    // Check for error results -- all ErrorKind::OccupiedK1AndVacantK2
    for (k1, k2) in (1..=6).map(|x| (x, x * 100)) {
        let hash1 = compute_hash(&map, k1);
        let hash2 = compute_hash(&map, k2);

        match map.raw_entry_mut().from_keys(&k1, &k2) {
            Ok(_) => panic!(),
            Err(error) => assert_eq!(error, ErrorKind::OccupiedK1AndVacantK2),
        }
        match map
            .raw_entry_mut()
            .from_keys_hashed_nocheck(hash1, &k1, hash2, &k2)
        {
            Ok(_) => panic!(),
            Err(error) => assert_eq!(error, ErrorKind::OccupiedK1AndVacantK2),
        }
        match map
            .raw_entry_mut()
            .from_hash(hash1, |k| *k == k1, hash2, |k| *k == k2)
        {
            Ok(_) => panic!(),
            Err(error) => assert_eq!(error, ErrorKind::OccupiedK1AndVacantK2),
        }
    }

    // Check for error results -- all ErrorKind::VacantK1AndOccupiedK2
    for (k1, k2) in (1..=6).map(|x| (x * 100, x * 10)) {
        let hash1 = compute_hash(&map, k1);
        let hash2 = compute_hash(&map, k2);

        match map.raw_entry_mut().from_keys(&k1, &k2) {
            Ok(_) => panic!(),
            Err(error) => assert_eq!(error, ErrorKind::VacantK1AndOccupiedK2),
        }
        match map
            .raw_entry_mut()
            .from_keys_hashed_nocheck(hash1, &k1, hash2, &k2)
        {
            Ok(_) => panic!(),
            Err(error) => assert_eq!(error, ErrorKind::VacantK1AndOccupiedK2),
        }
        match map
            .raw_entry_mut()
            .from_hash(hash1, |k| *k == k1, hash2, |k| *k == k2)
        {
            Ok(_) => panic!(),
            Err(error) => assert_eq!(error, ErrorKind::VacantK1AndOccupiedK2),
        }
    }

    // Check for error results -- all ErrorKind::KeysPointsToDiffEntries
    let keys_iter = (1..=6).map(|x| (x, if x < 6 { (x + 1) * 10 } else { (x - 5) * 10 }));

    for (k1, k2) in keys_iter {
        let hash1 = compute_hash(&map, k1);
        let hash2 = compute_hash(&map, k2);

        match map.raw_entry_mut().from_keys(&k1, &k2) {
            Ok(_) => panic!(),
            Err(error) => assert_eq!(error, ErrorKind::KeysPointsToDiffEntries),
        }
        match map
            .raw_entry_mut()
            .from_keys_hashed_nocheck(hash1, &k1, hash2, &k2)
        {
            Ok(_) => panic!(),
            Err(error) => assert_eq!(error, ErrorKind::KeysPointsToDiffEntries),
        }
        match map
            .raw_entry_mut()
            .from_hash(hash1, |k| *k == k1, hash2, |k| *k == k2)
        {
            Ok(_) => panic!(),
            Err(error) => assert_eq!(error, ErrorKind::KeysPointsToDiffEntries),
        }
    }
}

#[test]
fn test_key_without_hash_impl() {
    #[derive(Debug, PartialEq, Eq, Clone)]
    struct IntWrapper(u64);

    let mut m: DHashMap<IntWrapper, IntWrapper, (), ()> = DHashMap::default();
    {
        assert!(m
            .raw_entry()
            .from_hash(0, |k| k.0 == 0, 0, |k| k.0 == 0)
            .is_none());
    }
    {
        let vacant_entry = match m
            .raw_entry_mut()
            .from_hash(0, |k| k.0 == 0, 0, |k| k.0 == 0)
        {
            Ok(entry) => match entry {
                RawEntryMut::Occupied(..) => panic!("Found entry for key 0"),
                RawEntryMut::Vacant(e) => e,
            },
            Err(_) => panic!(),
        };
        vacant_entry.insert_with_hasher(0, IntWrapper(0), 0, IntWrapper(0), (), |k| k.0, |k| k.0);
    }
    {
        assert!(m
            .raw_entry()
            .from_hash(0, |k| k.0 == 0, 0, |k| k.0 == 0)
            .is_some());
        assert!(m
            .raw_entry()
            .from_hash(1, |k| k.0 == 1, 1, |k| k.0 == 1)
            .is_none());
        assert!(m
            .raw_entry()
            .from_hash(2, |k| k.0 == 2, 2, |k| k.0 == 2)
            .is_none());
    }
    {
        let vacant_entry = match m
            .raw_entry_mut()
            .from_hash(1, |k| k.0 == 1, 1, |k| k.0 == 1)
        {
            Ok(entry) => match entry {
                RawEntryMut::Occupied(..) => panic!("Found entry for key 0"),
                RawEntryMut::Vacant(e) => e,
            },
            Err(_) => panic!(),
        };
        vacant_entry.insert_with_hasher(1, IntWrapper(1), 1, IntWrapper(1), (), |k| k.0, |k| k.0);
    }
    {
        assert!(m
            .raw_entry()
            .from_hash(0, |k| k.0 == 0, 0, |k| k.0 == 0)
            .is_some());
        assert!(m
            .raw_entry()
            .from_hash(1, |k| k.0 == 1, 1, |k| k.0 == 1)
            .is_some());
        assert!(m
            .raw_entry()
            .from_hash(2, |k| k.0 == 2, 2, |k| k.0 == 2)
            .is_none());
    }
    {
        let occupied_entry = match m
            .raw_entry_mut()
            .from_hash(0, |k| k.0 == 0, 0, |k| k.0 == 0)
        {
            Ok(entry) => match entry {
                RawEntryMut::Occupied(e) => e,
                RawEntryMut::Vacant(..) => panic!("Couldn't find entry for key 0"),
            },
            Err(_) => panic!(),
        };
        assert_eq!(
            occupied_entry.remove_entry(),
            (IntWrapper(0), IntWrapper(0), ()),
        );
    }
    {
        assert!(m
            .raw_entry()
            .from_hash(0, |k| k.0 == 0, 0, |k| k.0 == 0)
            .is_none());
        assert!(m
            .raw_entry()
            .from_hash(1, |k| k.0 == 1, 1, |k| k.0 == 1)
            .is_some());
        assert!(m
            .raw_entry()
            .from_hash(2, |k| k.0 == 2, 2, |k| k.0 == 2)
            .is_none());
    }
    {
        let vacant_entry = match m
            .raw_entry_mut()
            .from_hash(0, |k| k.0 == 0, 0, |k| k.0 == 0)
        {
            Ok(entry) => match entry {
                RawEntryMut::Occupied(..) => panic!("Found entry for key 0"),
                RawEntryMut::Vacant(e) => e,
            },
            Err(_) => panic!(),
        };
        vacant_entry.insert_with_hasher(0, IntWrapper(0), 0, IntWrapper(0), (), |k| k.0, |k| k.0);
    }
    {
        assert!(m
            .raw_entry()
            .from_hash(0, |k| k.0 == 0, 0, |k| k.0 == 0)
            .is_some());
        assert!(m
            .raw_entry()
            .from_hash(1, |k| k.0 == 1, 1, |k| k.0 == 1)
            .is_some());
        assert!(m
            .raw_entry()
            .from_hash(2, |k| k.0 == 2, 2, |k| k.0 == 2)
            .is_none());
    }
    {
        let occupied_entry = match m
            .raw_entry_mut()
            .from_hash(0, |k| k.0 == 0, 0, |k| k.0 == 0)
        {
            Ok(entry) => match entry {
                RawEntryMut::Occupied(e) => e,
                RawEntryMut::Vacant(..) => panic!("Couldn't find entry for key 0"),
            },
            Err(_) => panic!(),
        };
        assert_eq!(occupied_entry.remove(), ());
    }
    {
        assert!(m
            .raw_entry()
            .from_hash(0, |k| k.0 == 0, 0, |k| k.0 == 0)
            .is_none());
        assert!(m
            .raw_entry()
            .from_hash(1, |k| k.0 == 1, 1, |k| k.0 == 1)
            .is_some());
        assert!(m
            .raw_entry()
            .from_hash(2, |k| k.0 == 2, 2, |k| k.0 == 2)
            .is_none());
    }
}

#[test]
#[cfg(feature = "raw")]
fn test_into_iter_refresh() {
    #[cfg(miri)]
    const N: usize = 32;
    #[cfg(not(miri))]
    const N: usize = 128;

    let mut rng = rand::thread_rng();
    for n in 0..N {
        let mut map = DHashMap::new();
        for i in 0..n {
            assert!(map.insert(i, i, 2 * i).is_none());
        }
        let hash_builder = map.hasher().clone();

        let mut it = unsafe { map.table.iter() };
        assert_eq!(it.len(), n);

        let mut i = 0;
        let mut left = n;
        let mut removed_v = Vec::new();
        loop {
            // occasionally remove some elements
            if i < n && rng.gen_bool(0.1) {
                let hash = super::make_insert_hash(&hash_builder, &i);

                unsafe {
                    let bucket_v = map.table.find_h1(hash, |q| q.0.eq(&i));
                    let bucket_k = map.table.find_h2(hash, |q| q.1.eq(&i));

                    match (bucket_v, bucket_k) {
                        (Some(bucket_v), Some(bucket_k)) => {
                            it.reflect_remove(&bucket_v);
                            let t_v = map.table.remove(bucket_k);
                            removed_v.push(t_v);

                            left -= 1;
                        }

                        (None, None) => {
                            assert!(
                                removed_v.contains(&(i, i, 2 * i)),
                                "{} not in {:?}",
                                i,
                                removed_v
                            );

                            let (bucket_v, _) = map.table.insert(
                                hash,
                                hash,
                                (i, i, 2 * i),
                                super::make_hasher_key1::<usize, usize, usize, _>(&hash_builder),
                                super::make_hasher_key2::<usize, usize, usize, _>(&hash_builder),
                            );

                            it.reflect_insert(&bucket_v);
                            let p_v = removed_v.iter().position(|e| e == &(i, i, 2 * i));

                            match p_v {
                                Some(p_v) => {
                                    removed_v.swap_remove(p_v);
                                }
                                None => {}
                            }
                            left += 1;
                        }
                        _ => panic!(),
                    }
                }
            }

            let bucket_v = it.next();

            if bucket_v.is_none() {
                break;
            }

            assert!(i < n);
            let t_v = unsafe { bucket_v.unwrap().as_ref() };
            assert!(!removed_v.contains(t_v));

            let (key1, key2, value) = t_v;

            assert_eq!(*value, 2 * key1);
            assert_eq!(*value, 2 * key2);
            i += 1;
        }
        assert!(i <= n);

        // just for safety:
        assert_eq!(map.table.len(), left);
    }
}

#[test]
#[cfg(feature = "raw")]
fn test_into_iter_reflect_remove() {
    #[cfg(miri)]
    const N: usize = 32;
    #[cfg(not(miri))]
    const N: usize = 128;

    let mut rng = rand::thread_rng();
    for n in 0..N {
        let mut map = DHashMap::new();
        for i in 0..n {
            assert!(map.insert(i, 2 * i as u32, 4 * i).is_none());
        }
        let hash_builder = map.hasher().clone();

        let mut iter = unsafe { map.table.iter() };
        assert_eq!(iter.len(), n);

        let mut index = 0;
        let mut left = n;
        let mut removed_data = Vec::new();
        loop {
            // occasionally remove some elements
            if index < n && rng.gen_bool(0.1) {
                let hash_1 = super::make_insert_hash(&hash_builder, &index);
                let hash_2 = super::make_insert_hash(&hash_builder, &(2 * index as u32));

                unsafe {
                    let data_bucket = map.table.find_h1(hash_1, |q| q.0.eq(&index));
                    let pointer_bucket = map.table.find_h2(hash_2, |q| q.1.eq(&(2 * index as u32)));

                    match (data_bucket, pointer_bucket) {
                        (Some(data_bucket), Some(pointer_bucket)) => {
                            iter.reflect_remove(&data_bucket);
                            let data_tuple = map.table.remove(pointer_bucket);
                            removed_data.push(data_tuple);

                            left -= 1;
                        }

                        (None, None) => {
                            let position = removed_data
                                .iter()
                                .position(|e| e == &(index, 2 * index as u32, 4 * index))
                                .expect(&format!("{} not in {:?}", index, removed_data));

                            removed_data.swap_remove(position);

                            let (data_bucket, _) = map.table.insert(
                                hash_1,
                                hash_2,
                                (index, 2 * index as u32, 4 * index),
                                super::make_hasher_key1::<usize, u32, usize, _>(&hash_builder),
                                super::make_hasher_key2::<usize, u32, usize, _>(&hash_builder),
                            );

                            iter.reflect_insert(&data_bucket);
                            left += 1;
                        }
                        (Some(_), None) => panic!("Not found pointer bucket at index {}", index),
                        (None, Some(_)) => panic!("Not found data bucket at index {}", index),
                    }
                }
            }

            let data_bucket = iter.next();

            if data_bucket.is_none() {
                break;
            }

            assert!(index < n);
            let data_tuple = unsafe { data_bucket.unwrap().as_ref() };
            assert!(!removed_data.contains(data_tuple));

            let (key1, key2, value) = data_tuple;

            assert_eq!(*value, 4 * key1);
            assert_eq!(*value, 2 * (*key2 as usize));
            index += 1;
        }
        assert!(index <= n);

        // just for safety:
        assert_eq!(map.table.len(), left);
    }
}

#[test]
#[cfg(feature = "raw")]
fn test_into_iter_reflect_insert() {
    #[cfg(miri)]
    const N: usize = 32;
    #[cfg(not(miri))]
    const N: usize = 128;

    for n in 2..N {
        let mut map = DHashMap::with_capacity(n);

        let mut left = 0_usize;

        for i in (1..n).step_by(2) {
            assert!(map.insert(i, 2 * i as u32, 4 * i).is_none());
            left += 1;
        }

        let hash_builder = map.hasher().clone();

        let mut iter = unsafe { map.table.iter() };
        assert_eq!(iter.len(), left);

        let mut index = 0;
        let mut removed_data = Vec::new();
        let mut inserted_data = Vec::new();
        let mut data_inserted = false;
        let mut reflect_inserted = 0_usize;

        loop {
            // remove or insert some elements
            if index < n {
                let hash_1 = super::make_insert_hash(&hash_builder, &index);
                let hash_2 = super::make_insert_hash(&hash_builder, &(2 * index as u32));

                unsafe {
                    let data_bucket = map.table.find_h1(hash_1, |q| q.0.eq(&index));
                    let pointer_bucket = map.table.find_h2(hash_2, |q| q.1.eq(&(2 * index as u32)));

                    match (data_bucket, pointer_bucket) {
                        (Some(data_bucket), Some(pointer_bucket)) => {
                            iter.reflect_remove(&data_bucket);
                            let data_tuple = map.table.remove(pointer_bucket);
                            removed_data.push(data_tuple);

                            left -= 1;
                        }

                        (None, None) => {
                            inserted_data.push((index, 2 * index as u32, 4 * index));

                            let (data_bucket, _) = map.table.insert(
                                hash_1,
                                hash_2,
                                (index, 2 * index as u32, 4 * index),
                                super::make_hasher_key1::<usize, u32, usize, _>(&hash_builder),
                                super::make_hasher_key2::<usize, u32, usize, _>(&hash_builder),
                            );

                            iter.reflect_insert(&data_bucket);
                            data_inserted = true;
                            left += 1;
                        }
                        (Some(_), None) => panic!("Not found pointer bucket at index {}", index),
                        (None, Some(_)) => panic!("Not found data bucket at index {}", index),
                    }
                }
            }

            let data_bucket = iter.next();

            if data_bucket.is_none() {
                break;
            }

            assert!(index < n);
            let data_tuple = unsafe { data_bucket.unwrap().as_ref() };
            assert!(!removed_data.contains(data_tuple));

            if data_inserted {
                reflect_inserted += usize::from(inserted_data.contains(data_tuple));
            }
            let (key1, key2, value) = data_tuple;

            assert_eq!(*value, 4 * key1);
            assert_eq!(*value, 2 * (*key2 as usize));
            index += 1;
        }
        assert!(index <= n);

        if data_inserted {
            assert!(reflect_inserted > 0);
        }

        // just for safety:
        assert_eq!(map.table.len(), left);
    }
}

#[test]
#[cfg(feature = "raw")]
fn test_into_pointer_iter_reflect_remove() {
    #[cfg(miri)]
    const N: usize = 32;
    #[cfg(not(miri))]
    const N: usize = 128;

    let mut rng = rand::thread_rng();
    for n in 0..N {
        let mut map = DHashMap::new();
        for i in 0..n {
            assert!(map.insert(i, 2 * i as u32, 4 * i).is_none());
        }
        let hash_builder = map.hasher().clone();

        let mut iter = unsafe { map.table.pointers_iter() };
        assert_eq!(iter.len(), n);

        let mut index = 0;
        let mut left = n;
        let mut removed_data = Vec::new();
        loop {
            // occasionally remove some elements
            if index < n && rng.gen_bool(0.1) {
                let hash_1 = super::make_insert_hash(&hash_builder, &index);
                let hash_2 = super::make_insert_hash(&hash_builder, &(2 * index as u32));

                unsafe {
                    let data_bucket = map.table.find_h1(hash_1, |q| q.0.eq(&index));
                    let pointer_bucket = map.table.find_h2(hash_2, |q| q.1.eq(&(2 * index as u32)));

                    match (data_bucket, pointer_bucket) {
                        (Some(_), Some(pointer_bucket)) => {
                            iter.reflect_remove(&pointer_bucket);
                            let data_tuple = map.table.remove(pointer_bucket);
                            removed_data.push(data_tuple);

                            left -= 1;
                        }

                        (None, None) => {
                            let position = removed_data
                                .iter()
                                .position(|e| e == &(index, 2 * index as u32, 4 * index))
                                .expect(&format!("{} not in {:?}", index, removed_data));

                            removed_data.swap_remove(position);

                            let (_, pointer_bucket) = map.table.insert(
                                hash_1,
                                hash_2,
                                (index, 2 * index as u32, 4 * index),
                                super::make_hasher_key1::<usize, u32, usize, _>(&hash_builder),
                                super::make_hasher_key2::<usize, u32, usize, _>(&hash_builder),
                            );

                            iter.reflect_insert(&pointer_bucket);
                            left += 1;
                        }
                        (Some(_), None) => panic!("Not found pointer bucket at index {}", index),
                        (None, Some(_)) => panic!("Not found data bucket at index {}", index),
                    }
                }
            }

            let pointer_bucket = iter.next();

            if pointer_bucket.is_none() {
                break;
            }

            assert!(index < n);
            let data_tuple = unsafe { pointer_bucket.unwrap().as_data_ref() };
            assert!(!removed_data.contains(data_tuple));

            let (key1, key2, value) = data_tuple;

            assert_eq!(*value, 4 * key1);
            assert_eq!(*value, 2 * (*key2 as usize));
            index += 1;
        }
        assert!(index <= n);

        // just for safety:
        assert_eq!(map.table.len(), left);
    }
}

#[test]
#[cfg(feature = "raw")]
fn test_into_pointer_iter_reflect_insert() {
    #[cfg(miri)]
    const N: usize = 32;
    #[cfg(not(miri))]
    const N: usize = 128;

    for n in 2..N {
        let mut map = DHashMap::with_capacity(n);

        let mut left = 0_usize;

        for i in (1..n).step_by(2) {
            assert!(map.insert(i, 2 * i as u32, 4 * i).is_none());
            left += 1;
        }

        let hash_builder = map.hasher().clone();

        let mut iter = unsafe { map.table.pointers_iter() };
        assert_eq!(iter.len(), left);

        let mut index = 0;
        let mut removed_data = Vec::new();
        let mut inserted_data = Vec::new();
        let mut data_inserted = false;
        let mut reflect_inserted = 0_usize;

        loop {
            // remove or insert some elements
            if index < n {
                let hash_1 = super::make_insert_hash(&hash_builder, &index);
                let hash_2 = super::make_insert_hash(&hash_builder, &(2 * index as u32));

                unsafe {
                    let data_bucket = map.table.find_h1(hash_1, |q| q.0.eq(&index));
                    let pointer_bucket = map.table.find_h2(hash_2, |q| q.1.eq(&(2 * index as u32)));

                    match (data_bucket, pointer_bucket) {
                        (Some(_), Some(pointer_bucket)) => {
                            iter.reflect_remove(&pointer_bucket);
                            let data_tuple = map.table.remove(pointer_bucket);
                            removed_data.push(data_tuple);

                            left -= 1;
                        }

                        (None, None) => {
                            inserted_data.push((index, 2 * index as u32, 4 * index));

                            let (_, pointer_bucket) = map.table.insert(
                                hash_1,
                                hash_2,
                                (index, 2 * index as u32, 4 * index),
                                super::make_hasher_key1::<usize, u32, usize, _>(&hash_builder),
                                super::make_hasher_key2::<usize, u32, usize, _>(&hash_builder),
                            );

                            iter.reflect_insert(&pointer_bucket);
                            data_inserted = true;
                            left += 1;
                        }
                        (Some(_), None) => panic!("Not found pointer bucket at index {}", index),
                        (None, Some(_)) => panic!("Not found data bucket at index {}", index),
                    }
                }
            }

            let data_bucket = iter.next();

            if data_bucket.is_none() {
                break;
            }

            assert!(index < n);
            let data_tuple = unsafe { data_bucket.unwrap().as_data_ref() };
            assert!(!removed_data.contains(data_tuple));

            if data_inserted {
                reflect_inserted += usize::from(inserted_data.contains(data_tuple));
            }
            let (key1, key2, value) = data_tuple;

            assert_eq!(*value, 4 * key1);
            assert_eq!(*value, 2 * (*key2 as usize));
            index += 1;
        }
        assert!(index <= n);

        if data_inserted {
            assert!(reflect_inserted > 0);
        }

        // just for safety:
        assert_eq!(map.table.len(), left);
    }
}

#[test]
fn test_const_with_hasher() {
    use core::hash::BuildHasher;
    use std::collections::hash_map::DefaultHasher;

    #[derive(Clone)]
    struct MyHasher;
    impl BuildHasher for MyHasher {
        type Hasher = DefaultHasher;

        fn build_hasher(&self) -> DefaultHasher {
            DefaultHasher::new()
        }
    }

    const EMPTY_MAP: DHashMap<u32, u32, std::string::String, MyHasher> =
        DHashMap::with_hasher(MyHasher);

    let mut map = EMPTY_MAP;
    map.insert(1, 17, "seventeen".to_owned());

    assert_eq!("seventeen", map[&1]);
    assert_eq!(Some(&"seventeen".to_owned()), map.get_key1(&1));
    assert_eq!(Some(&"seventeen".to_owned()), map.get_key2(&17));
    assert_eq!(Some(&"seventeen".to_owned()), map.get_keys(&1, &17));

    assert!(map.contains_key1(&1));
    assert!(map.contains_key2(&17));
    assert!(map.contains_keys(&1, &17));

    assert_eq!(map.len(), 1);

    map.insert(2, 27, "twenty_seven".to_owned());
    map.insert(3, 37, "thirty_seven".to_owned());
    map.insert(4, 47, "forty_seven".to_owned());
    map.insert(5, 57, "fifty_seven".to_owned());
    map.insert(6, 67, "sixty_seven".to_owned());
    map.insert(7, 77, "siventy_seven".to_owned());
    map.insert(8, 87, "eighty_seven".to_owned());
    map.insert(9, 97, "ninety_seven".to_owned());

    assert_eq!("seventeen", map[&1]);
    assert_eq!("twenty_seven", map[&2]);
    assert_eq!("thirty_seven", map[&3]);
    assert_eq!("forty_seven", map[&4]);
    assert_eq!("fifty_seven", map[&5]);
    assert_eq!("sixty_seven", map[&6]);
    assert_eq!("siventy_seven", map[&7]);
    assert_eq!("eighty_seven", map[&8]);
    assert_eq!("ninety_seven", map[&9]);

    assert!(map.contains_key1(&1));
    assert!(map.contains_key1(&2));
    assert!(map.contains_key1(&3));
    assert!(map.contains_key1(&4));
    assert!(map.contains_key1(&5));
    assert!(map.contains_key1(&6));
    assert!(map.contains_key1(&7));
    assert!(map.contains_key1(&8));
    assert!(map.contains_key1(&9));
    assert_eq!(Some(&"seventeen".to_owned()), map.get_key1(&1));
    assert_eq!(Some(&"twenty_seven".to_owned()), map.get_key1(&2));
    assert_eq!(Some(&"thirty_seven".to_owned()), map.get_key1(&3));
    assert_eq!(Some(&"forty_seven".to_owned()), map.get_key1(&4));
    assert_eq!(Some(&"fifty_seven".to_owned()), map.get_key1(&5));
    assert_eq!(Some(&"sixty_seven".to_owned()), map.get_key1(&6));
    assert_eq!(Some(&"siventy_seven".to_owned()), map.get_key1(&7));
    assert_eq!(Some(&"eighty_seven".to_owned()), map.get_key1(&8));
    assert_eq!(Some(&"ninety_seven".to_owned()), map.get_key1(&9));

    assert!(map.contains_key2(&17));
    assert!(map.contains_key2(&27));
    assert!(map.contains_key2(&37));
    assert!(map.contains_key2(&47));
    assert!(map.contains_key2(&57));
    assert!(map.contains_key2(&67));
    assert!(map.contains_key2(&77));
    assert!(map.contains_key2(&87));
    assert!(map.contains_key2(&97));
    assert_eq!(Some(&"seventeen".to_owned()), map.get_key2(&17));
    assert_eq!(Some(&"twenty_seven".to_owned()), map.get_key2(&27));
    assert_eq!(Some(&"thirty_seven".to_owned()), map.get_key2(&37));
    assert_eq!(Some(&"forty_seven".to_owned()), map.get_key2(&47));
    assert_eq!(Some(&"fifty_seven".to_owned()), map.get_key2(&57));
    assert_eq!(Some(&"sixty_seven".to_owned()), map.get_key2(&67));
    assert_eq!(Some(&"siventy_seven".to_owned()), map.get_key2(&77));
    assert_eq!(Some(&"eighty_seven".to_owned()), map.get_key2(&87));
    assert_eq!(Some(&"ninety_seven".to_owned()), map.get_key2(&97));

    assert!(map.contains_keys(&1, &17));
    assert!(map.contains_keys(&2, &27));
    assert!(map.contains_keys(&3, &37));
    assert!(map.contains_keys(&4, &47));
    assert!(map.contains_keys(&5, &57));
    assert!(map.contains_keys(&6, &67));
    assert!(map.contains_keys(&7, &77));
    assert!(map.contains_keys(&8, &87));
    assert!(map.contains_keys(&9, &97));
    assert_eq!(Some(&"seventeen".to_owned()), map.get_keys(&1, &17));
    assert_eq!(Some(&"twenty_seven".to_owned()), map.get_keys(&2, &27));
    assert_eq!(Some(&"thirty_seven".to_owned()), map.get_keys(&3, &37));
    assert_eq!(Some(&"forty_seven".to_owned()), map.get_keys(&4, &47));
    assert_eq!(Some(&"fifty_seven".to_owned()), map.get_keys(&5, &57));
    assert_eq!(Some(&"sixty_seven".to_owned()), map.get_keys(&6, &67));
    assert_eq!(Some(&"siventy_seven".to_owned()), map.get_keys(&7, &77));
    assert_eq!(Some(&"eighty_seven".to_owned()), map.get_keys(&8, &87));
    assert_eq!(Some(&"ninety_seven".to_owned()), map.get_keys(&9, &97));
}

#[test]
fn test_get_each_mut() {
    let mut map = DHashMap::new();
    map.insert("one".to_owned(), "one".to_owned(), 1);
    map.insert("two".to_owned(), "two".to_owned(), 2);
    map.insert("three".to_owned(), "three".to_owned(), 3);
    map.insert("four".to_owned(), "four".to_owned(), 4);

    let xs = map.get_many_mut_key1(["one", "two", "three", "four"]);
    assert_eq!(xs, Some([&mut 1, &mut 2, &mut 3, &mut 4]));

    let xs = map.get_many_mut_key1(["one", "two"]);
    assert_eq!(xs, Some([&mut 1, &mut 2]));

    let xs = map.get_many_mut_key1(["one", "three"]);
    assert_eq!(xs, Some([&mut 1, &mut 3]));

    let xs = map.get_many_mut_key1(["one", "four"]);
    assert_eq!(xs, Some([&mut 1, &mut 4]));

    let xs = map.get_many_mut_key1(["one", "five"]);
    assert_eq!(xs, None);

    let xs = map.get_many_mut_key1(["one", "one"]);
    assert_eq!(xs, None);

    let xs = map.get_many_mut_key1(["five", "five"]);
    assert_eq!(xs, None);

    let ys = map.get_many_key1_value_mut(["one", "two", "three", "four"]);
    assert_eq!(
        ys,
        Some([
            (&"one".to_owned(), &"one".to_owned(), &mut 1),
            (&"two".to_owned(), &"two".to_owned(), &mut 2),
            (&"three".to_owned(), &"three".to_owned(), &mut 3),
            (&"four".to_owned(), &"four".to_owned(), &mut 4)
        ]),
    );

    let ys = map.get_many_key1_value_mut(["one", "two"]);
    assert_eq!(
        ys,
        Some([
            (&"one".to_owned(), &"one".to_owned(), &mut 1),
            (&"two".to_owned(), &"two".to_owned(), &mut 2)
        ]),
    );

    let ys = map.get_many_key1_value_mut(["one", "three"]);
    assert_eq!(
        ys,
        Some([
            (&"one".to_owned(), &"one".to_owned(), &mut 1),
            (&"three".to_owned(), &"three".to_owned(), &mut 3),
        ]),
    );

    let ys = map.get_many_key1_value_mut(["one", "four"]);
    assert_eq!(
        ys,
        Some([
            (&"one".to_owned(), &"one".to_owned(), &mut 1),
            (&"four".to_owned(), &"four".to_owned(), &mut 4)
        ]),
    );

    let ys = map.get_many_key1_value_mut(["one", "five"]);
    assert_eq!(ys, None);

    let ys = map.get_many_key1_value_mut(["one", "one"]);
    assert_eq!(ys, None);

    let xs = map.get_many_mut_key2(["one", "two", "three", "four"]);
    assert_eq!(xs, Some([&mut 1, &mut 2, &mut 3, &mut 4]));

    let xs = map.get_many_mut_key2(["one", "two"]);
    assert_eq!(xs, Some([&mut 1, &mut 2]));

    let xs = map.get_many_mut_key2(["one", "three"]);
    assert_eq!(xs, Some([&mut 1, &mut 3]));

    let xs = map.get_many_mut_key2(["one", "four"]);
    assert_eq!(xs, Some([&mut 1, &mut 4]));

    let xs = map.get_many_mut_key2(["one", "five"]);
    assert_eq!(xs, None);

    let xs = map.get_many_mut_key2(["one", "one"]);
    assert_eq!(xs, None);

    let xs = map.get_many_mut_key2(["five", "five"]);
    assert_eq!(xs, None);

    let ys = map.get_many_key2_value_mut(["one", "two", "three", "four"]);
    assert_eq!(
        ys,
        Some([
            (&"one".to_owned(), &"one".to_owned(), &mut 1),
            (&"two".to_owned(), &"two".to_owned(), &mut 2),
            (&"three".to_owned(), &"three".to_owned(), &mut 3),
            (&"four".to_owned(), &"four".to_owned(), &mut 4)
        ]),
    );

    let ys = map.get_many_key2_value_mut(["one", "two"]);
    assert_eq!(
        ys,
        Some([
            (&"one".to_owned(), &"one".to_owned(), &mut 1),
            (&"two".to_owned(), &"two".to_owned(), &mut 2)
        ]),
    );

    let ys = map.get_many_key2_value_mut(["one", "three"]);
    assert_eq!(
        ys,
        Some([
            (&"one".to_owned(), &"one".to_owned(), &mut 1),
            (&"three".to_owned(), &"three".to_owned(), &mut 3),
        ]),
    );

    let ys = map.get_many_key2_value_mut(["one", "four"]);
    assert_eq!(
        ys,
        Some([
            (&"one".to_owned(), &"one".to_owned(), &mut 1),
            (&"four".to_owned(), &"four".to_owned(), &mut 4)
        ]),
    );

    let ys = map.get_many_key2_value_mut(["one", "five"]);
    assert_eq!(ys, None);

    let ys = map.get_many_key2_value_mut(["one", "one"]);
    assert_eq!(ys, None);

    ////////////////////
    let xs = map.get_many_mut_keys([
        ("one", "one"),
        ("two", "two"),
        ("three", "three"),
        ("four", "four"),
    ]);
    assert_eq!(xs, Some([&mut 1, &mut 2, &mut 3, &mut 4]));

    let xs = map.get_many_mut_keys([("one", "one"), ("two", "two")]);
    assert_eq!(xs, Some([&mut 1, &mut 2]));

    let xs = map.get_many_mut_keys([("one", "one"), ("three", "three")]);
    assert_eq!(xs, Some([&mut 1, &mut 3]));

    let xs = map.get_many_mut_keys([("one", "one"), ("four", "four")]);
    assert_eq!(xs, Some([&mut 1, &mut 4]));

    let xs = map.get_many_mut_keys([("one", "one"), ("five", "five")]);
    assert_eq!(xs, None);

    let xs = map.get_many_mut_keys([("one", "one"), ("one", "one")]);
    assert_eq!(xs, None);

    let xs = map.get_many_mut_keys([("five", "five"), ("five", "five")]);
    assert_eq!(xs, None);

    let xs = map.get_many_mut_keys([("one", "one"), ("five", "five")]);
    assert_eq!(xs, None);

    let xs = map.get_many_mut_keys([("one", "one"), ("one", "one")]);
    assert_eq!(xs, None);

    let xs = map.get_many_mut_keys([("one", "two"), ("three", "four")]);
    assert_eq!(xs, None);

    let xs = map.get_many_mut_keys([("one", "two"), ("one", "two")]);
    assert_eq!(xs, None);

    let xs = map.get_many_mut_keys([("two", "one"), ("four", "four")]);
    assert_eq!(xs, None);

    let ys = map.get_many_keys_value_mut([
        ("one", "one"),
        ("two", "two"),
        ("three", "three"),
        ("four", "four"),
    ]);
    assert_eq!(
        ys,
        Some([
            (&"one".to_owned(), &"one".to_owned(), &mut 1),
            (&"two".to_owned(), &"two".to_owned(), &mut 2),
            (&"three".to_owned(), &"three".to_owned(), &mut 3),
            (&"four".to_owned(), &"four".to_owned(), &mut 4)
        ]),
    );

    let ys = map.get_many_keys_value_mut([("one", "one"), ("two", "two")]);
    assert_eq!(
        ys,
        Some([
            (&"one".to_owned(), &"one".to_owned(), &mut 1),
            (&"two".to_owned(), &"two".to_owned(), &mut 2),
        ]),
    );

    let ys = map.get_many_keys_value_mut([("one", "one"), ("three", "three")]);
    assert_eq!(
        ys,
        Some([
            (&"one".to_owned(), &"one".to_owned(), &mut 1),
            (&"three".to_owned(), &"three".to_owned(), &mut 3),
        ]),
    );

    let ys = map.get_many_keys_value_mut([("one", "one"), ("four", "four")]);
    assert_eq!(
        ys,
        Some([
            (&"one".to_owned(), &"one".to_owned(), &mut 1),
            (&"four".to_owned(), &"four".to_owned(), &mut 4)
        ]),
    );

    let ys = map.get_many_keys_value_mut([("one", "one"), ("five", "five")]);
    assert_eq!(ys, None);

    let ys = map.get_many_keys_value_mut([("one", "one"), ("one", "one")]);
    assert_eq!(ys, None);

    let ys = map.get_many_keys_value_mut([("one", "two"), ("three", "four")]);
    assert_eq!(ys, None);

    let ys = map.get_many_keys_value_mut([("one", "two"), ("one", "two")]);
    assert_eq!(ys, None);

    let ys = map.get_many_keys_value_mut([("two", "one"), ("four", "four")]);
    assert_eq!(ys, None);
}

#[test]
#[should_panic = "panic in drop"]
fn test_clone_from_double_drop() {
    #[derive(Clone)]
    struct CheckedDrop {
        panic_in_drop: bool,
        dropped: bool,
    }
    impl Drop for CheckedDrop {
        fn drop(&mut self) {
            if self.panic_in_drop {
                self.dropped = true;
                panic!("panic in drop");
            }
            if self.dropped {
                panic!("double drop");
            }
            self.dropped = true;
        }
    }
    const DISARMED: CheckedDrop = CheckedDrop {
        panic_in_drop: false,
        dropped: false,
    };
    const ARMED: CheckedDrop = CheckedDrop {
        panic_in_drop: true,
        dropped: false,
    };

    let mut map1 = DHashMap::new();
    map1.insert(1, 1, DISARMED);
    map1.insert(2, 2, DISARMED);
    map1.insert(3, 3, DISARMED);
    map1.insert(4, 4, DISARMED);

    let mut map2 = DHashMap::new();
    map2.insert(1, 1, DISARMED);
    map2.insert(2, 2, ARMED);
    map2.insert(3, 3, DISARMED);
    map2.insert(4, 4, DISARMED);

    map2.clone_from(&map1);
}

mod test_drain_filter {
    use super::*;

    use core::sync::atomic::{AtomicUsize, Ordering};
    use std::panic::{catch_unwind, AssertUnwindSafe};

    trait EqSorted: Iterator {
        fn eq_sorted<I: IntoIterator<Item = Self::Item>>(self, other: I) -> bool;
    }

    impl<T: Iterator> EqSorted for T
    where
        T::Item: Eq + Ord,
    {
        fn eq_sorted<I: IntoIterator<Item = Self::Item>>(self, other: I) -> bool {
            let mut v: Vec<_> = self.collect();
            v.sort_unstable();
            v.into_iter().eq(other)
        }
    }

    #[test]
    fn empty() {
        let mut map: DHashMap<i32, i32, i32> = DHashMap::new();
        map.drain_filter(|_, _, _| panic!("there's nothing to decide on"));
        assert!(map.is_empty());
    }

    #[test]
    fn consuming_nothing() {
        let tuples = (0..3).map(|i| (i, i * 2, i * 3));
        let mut map: DHashMap<_, _, _> = tuples.collect();
        assert!(map
            .drain_filter(|_, _, _| false)
            .eq_sorted(core::iter::empty()));
        assert_eq!(map.len(), 3);

        let DHashMap { table, .. } = map;

        let mut table = table.into_iter().collect::<Vec<_>>();

        table.sort_unstable();

        for (i, (k1, k2, v)) in table.into_iter().enumerate() {
            assert_eq!(k1, i);
            assert_eq!(k2, i * 2);
            assert_eq!(v, i * 3);
        }
    }

    #[test]
    fn consuming_all() {
        let tuples = (0..3).map(|i| (i, i * 2, i * 3));
        let mut map: DHashMap<_, _, _> = tuples.clone().collect();
        assert!(map.drain_filter(|_, _, _| true).eq_sorted(tuples));
        assert!(map.is_empty());
    }

    #[test]
    fn mutating_and_keeping() {
        let tuples = (0..3).map(|i| (i, i * 2, i * 3));
        let mut map: DHashMap<_, _, _> = tuples.collect();
        assert!(map
            .drain_filter(|_, _, v| {
                *v += 6;
                false
            })
            .eq_sorted(core::iter::empty()));
        assert!(map
            .clone()
            .into_keys()
            .eq_sorted((0..3).map(|i| (i, i * 2))));
        assert!(map.into_values().eq_sorted((0..3).map(|i| i * 3 + 6)));
    }

    #[test]
    fn mutating_and_removing() {
        let tuples = (0..3).map(|i| (i, i * 2, i * 3));
        let mut map: DHashMap<_, _, _> = tuples.collect();
        assert!(map
            .drain_filter(|_, _, v| {
                *v += 6;
                true
            })
            .eq_sorted((0..3).map(|i| (i, i * 2, i * 3 + 6))));
        assert!(map.is_empty());
    }

    #[test]
    fn drop_panic_leak() {
        static PREDS: AtomicUsize = AtomicUsize::new(0);
        static DROPS: AtomicUsize = AtomicUsize::new(0);

        struct D;
        impl Drop for D {
            fn drop(&mut self) {
                if DROPS.fetch_add(1, Ordering::SeqCst) == 1 {
                    panic!("panic in `drop`");
                }
            }
        }

        let mut map = (0..3).map(|i| (i, i, D)).collect::<DHashMap<_, _, _>>();

        catch_unwind(move || {
            drop(map.drain_filter(|_, _, _| {
                PREDS.fetch_add(1, Ordering::SeqCst);
                true
            }))
        })
        .unwrap_err();

        assert_eq!(PREDS.load(Ordering::SeqCst), 3);
        assert_eq!(DROPS.load(Ordering::SeqCst), 3);
    }

    #[test]
    fn pred_panic_leak() {
        static PREDS: AtomicUsize = AtomicUsize::new(0);
        static DROPS: AtomicUsize = AtomicUsize::new(0);

        struct D;
        impl Drop for D {
            fn drop(&mut self) {
                DROPS.fetch_add(1, Ordering::SeqCst);
            }
        }

        let mut map = (0..3).map(|i| (i, i, D)).collect::<DHashMap<_, _, _>>();

        catch_unwind(AssertUnwindSafe(|| {
            drop(
                map.drain_filter(|_, _, _| match PREDS.fetch_add(1, Ordering::SeqCst) {
                    0 => true,
                    _ => panic!(),
                }),
            )
        }))
        .unwrap_err();

        assert_eq!(PREDS.load(Ordering::SeqCst), 2);
        assert_eq!(DROPS.load(Ordering::SeqCst), 1);
        assert_eq!(map.len(), 2);
    }

    // Same as above, but attempt to use the iterator again after the panic in the predicate
    #[test]
    fn pred_panic_reuse() {
        static PREDS: AtomicUsize = AtomicUsize::new(0);
        static DROPS: AtomicUsize = AtomicUsize::new(0);

        struct D;
        impl Drop for D {
            fn drop(&mut self) {
                DROPS.fetch_add(1, Ordering::SeqCst);
            }
        }

        let mut map = (0..3).map(|i| (i, i, D)).collect::<DHashMap<_, _, _>>();

        {
            let mut it = map.drain_filter(|_, _, _| match PREDS.fetch_add(1, Ordering::SeqCst) {
                0 => true,
                _ => panic!(),
            });
            catch_unwind(AssertUnwindSafe(|| while it.next().is_some() {})).unwrap_err();
            // Iterator behaviour after a panic is explicitly unspecified,
            // so this is just the current implementation:
            let result = catch_unwind(AssertUnwindSafe(|| it.next()));
            assert!(result.is_err());
        }

        assert_eq!(PREDS.load(Ordering::SeqCst), 3);
        assert_eq!(DROPS.load(Ordering::SeqCst), 1);
        assert_eq!(map.len(), 2);
    }
}

#[test]
fn from_array() {
    let map: DHashMap<i32, i32, i32, _, Global> = DHashMap::from([(1, 2, 3), (4, 5, 6), (7, 8, 9)]);
    let unordered_duplicates = DHashMap::from([
        (1, 2, 3),
        (4, 5, 6),
        (7, 8, 9),
        (7, 8, 9),
        (1, 2, 3),
        (4, 5, 6),
    ]);
    assert_eq!(map, unordered_duplicates);

    // This next line must infer the hasher type parameter.
    // If you make a change that causes this line to no longer infer,
    // that's a problem!
    let _must_not_require_type_annotation: DHashMap<_, _, _, _, Global> =
        DHashMap::from([(1, 2, 3)]);
}
