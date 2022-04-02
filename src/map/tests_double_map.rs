// use super::{InsertError, TryInsertError, OccupiedError};
// use super::ErrorKind;
use super::DHashMap;

#[test]
fn test_zero_capacities() {
    type HM = DHashMap<i32, i32, i32>;
    use std::collections::hash_map::RandomState;

    let m = HM::new();
    assert_eq!(m.capacity(), 0);
    assert_eq!(m.value_map.capacity(), 0);
    assert_eq!(m.key_map.capacity(), 0);

    let m = HM::with_hasher(RandomState::new());
    assert_eq!(m.capacity(), 0);
    assert_eq!(m.value_map.capacity(), 0);
    assert_eq!(m.key_map.capacity(), 0);

    let m = HM::with_capacity(0);
    assert_eq!(m.capacity(), 0);
    assert_eq!(m.value_map.capacity(), 0);
    assert_eq!(m.key_map.capacity(), 0);

    let m = HM::with_capacity_and_hasher(0, RandomState::new());
    assert_eq!(m.capacity(), 0);
    assert_eq!(m.value_map.capacity(), 0);
    assert_eq!(m.key_map.capacity(), 0);

    let mut m = HM::new();
    m.insert(1, 1, 1);
    m.insert(2, 2, 2);
    assert_eq!(m.get_key1(&1), Some(&1));
    assert_eq!(m.get_key1(&2), Some(&2));
    m.remove_key1(&1);
    m.remove_key1(&2);
    m.shrink_to_fit();
    assert_eq!(m.capacity(), 0);
    assert_eq!(m.value_map.capacity(), 0);
    assert_eq!(m.key_map.capacity(), 0);

    let mut m = HM::new();
    m.insert(1, 1, 1);
    m.insert(2, 2, 2);
    assert_eq!(m.get_key2(&1), Some(&1));
    assert_eq!(m.get_key2(&2), Some(&2));
    m.remove_key2(&1);
    m.remove_key2(&2);
    m.shrink_to_fit();
    assert_eq!(m.capacity(), 0);
    assert_eq!(m.value_map.capacity(), 0);
    assert_eq!(m.key_map.capacity(), 0);

    let mut m = HM::new();
    let _ = m.try_insert(1, 1, 1);
    let _ = m.try_insert(2, 2, 2);
    assert_eq!(m.get_key1(&1), Some(&1));
    assert_eq!(m.get_key1(&2), Some(&2));
    m.remove_key1(&1);
    m.remove_key1(&2);
    m.shrink_to_fit();
    assert_eq!(m.capacity(), 0);
    assert_eq!(m.value_map.capacity(), 0);
    assert_eq!(m.key_map.capacity(), 0);

    let mut m = HM::new();
    let _ = m.try_insert(1, 1, 1);
    let _ = m.try_insert(2, 2, 2);
    assert_eq!(m.get_key2(&1), Some(&1));
    assert_eq!(m.get_key2(&2), Some(&2));
    m.remove_key2(&1);
    m.remove_key2(&2);
    m.shrink_to_fit();
    assert_eq!(m.capacity(), 0);
    assert_eq!(m.value_map.capacity(), 0);
    assert_eq!(m.key_map.capacity(), 0);

    let mut m = HM::new();
    m.insert_unchecked(1, 1, 1);
    m.insert_unchecked(2, 2, 2);
    assert_eq!(m.get_key1(&1), Some(&1));
    assert_eq!(m.get_key1(&2), Some(&2));
    m.remove_key1(&1);
    m.remove_key1(&2);
    m.shrink_to_fit();
    assert_eq!(m.capacity(), 0);
    assert_eq!(m.value_map.capacity(), 0);
    assert_eq!(m.key_map.capacity(), 0);

    let mut m = HM::new();
    m.insert_unchecked(1, 1, 1);
    m.insert_unchecked(2, 2, 2);
    assert_eq!(m.get_key2(&1), Some(&1));
    assert_eq!(m.get_key2(&2), Some(&2));
    m.remove_key2(&1);
    m.remove_key2(&2);
    m.shrink_to_fit();
    assert_eq!(m.capacity(), 0);
    assert_eq!(m.value_map.capacity(), 0);
    assert_eq!(m.key_map.capacity(), 0);

    let mut m = HM::new();
    let _ = m.entry(1, 1).map(|e| e.or_insert(1));
    let _ = m.entry(2, 2).map(|e| e.or_insert(2));
    assert_eq!(m.get_key1(&1), Some(&1));
    assert_eq!(m.get_key1(&2), Some(&2));
    m.remove_key1(&1);
    m.remove_key1(&2);
    m.shrink_to_fit();
    assert_eq!(m.capacity(), 0);
    assert_eq!(m.value_map.capacity(), 0);
    assert_eq!(m.key_map.capacity(), 0);

    let mut m = HM::new();
    let _ = m.entry(1, 1).map(|e| e.or_insert(1));
    let _ = m.entry(2, 2).map(|e| e.or_insert(2));
    assert_eq!(m.get_key2(&1), Some(&1));
    assert_eq!(m.get_key2(&2), Some(&2));
    m.remove_key2(&1);
    m.remove_key2(&2);
    m.shrink_to_fit();
    assert_eq!(m.capacity(), 0);
    assert_eq!(m.value_map.capacity(), 0);
    assert_eq!(m.key_map.capacity(), 0);

    let mut m = HM::new();
    m.reserve(0);
    assert_eq!(m.capacity(), 0);
    assert_eq!(m.value_map.capacity(), 0);
    assert_eq!(m.key_map.capacity(), 0);
}

#[test]
fn test_create_capacity_zero() {
    let mut m = DHashMap::with_capacity(0);

    assert!(m.insert(1, 1, 10).is_none());

    assert_eq!(m.get_key1(&1), Some(&10));
    assert_eq!(m.get_key1(&0), None);
    assert_eq!(m.get_key2(&1), Some(&10));
    assert_eq!(m.get_key2(&0), None);
    //assert!(m.contains_key1(&1));
    //assert!(!m.contains_key1(&0));
}

#[test]
fn test_insert() {
    let mut m = DHashMap::new();
    assert_eq!(m.len(), 0);
    assert!(m.insert(1, 3, 10).is_none());
    assert_eq!(m.len(), 1);
    assert!(m.insert(2, 4, 20).is_none());
    assert_eq!(m.len(), 2);
    assert_eq!(*m.get_key1(&1).unwrap(), 10);
    assert_eq!(*m.get_key1(&2).unwrap(), 20);
    assert_eq!(*m.get_key2(&3).unwrap(), 10);
    assert_eq!(*m.get_key2(&4).unwrap(), 20);
}

#[test]
fn test_clone() {
    let mut m = DHashMap::new();
    assert_eq!(m.len(), 0);
    assert!(m.insert(1, 3, 10).is_none());
    assert_eq!(m.len(), 1);
    assert!(m.insert(2, 4, 20).is_none());
    assert_eq!(m.len(), 2);
    let m2 = m.clone();
    assert_eq!(*m2.get_key1(&1).unwrap(), 10);
    assert_eq!(*m2.get_key1(&2).unwrap(), 20);
    assert_eq!(*m2.get_key2(&3).unwrap(), 10);
    assert_eq!(*m2.get_key2(&4).unwrap(), 20);
    assert_eq!(m2.len(), 2);
}