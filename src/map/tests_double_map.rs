// use super::{InsertError, TryInsertError, OccupiedError};
// use super::ErrorKind;
use super::DHashMap;
use core::cell::RefCell;

#[test]
fn test_zero_capacities() {
    type HM = DHashMap<i32, i32, i32>;
    use std::collections::hash_map::RandomState;

    let m = HM::new();
    assert_eq!(m.capacity(), 0);
    assert_eq!(m.value_map.capacity(), 0);
    assert_eq!(m.key_map.capacity(), 0);

    let m = HM::default();
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

// thread_local! { static DROP_VECTOR: RefCell<Vec<i32>> = RefCell::new(Vec::new()) }
//
// #[derive(Hash, PartialEq, Eq)]
// struct Droppable {
//     k: usize,
// }
//
// impl Droppable {
//     fn new(k: usize) -> Droppable {
//         DROP_VECTOR.with(|slot| {
//             slot.borrow_mut()[k] += 1;
//         });
//
//         Droppable { k }
//     }
// }
//
// impl Drop for Droppable {
//     fn drop(&mut self) {
//         DROP_VECTOR.with(|slot| {
//             slot.borrow_mut()[self.k] -= 1;
//         });
//     }
// }
//
// impl Clone for Droppable {
//     fn clone(&self) -> Droppable {
//         Droppable::new(self.k)
//     }
// }
//
// #[test]
// fn test_drops() {
//     DROP_VECTOR.with(|slot| {
//         *slot.borrow_mut() = vec![0; 200];
//     });
//
//     {
//         let mut m = DHashMap::new();
//
//         DROP_VECTOR.with(|v| {
//             for i in 0..200 {
//                 assert_eq!(v.borrow()[i], 0);
//             }
//         });
//
//         for i in 0..100 {
//             let d1_1 = Droppable::new(i);
//             let d1_2 = Droppable::new(i);
//             let d2 = Droppable::new(i + 100);
//             m.insert(d1_1, d1_2, d2);
//         }
//
//         DROP_VECTOR.with(|v| {
//             for i in 0..200 {
//                 assert_eq!(v.borrow()[i], 1);
//             }
//         });
//
//         for i in 0..50 {
//             let k = Droppable::new(i);
//             let v = m.remove_key1(&k);
//
//             assert!(v.is_some());
//
//             DROP_VECTOR.with(|v| {
//                 assert_eq!(v.borrow()[i], 1);
//                 assert_eq!(v.borrow()[i + 100], 1);
//             });
//         }
//
//         DROP_VECTOR.with(|v| {
//             for i in 0..50 {
//                 assert_eq!(v.borrow()[i], 0);
//                 assert_eq!(v.borrow()[i + 100], 0);
//             }
//
//             for i in 50..100 {
//                 assert_eq!(v.borrow()[i], 1);
//                 assert_eq!(v.borrow()[i + 100], 1);
//             }
//         });
//     }
//
//     DROP_VECTOR.with(|v| {
//         for i in 0..200 {
//             assert_eq!(v.borrow()[i], 0);
//         }
//     });
// }

//
// #[test]
// fn test_insert() {
//     let mut m = DHashMap::new();
//     assert_eq!(m.len(), 0);
//     assert!(m.insert(1, "a", 2).is_none());
//     assert_eq!(m.len(), 1);
//     assert!(m.insert(2, "b", 4).is_none());
//     assert_eq!(m.len(), 2);
//
//     assert_eq!(*m.get_key1(&1).unwrap(), 2);
//     assert_eq!(*m.get_key1(&2).unwrap(), 4);
//
//     assert_eq!(*m.get_key2(&"a").unwrap(), 2);
//     assert_eq!(*m.get_key2(&"b").unwrap(), 4);
// }
//
// #[test]
// fn test_insert2() {
//     // use double_map::{DHashMap, TryInsertError, ErrorKind, OccupiedEntry,
//     //OccupiedError, InsertError};
//
//     let mut map = DHashMap::new();
//
//     // Return mutable reference to the value if keys vacant
//     let value = map.try_insert(1, "a", "One").unwrap();
//     assert_eq!(value, &"One");
//     *value = "First";
//     assert_eq!(map.get_key1(&1), Some(&"First"));
//
//     // If the map did have these key present, and both keys refers to
//     // the same value, nothing is updated, and the provided value
//     // is returned inside `Err(TryInsertError::Occupied(_))` variants
//     map.try_insert(2, "b", "Two");
//     match map.try_insert(2, "b", "Second") {
//         Err(error) => match error {
//             TryInsertError::Occupied(OccupiedError{ entry, value }) => {
//                 assert_eq!(entry.keys(), (&2, &"b"));
//                 assert_eq!(entry.get(), &"Two");
//                 assert_eq!(value, "Second");
//             }
//             _ => unreachable!()
//         }
//         _ => unreachable!(),
//     }
//     assert_eq!(map.get_key1(&2), Some(&"Two"));
//
//     // Return `ErrorKind::OccupiedK1AndVacantK2` if key #1 is already
//     // exists with some value, but key #2 is vacant. Error structure
//     // also contain provided keys and value
//     match map.try_insert(1, "c", "value") {
//         Err(error) => match error {
//             TryInsertError::Insert(InsertError{ error, keys, value }) => {
//                 assert_eq!(error, ErrorKind::OccupiedK1AndVacantK2);
//                 assert_eq!(keys, (1, "c"));
//                 assert_eq!(value, "value");
//             }
//             _ => unreachable!()
//         }
//         _ => unreachable!(),
//     }
//
//     // Return `ErrorKind::VacantK1AndOccupiedK2` if key #1 is vacant,
//     // but key #2 is already exists with some value.
//     match map.try_insert(3, "a", "value") {
//         Err(error) => match error {
//             TryInsertError::Insert(InsertError{ error, .. }) => {
//                 assert_eq!(error, ErrorKind::VacantK1AndOccupiedK2);
//             }
//             _ => unreachable!()
//         }
//         _ => unreachable!(),
//     }
//
//     // Return `ErrorKind::KeysPointsToDiffEntries` if both
//     // key #1 and key #2 are already exists with some values,
//     // but points to different entries (values).
//     match map.try_insert(1, "b", "value") {
//         Err(error) => match error {
//             TryInsertError::Insert(InsertError{ error, .. }) => {
//                 assert_eq!(error, ErrorKind::KeysPointsToDiffEntries);
//             }
//             _ => unreachable!()
//         }
//         _ => unreachable!(),
//     }
// }