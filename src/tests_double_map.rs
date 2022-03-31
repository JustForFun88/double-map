use super::{InsertError, TryInsertError, OccupiedError};
use super::ErrorKind;
use super::Entry::{Occupied, Vacant};
use super::DHashMap;

#[test]
fn test_insert() {
    let mut m = DHashMap::new();
    assert_eq!(m.len(), 0);
    assert!(m.insert(1, "a", 2).is_none());
    assert_eq!(m.len(), 1);
    assert!(m.insert(2, "b", 4).is_none());
    assert_eq!(m.len(), 2);

    assert_eq!(*m.get_key1(&1).unwrap(), 2);
    assert_eq!(*m.get_key1(&2).unwrap(), 4);

    assert_eq!(*m.get_key2(&"a").unwrap(), 2);
    assert_eq!(*m.get_key2(&"b").unwrap(), 4);
}

#[test]
fn test_insert2() {
    // use double_map::{DHashMap, TryInsertError, ErrorKind, OccupiedEntry,
    //OccupiedError, InsertError};

    let mut map = DHashMap::new();

    // Return mutable reference to the value if keys vacant
    let value = map.try_insert(1, "a", "One").unwrap();
    assert_eq!(value, &"One");
    *value = "First";
    assert_eq!(map.get_key1(&1), Some(&"First"));

    // If the map did have these key present, and both keys refers to
    // the same value, nothing is updated, and the provided value
    // is returned inside `Err(TryInsertError::Occupied(_))` variants
    map.try_insert(2, "b", "Two");
    match map.try_insert(2, "b", "Second") {
        Err(error) => match error {
            TryInsertError::Occupied(OccupiedError{ entry, value }) => {
                assert_eq!(entry.keys(), (&2, &"b"));
                assert_eq!(entry.get(), &"Two");
                assert_eq!(value, "Second");
            }
            _ => unreachable!()
        }
        _ => unreachable!(),
    }
    assert_eq!(map.get_key1(&2), Some(&"Two"));

    // Return `ErrorKind::OccupiedK1AndVacantK2` if key #1 is already
    // exists with some value, but key #2 is vacant. Error structure
    // also contain provided keys and value
    match map.try_insert(1, "c", "value") {
        Err(error) => match error {
            TryInsertError::Insert(InsertError{ error, keys, value }) => {
                assert_eq!(error, ErrorKind::OccupiedK1AndVacantK2);
                assert_eq!(keys, (1, "c"));
                assert_eq!(value, "value");
            }
            _ => unreachable!()
        }
        _ => unreachable!(),
    }

    // Return `ErrorKind::VacantK1AndOccupiedK2` if key #1 is vacant,
    // but key #2 is already exists with some value.
    match map.try_insert(3, "a", "value") {
        Err(error) => match error {
            TryInsertError::Insert(InsertError{ error, .. }) => {
                assert_eq!(error, ErrorKind::VacantK1AndOccupiedK2);
            }
            _ => unreachable!()
        }
        _ => unreachable!(),
    }

    // Return `ErrorKind::KeysPointsToDiffEntries` if both
    // key #1 and key #2 are already exists with some values,
    // but points to different entries (values).
    match map.try_insert(1, "b", "value") {
        Err(error) => match error {
            TryInsertError::Insert(InsertError{ error, .. }) => {
                assert_eq!(error, ErrorKind::KeysPointsToDiffEntries);
            }
            _ => unreachable!()
        }
        _ => unreachable!(),
    }
}