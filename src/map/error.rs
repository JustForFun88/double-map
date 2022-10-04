use super::*;
use core::fmt::{self, Debug};

/// A view into an error kind returned by [`entry`](DoubleMap::entry), [`insert`](DoubleMap::insert),
/// [`try_insert`](DoubleMap::try_insert) methods of the [`DoubleMap`].
/// It is part of the [`EntryError`] structure, [`InsertError`] structure and [`TryInsertError`]
/// enum.
///
/// Explains why [`entry`](DoubleMap::entry), [`insert`](DoubleMap::insert),
/// [`try_insert`](DoubleMap::try_insert) methods fail.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum ErrorKind {
    /// Returns when `K1` key is vacant, but `K2` key already exists with some value.
    VacantK1AndOccupiedK2,
    /// Returns when `K1` key already exists with some value, but `K2` key is vacant.
    OccupiedK1AndVacantK2,
    /// Returns when both `K1` and `K2` keys already exist with some values, but point
    /// to different entries (values).
    KeysPointsToDiffEntries,
}

impl fmt::Display for ErrorKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let error_txt = match *self {
            ErrorKind::OccupiedK1AndVacantK2 => "occupied key1 but vacant key2",
            ErrorKind::VacantK1AndOccupiedK2 => "vacant key1 but occupied key2",
            ErrorKind::KeysPointsToDiffEntries => {
                "key1 and key2 exist, but point to different entries"
            }
        };
        write!(f, "{}", error_txt)
    }
}

/// The error returned by [`entry`](DoubleMap::entry) method when there is no way to distinguish
/// which entry should be returned. For more information about error kinds look at [`ErrorKind`]
/// enum.
///
/// Contains the [`ErrorKind`] enum, and the values of provided keys (that can be used for another
/// purpose).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct EntryError<K1, K2> {
    /// A view into an error kind returned by [`entry`](DoubleMap::entry),
    /// [`insert`](DoubleMap::insert), [`try_insert`](DoubleMap::try_insert) methods of the [`DoubleMap`].
    /// It is part of the [`EntryError`] structure, [`InsertError`] structure and [`TryInsertError`]
    /// enum. Explains [`entry`](DoubleMap::entry), [`insert`](DoubleMap::insert),
    /// [`try_insert`](DoubleMap::try_insert) methods fail. For more information about error
    /// kind look at [`ErrorKind`] enum.
    pub error: ErrorKind,
    /// The provided values of keys that were returned because of error. For more information about
    /// error kind look at [`ErrorKind`] enum.
    pub keys: (K1, K2),
}

impl<K1: Debug, K2: Debug> fmt::Display for EntryError<K1, K2> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let &(ref key1, ref key2) = &self.keys;
        match self.error {
            ErrorKind::VacantK1AndOccupiedK2 => write!(
                f,
                "failed to get entry, because key1 = {:?} - vacant, but key2 = {:?} - exists",
                key1, key2
            ),
            ErrorKind::OccupiedK1AndVacantK2 => write!(
                f,
                "failed to get entry, because key1 = {:?} - exists, but key2 = {:?} - vacant",
                key1, key2
            ),
            ErrorKind::KeysPointsToDiffEntries => write!(
                f,
                "failed to get entry, because key1 = {:?} and key2 = {:?} point to different entries",
                key1, key2
            ),
        }
    }
}

/// The error returned by [`insert`](DoubleMap::insert) method (and also
/// [`try_insert`](DoubleMap::try_insert) method) when there is no way to distinguish
/// how given value with `K1` and `K2` keys should be inserted. It is also part of the
/// [`TryInsertError`] enum which is returned by [`try_insert`](DoubleMap::try_insert) method
/// of [`DoubleMap`]. For more information about error kinds look at [`ErrorKind`] enum.
///
/// Contains the [`ErrorKind`] enum, the provided keys and value that were not inserted.
/// These returned keys and value can be used for another purpose.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct InsertError<K1, K2, V> {
    /// A view into an error kind returned by [`entry`](DoubleMap::entry),
    /// [`insert`](DoubleMap::insert), [`try_insert`](DoubleMap::try_insert) methods of the [`DoubleMap`].
    /// It is part of the [`EntryError`] structure, [`InsertError`] structure and [`TryInsertError`]
    /// enum. Explains [`entry`](DoubleMap::entry), [`insert`](DoubleMap::insert),
    /// [`try_insert`](DoubleMap::try_insert) methods fail. For more information about error
    /// kind look at [`ErrorKind`] enum.
    pub error: ErrorKind,
    /// The provided keys that were returned because of error. For more information about
    /// error kind look at [`ErrorKind`] enum.
    pub keys: (K1, K2),
    /// The value which was not inserted because of the error. For more information about error
    /// kind look at [`ErrorKind`] enum.
    pub value: V,
}

impl<K1: Debug, K2: Debug, V: Debug> fmt::Display for InsertError<K1, K2, V> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let &(ref key1, ref key2) = &self.keys;
        match self.error {
            ErrorKind::VacantK1AndOccupiedK2 => write!(
                f,
                "failed to insert {:?}, because of key1 = {:?} - vacant, but key2 = {:?} - exists",
                self.value, key1, key2
            ),
            ErrorKind::OccupiedK1AndVacantK2 => write!(
                f,
                "failed to insert {:?}, because of key1 = {:?} - exists, but key2 = {:?} - vacant",
                self.value, key1, key2
            ),
            ErrorKind::KeysPointsToDiffEntries => write!(
                f,
                "failed to insert {:?}, because of key1 = {:?} and key2 = {:?} point to different entries",
                self.value, key1, key2
            ),
        }
    }
}

/// The error returned by [`try_insert`](DoubleMap::try_insert) (as a part of the [`TryInsertError`]
/// enum) when the keys already exist and point to the same value.
///
/// Contains the occupied entry, and the value that was not inserted. It is part of the
/// [`TryInsertError`] enum.
pub struct OccupiedError<'a, K1, K2, V, S, A: Allocator + Clone = Global> {
    /// The entry in the map that was already occupied. It contains [`OccupiedEntry`] structure
    /// which is also a part of the [`Entry`] enum.
    pub entry: OccupiedEntry<'a, K1, K2, V, S, A>,
    /// The value which was not inserted, because the entry was already occupied.
    pub value: V,
}

impl<K1: Debug, K2: Debug, V: Debug, S, A: Allocator + Clone> Debug
    for OccupiedError<'_, K1, K2, V, S, A>
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("OccupiedError")
            .field("key1", self.entry.key1())
            .field("key2", self.entry.key2())
            .field("old_value", self.entry.get())
            .field("new_value", &self.value)
            .finish()
    }
}

impl<'a, K1: Debug, K2: Debug, V: Debug, S, A: Allocator + Clone> fmt::Display
    for OccupiedError<'a, K1, K2, V, S, A>
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "failed to insert {:?}, key1 = {:?} and key2 = {:?} already exist with value {:?}",
            self.value,
            self.entry.key1(),
            self.entry.key2(),
            self.entry.get(),
        )
    }
}

/// The error returned by [`try_insert`](DoubleMap::try_insert) method when the keys already exist
/// and point to the same value (look at [`OccupiedError`]) or there is no way to distinguish how
/// given value with `K1` and `K2` keys should be inserted. For more information about error kinds
/// look at [`OccupiedError`], [`InsertError`] structures and [`ErrorKind`] enum.
///
/// Depending of error kind, this enum can contain:
/// - When there is [`TryInsertError::Occupied`] variant, it contains the occupied entry, and
/// the value that was not inserted (through [`OccupiedError`] structure).
/// - When there is [`TryInsertError::Insert`] variant, it contains the [`ErrorKind`] enum,
/// the provided keys and value that were not inserted (through [`InsertError`] structure).
pub enum TryInsertError<'a, K1, K2, V, S, A: Allocator + Clone = Global> {
    /// The error kind returned by [`try_insert`](DoubleMap::try_insert) when the keys already
    /// exist and point to the same value. Contains the [`OccupiedError`] structure.
    Occupied(OccupiedError<'a, K1, K2, V, S, A>),
    /// The error kind returned by [`try_insert`](DoubleMap::try_insert) method when there is no
    /// way to distinguish how given value with `K1` and `K2` keys should be inserted. For more
    /// information about error kinds look at [`InsertError`] structure and [`ErrorKind`] enum.
    ///
    /// Contains the [`InsertError`] structure.
    Insert(InsertError<K1, K2, V>),
}

impl<'a, K1: Debug, K2: Debug, V: Debug, S, A> Debug for TryInsertError<'a, K1, K2, V, S, A>
where
    A: Allocator + Clone,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match *self {
            TryInsertError::Occupied(ref o) => f.debug_tuple("TryInsertError").field(o).finish(),
            TryInsertError::Insert(ref ins) => f.debug_tuple("TryInsertError").field(ins).finish(),
        }
    }
}

impl<'a, K1: Debug, K2: Debug, V: Debug, S, A> fmt::Display for TryInsertError<'a, K1, K2, V, S, A>
where
    A: Allocator + Clone,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            TryInsertError::Occupied(error) => write!(f, "{}", error),
            TryInsertError::Insert(error) => write!(f, "{}", error),
        }
    }
}
