# Change Log

All notable changes to this project will be documented in this file.

## [v0.11.0] - 2022-04-22

### Added

- [`Eq`](https://doc.rust-lang.org/beta/core/cmp/trait.Eq.html) trait implementation for `DHashMap`;
- [`IntoIterator`](https://doc.rust-lang.org/core/iter/trait.IntoIterator.html) trait implementation for `DHashMap`;

### Changed

Nothing

### Removed

Nothing

### Fixed

Nothing

## [v0.10.0] - 2022-04-21

### Added

- **`drain`** `DHashMap` method that clears the map, returning all keys-value tuples
as an arbitrary order iterator;
- **`get_mut_keys`** `DHashMap` method that returns a mutable reference to the value corresponding
to the given primary key `(key #1)` and secondary key `(key #2)` if they both exist and refer to
the same value;
- **`remove_keys`** `DHashMap` method that removes element from the map corresponding to the
given primary key `(key #1)` and secondary key `(key #2)` returning the value at the keys if
the keys was previously in the map and refer to the same value;
- Add some clarifications to `capacity`, `len`, `is_empty` methods documentations.

### Changed

Nothing

### Removed

Nothing

### Fixed

Nothing

## [v0.9.0] - 2022-04-20

### Added

- [`PartialEq`](https://doc.rust-lang.org/core/cmp/trait.PartialEq.html) trait implementation for `DHashMap`;
- [`Debug`](https://doc.rust-lang.org/core/fmt/trait.Debug.html) trait implementation for `DHashMap`;

### Changed

Improve realizations of some methods (`get_key1`, `get_key2`, `get_keys`, `get_key1_value`, `get_key2_value`,
`get_keys_value`, `contains_keys`, `get_mut_key1`, `get_mut_key2`, `remove_key1`, `remove_key2`, `insert_unchecked`)

### Removed

- Removed unnecessary lifetime bounds on implementations of
[`ExactSizeIterator`](https://doc.rust-lang.org/stable/core/iter/trait.ExactSizeIterator.html)
for `Iter`, `Keys`, `Values`, `IterMut`, `ValuesMut` structures;
- Removed `K1: Clone` and `K2: Clone` bounds for all `VacantEntry` methods except `insert` method;
- Removed unnecessary `K1: Eq + Hash` and `K2: Eq + Hash` bounds for all `Entry` methods. Remained
`K1: Clone` and `K2: Clone` bounds only for the methods that need on it.
- Removed unnecessary `K1: Eq + Hash + Clone` and `K2: Eq + Hash + Clone` on implementations of
[`Display`](https://doc.rust-lang.org/core/fmt/trait.Display.html) and
[`Error `](https://doc.rust-lang.org/std/error/trait.Error.html) traits for `OccupiedError` structure.
- Removed unnecessary `K1: Eq + Hash + Clone` and `K2: Eq + Hash + Clone` on implementations of
[`Display`](https://doc.rust-lang.org/core/fmt/trait.Display.html) and
[`Error `](https://doc.rust-lang.org/std/error/trait.Error.html) traits  for `TryInsertError` structure.

### Fixed

Nothing

## [v0.8.0] - 2022-04-13

### Added

- **`get_keys`** `DHashMap` method that returns a reference to the value corresponding to the given primary
key and secondary key if they both exist and refer to the same value;
- **`get_key1_value`** `DHashMap` method that returns a reference to the key-value pair corresponding
to the given primary key: return the tuple of type `(&'a K1, &'a V)`;
- **`get_key2_value`** `DHashMap` method that returns a reference to the key-value pair corresponding
to the given secondary key: return the tuple of type `(&'a K2, &'a V)`;
- **`get_keys_value`** `DHashMap` method that returns a reference to the keys-value tuple corresponding
to the given primary key and secondary key if they both exist and refer to the same value: return
the tuple of type `(&'a K1, &'a K2, &'a V)`;

### Changed

Fixed several typos in previous documentation.

### Removed

Nothign

### Fixed

Nothing

## [v0.7.0] - 2022-04-11

### Added

- **`contains_key1`** `DHashMap` method that returns true if the map contains a value for the specified primary
key;
- **`contains_key2`** `DHashMap` method that returns true if the map contains a value for the specified secondary
key;
- **`contains_keys`** `DHashMap` method that returns true if the map contains a value for the specified primary
key and secondary key and also they both refer to the same value;

### Changed

Nothign

### Removed

Nothign

### Fixed

Nothing

## [v0.6.0] - 2022-04-10

### Added

- **`keys`** `DHashMap` method for creation an iterator visiting all keys in arbitrary order;
- **`values`** `DHashMap` method for creation an iterator visiting all values in arbitrary order;
- **`values_mut`** `DHashMap` method for creation an iterator visiting all values mutably in arbitrary order.

### Changed

Nothign

### Removed

Nothign

### Fixed

Nothing

## [v0.5.0] - 2022-04-05

### Added

- **`iter_mut`** `DHashMap` method for creation an iterator visiting all keys-value tuples in arbitrary
order, with mutable references to the values.

### Changed

Nothign

### Removed

Nothign

### Fixed

Nothing

## [v0.4.1] - 2022-04-04

### Added

Nothing

### Changed

Improved **`iter`** `DHashMap` method documentation.

### Removed

Nothign

### Fixed

Nothing

## [v0.4.0] - 2022-04-04

### Added

- **`iter`** `DHashMap` method for creation an iterator visiting all keys-value tuples in arbitrary order.

### Changed

Nothign

### Removed

Nothign

### Fixed

Nothing

## [v0.3.0] - 2022-04-03

### Added

- [`Default`](https://doc.rust-lang.org/core/default/trait.Default.html) trait implementation for `DHashMap`;
- `dhashmap!` for creation a `DHashMap<K1, K2, V, `[`RandomState`]`>`
from a list of sequentially given keys and values;
- Add documentation for [`Extend`](https://doc.rust-lang.org/core/iter/trait.Extend.html) trait;
- Add documentation for [`FromIterator`](https://doc.rust-lang.org/core/iter/trait.FromIterator.html) trait.

[`RandomState`]: (https://doc.rust-lang.org/std/collections/hash_map/struct.RandomState.html)

### Changed

Nothign

### Removed

Nothign

### Fixed

Nothing

## [v0.2.0] - 2022-04-02

### Added

- [`Extend`](https://doc.rust-lang.org/core/iter/trait.Extend.html) trait implementation for `DHashMap`;
- [`FromIterator`](https://doc.rust-lang.org/core/iter/trait.FromIterator.html) trait implementation for `DHashMap`.

### Changed

- Documentation was improved;
- `DHashMap` was moved to separate module `dhash_map`;
- `TryInsertError::Other` variant changed to the `TryInsertError::Insert` variant.

### Removed

Nothign

### Fixed

- `DHashMap::entry` method (and through this `DHashMap::try_insert`, `DHashMap::insert` methods) realizations
was changed.

### Compatibility

- Because of moving `DHashMap` to the separate module `dhash_map`, `EntryError` structure, `InsertError` structure,
`OccupiedEntry` structure, `OccupiedError` structure, `VacantEntry` structure, `Entry` enum,
`ErrorKind` enum, `TryInsertError` enum can not be used directly from crate root like `use double_map::DHashMap`.
You need change syntax to use submodule, like this `use double_map::dhash_map::EntryError`;
- `TryInsertError::Other` variant changed to the `TryInsertError::Insert` variant.

## [v0.1.1] - 2022-03-29

### Added

[Change log](CHANGELOG.md)

### Changed

[Readme](README.md)

### Removed

Nothign

### Fixed

Nothing


## [v0.1.0] - 2022-03-29

### Added

Initial publication. Created `DHashmap` data structure, and add some methods to it[^1]:
- **`new`:** creates a new empty `DHashMap`;
- **`with_capacity`:** creates an empty `DHashMap` with the specified capacity;
- **`with_hasher`:** creates an empty `DHashMap` which will use the given hash builder to hash keys;
- **`with_capacity_and_hasher`:** creates an empty `DHashMap` with the specified capacity, using
`hash_builder` to hash the keys;
- **`capacity`:** returns the number of elements the map can hold without reallocating;
- **`len`:** returns the number of elements in the map.;
- **`is_empty`:** returns `true` if the map contains no elements;
- **`clear`:** clears the map, removing all keys-value tuples `(K1, K2, V)`. Keeps the allocated memory for reuse;
- **`hasher`:** returns a reference to the map's `BuildHasher`;
- **`reserve`:** reserves capacity for at least `additional` more elements;
- **`try_reserve`:**  tries to reserve capacity for at least `additional` more elements;
- **`shrink_to_fit`:** shrinks the capacity of the map as much as possible;
- **`shrink_to`:** shrinks the capacity of the map with a lower limit;
- **`entry`:** tries to gets the given keys' corresponding entry in the map for in-place manipulation;
return error if primary `K1` key or secondary `K2` ***not*** both vacant or exist and refers to the
same value. Given keys returned inside `error` structure;
- **`get_key1`:** returns a reference to the value corresponding to the given primary key `(K1)`;
- **`get_key2`:** returns a reference to the value corresponding to the given secondary key `(K2)`;
- **`get_mut_key1`:** returns a mutable reference to the value corresponding to the given primary key `(K1)`;
- **`get_mut_key2`:** returns a reference to the value corresponding to the given secondary key `(K2)`;
- **`insert_unchecked`:** insert keys-value tuple `(K1, K2, V)` into the map ***without*** checking
that primary `K1` key or secondary `K2` key vacant or exist in map and refers to the same value;
- **`insert`:** insert keys-value tuple `(K1, K2, V)` into the map `(K1, K2, V)` ***with*** checking
that primary `K1` key or secondary `K2` key vacant or exist in map and refers to the same value;
return error if its failure. Given keys and value returned inside `error` structure;
- **`try_insert`:** tries insert keys-value tuple `(K1, K2, V)` into the map if they vacant and
returning error if any of keys or both keys exist in the map. Given value or value and keys
together returned inside `error` enum (depends error type);
- **`remove_key1`:** remove element from map corresponding to the given primary key `(K1)`;
- **`remove_key2`:** remove element from map corresponding to the given secondary key `(K2)`.
[^1]: The `K1`, `K2`, `V` abbreviations means: `K1` - a primary key of type `K1`; `K2` - a secondary key of type `K2`; `V` - a value of type `K2`.

### Changed

Nothign

### Removed

Nothign

### Fixed

Nothing