# Change Log

All notable changes to this project will be documented in this file.

## [v0.5.0] - 2022-04-05

### Added

- **`iter_mut`** `DHashMap` method for creation a mutable iterator visiting all keys-value tuples in arbitrary order.

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