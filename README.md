Double Map
==========

[![Crates.io](https://img.shields.io/crates/v/double-map.svg)](https://crates.io/crates/double-map)
[![Documentation](https://img.shields.io/docsrs/double-map/latest)](https://docs.rs/double-map)
[![Rust](https://img.shields.io/badge/rust-1.56.1%2B-blue.svg?maxAge=3600)](https://github.com/JustForFun88/double-map)

Like a [HashMap], but allows you to use two different keys to the same value/data.

Sometimes during development, it may be necessary to have a data structure like
a `HashMap` but with two different keys referring to the same data.

For example, if you have some data with a unique ID and a name, then you create
a structure that contains the name, and store it in a ***normal*** `HashMap` using
the unique ID as the key. However, finding the element throughout the name will be
performed with O(n) time. The same is true for the reverse case.

This crate tries to resolve this contradiction by providing a DHashMap structure -
a map where you can add, look up and remove elements using either the first key
of type `K1` or the second key of type `K2`.

Internally, it uses two maps: the first is of type `HashMap<K1, (K2, V)>` and
the second is of type `HashMap<K2, K1>`. Using two `HashMap`'s inside instead
one brings to the performance and memory penalty.

It is recommended to use the first key of type `K1` of quick access to the data,
because indexing by the second key of type `K2` requires two `HashMap` lookups.

## [Change log](CHANGELOG.md)

## Current Status

Double Map is in active development. The design goal is implementing the whole [HashMap]
interface. Look at [Change log](CHANGELOG.md) for more information. 

### Methods

- [x] `new`: Done sinse `v0.1.0` 
- [x] `with_capacity`: Done sinse `v0.1.0` 
- [x] `with_hasher`: Done sinse `v0.1.0` 
- [x] `with_capacity_and_hasher`: Done sinse `v0.1.0` 
- [x] `capacity`: Done sinse `v0.1.0` 
- [ ] `keys`: Under development 
- [ ] `into_keys`: Under development 
- [ ] `values`: Under development 
- [ ] `values_mut`: Under development 
- [ ] `into_values`: Under development 
- [ ] `iter Under`: development 
- [ ] `iter_mut`: Under development 
- [x] `len`: Done sinse `v0.1.0` 
- [x] `is_empty`: Done sinse `v0.1.0` 
- [ ] `drain`: Under development 
- [ ] `drain_filter`: Under development 
- [ ] `retain`: Under development 
- [x] `clear`: Done sinse `v0.1.0` 
- [x] `hasher`: Done sinse `v0.1.0` 
- [x] `reserve`: Done sinse `v0.1.0` 
- [x] `try_reserve`: Done sinse `v0.1.0` 
- [x] `shrink_to_fit`: Done sinse `v0.1.0` 
- [x] `shrink_to`: Done sinse `v0.1.0` 
- [x] `entry`: Done sinse `v0.1.0` 
- [x] `get`: Done sinse `v0.1.0` (`get_key1` and `get_key2` methods) 
- [ ] `get_key_value`: Under development 
- [ ] `contains_key`: Under development 
- [x] `get_mut`: Done sinse `v0.1.0` (`get_mut_key1` and `get_mut_key2` methods) 
- [x] `insert`: Done sinse `v0.1.0` (`insert_unchecked` and `insert` methods) 
- [x] `try_insert`: Done sinse `v0.1.0` 
- [x] `remove`: Done sinse `v0.1.0` (`remove_key1` and `remove_key2` methods) 
- [ ] `remove_entry`: Under development 
- [ ] `raw_entry_mut`: Under development 
- [ ] `raw_entry`: Under development 
 
### Trait Implementations
- [ ] `Clone`: Under development
- [ ] `Debug`: Under development
- [ ] `Default`: Under development
- [ ] `Extend`: Under development
- [ ] `From`: Under development
- [ ] `FromIterator`: Under development
- [ ] `Index`: Under development
- [ ] `IntoIterator`: Under development
- [ ] `PartialEq`: Under development

## License

Licensed under Apache License, Version 2.0, ([LICENSE](LICENSE) or https://www.apache.org/licenses/LICENSE-2.0)
at your option.

### Contribution

Unless you explicitly state otherwise, any contribution intentionally submitted
for inclusion in the work by you, as defined in the Apache-2.0 license, shall be licensed as above, without any
additional terms or conditions.

[HashMap]: https://doc.rust-lang.org/std/collections/struct.HashMap.html