use super::*;
use core::ops::AddAssign;

#[cfg(miri)]
const N: u64 = 32;
#[cfg(not(miri))]
const N: u64 = 128;

fn create_arr<T: AddAssign<T> + Copy, const N: usize>(start: T, step: T, skip: usize) -> [T; N] {
    let mut outs: [T; N] = [start; N];
    let mut element = step;
    for v in outs.iter_mut().skip(skip + 1) {
        *v += element;
        element += step;
    }
    outs
}

fn rehash_in_place<T, F1, F2>(table: &mut RawTable<T>, hasher_1: F1, hasher_2: F2)
where
    F1: Fn(&T) -> u64,
    F2: Fn(&T) -> u64,
{
    unsafe {
        table.table.rehash_in_place::<T>(
            &|table, index| hasher_1(table.data_bucket::<T>(index).as_ref()),
            &|table, index| hasher_2(table.pointer_bucket::<T>(index).as_data_ref()),
            mem::size_of::<T>(),
            if mem::needs_drop::<T>() {
                Some(mem::transmute(ptr::drop_in_place::<T> as unsafe fn(*mut T)))
            } else {
                None
            },
        );
    }
}

#[test]
fn map_drop() {
    let mut table = RawTable::new();
    let hasher_1 = |i: &u8| *i as u64;
    let hasher_2 = |i: &u8| *i as u64;
    for i in 0_u64..N as u64 {
        table.insert(i, i, i as u8, hasher_1, hasher_2);
    }
    drop(table);
}

#[test]
fn map_rehash() {
    let mut table = RawTable::new();
    let hasher_1 = |i: &u64| *i;
    let hasher_2 = |i: &u64| *i;
    for i in 0_u64..N {
        table.insert(i, i, i, hasher_1, hasher_2);
    }

    for i in 0_64..N {
        unsafe {
            assert_eq!(table.find_h1(i, |x| *x == i).map(|b| b.read()), Some(i));
        }
        unsafe {
            assert_eq!(
                table.find_h2(i, |x| *x == i).map(|b| b.read_data()),
                Some(i)
            );
        }

        unsafe {
            assert_eq!(
                table
                    .find(i, |x| *x == i, i, |x| *x == i)
                    .map(|(b1, b2)| (b1.read(), b2.read_data())),
                Some((i, i))
            );
        }
        assert!(table.find_h1(i + 100, |x| *x == i + 100).is_none());
        assert!(table.find_h2(i + 100, |x| *x == i + 100).is_none());

        assert!(table
            .find(i, |x| *x == i, i + 100, |x| *x == i + 100)
            .is_none());
        assert!(table
            .find(i + 100, |x| *x == i + 100, i, |x| *x == i)
            .is_none());
        assert!(table
            .find(i + 100, |x| *x == i + 100, i + 100, |x| *x == i + 100)
            .is_none());
    }

    rehash_in_place(&mut table, hasher_1, hasher_2);

    for i in 0_64..N {
        unsafe {
            assert_eq!(table.find_h1(i, |x| *x == i).map(|b| b.read()), Some(i));
        }
        unsafe {
            assert_eq!(
                table.find_h2(i, |x| *x == i).map(|b| b.read_data()),
                Some(i)
            );
        }

        unsafe {
            assert_eq!(
                table
                    .find(i, |x| *x == i, i, |x| *x == i)
                    .map(|(b1, b2)| (b1.read(), b2.read_data())),
                Some((i, i))
            );
        }
        assert!(table.find_h1(i + 100, |x| *x == i + 100).is_none());
        assert!(table.find_h2(i + 100, |x| *x == i + 100).is_none());

        assert!(table
            .find(i, |x| *x == i, i + 100, |x| *x == i + 100)
            .is_none());
        assert!(table
            .find(i + 100, |x| *x == i + 100, i, |x| *x == i)
            .is_none());
        assert!(table
            .find(i + 100, |x| *x == i + 100, i + 100, |x| *x == i + 100)
            .is_none());
    }
}

#[test]
fn map_clone() {
    let mut table = RawTable::new();
    let hasher_1 = |i: &u64| *i;
    let hasher_2 = |i: &u64| *i;
    for i in 0_u64..N {
        table.insert(i, i, i, hasher_1, hasher_2);
    }

    let table_two = table.clone();

    // and we can use table_two
    for i in 0_64..N {
        unsafe {
            assert_eq!(table_two.find_h1(i, |x| *x == i).map(|b| b.read()), Some(i));
        }
        unsafe {
            assert_eq!(
                table_two.find_h2(i, |x| *x == i).map(|b| b.read_data()),
                Some(i)
            );
        }

        unsafe {
            assert_eq!(
                table_two
                    .find(i, |x| *x == i, i, |x| *x == i)
                    .map(|(b1, b2)| (b1.read(), b2.read_data())),
                Some((i, i))
            );
        }
        assert!(table_two.find_h1(i + 100, |x| *x == i + 100).is_none());
        assert!(table_two.find_h2(i + 100, |x| *x == i + 100).is_none());

        assert!(table_two
            .find(i, |x| *x == i, i + 100, |x| *x == i + 100)
            .is_none());
        assert!(table_two
            .find(i + 100, |x| *x == i + 100, i, |x| *x == i)
            .is_none());
        assert!(table_two
            .find(i + 100, |x| *x == i + 100, i + 100, |x| *x == i + 100)
            .is_none());
    }
}

#[test]
fn map_data_iter() {
    let mut table = RawTable::new();
    const SIZE: usize = N as usize + 5;
    let hasher_1 = |i: &u64| *i;
    let hasher_2 = |i: &u64| *i;
    for i in 0_u64..N {
        table.insert(i, i, i, hasher_1, hasher_2);
    }

    // creating a little bit larger array
    let mut arr = [0_u64; SIZE];

    for (arr_item, map_item) in arr.iter_mut().zip(unsafe { table.iter() }) {
        *arr_item = unsafe { map_item.read() };
    }

    arr.sort_unstable();
    // arr must equal to [0, 0, 0, 0, 0, 0, 1, 2, ..., 98, 99]
    assert_eq!(arr, create_arr::<u64, SIZE>(0, 1, 5));

    rehash_in_place(&mut table, hasher_1, hasher_2);

    // creating a little bit larger array
    let mut arr = [0_u64; SIZE];

    for (arr_item, map_item) in arr.iter_mut().zip(unsafe { table.iter() }) {
        *arr_item = unsafe { map_item.read() };
    }

    arr.sort_unstable();
    // arr must equal to [0, 0, 0, 0, 0, 0, 1, 2, ..., 98, 99]
    assert_eq!(arr, create_arr::<u64, SIZE>(0, 1, 5));

    let mut table_two = table.clone();
    drop(table);

    // creating a little bit larger array
    let mut arr = [0_u64; SIZE];

    for (arr_item, map_item) in arr.iter_mut().zip(unsafe { table_two.iter() }) {
        *arr_item = unsafe { map_item.read() };
    }

    arr.sort_unstable();
    // arr must equal to [0, 0, 0, 0, 0, 0, 1, 2, ..., 98, 99]
    assert_eq!(arr, create_arr::<u64, SIZE>(0, 1, 5));

    rehash_in_place(&mut table_two, hasher_1, hasher_2);

    // creating a little bit larger array
    let mut arr = [0_u64; SIZE];

    for (arr_item, map_item) in arr.iter_mut().zip(unsafe { table_two.iter() }) {
        *arr_item = unsafe { map_item.read() };
    }

    arr.sort_unstable();
    // arr must equal to [0, 0, 0, 0, 0, 0, 1, 2, ..., 98, 99]
    assert_eq!(arr, create_arr::<u64, SIZE>(0, 1, 5));
}

#[test]
fn map_pointer_iter() {
    let mut table = RawTable::new();
    const SIZE: usize = N as usize + 5;
    let hasher_1 = |i: &u64| *i;
    let hasher_2 = |i: &u64| *i;
    for i in 0_u64..N {
        table.insert(i, i, i, hasher_1, hasher_2);
    }

    // creating a little bit larger array
    let mut arr = [0_u64; SIZE];

    for (arr_item, map_item) in arr.iter_mut().zip(unsafe { table.pointers_iter() }) {
        *arr_item = unsafe { map_item.read_data() };
    }

    arr.sort_unstable();
    // arr must equal to [0, 0, 0, 0, 0, 0, 1, 2, ..., 98, 99]
    assert_eq!(arr, create_arr::<u64, SIZE>(0, 1, 5));

    rehash_in_place(&mut table, hasher_1, hasher_2);

    // creating a little bit larger array
    let mut arr = [0_u64; SIZE];

    for (arr_item, map_item) in arr.iter_mut().zip(unsafe { table.pointers_iter() }) {
        *arr_item = unsafe { map_item.read_data() };
    }

    arr.sort_unstable();
    // arr must equal to [0, 0, 0, 0, 0, 0, 1, 2, ..., 98, 99]
    assert_eq!(arr, create_arr::<u64, SIZE>(0, 1, 5));

    let mut table_two = table.clone();
    drop(table);

    // creating a little bit larger array
    let mut arr = [0_u64; SIZE];

    for (arr_item, map_item) in arr.iter_mut().zip(unsafe { table_two.pointers_iter() }) {
        *arr_item = unsafe { map_item.read_data() };
    }

    arr.sort_unstable();
    // arr must equal to [0, 0, 0, 0, 0, 0, 1, 2, ..., 98, 99]
    assert_eq!(arr, create_arr::<u64, SIZE>(0, 1, 5));

    rehash_in_place(&mut table_two, hasher_1, hasher_2);

    // creating a little bit larger array
    let mut arr = [0_u64; SIZE];

    for (arr_item, map_item) in arr.iter_mut().zip(unsafe { table_two.pointers_iter() }) {
        *arr_item = unsafe { map_item.read_data() };
    }

    arr.sort_unstable();
    // arr must equal to [0, 0, 0, 0, 0, 0, 1, 2, ..., 98, 99]
    assert_eq!(arr, create_arr::<u64, SIZE>(0, 1, 5));
}

#[test]
fn map_drain() {
    let mut table = RawTable::new();
    const SIZE: usize = N as usize + 5;
    let hasher_1 = |i: &u64| *i;
    let hasher_2 = |i: &u64| *i;
    for i in 0_u64..N {
        table.insert(i, i, i, hasher_1, hasher_2);
    }

    let buckets_before_drain = table.buckets();

    // creating a little bit larger array
    let mut arr = [0_u64; SIZE];
    let mut table_two = table.clone();

    for (arr_item, map_item) in arr.iter_mut().zip(table.drain()) {
        *arr_item = map_item;
    }

    arr.sort_unstable();
    assert_eq!(arr, create_arr::<u64, SIZE>(0, 1, 5));

    assert_eq!(table.buckets(), buckets_before_drain);
    assert_eq!(table.len(), 0);
    assert!(table.is_empty());
    drop(table);

    // creating a little bit larger array
    let mut arr = [0_u64; SIZE];

    for (arr_item, map_item) in arr.iter_mut().zip(table_two.drain()) {
        *arr_item = map_item;
    }

    arr.sort_unstable();
    assert_eq!(arr, create_arr::<u64, SIZE>(0, 1, 5));
}

#[test]
#[should_panic = "panic in clear"]
fn map_clear_double_drop() {
    struct CheckedDrop {
        panic_in_clear: bool,
        dropped: bool,
        index: u64,
    }

    impl Drop for CheckedDrop {
        fn drop(&mut self) {
            if self.panic_in_clear {
                self.dropped = true;
                panic!("panic in clear");
            }
            if self.dropped {
                panic!("double drop");
            }
            self.dropped = true;
        }
    }

    let mut table = RawTable::new();
    let hasher_1 = |i: &CheckedDrop| i.index;
    let hasher_2 = |i: &CheckedDrop| i.index;

    for i in 0_u64..10 {
        let value = if i < 5 {
            CheckedDrop {
                panic_in_clear: false,
                dropped: false,
                index: i,
            }
        } else {
            CheckedDrop {
                panic_in_clear: true,
                dropped: false,
                index: i,
            }
        };
        table.insert(i, i, value, hasher_1, hasher_2);
    }

    assert_eq!(table.len(), 10);

    for i in 0_u64..10 {
        assert!(table.find_h1(i, |x| x.index == i).is_some());
    }
    table.clear();
}

#[test]
#[should_panic = "panic in first hash"]
fn map_panic_in_h1_rehash() {
    struct CheckedDrop {
        dropped: bool,
        index: u64,
    }

    impl Drop for CheckedDrop {
        fn drop(&mut self) {
            if self.dropped {
                panic!("double drop");
            }
            self.dropped = true;
        }
    }

    let mut table = RawTable::new();
    let hasher_1 = |i: &CheckedDrop| i.index;
    let hasher_2 = |i: &CheckedDrop| i.index;

    for i in 0_u64..10 {
        let value = CheckedDrop {
            dropped: false,
            index: i,
        };
        table.insert(i, i, value, hasher_1, hasher_2);
    }

    assert_eq!(table.len(), 10);

    for i in 0_u64..10 {
        assert!(table.find_h1(i, |x| x.index == i).is_some());
    }

    // garbage hash function
    let hasher_1 = |_i: &CheckedDrop| panic!("panic in first hash");
    rehash_in_place(&mut table, hasher_1, hasher_2);
}

#[test]
#[should_panic = "panic in second hash"]
fn map_panic_in_h2_rehash() {
    struct CheckedDrop {
        dropped: bool,
        index: u64,
    }

    impl Drop for CheckedDrop {
        fn drop(&mut self) {
            if self.dropped {
                panic!("double drop");
            }
            self.dropped = true;
        }
    }

    let mut table = RawTable::new();
    let hasher_1 = |i: &CheckedDrop| i.index;
    let hasher_2 = |i: &CheckedDrop| i.index;

    for i in 0_u64..10 {
        let value = CheckedDrop {
            dropped: false,
            index: i,
        };
        table.insert(i, i, value, hasher_1, hasher_2);
    }

    assert_eq!(table.len(), 10);

    for i in 0_u64..10 {
        assert!(table.find_h1(i, |x| x.index == i).is_some());
    }

    // garbage hash function
    let hasher_2 = |_i: &CheckedDrop| panic!("panic in second hash");
    rehash_in_place(&mut table, hasher_1, hasher_2);
}

#[test]
#[should_panic = "panic in clone"]
fn map_clone_double_drop() {
    struct CheckedClone {
        panic_in_clone: bool,
        dropped: bool,
    }

    impl Drop for CheckedClone {
        fn drop(&mut self) {
            if self.dropped {
                panic!("double drop");
            }
            self.dropped = true;
        }
    }

    impl Clone for CheckedClone {
        fn clone(&self) -> Self {
            if self.panic_in_clone {
                panic!("panic in clone");
            } else {
                Self {
                    panic_in_clone: self.panic_in_clone,
                    dropped: self.dropped,
                }
            }
        }
    }

    const DISARMED: CheckedClone = CheckedClone {
        panic_in_clone: false,
        dropped: false,
    };
    const ARMED: CheckedClone = CheckedClone {
        panic_in_clone: true,
        dropped: false,
    };

    // We just allocate the required amount of memory, since our garbage hash function is good for nothing.
    let mut table = RawTable::with_capacity(3);
    // garbage hash function
    let hasher_1 = |_i: &CheckedClone| 0;
    // yet another one
    let hasher_2 = |_i: &CheckedClone| 0;
    // Just insert 3 element because if we insert 4 there will be additional allocation
    table.insert(1, 1, DISARMED, hasher_1, hasher_2);
    table.insert(2, 2, DISARMED, hasher_1, hasher_2);
    table.insert(3, 3, ARMED, hasher_1, hasher_2);

    assert_eq!(table.len(), 3);

    let _table_two = table.clone();
}

#[test]
#[should_panic = "panic in clone_from"]
fn map_clone_from_double_drop() {
    #[derive(Clone)]
    struct CheckedDrop {
        panic_in_drop: bool,
        dropped: bool,
    }
    impl Drop for CheckedDrop {
        fn drop(&mut self) {
            if self.panic_in_drop {
                self.dropped = true;
                panic!("panic in clone_from");
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

    // We just allocate the required amount of memory, since our garbage hash function is good for nothing.
    let mut table = RawTable::with_capacity(3);
    // garbage hash function
    let hasher_1 = |_i: &CheckedDrop| 0;
    // yet another one
    let hasher_2 = |_i: &CheckedDrop| 0;
    // Just insert 3 element because if we insert 4 there will be additional allocation
    table.insert(1, 1, DISARMED, hasher_1, hasher_2);
    table.insert(2, 2, DISARMED, hasher_1, hasher_2);
    table.insert(3, 3, DISARMED, hasher_1, hasher_2);

    assert_eq!(table.len(), 3);

    // We just allocate the required amount of memory, since our garbage hash function is good for nothing.
    let mut table_two = RawTable::with_capacity(3);
    // garbage hash function
    let hasher_1 = |_i: &CheckedDrop| 0;
    // yet another one
    let hasher_2 = |_i: &CheckedDrop| 0;
    // Just insert 3 element because if we insert 4 there will be additional allocation
    table_two.insert(1, 1, DISARMED, hasher_1, hasher_2);
    table_two.insert(2, 2, DISARMED, hasher_1, hasher_2);
    table_two.insert(3, 3, ARMED, hasher_1, hasher_2);

    assert_eq!(table_two.len(), 3);

    table_two.clone_from(&table);
}
