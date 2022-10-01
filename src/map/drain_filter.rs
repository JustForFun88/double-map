use super::*;

/// A draining iterator over entries of a `DoubleMap` which don't satisfy the predicate
/// `f(&K1, &K2, &mut V)` in arbitrary order. The iterator element type is `(K1, K2, V)`.
///
/// This `struct` is created by the [`drain_filter`] method on [`DoubleMap`]. See its
/// documentation for more.
///
/// [`drain_filter`]: struct.DoubleMap.html#method.drain_filter
/// [`DoubleMap`]: struct.DoubleMap.html
///
/// # Examples
///
/// ```
/// use double_map::DoubleMap;
///
/// let mut map = DoubleMap::<i32, i32, &str>::from([
///     (1, 2, "a"),
///     (2, 5, "b"),
///     (3, 8, "c"),
///     (4, 11, "d"),
///     (5, 14, "e"),
///     (6, 17, "e"),
/// ]);
///
/// let mut drain_filter = map.drain_filter(|k1, k2, _v| k1 % 2 != 0 && k2 % 2 == 0);
/// let mut vec = vec![
///     drain_filter.next(),
///     drain_filter.next(),
///     drain_filter.next(),
/// ];
///
/// // The `DrainFilter` iterator produces items in arbitrary order, so the
/// // items must be sorted to test them against a sorted array.
/// vec.sort_unstable();
/// assert_eq!(
///     vec,
///     [Some((1, 2, "a")), Some((3, 8, "c")), Some((5, 14, "e"))]
/// );
///
/// // It is fused iterator
/// assert_eq!(drain_filter.next(), None);
/// assert_eq!(drain_filter.next(), None);
/// drop(drain_filter);
///
/// assert_eq!(map.len(), 3);
/// ```
pub struct DrainFilter<'a, K1, K2, V, F, A: Allocator + Clone = Global>
where
    F: FnMut(&K1, &K2, &mut V) -> bool,
{
    pub(super) f: F,
    pub(super) inner: DrainFilterInner<'a, K1, K2, V, A>,
}

impl<'a, K1, K2, V, F, A> Drop for DrainFilter<'a, K1, K2, V, F, A>
where
    F: FnMut(&K1, &K2, &mut V) -> bool,
    A: Allocator + Clone,
{
    #[cfg_attr(feature = "inline-more", inline)]
    fn drop(&mut self) {
        while let Some(item) = self.next() {
            let guard = ConsumeAllOnDrop(self);
            drop(item);
            mem::forget(guard);
        }
    }
}

struct ConsumeAllOnDrop<'a, T: Iterator>(pub &'a mut T);

impl<T: Iterator> Drop for ConsumeAllOnDrop<'_, T> {
    #[cfg_attr(feature = "inline-more", inline)]
    fn drop(&mut self) {
        self.0.for_each(drop);
    }
}

impl<K1, K2, V, F, A> Iterator for DrainFilter<'_, K1, K2, V, F, A>
where
    F: FnMut(&K1, &K2, &mut V) -> bool,
    A: Allocator + Clone,
{
    type Item = (K1, K2, V);

    #[cfg_attr(feature = "inline-more", inline)]
    fn next(&mut self) -> Option<Self::Item> {
        self.inner.next(&mut self.f)
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        (0, self.inner.iter.size_hint().1)
    }
}

impl<K1, K2, V, F> FusedIterator for DrainFilter<'_, K1, K2, V, F> where
    F: FnMut(&K1, &K2, &mut V) -> bool
{
}

pub(super) struct DrainFilterInner<'a, K1, K2, V, A: Allocator + Clone> {
    pub iter: RawPointerIter<(K1, K2, V)>,
    pub table: &'a mut RawTable<(K1, K2, V), A>,
}

impl<K1, K2, V, A: Allocator + Clone> DrainFilterInner<'_, K1, K2, V, A> {
    #[cfg_attr(feature = "inline-more", inline)]
    pub(super) fn next<F>(&mut self, f: &mut F) -> Option<(K1, K2, V)>
    where
        F: FnMut(&K1, &K2, &mut V) -> bool,
    {
        unsafe {
            for item in &mut self.iter {
                let &mut (ref key1, ref key2, ref mut value) = item.as_data_mut();
                if f(key1, key2, value) {
                    return Some(self.table.remove(item));
                }
            }
        }
        None
    }
}
