use super::*;

/// A draining iterator over the entries of a `DHashMap` in arbitrary order.
/// The iterator element type is `(K1, K2, V)`.
///
/// This `struct` is created by the [`drain`](DHashMap::drain) method
/// on [`DHashMap`]. See its documentation for more.
///
/// # Example
///
/// ```
/// use double_map::{dhashmap, DHashMap};
///
/// let mut map = dhashmap! {
///     1, "a" => "One",
///     2, "b" => "Two",
///     3, "c" => "Three",
/// };
///
/// let mut drain_iter = map.drain();
/// let mut vec = vec![drain_iter.next(), drain_iter.next(), drain_iter.next()];
///
/// // The `Drain` iterator produces tuples in arbitrary order, so the
/// // tuples must be sorted to test them against a sorted array.
/// vec.sort_unstable();
/// assert_eq!(
///     vec,
///     [
///         Some((1, "a", "One")),
///         Some((2, "b", "Two")),
///         Some((3, "c", "Three"))
///     ]
/// );
///
/// // It is fused iterator
/// assert_eq!(drain_iter.next(), None);
/// assert_eq!(drain_iter.next(), None);
/// ```
pub struct Drain<'a, K1, K2, V, A: Allocator + Clone = Global> {
    pub(super) inner: RawDrain<'a, (K1, K2, V), A>,
}

impl<K1, K2, V, A: Allocator + Clone> Drain<'_, K1, K2, V, A> {
    #[cfg_attr(feature = "inline-more", inline)]
    pub(super) fn iter(&self) -> Iter<'_, K1, K2, V> {
        Iter {
            inner: self.inner.iter(),
            marker: PhantomData,
        }
    }
}

impl<'a, K1, K2, V, A: Allocator + Clone> Iterator for Drain<'a, K1, K2, V, A> {
    type Item = (K1, K2, V);

    #[cfg_attr(feature = "inline-more", inline)]
    fn next(&mut self) -> Option<(K1, K2, V)> {
        self.inner.next()
    }

    #[cfg_attr(feature = "inline-more", inline)]
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.inner.size_hint()
    }
}

impl<K1, K2, V, A: Allocator + Clone> ExactSizeIterator for Drain<'_, K1, K2, V, A> {
    #[cfg_attr(feature = "inline-more", inline)]
    fn len(&self) -> usize {
        self.inner.len()
    }
}

impl<K1, K2, V, A: Allocator + Clone> FusedIterator for Drain<'_, K1, K2, V, A> {}

impl<K1: Debug, K2: Debug, V: Debug, A> fmt::Debug for Drain<'_, K1, K2, V, A>
where
    A: Allocator + Clone,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_list().entries(self.iter()).finish()
    }
}
