use super::*;

/// An owning iterator over the keys of a `DoubleMap` in arbitrary order.
/// The iterator element type is `(K1, K2)`.
///
/// This `struct` is created by the [`into_keys`] method on [`DoubleMap`].
/// See its documentation for more.
/// The map cannot be used after calling that method.
///
/// [`into_keys`]: struct.DoubleMap.html#method.into_keys
/// [`DoubleMap`]: struct.DoubleMap.html
///
/// # Examples
///
/// ```
/// use double_map::{doublemap, DoubleMap};
///
/// let map = doublemap! {
///     1, "a" => "One",
///     2, "b" => "Two",
///     3, "c" => "Three",
/// };
///
/// let mut keys = map.into_keys();
/// let mut vec = vec![keys.next(), keys.next(), keys.next()];
///
/// // The `IntoKeys` iterator produces tuples in arbitrary order, so the
/// // tuples must be sorted to test them against a sorted array.
/// vec.sort_unstable();
/// assert_eq!(vec, [Some((1, "a")), Some((2, "b")), Some((3, "c"))]);
///
/// // It is fused iterator
/// assert_eq!(keys.next(), None);
/// assert_eq!(keys.next(), None);
/// ```
pub struct IntoKeys<K1, K2, V, A: Allocator + Clone = Global> {
    pub(super) inner: IntoIter<K1, K2, V, A>,
}

impl<K1, K2, V, A: Allocator + Clone> Iterator for IntoKeys<K1, K2, V, A> {
    type Item = (K1, K2);

    #[inline]
    fn next(&mut self) -> Option<(K1, K2)> {
        match self.inner.next() {
            Some((k1, k2, _)) => Some((k1, k2)),
            None => None,
        }
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.inner.size_hint()
    }
}

impl<K1, K2, V, A: Allocator + Clone> ExactSizeIterator for IntoKeys<K1, K2, V, A> {
    #[inline]
    fn len(&self) -> usize {
        self.inner.len()
    }
}

impl<K1, K2, V, A: Allocator + Clone> FusedIterator for IntoKeys<K1, K2, V, A> {}

impl<K1: Debug, K2: Debug, V, A: Allocator + Clone> fmt::Debug for IntoKeys<K1, K2, V, A> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_list()
            .entries(self.inner.iter().map(|(k1, k2, _)| (k1, k2)))
            .finish()
    }
}
