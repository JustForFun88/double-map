use super::*;

/// An owning iterator over the values of a `DHashMap` in arbitrary order.
/// The iterator element type is `V`.
///
/// This `struct` is created by the [`into_values`] method on [`DHashMap`].
/// See its documentation for more. The map cannot be used after calling that method.
///
/// [`into_values`]: struct.DHashMap.html#method.into_values
/// [`DHashMap`]: struct.DHashMap.html
///
/// # Examples
///
/// ```
/// use double_map::{dhashmap, DHashMap};
///
/// let map = dhashmap! {
///     1, "one" => "a",
///     2, "two" => "b",
///     3, "three" => "c",
/// };
///
/// let mut values = map.into_values();
/// let mut vec = vec![values.next(), values.next(), values.next()];
///
/// // The `IntoValues` iterator produces tuples in arbitrary order, so the
/// // tuples must be sorted to test them against a sorted array.
/// vec.sort_unstable();
/// assert_eq!(vec, [Some("a"), Some("b"), Some("c")]);
///
/// // It is fused iterator
/// assert_eq!(values.next(), None);
/// assert_eq!(values.next(), None);
/// ```
pub struct IntoValues<K1, K2, V, A: Allocator + Clone = Global> {
    pub(super) inner: IntoIter<K1, K2, V, A>,
}

impl<K1, K2, V, A: Allocator + Clone> Iterator for IntoValues<K1, K2, V, A> {
    type Item = V;

    #[inline]
    fn next(&mut self) -> Option<V> {
        match self.inner.next() {
            Some((_, _, v)) => Some(v),
            None => None,
        }
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.inner.size_hint()
    }
}

impl<K1, K2, V, A: Allocator + Clone> ExactSizeIterator for IntoValues<K1, K2, V, A> {
    #[inline]
    fn len(&self) -> usize {
        self.inner.len()
    }
}

impl<K1, K2, V, A: Allocator + Clone> FusedIterator for IntoValues<K1, K2, V, A> {}

impl<K1, K2, V: Debug, A: Allocator + Clone> fmt::Debug for IntoValues<K1, K2, V, A> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_list()
            .entries(self.inner.iter().map(|(_, _, v)| v))
            .finish()
    }
}
