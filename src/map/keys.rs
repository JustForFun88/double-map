use super::*;

/// An iterator over the keys of a `DoubleMap` in arbitrary order.
/// The iterator element type is `(&'a K1, &'a K2)`.
///
/// This `struct` is created by the [`keys`](DoubleMap::keys) method
/// on [`DoubleMap`]. See its documentation for more.
///
/// # Example
///
/// ```
/// use double_map::{DoubleMap, doublemap};
///
/// let map = doublemap!{
///     1, "a" => "One",
///     2, "b" => "Two",
///     3, "c" => "Three",
/// };
///
/// let mut keys = map.keys();
/// let mut vec = vec![keys.next(), keys.next(), keys.next()];
///
/// // The `Keys` iterator produces tuples in arbitrary order, so the
/// // tuples must be sorted to test them against a sorted array.
/// vec.sort_unstable();
/// assert_eq!(vec, [Some((&1, &"a")), Some((&2, &"b")), Some((&3, &"c"))]);
///
/// // It is fused iterator
/// assert_eq!(keys.next(), None);
/// assert_eq!(keys.next(), None);
/// ```
pub struct Keys<'a, K1, K2, V> {
    pub(super) inner: Iter<'a, K1, K2, V>,
}

impl<K1, K2, V> Clone for Keys<'_, K1, K2, V> {
    #[cfg_attr(feature = "inline-more", inline)]
    fn clone(&self) -> Self {
        Keys {
            inner: self.inner.clone(),
        }
    }
}

impl<K1: Debug, K2: Debug, V> fmt::Debug for Keys<'_, K1, K2, V> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_list().entries(self.clone()).finish()
    }
}

impl<'a, K1, K2, V> Iterator for Keys<'a, K1, K2, V> {
    type Item = (&'a K1, &'a K2);

    #[cfg_attr(feature = "inline-more", inline)]
    fn next(&mut self) -> Option<(&'a K1, &'a K2)> {
        // Avoid `Option::map` because it bloats LLVM IR.
        match self.inner.next() {
            Some((k1, k2, _)) => Some((k1, k2)),
            None => None,
        }
    }

    #[cfg_attr(feature = "inline-more", inline)]
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.inner.size_hint()
    }
}

impl<K1, K2, V> ExactSizeIterator for Keys<'_, K1, K2, V> {
    #[cfg_attr(feature = "inline-more", inline)]
    fn len(&self) -> usize {
        self.inner.len()
    }
}

impl<K1, K2, V> FusedIterator for Keys<'_, K1, K2, V> {}
