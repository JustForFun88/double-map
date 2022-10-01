use super::*;

/// An iterator over the values of a `DoubleMap` in arbitrary order.
/// The iterator element type is `&'a V`.
///
/// This `struct` is created by the [`values`](DoubleMap::values) method
/// on [`DoubleMap`]. See its documentation for more.
///
/// # Example
///
/// ```
/// use double_map::{DoubleMap, doublemap};
///
/// let map = doublemap!{
///     1, "a" => 10,
///     2, "b" => 20,
///     3, "c" => 30,
/// };
///
/// let mut values = map.values();
/// let mut vec = vec![values.next(), values.next(), values.next()];
///
/// // The `Values` iterator produces values in arbitrary order, so the
/// // values must be sorted to test them against a sorted array.
/// vec.sort_unstable();
/// assert_eq!(vec, [Some(&10), Some(&20), Some(&30)]);
///
/// // It is fused iterator
/// assert_eq!(values.next(), None);
/// assert_eq!(values.next(), None);
/// ```
pub struct Values<'a, K1, K2, V> {
    pub(super) inner: Iter<'a, K1, K2, V>,
}

impl<K1, K2, V> Clone for Values<'_, K1, K2, V> {
    #[cfg_attr(feature = "inline-more", inline)]
    fn clone(&self) -> Self {
        Values {
            inner: self.inner.clone(),
        }
    }
}

impl<K1, K2, V: Debug> fmt::Debug for Values<'_, K1, K2, V> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_list().entries(self.clone()).finish()
    }
}

impl<'a, K1, K2, V> Iterator for Values<'a, K1, K2, V> {
    type Item = &'a V;

    #[cfg_attr(feature = "inline-more", inline)]
    fn next(&mut self) -> Option<&'a V> {
        // Avoid `Option::map` because it bloats LLVM IR.
        match self.inner.next() {
            Some((_, _, v)) => Some(v),
            None => None,
        }
    }

    #[cfg_attr(feature = "inline-more", inline)]
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.inner.size_hint()
    }
}

impl<K1, K2, V> ExactSizeIterator for Values<'_, K1, K2, V> {
    #[cfg_attr(feature = "inline-more", inline)]
    fn len(&self) -> usize {
        self.inner.len()
    }
}

impl<K1, K2, V> FusedIterator for Values<'_, K1, K2, V> {}
