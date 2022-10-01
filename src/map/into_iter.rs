use super::*;

/// An owning iterator over the entries of a `DoubleMap` in arbitrary order.
/// The iterator element type is `(K1, K2, V)`.
///
/// This `struct` is created by the [`into_iter`] method on [`DoubleMap`]
/// (provided by the [`IntoIterator`] trait). See its documentation for more.
/// The map cannot be used after calling that method.
///
/// [`into_iter`]: struct.DoubleMap.html#method.into_iter
/// [`DoubleMap`]: struct.DoubleMap.html
/// [`IntoIterator`]: https://doc.rust-lang.org/core/iter/trait.IntoIterator.html
///
/// # Example
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
/// let mut iter = map.into_iter();
/// let mut vec = vec![iter.next(), iter.next(), iter.next()];
///
/// // The `IntoIter` iterator produces tuples in arbitrary order, so the
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
/// assert_eq!(iter.next(), None);
/// assert_eq!(iter.next(), None);
/// ```
pub struct IntoIter<K1, K2, V, A: Allocator + Clone = Global> {
    pub(super) inner: RawIntoDataIter<(K1, K2, V), A>,
}

impl<K1, K2, V, A: Allocator + Clone> IntoIter<K1, K2, V, A> {
    #[cfg_attr(feature = "inline-more", inline)]
    pub(super) fn iter(&self) -> Iter<'_, K1, K2, V> {
        Iter {
            inner: self.inner.iter(),
            marker: PhantomData,
        }
    }
}

impl<K1, K2, V, A: Allocator + Clone> Iterator for IntoIter<K1, K2, V, A> {
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

impl<K1, K2, V, A: Allocator + Clone> ExactSizeIterator for IntoIter<K1, K2, V, A> {
    #[cfg_attr(feature = "inline-more", inline)]
    fn len(&self) -> usize {
        self.inner.len()
    }
}
impl<K1, K2, V, A: Allocator + Clone> FusedIterator for IntoIter<K1, K2, V, A> {}

impl<K1: Debug, K2: Debug, V: Debug, A> fmt::Debug for IntoIter<K1, K2, V, A>
where
    A: Allocator + Clone,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_list().entries(self.iter()).finish()
    }
}
