use super::*;

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
