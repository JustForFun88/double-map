use super::*;

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
