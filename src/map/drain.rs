use super::*;

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
