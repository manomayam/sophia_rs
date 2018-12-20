// this module is transparently re-exported by its parent `graph`

use std::collections::HashMap;
use std::iter::empty;

use super::*;
use ::graph::index::remove_one_val;

/// A [`GraphWrapper`](trait.GraphWrapper.html)
/// indexing triples by subject, then by predicate, then by object.
/// 
/// Compared to its wrapped graph,
/// it overrides the methods that can efficiently be implemented using this index.
/// 
#[derive(Default)]
pub struct SpoWrapper<T> where
    T: IndexedMutableGraph,
{
    wrapped: T,
    s2p: HashMap<T::Index, Vec<T::Index>>,
    sp2o: HashMap<(T::Index, T::Index), Vec<T::Index>>,
}

impl<T> SpoWrapper<T> where
    T: IndexedMutableGraph + Default,
    T::Index: Default,
{
    pub fn new() -> Self {
        Self::default()
    }
}

impl<T> GraphWrapper for SpoWrapper<T> where
    T: IndexedMutableGraph,
{
    type Wrapped = T;

    fn get_wrapped(&self) -> &T {
        &self.wrapped
    }

    fn get_wrapped_mut(&mut self) -> &mut T {
        &mut self.wrapped
    }

    fn gw_iter_for_s<'a, U> (&'a self, s: &'a Term<U>) -> GFallibleTripleIterator<'a, Self::Wrapped>
    where
        U: Borrow<str>,
    {
        if let Some(si) = self.wrapped.get_index(s) {
            if let Some(pis) = self.s2p.get(&si) {
                let s = self.wrapped.get_term(si).unwrap();
                return Box::new(
                    pis.iter()
                    .map(move |pi| (
                        s,
                        self.wrapped.get_term(*pi).unwrap(),
                        self.sp2o.get(&(si, *pi)).unwrap(),
                    ))
                    .flat_map(move |(s,p,ois)|
                        ois.iter()
                        .map(move |oi| Ok((
                            s, p, self.wrapped.get_term(*oi).unwrap(),
                        )))
                    )
                )
            }
        }
        Box::new(empty())
    }

    fn gw_iter_for_sp<'a, U, V> (&'a self, s: &'a Term<U>, p: &'a Term<V>) -> GFallibleTripleIterator<'a, Self::Wrapped>
    where
        U: Borrow<str>,
        V: Borrow<str>,
    {
        if let Some(si) = self.wrapped.get_index(s) {
            if let Some(pi) = self.wrapped.get_index(p) {
                if let Some(ois) = self.sp2o.get(&(si, pi)) {
                    let s = self.wrapped.get_term(si).unwrap();
                    let p = self.wrapped.get_term(pi).unwrap();
                    return Box::new(
                        ois.iter()
                        .map(move |oi| Ok((
                            s, p, self.wrapped.get_term(*oi).unwrap(),
                        )))
                    )
                }
            }
        }
        Box::new(empty())
    }

    fn gw_hint_for_s<U> (&self, s: &Term<U>) -> (usize, Option<usize>) where
        U: Borrow<str>,
    {
        match self.get_index(s) {
            None => (0, Some(0)),
            Some(si) => {
                let (_, max) = self.wrapped.hint();
                let min = self.s2p.get(&si).unwrap().len();
                (min, max)
            }
        }
    }

    fn gw_hint_for_sp<U, V> (&self, s: &Term<U>, p: &Term<V>) -> (usize, Option<usize>) where
        U: Borrow<str>,
        V: Borrow<str>,
    {
        if let Some(si) = self.get_index(s) {
            if let Some(pi) = self.get_index(p) {
                let nb = self.sp2o.get(&(si, pi)).unwrap().len();
                return (nb, Some(nb));
            }
        }
        (0, Some(0))
    }
}

impl<T> Graph for SpoWrapper<T> where
    T: IndexedMutableGraph,
{
    impl_graph_for_wrapper!();
}

impl<T> IndexedMutableGraph for SpoWrapper<T> where
    T: IndexedMutableGraph,
{
    type Index = T::Index;

    #[inline]
    fn get_index<U> (&self, t: &Term<U>) -> Option<Self::Index> where
        U: Borrow<str>,
    {
        self.wrapped.get_index(t)
    }

    #[inline]
    fn get_term(&self, i: Self::Index) -> Option<&Term<Self::Holder>>
    {
        self.wrapped.get_term(i)
    }

    fn insert_indexed<U, V, W> (&mut self, s: &Term<U>, p: &Term<V>, o: &Term<W>) -> Option<(Self::Index, Self::Index, Self::Index)> where
        U: Borrow<str>,
        V: Borrow<str>,
        W: Borrow<str>,
    {
        let modified = self.wrapped.insert_indexed(s, p, o);
        if let Some((si, pi, oi)) = modified {
            self.s2p.entry(si).or_insert_with(|| Vec::new()).push(pi);
            self.sp2o.entry((si, pi)).or_insert_with(|| Vec::new()).push(oi);
        }
        modified
    }

    fn remove_indexed<U, V, W> (&mut self, s: &Term<U>, p: &Term<V>, o: &Term<W>) -> Option<(Self::Index, Self::Index, Self::Index)> where
        U: Borrow<str>,
        V: Borrow<str>,
        W: Borrow<str>,
    {
        let modified = self.wrapped.remove_indexed(s, p, o);
        if let Some((si, pi, oi)) = modified {    
            remove_one_val(&mut self.s2p, si, pi);
            remove_one_val(&mut self.sp2o, (si, pi), oi);
        }
        modified
    }

    fn shrink_to_fit(&mut self) {
        self.wrapped.shrink_to_fit();
        self.s2p.shrink_to_fit();
        self.sp2o.shrink_to_fit();
    }
}

impl<T> MutableGraph for SpoWrapper<T> where
    T: IndexedMutableGraph,
{
    impl_mutable_graph_for_indexed_mutable_graph!();
}

impl<T> SetGraph for SpoWrapper<T> where
    T: IndexedMutableGraph + SetGraph,
{}



#[cfg(test)]
type SpoGraph = SpoWrapper<LightGraph>;
#[cfg(test)]
test_graph_impl!(SpoGraph);
