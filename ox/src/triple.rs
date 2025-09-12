//! I provide impementations of [`sophia_api::triple::Triple`] based on [`oxrdf::Triple`].

use crate::{
    quad::{OxGraphName as _, OxQuad, OxQuadRef},
    term::{OxRdfModelError, OxRdfTermVariantError},
};
use oxrdf::TryFromTermError;
use sophia_api::{
    term::{GraphName, Term},
    triple::Triple,
};
use std::fmt::Display;

use crate::term::{OxTerm, OxTermRef};

/// An implementation of [`Triple`] based on [`oxrdf::Triple`].
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct OxTriple(pub(crate) oxrdf::Triple);

impl AsRef<oxrdf::Triple> for OxTriple {
    fn as_ref(&self) -> &oxrdf::Triple {
        &self.0
    }
}

impl From<oxrdf::Triple> for OxTriple {
    fn from(t: oxrdf::Triple) -> Self {
        OxTriple(t)
    }
}

impl Display for OxTriple {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.0.fmt(f)
    }
}

impl<T: Term> TryFrom<[T; 3]> for OxTriple {
    type Error = OxRdfModelError;

    fn try_from([s, p, o]: [T; 3]) -> Result<Self, Self::Error> {
        Ok(OxTriple::try_from_terms(
            s.try_into_term::<OxTerm>()?,
            p.try_into_term::<OxTerm>()?,
            o.try_into_term::<OxTerm>()?,
        )
        .map_err(Into::<OxRdfTermVariantError>::into)?)
    }
}

impl Triple for OxTriple {
    type Term = OxTerm;
    type BorrowTerm<'x>
        = OxTermRef<'x>
    where
        Self::Term: 'x,
        Self: 'x;

    fn s(&self) -> OxTermRef<'_> {
        OxTermRef(self.0.subject.as_ref().into())
    }

    fn p(&self) -> OxTermRef<'_> {
        OxTermRef(self.0.predicate.as_ref().into())
    }

    fn o(&self) -> OxTermRef<'_> {
        OxTermRef(self.0.object.as_ref().into())
    }

    fn to_spo(self) -> [Self::Term; 3]
    where
        Self: Sized,
    {
        [
            OxTerm(self.0.subject.into()),
            OxTerm(self.0.predicate.into()),
            OxTerm(self.0.object.into()),
        ]
    }
}

impl OxTriple {
    /// Get the reference triple.
    pub fn as_ref(&self) -> OxTripleRef<'_> {
        OxTripleRef(self.0.as_ref())
    }

    /// Builds an RDF [triple](https://www.w3.org/TR/rdf11-concepts/#dfn-rdf-triple) from [`OxTerm`]s.
    ///
    /// Returns a [`TryFromTermError`] error if the generated triple would be ill-formed.
    pub fn try_from_terms(
        s: impl Into<OxTerm>,
        p: impl Into<OxTerm>,
        o: impl Into<OxTerm>,
    ) -> Result<Self, TryFromTermError> {
        Ok(Self(oxrdf::Triple::from_terms(
            s.into(),
            p.into(),
            o.into(),
        )?))
    }

    /// Encodes that this triple is in an [RDF dataset](https://www.w3.org/TR/rdf11-concepts/#dfn-rdf-dataset).
    ///
    /// Returns error if the graph_name term is Some and not a named node or blank node.
    #[inline]
    pub fn in_graph(self, gn: GraphName<OxTerm>) -> Result<OxQuad, OxRdfTermVariantError> {
        let ogn = oxrdf::GraphName::try_from_option(gn.map(|gt| gt.0))?;

        Ok(OxQuad(self.0.in_graph(ogn)))
    }
}

/// An implementation of [`Triple`] based on [`oxrdf::TripleRef`].
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct OxTripleRef<'a>(pub(crate) oxrdf::TripleRef<'a>);

impl<'a> AsRef<oxrdf::TripleRef<'a>> for OxTripleRef<'a> {
    fn as_ref(&self) -> &oxrdf::TripleRef<'a> {
        &self.0
    }
}

impl<'a> From<oxrdf::TripleRef<'a>> for OxTripleRef<'a> {
    fn from(t: oxrdf::TripleRef<'a>) -> Self {
        OxTripleRef(t)
    }
}

impl<'a> Display for OxTripleRef<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.0.fmt(f)
    }
}

impl<'a> Triple for OxTripleRef<'a> {
    type Term = OxTermRef<'a>;
    type BorrowTerm<'x>
        = OxTermRef<'x>
    where
        Self::Term: 'x,
        Self: 'x;

    fn s(&self) -> OxTermRef<'_> {
        OxTermRef(self.0.subject.into())
    }

    fn p(&self) -> OxTermRef<'_> {
        OxTermRef(self.0.predicate.into())
    }

    fn o(&self) -> OxTermRef<'_> {
        OxTermRef(self.0.object.into())
    }

    fn to_spo(self) -> [Self::Term; 3]
    where
        Self: Sized,
    {
        [
            OxTermRef(self.0.subject.into()),
            OxTermRef(self.0.predicate.into()),
            OxTermRef(self.0.object.into()),
        ]
    }
}

impl<'a> OxTripleRef<'a> {
    /// Convert to an owned triple.
    pub fn into_owned(self) -> OxTriple {
        OxTriple(self.0.into_owned())
    }

    /// Encodes that this triple is in an [RDF dataset](https://www.w3.org/TR/rdf11-concepts/#dfn-rdf-dataset).
    ///
    /// Returns error if the graph_name term is Some and not a named node or blank node.
    #[inline]
    pub fn in_graph(
        self,
        gn: GraphName<OxTermRef<'a>>,
    ) -> Result<OxQuadRef<'a>, OxRdfTermVariantError> {
        let ogn = oxrdf::GraphNameRef::try_from_option(gn.map(|gt| gt.0))?;

        Ok(OxQuadRef(self.0.in_graph(ogn)))
    }
}
