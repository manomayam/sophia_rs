//! I provide impementations of [`sophia_api::quad::Quad`] based on [`oxrdf::Quad`].

use crate::{
    term::{OxRdfModelError, OxRdfTermVariantError},
    triple::OxTriple,
};
use sophia_api::{
    quad::{Quad, Spog},
    term::{GraphName, Term},
};
use std::fmt::Display;

use crate::term::{OxTerm, OxTermRef};

/// An implementation of [`Quad`] based on [`oxrdf::Quad`].
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct OxQuad(pub(crate) oxrdf::Quad);

impl AsRef<oxrdf::Quad> for OxQuad {
    fn as_ref(&self) -> &oxrdf::Quad {
        &self.0
    }
}

impl From<oxrdf::Quad> for OxQuad {
    fn from(t: oxrdf::Quad) -> Self {
        OxQuad(t)
    }
}

impl Display for OxQuad {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.0.fmt(f)
    }
}

impl<T: Term> TryFrom<Spog<T>> for OxQuad {
    type Error = OxRdfModelError;

    fn try_from(spog: Spog<T>) -> Result<Self, Self::Error> {
        Ok(OxTriple::try_from(spog.0)?
            .in_graph(spog.1.map(|gt| gt.try_into_term()).transpose()?)?)
    }
}

impl Quad for OxQuad {
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

    fn g(&self) -> GraphName<Self::BorrowTerm<'_>> {
        self.0
            .graph_name
            .as_ref()
            .into_option()
            .map(|g| OxTermRef(g))
    }

    fn to_spog(self) -> Spog<Self::Term>
    where
        Self: Sized,
    {
        (
            [
                OxTerm(self.0.subject.into()),
                OxTerm(self.0.predicate.into()),
                OxTerm(self.0.object.into()),
            ],
            self.0.graph_name.into_option().map(|g| OxTerm(g)),
        )
    }
}

impl OxQuad {
    /// Get the reference quad.
    pub fn as_ref(&self) -> OxQuadRef<'_> {
        OxQuadRef(self.0.as_ref())
    }
}

pub(crate) trait OxGraphName {
    type Term;
    fn into_option(self) -> Option<Self::Term>;

    fn try_from_option(g: Option<Self::Term>) -> Result<Self, OxRdfTermVariantError>
    where
        Self: Sized;
}

impl OxGraphName for oxrdf::GraphName {
    type Term = oxrdf::Term;

    fn into_option(self) -> Option<Self::Term> {
        match self {
            oxrdf::GraphName::DefaultGraph => None,
            oxrdf::GraphName::NamedNode(n) => Some(n.into()),
            oxrdf::GraphName::BlankNode(b) => Some(b.into()),
        }
    }

    fn try_from_option(graph_name: Option<Self::Term>) -> Result<Self, OxRdfTermVariantError>
    where
        Self: Sized,
    {
        if let Some(gt) = graph_name {
            match gt {
                oxrdf::Term::NamedNode(n) => Ok(oxrdf::GraphName::NamedNode(n)),
                oxrdf::Term::BlankNode(b) => Ok(oxrdf::GraphName::BlankNode(b)),
                _ => Err(OxRdfTermVariantError {
                    term: OxTerm(gt),
                    target: "GraphName".into(),
                }),
            }
        } else {
            Ok(oxrdf::GraphName::DefaultGraph)
        }
    }
}

impl<'a> OxGraphName for oxrdf::GraphNameRef<'a> {
    type Term = oxrdf::TermRef<'a>;

    fn into_option(self) -> Option<Self::Term> {
        match self {
            oxrdf::GraphNameRef::DefaultGraph => None,
            oxrdf::GraphNameRef::NamedNode(n) => Some(n.into()),
            oxrdf::GraphNameRef::BlankNode(b) => Some(b.into()),
        }
    }

    fn try_from_option(g: Option<Self::Term>) -> Result<Self, OxRdfTermVariantError>
    where
        Self: Sized,
    {
        if let Some(gt) = g {
            match gt {
                oxrdf::TermRef::NamedNode(n) => Ok(oxrdf::GraphNameRef::NamedNode(n)),
                oxrdf::TermRef::BlankNode(b) => Ok(oxrdf::GraphNameRef::BlankNode(b)),
                _ => Err(OxRdfTermVariantError {
                    term: OxTerm(gt.into_owned()),
                    target: "GraphName".into(),
                }),
            }
        } else {
            Ok(oxrdf::GraphNameRef::DefaultGraph)
        }
    }
}

/// An implementation of [`Quad`] based on [`oxrdf::QuadRef`].
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct OxQuadRef<'a>(pub(crate) oxrdf::QuadRef<'a>);

impl<'a> AsRef<oxrdf::QuadRef<'a>> for OxQuadRef<'a> {
    fn as_ref(&self) -> &oxrdf::QuadRef<'a> {
        &self.0
    }
}

impl<'a> From<oxrdf::QuadRef<'a>> for OxQuadRef<'a> {
    fn from(t: oxrdf::QuadRef<'a>) -> Self {
        OxQuadRef(t)
    }
}

impl<'a> Display for OxQuadRef<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.0.fmt(f)
    }
}

impl<'a> Quad for OxQuadRef<'a> {
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

    fn g(&self) -> GraphName<Self::BorrowTerm<'_>> {
        self.0.graph_name.into_option().map(|g| OxTermRef(g))
    }

    fn to_spog(self) -> Spog<Self::Term>
    where
        Self: Sized,
    {
        (
            [
                OxTermRef(self.0.subject.into()),
                OxTermRef(self.0.predicate.into()),
                OxTermRef(self.0.object.into()),
            ],
            self.0.graph_name.into_option().map(|g| OxTermRef(g)),
        )
    }
}

impl<'a> OxQuadRef<'a> {
    /// Convert to an owned quad.
    pub fn into_owned(self) -> OxQuad {
        OxQuad(self.0.into_owned())
    }
}
