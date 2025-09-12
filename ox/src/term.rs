//! I provide impementations of [`sophia_api::term::Term`] based on [`oxrdf::Term`].
//!

use sophia_api::{
    MownStr,
    term::{BaseDirection, BnodeId, IriRef, LanguageTag, Term, TermKind, TryFromTerm, VarName},
    triple::Triple,
};
use std::{borrow::Borrow, fmt::Display};

use crate::{
    TryFromTermError,
    triple::{OxTriple, OxTripleRef},
};

/// An RDF term based on `oxrdf::Term`.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct OxTerm(pub(crate) oxrdf::Term);

impl AsRef<oxrdf::Term> for OxTerm {
    fn as_ref(&self) -> &oxrdf::Term {
        &self.0
    }
}

impl From<oxrdf::Term> for OxTerm {
    fn from(t: oxrdf::Term) -> Self {
        OxTerm(t)
    }
}

impl From<OxTerm> for oxrdf::Term {
    fn from(t: OxTerm) -> Self {
        t.0
    }
}

impl Display for OxTerm {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.0.fmt(f)
    }
}

impl Term for OxTerm {
    type BorrowTerm<'x>
        = OxTermRef<'x>
    where
        Self: 'x;

    fn kind(&self) -> TermKind {
        match &self.0 {
            oxrdf::Term::NamedNode(_) => TermKind::Iri,
            oxrdf::Term::BlankNode(_) => TermKind::BlankNode,
            oxrdf::Term::Literal(_) => TermKind::Literal,
            oxrdf::Term::Triple(_) => TermKind::Triple,
        }
    }

    fn borrow_term(&self) -> Self::BorrowTerm<'_> {
        OxTermRef(self.0.as_ref())
    }

    fn iri(&self) -> Option<IriRef<MownStr<'_>>> {
        if let oxrdf::Term::NamedNode(n) = &self.0 {
            Some(IriRef::new_unchecked(n.as_str().into()))
        } else {
            None
        }
    }

    fn bnode_id(&self) -> Option<BnodeId<MownStr<'_>>> {
        if let oxrdf::Term::BlankNode(b) = &self.0 {
            // oxrdf blank node representation confirms to turtle blank node grammer.
            Some(BnodeId::new_unchecked(b.as_str().into()))
        } else {
            None
        }
    }

    fn lexical_form(&self) -> Option<MownStr<'_>> {
        if let oxrdf::Term::Literal(l) = &self.0 {
            Some(l.value().into())
        } else {
            None
        }
    }

    fn datatype(&self) -> Option<IriRef<MownStr<'_>>> {
        if let oxrdf::Term::Literal(l) = &self.0 {
            Some(IriRef::new_unchecked(l.datatype().as_str().into()))
        } else {
            None
        }
    }

    fn language_tag(&self) -> Option<LanguageTag<MownStr<'_>>> {
        if let oxrdf::Term::Literal(l) = &self.0 {
            l.language()
                .map(|tag| LanguageTag::new_unchecked(tag.into()))
        } else {
            None
        }
    }

    fn base_direction(&self) -> Option<BaseDirection> {
        None // oxrdf::Term does not support base direction
    }

    fn variable(&self) -> Option<VarName<MownStr<'_>>> {
        // oxrdf::Term currently doesn't has support for variable varient.
        None
    }

    fn triple(&self) -> Option<[Self::BorrowTerm<'_>; 3]> {
        if let oxrdf::Term::Triple(t) = &self.0 {
            Some(OxTripleRef(t.as_ref().as_ref()).to_spo())
        } else {
            None
        }
    }
    fn to_triple(self) -> Option<[Self; 3]> {
        if let oxrdf::Term::Triple(t) = self.0 {
            Some(OxTriple(*t).to_spo())
        } else {
            None
        }
    }
}

// Conversion from iri terms
impl<S: Borrow<str>> From<IriRef<S>> for OxTerm {
    fn from(iri: IriRef<S>) -> Self {
        OxTerm(oxrdf::NamedNode::new_unchecked(iri.as_str()).into())
    }
}

// Conversion from blank node terms
impl<S: Borrow<str>> From<BnodeId<S>> for OxTerm {
    fn from(bnode_id: BnodeId<S>) -> Self {
        OxTerm(oxrdf::BlankNode::new_unchecked(bnode_id.as_str()).into())
    }
}

// Conversion from typed literal terms
impl<S: Borrow<str>> From<(String, IriRef<S>)> for OxTerm {
    fn from((lv, dt): (String, IriRef<S>)) -> Self {
        let datatype = oxrdf::NamedNode::new_unchecked(dt.as_str());
        OxTerm(oxrdf::Literal::new_typed_literal(lv, datatype).into())
    }
}

// Conversion from language tagged literal terms
impl<S: Borrow<str>> From<(String, LanguageTag<S>)> for OxTerm {
    fn from((lv, lt): (String, LanguageTag<S>)) -> Self {
        // oxrdf expects the language tag to be in lowercase.
        let lt = lt.as_str().to_lowercase();
        OxTerm(oxrdf::Literal::new_language_tagged_literal_unchecked(lv, lt).into())
    }
}

// Conversion from triple terms
impl<T: Term> TryFrom<[T; 3]> for OxTerm {
    type Error = OxRdfModelError;

    fn try_from(triple: [T; 3]) -> Result<Self, Self::Error> {
        let ox_triple: OxTriple = triple.try_into()?;
        Ok(OxTerm(Box::new(ox_triple.0).into()))
    }
}

impl TryFromTerm for OxTerm {
    type Error = OxRdfModelError;

    fn try_from_term<T: Term>(term: T) -> Result<Self, Self::Error> {
        // Case of namednode
        if let Some(iri) = term.iri() {
            Ok(iri.into())
        }
        // Case of blank node
        else if let Some(bnode_id) = term.bnode_id() {
            Ok(bnode_id.into())
        }
        // Case of literarl
        else if let Some(lv) = term.lexical_form() {
            // case of language tagged literal
            if let Some(lt) = term.language_tag() {
                // Note that in this case also term.datatype() returns Some(rdf::langString)
                Ok((lv.into(), lt).into())
            }
            // case of typed literal
            else if let Some(dt) = term.datatype() {
                Ok((lv.into(), dt).into())
            }
            // case of simple literal
            else {
                Ok(OxTerm(oxrdf::Literal::new_simple_literal(lv).into()))
            }
        }
        // Case of quoted triple
        else if let Some(triple) = term.to_triple() {
            triple.try_into()
        }
        // Case of variable. OxTerm doesn't represent variables
        else {
            Err(OxRdfModelError::NotStrictRdfTerm)
        }
    }
}

/// Error type for oxterm model error
#[derive(Debug, Clone, thiserror::Error)]
pub enum OxRdfModelError {
    /// Given term is not a strict rdf term
    #[error("Given term is not a strict rdf term")]
    NotStrictRdfTerm,

    /// Given term is not a valid triple term
    #[error("Given term is not a valid triple term: {0}")]
    InvalidTripleTerm(#[from] TryFromTermError),
}

/// A reference to an RDF term based on `oxrdf::TermRef`.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub struct OxTermRef<'a>(pub oxrdf::TermRef<'a>);

impl OxTerm {
    /// Get the reference term.
    pub fn as_ref(&self) -> OxTermRef<'_> {
        OxTermRef(self.0.as_ref())
    }
}

impl<'a> AsRef<oxrdf::TermRef<'a>> for OxTermRef<'a> {
    fn as_ref(&self) -> &oxrdf::TermRef<'a> {
        &self.0
    }
}

impl<'a> From<oxrdf::TermRef<'a>> for OxTermRef<'a> {
    fn from(t: oxrdf::TermRef<'a>) -> Self {
        OxTermRef(t)
    }
}

impl<'a> From<OxTermRef<'a>> for oxrdf::TermRef<'a> {
    fn from(t: OxTermRef<'a>) -> Self {
        t.0
    }
}

impl<'a> Display for OxTermRef<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.0.fmt(f)
    }
}

impl<'a> Term for OxTermRef<'a> {
    type BorrowTerm<'x>
        = Self
    where
        Self: 'x;
    fn kind(&self) -> TermKind {
        match self.0 {
            oxrdf::TermRef::NamedNode(_) => TermKind::Iri,
            oxrdf::TermRef::BlankNode(_) => TermKind::BlankNode,
            oxrdf::TermRef::Literal(_) => TermKind::Literal,
            oxrdf::TermRef::Triple(_) => TermKind::Triple,
        }
    }
    fn borrow_term(&self) -> Self {
        *self
    }
    fn iri(&self) -> Option<IriRef<MownStr<'_>>> {
        if let oxrdf::TermRef::NamedNode(n) = self.0 {
            Some(IriRef::new_unchecked(n.as_str().into()))
        } else {
            None
        }
    }
    fn bnode_id(&self) -> Option<BnodeId<MownStr<'_>>> {
        if let oxrdf::TermRef::BlankNode(b) = self.0 {
            Some(BnodeId::new_unchecked(b.as_str().into()))
        } else {
            None
        }
    }
    fn lexical_form(&self) -> Option<MownStr<'_>> {
        if let oxrdf::TermRef::Literal(l) = self.0 {
            Some(l.value().into())
        } else {
            None
        }
    }
    fn datatype(&self) -> Option<IriRef<MownStr<'_>>> {
        if let oxrdf::TermRef::Literal(l) = self.0 {
            Some(IriRef::new_unchecked(l.datatype().as_str().into()))
        } else {
            None
        }
    }
    fn language_tag(&self) -> Option<LanguageTag<MownStr<'_>>> {
        if let oxrdf::TermRef::Literal(l) = self.0 {
            l.language()
                .map(|tag| LanguageTag::new_unchecked(tag.into()))
        } else {
            None
        }
    }
    fn base_direction(&self) -> Option<BaseDirection> {
        None
    }
    fn variable(&self) -> Option<VarName<MownStr<'_>>> {
        None
    }
    fn triple(&self) -> Option<[Self; 3]> {
        if let oxrdf::TermRef::Triple(t) = self.0 {
            Some(OxTripleRef(t.as_ref()).to_spo())
        } else {
            None
        }
    }
    fn to_triple(self) -> Option<[Self; 3]> {
        self.triple()
    }
}

impl<'a> OxTermRef<'a> {
    /// Convert to an owned term.
    pub fn into_owned(self) -> OxTerm {
        OxTerm(self.0.into_owned())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use sophia_api::{
        ns::{rdf, xsd},
        term::{SimpleTerm, assert_consistent_term_impl},
    };

    #[test]
    fn ox_term_iri() {
        let ot: OxTerm = rdf::type_.try_into_term().expect("Must be valid");
        assert_consistent_term_impl(&ot);
        assert_eq!(ot.kind(), TermKind::Iri);
        assert!(Term::eq(&ot.iri().unwrap(), rdf::type_));
    }

    #[test]
    fn ox_term_bnode() {
        let bn = BnodeId::new_unchecked("x");
        let ot: OxTerm = bn.into();
        assert_consistent_term_impl(&ot);
        assert_eq!(ot.kind(), TermKind::BlankNode);
        assert_eq!(&ot.bnode_id().unwrap(), "x");
    }

    #[test]
    fn ox_term_typed_literal() {
        let ot: OxTerm = 42.try_into_term().expect("Must be valid");
        assert_consistent_term_impl(&ot);
        assert_eq!(ot.kind(), TermKind::Literal);
        assert_eq!(ot.lexical_form().unwrap(), "42");
        assert!(Term::eq(&ot.datatype().unwrap(), xsd::integer));
    }

    #[test]
    fn ox_term_language_string() {
        let en = LanguageTag::new_unchecked("en");
        let ot: OxTerm = ("hello" * en).try_into_term().expect("Must be valid");
        assert_consistent_term_impl(&ot);
        assert_eq!(ot.kind(), TermKind::Literal);
        assert_eq!(ot.lexical_form().unwrap(), "hello");
        assert!(Term::eq(&ot.datatype().unwrap(), rdf::langString));
        assert_eq!(ot.language_tag().unwrap(), en);
    }

    #[test]
    fn ox_term_triple() {
        let spo = [rdf::type_, rdf::type_, rdf::Property].map(Term::into_term);
        let qt = SimpleTerm::Triple(Box::new(spo));
        let ot: OxTerm = qt.try_into_term().expect("Must be valid");
        assert_consistent_term_impl(&ot);
        assert_eq!(ot.kind(), TermKind::Triple);
        let spo = ot.triple().unwrap();
        assert!(Term::eq(&spo[0], rdf::type_));
        assert!(Term::eq(&spo[1], rdf::type_));
        assert!(Term::eq(&spo[2], rdf::Property));

        let spo2: [SimpleTerm; 3] = [
            rdf::type_.into_term(),
            42.into_term(),
            rdf::Property.into_term(),
        ];
        let qt = SimpleTerm::Triple(Box::new(spo2.clone()));
        assert!(
            qt.try_into_term::<OxTerm>().is_err(),
            "String literal must not be allowed as predicate"
        );
    }

    #[test]
    fn ox_term_variable() {
        let v = VarName::new_unchecked("x");
        assert!(
            v.try_into_term::<OxTerm>().is_err(),
            "Variables are not representable by oxterm"
        );
    }
}
