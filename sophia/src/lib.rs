//! This meta-crate aims to provide a comprehensive toolkit
//! for working with [RDF] and [Linked Data] in Rust.
//!
//! It provides a unified access to a number of smaller crates,
//! that make the Sophia toolkit:
//!
//! * [`api`]
//! * [`c14n`]
//! * [`inmem`]
//! * [`iri`]
//! * [`isomorphism`]
//! * [`jsonld`]
//! * [`resource`]
//! * [`turtle`]
//! * [`term`]
//! * [`xml`] (with the `xml` feature enabled)
//!
//! # Getting Started
//!
//! See the [Sophia book](https://pchampin.github.io/sophia_rs/ch01_getting_started.html)
//!
//!
//! [RDF]: https://www.w3.org/TR/rdf-primer/
//! [Linked Data]: http://linkeddata.org/

pub use sophia_api as api;
pub use sophia_c14n as c14n;
pub use sophia_inmem as inmem;
pub use sophia_iri as iri;
pub use sophia_isomorphism as isomorphism;
#[cfg(feature = "jsonld")]
pub use sophia_jsonld as jsonld;
pub use sophia_resource as resource;
pub use sophia_term as term;
pub use sophia_turtle as turtle;
#[cfg(feature = "xml")]
pub use sophia_xml as xml;

/// Including tests from all code snippets in the book
/// from https://github.com/rust-lang/mdBook/issues/706#issuecomment-1085137304
#[cfg(doctest)]
mod booktest {
    macro_rules! booktest {
        ($i:ident) => {
            #[doc = include_str!(concat!("../../book/src/", stringify!($i), ".md"))]
            mod $i {}
        };
    }
    booktest!(ch01_getting_started);
    booktest!(ch02_rdf_terms);
    booktest!(ch90_changes_since_07);
}
