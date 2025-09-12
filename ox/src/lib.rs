//! This crate is part of [Sophia],
//! an [RDF] and [Linked Data] toolkit in Rust.
//!
//! It provides sophia adapters for the [Oxrdf](https://crates.io/crates/oxrdf) crate.
//!
//! [Sophia]: https://docs.rs/sophia/latest/sophia/
//! [RDF]: https://www.w3.org/TR/rdf-primer/
//! [Linked Data]: http://linkeddata.org/
#![deny(missing_docs)]

pub mod dataset;
pub mod graph;
pub mod quad;
pub mod source;
pub mod term;
pub mod triple;

pub use oxrdf::TryFromTermError;
