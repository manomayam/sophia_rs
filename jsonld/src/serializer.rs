//! A JSON-LD serializer implementing the
//! [`Serialize RDF as JSON-LD Algorithm`].
//!
//! [`Serialize RDF as JSON-LD Algorithm`]: https://www.w3.org/TR/json-ld11-api/#serialize-rdf-as-json-ld-algorithm

use crate::error::*;
use crate::loader::NoLoader;
use crate::options::*;
use json_syntax::print::Indent;
use json_syntax::print::{Options, Print};
use json_syntax::Value as JsonValue;
use sophia_api::serializer::*;
use sophia_api::source::{QuadSource, SinkError, StreamResult};

mod engine;
mod rdf_object;
#[cfg(test)]
mod test;

/// A JSON-LD serializer.
///
/// ## Developers
///
/// * the generic parameter `W` is the output type of the serializer (typically a [`std::io::Write`])
/// * the generic parameter `L` is the type of the [document loader](`json_ld::Loader`)
pub struct JsonLdSerializer<'lf, W, L = NoLoader> {
    options: JsonLdOptions<'lf, L>,
    target: W,
}

impl<'lf, W> JsonLdSerializer<'lf, W> {
    /// Build a new JSON-LD serializer with the default options (no document loader).
    #[inline]
    pub fn new(target: W) -> Self {
        Self::new_with_options(target, JsonLdOptions::default())
    }
}

impl<'lf, W, L> JsonLdSerializer<'lf, W, L> {
    /// Build a new JSON-LD serializer writing to `write`, with the given options.
    pub fn new_with_options(target: W, options: JsonLdOptions<'lf, L>) -> Self {
        JsonLdSerializer { target, options }
    }

    /// Borrow this serializer's options.
    pub fn options(&self) -> &JsonLdOptions<L> {
        &self.options
    }

    /// Convert a quad stream into a Json object
    fn convert_quads<QS>(
        &mut self,
        source: QS,
    ) -> StreamResult<JsonValue<()>, QS::Error, JsonLdError>
    where
        QS: QuadSource,
    {
        let mut engine = engine::Engine::new_with_options(&self.options);
        engine.process_quads(source)?;
        engine.into_json().map_err(SinkError)
    }
}

impl<'lf, W, L> QuadSerializer for JsonLdSerializer<'lf, W, L>
where
    W: std::io::Write,
{
    type Error = JsonLdError;

    fn serialize_quads<QS>(&mut self, source: QS) -> StreamResult<&mut Self, QS::Error, Self::Error>
    where
        QS: QuadSource,
    {
        let result = self.convert_quads(source)?;
        // TODO if the options contains a context,
        // try to compact 'result' before serializing.
        //
        // For this,
        // - first convert result into an ExpandedDocument
        //   using the TryFromJson trait
        // - then extract the context from the options
        // - compact the ExpandeDocument using this context
        let json_txt = match self.options.spaces() {
            0 => result.compact_print().to_string(),
            x => {
                let mut options = Options::pretty();
                options.indent = Indent::Spaces(x as u8);
                result.print_with(options).to_string()
            }
        };
        self.target
            .write(json_txt.as_bytes())
            .map_err(|e| SinkError(e.into()))?;
        Ok(self)
    }
}

/// A utility type alias of [`JsonLdSerializer`] with `[JsonTarget]` as its target.
///
/// ## Developers
///
/// * the generic parameter `L` is the type of the [document loader](`json_ld::Loader`)
///   (determined by the `options` parameters)
pub type Jsonifier<'lf, L = NoLoader> = JsonLdSerializer<'lf, JsonTarget, L>;

/// This type is just a placeholder [`JsonLdSerializer`]
/// targetting a [`JsonValue`].
/// See [`new_jsonifier`] and [`new_jsonifier_with`].
///
/// [`new_jsonifier`]: struct.JsonLdSerializer.html#method.new_jsonifier
/// [`new_jsonifier_with`]: struct.JsonLdSerializer.html#method.new_jsonifier_with
#[derive(Clone, Debug)]
pub struct JsonTarget(JsonValue<()>);

impl<'lf> Jsonifier<'lf> {
    /// Create a new serializer which targets a [`JsonValue`].
    #[inline]
    pub fn new_jsonifier() -> Self {
        JsonLdSerializer::new(JsonTarget(JsonValue::Null))
    }
}

impl<'lf, L> Jsonifier<'lf, L> {
    /// Create a new serializer which targets a [`JsonValue`] with a custom options.
    #[inline]
    pub fn new_jsonifier_with_options(options: JsonLdOptions<'lf, L>) -> Self {
        JsonLdSerializer::new_with_options(JsonTarget(JsonValue::Null), options)
    }

    /// Get a reference to the converted JsonValue
    #[inline]
    pub fn as_json(&self) -> &JsonValue<()> {
        &self.target.0
    }

    /// Extract the converted JsonValue
    #[inline]
    pub fn to_json(&mut self) -> JsonValue<()> {
        let mut ret = JsonValue::Null;
        std::mem::swap(&mut self.target.0, &mut ret);
        ret
    }
}

impl<'lf, L> QuadSerializer for Jsonifier<'lf, L> {
    type Error = JsonLdError;

    fn serialize_quads<QS>(&mut self, source: QS) -> StreamResult<&mut Self, QS::Error, Self::Error>
    where
        QS: QuadSource,
    {
        self.target.0 = self.convert_quads(source)?;
        Ok(self)
    }
}

/// A utility type alias representing a [`JsonLdSerializer`] which targets a string.
///
/// ## Developers
///
/// * the generic parameter `L` is the type of the [document loader](`json_ld::Loader`)
///   (determined by the `options` parameters)
pub type JsonLdStringifier<'lf, L = NoLoader> = JsonLdSerializer<'lf, Vec<u8>, L>;

impl<'lf> JsonLdStringifier<'lf, NoLoader> {
    /// Create a new serializer which targets a string.
    #[inline]
    pub fn new_stringifier() -> Self {
        JsonLdSerializer::new(Vec::new())
    }
}

impl<'lf, L> JsonLdStringifier<'lf, L> {
    /// Create a new serializer which targets a string with a custom options.
    #[inline]
    pub fn new_stringifier_with_options(options: JsonLdOptions<'lf, L>) -> Self {
        JsonLdSerializer::new_with_options(Vec::new(), options)
    }
}

impl<'lf, L> Stringifier for JsonLdStringifier<'lf, L> {
    fn as_utf8(&self) -> &[u8] {
        &self.target[..]
    }
}
