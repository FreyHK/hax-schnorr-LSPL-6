//! Formally verified implementation of the Schnorr protocol over elliptic curves.
//! See [theory](theory/index.html) for the properties that this implementation
//! has been verified to satisfy.

pub mod elliptic_curve;
pub mod point;
pub mod schnorr;
pub mod abstract_structures;
#[cfg(test)]
pub mod bigint;
#[cfg(test)]
pub mod standard_curves;
pub mod theory;