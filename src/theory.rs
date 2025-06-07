//! Specifies the the properties of elliptic curves and the Schnorr
//! protocol, that this implementation has been formally verified to satisfy.

#[allow(unused_imports)]
use crate::point::Point;
#[allow(unused_imports)]
use crate::elliptic_curve::EllipticCurve;
#[allow(unused_imports)]
use crate::abstract_structures::{Scalar, Field};
#[allow(unused_imports)]
use crate::schnorr::{gen_key, commitment, challenge, respond, verify};


/// Curve Group Property: Additions is closed under the curve
#[hax_lib::lemma]
pub fn ec_add_closed <F: Field, S : Scalar> (
    curve: EllipticCurve<F, S>,
    p : &Point<F>,
    q : &Point<F>,
) -> Proof<{ 
    hax_lib::implies(curve.is_on_curve(p) && curve.is_on_curve(q),
    || curve.is_on_curve(&curve.add(p, q)))
}> {}

/// Curve Group Property: Negation is closed under the curve
#[hax_lib::lemma]
fn ec_neg_closed <F: Field, S : Scalar> (
    curve: EllipticCurve<F, S>,
    p : &Point<F>,
) -> Proof<{ 
    hax_lib::implies(curve.is_on_curve(p),
    || curve.is_on_curve(&curve.neg(p)))
 }> {}


/// Curve Group Property: Scalar multiplication is closed under the curve
#[hax_lib::lemma]
fn ec_mul_closed <F: Field, S : Scalar> (
    curve: EllipticCurve<F, S>,
    p : &Point<F>,
    x: S,
) -> Proof<{ 
    hax_lib::implies(curve.is_on_curve(p),
    || curve.is_on_curve(&curve.mul(p, &x)))
 }> {}


/// Curve Group Property: Addition with identity element
#[hax_lib::lemma]
fn ec_add_inf_r <F: Field, S : Scalar> (
    curve: EllipticCurve<F, S>,
    p : Point<F>,
) -> Proof<{ 
    curve.add(&p, &Point::Infinity) == p
 }> {}

/// Curve Group Property: Addition with negative element
#[hax_lib::lemma]
fn ec_add_neg_r <F: Field, S : Scalar> (
    curve: EllipticCurve<F, S>,
    p : &Point<F>,
) -> Proof<{ 
    hax_lib::implies(curve.is_on_curve(p),
    || curve.add(p, &curve.neg(p)) == Point::Infinity)
 }> {}

/// Curve Group Property: Coommutativity of addition
#[hax_lib::lemma]
fn ec_add_comm <F: Field, S : Scalar> (
    curve: EllipticCurve<F, S>,
    p : &Point<F>,
    q : &Point<F>,
) -> Proof<{ 
    hax_lib::implies(curve.is_on_curve(p) && curve.is_on_curve(q),
    || curve.add(&p, &q) == curve.add(&q, &p)) 
 }> {}

/// Curve Group Property: Associativity of addition
#[hax_lib::lemma]
fn ec_add_assoc <F: Field, S : Scalar> (
    curve: EllipticCurve<F, S>,
    p : &Point<F>,
    q : &Point<F>,
    r : &Point<F>,
) -> Proof<{ 
    hax_lib::implies(curve.is_on_curve(p) && curve.is_on_curve(q) && curve.is_on_curve(r),
    || curve.add(&curve.add(&p, &q), &r) == curve.add(&p, &curve.add(&q, &r)))
 }> {}

/// Curve Group Property: Distributivity of scalar multiplication over addition
#[hax_lib::lemma]
fn ec_mul_distr <F: Field, S:Scalar> (
    curve: EllipticCurve<F, S>,
    x: S,
    y: S,
) -> Proof<{ 
    curve.mul(curve.generator(), &S::add(&x, &y)) == curve.add(&curve.mul(curve.generator(), &x), &curve.mul(curve.generator(), &y))
 }> {}

/// Curve Group Property: Distributivity of scalar multiplication
#[hax_lib::lemma]
fn ec_mul_mul <F: Field, S : Scalar> (
    curve: EllipticCurve<F, S>,
    x: S,
    y: S,
) -> Proof<{ 
    curve.mul(curve.generator(), &S::mul(&x, &y)) == curve.mul(&curve.mul(curve.generator(), &x), &y)
 }> {}


/// Strengthened Completeness of the Schnorr Protocol
/// The verifer will accept the proof if and only if the prover responds correctly
#[hax_lib::lemma]
fn schnorr_strengthened_completeness <F: Field, S : Scalar> (
    curve: EllipticCurve<F, S>,
    a: S,
    v: S,
    c: S,
    r: S,
) -> Proof<{ 
    let A = gen_key(&curve, &a);
    let V = commitment(&curve, &v);
    let c = challenge(&curve, &c);
    hax_lib::implies(a != S::zero(), ||
        hax_lib::implies(r == respond(&v, &a, &c), || verify(&curve, &V, &r, &A, &c))
        && hax_lib::implies(verify(&curve, &V, &r, &A, &c), || r == respond(&v, &a, &c))
    )
}> {}


/// Helper lemma for proof of Soundness of the Schnorr Protocol
/// Prover not knowing the secret key can only convince the verifier 
/// with negligible probability
/// 
/// This is a helper lemma that proves that if the verififer
/// can produce two valid responses for two different challenges,
/// then the prover must know the secret key.
#[hax_lib::lemma]
fn schnorr_soundness_aux <F: Field, S : Scalar> (
    curve: EllipticCurve<F, S>,
    a: S,
    v: S,
    r1: S,
    r2: S,
    c1: S,
    c2: S,
) -> Proof<{ 
    let A = gen_key(&curve, &a);
    let V = commitment(&curve, &v);
    let c1 = challenge(&curve, &c1);
    let c2 = challenge(&curve, &c2);
    hax_lib::implies(
        verify(&curve, &V, &r1, &A, &c1) 
        && verify(&curve, &V, &r2, &A, &c2)
        && c1 != c2, 
        || a == S::div(
            &S::sub(&r1, &r2),
            &S::sub(&c2, &c1)
        )
    )
 }> {}