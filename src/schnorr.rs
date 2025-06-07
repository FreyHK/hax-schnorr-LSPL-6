//! Implementation of the Schnorr Identification Scheme over elliptic curves.


use crate::abstract_structures::{Field, Scalar};
use crate::elliptic_curve::{EllipticCurve};
use crate::point::Point;

/// In the setup of the scheme, Alice publishes her public key
/// `A = G x [a]`, where `a` is the private key chosen uniformly at random
/// from `[1, n-1]`.
#[allow(non_snake_case)]
pub fn gen_key <F: Field, S: Scalar> (curve: &EllipticCurve<F, S>, a: &S) -> Point<F> {
    let G = curve.generator();
    let A = curve.mul(G, a);
    A
}

/// Alice chooses `a` number `v` uniformly at random from `[1, n-1]` and
/// computes `V = G x [v]`.  She sends V to Bob.
#[allow(non_snake_case)]
pub fn commitment <F: Field, S : Scalar> (curve: &EllipticCurve<F, S>, v: &S) -> Point<F> {
    let G = curve.generator();
    let V = curve.mul(G, v);
    V
}

/// Bob chooses a challenge `c` uniformly at random from `[0, 2^t-1]`,
/// where `t` is the bit length of the challenge (say, `t = 80`).  Bob
/// sends `c` to Alice.
#[allow(unused)]
pub fn challenge <F: Field, S: Scalar> (curve: &EllipticCurve<F, S>, c: &S) -> S {
    c.clone()
}

/// Alice computes `r = v - a * c mod n` and sends it to Bob.
pub fn respond<S: Scalar>(v: &S, a: &S, c: &S) -> S {
    let r = S::sub(v, &S::mul(a, c));
    r
}

/// Verify `A` is a valid point on the curve and `A x [h]` is not the
/// point at infinity. To verify `V = G x [r] + A x [c]`.
#[allow(non_snake_case)]
pub fn verify <F: Field, S: Scalar> (curve: &EllipticCurve<F, S>, V: &Point<F>, r: &S, A: &Point<F>, c: &S) -> bool {
    curve.is_on_curve(A) 
    && curve.mul(A, curve.h()) != Point::Infinity 
    && V == &curve.add(&curve.mul(curve.generator(), &r), &curve.mul(A, &c))
}

#[cfg(test)]
mod tests {

    use super::*;

    use quickcheck::quickcheck;
    use quickcheck::TestResult;

    use crate::standard_curves::{create_secp192r1_curve, create_secp256k1_curve, create_brainpoolP160r1};
    use crate::standard_curves::{SSecp192r1, SSecp256k1, SP160r1};

    quickcheck! {
        #[allow(non_snake_case)]
        fn prop_verify_Secp192r1(sk: SSecp192r1, v: SSecp192r1, c: SSecp192r1) -> TestResult {
            if sk == SSecp192r1::zero() || v == SSecp192r1::zero() || c == SSecp192r1::zero() {
                return TestResult::discard();
            }
            let curve = create_secp192r1_curve();
            let pk = gen_key(&curve, &sk);
            let V = commitment(&curve, &v);
            let r = respond(&v, &sk, &c);
            TestResult::from_bool(verify(&curve, &V, &r, &pk, &c))
        }

        #[allow(non_snake_case)]
        fn prop_verify_Secp256k1 (sk: SSecp256k1, v: SSecp256k1, c: SSecp256k1) -> TestResult {
            if sk == SSecp256k1::zero() || v == SSecp256k1::zero() || c == SSecp256k1::zero() {
                return TestResult::discard();
            }
            let curve = create_secp256k1_curve();
            let pk = gen_key(&curve, &sk);
            let V = commitment(&curve, &v);
            let r = respond(&v, &sk, &c);
            TestResult::from_bool(verify(&curve, &V, &r, &pk, &c))
        }

        #[allow(non_snake_case)]
        fn prop_verify_brainpoolP160r1 (sk: SP160r1, v: SP160r1, c: SP160r1) -> TestResult {
            // Ignore zero values (not allowed)
            if sk == SP160r1::zero() || v == SP160r1::zero() || c == SP160r1::zero() {
                return TestResult::discard();
            }
            let curve = create_brainpoolP160r1();
            let pk = gen_key(&curve, &sk);
            let V = commitment(&curve, &v);
            let r = respond(&v, &sk, &c);
            TestResult::from_bool(verify(&curve, &V, &r, &pk, &c))
        }
    }

    #[test]
    #[allow(non_snake_case)]
    fn test_alice_bob_secp192r1() {
        let curve = create_secp192r1_curve();
        let sk = SSecp192r1::from_hex("0xffffffffffffffffffffffff99def836146bc9b1b4d22830");
        let pk = gen_key(&curve, &sk); // public key
        let v = SSecp192r1::from_hex("0xfffffffffffffffffffffff91b4d29d619bef83246bc830");
        let V = commitment(&curve, &v);
        let c = challenge(&curve, &SSecp192r1::from_hex("0x19999999999999C03200"));
        let r = respond(&v, &sk, &c);
        assert!(verify(&curve, &V, &r, &pk, &c));
    }

    #[test]
    #[allow(non_snake_case)]
    fn test_wrong_commitment () {
        let curve = create_secp192r1_curve();

        let sk = SSecp192r1::from_hex("0xffffffffffffffffffffffff99def836146bc9b1b4d22830");
        let pk = gen_key(&curve, &sk); // public key

        let v = SSecp192r1::from_hex("0xffffffffffffffffffffffff99def836146bc9b1b4d22830");
        let V_wrong = commitment(&curve, &SSecp192r1::from_hex("0xffff9bf1b4d22ff9b83fff0"));

        let c = challenge(&curve, &SSecp192r1::from_hex("0x19999999999999C03200"));

        let r = respond(&v, &sk, &c);

        let c_wrong = challenge(&curve, &SSecp192r1::from_hex("0x199C3200999999990"));
        assert_eq!(verify(&curve, &V_wrong, &r, &pk, &c_wrong), false);
    }

    #[test]
    #[allow(non_snake_case)]
    fn test_wrong_response () {
        let curve = create_secp192r1_curve();

        let sk = SSecp192r1::from_hex("0xffffffffffffffffffffffff99def836146bc9b1b4d22830");
        let pk = gen_key(&curve, &sk); // public key

        let v = SSecp192r1::from_hex("0xffffffffffffffffffffffff99def836146bc9b1b4d22830");
        let V = commitment(&curve, &v);

        let c = challenge(&curve, &SSecp192r1::from_hex("0x19999999999999C03200"));

        let r_wrong = respond(
                &SSecp192r1::from_hex("0x199C0399999F99200"), 
                &SSecp192r1::from_hex("0x199999099C032E90"), 
                &SSecp192r1::from_hex("0x199999C039992C00"));

        assert_eq!(verify(&curve, &V, &r_wrong, &pk, &c), false);
    }

    #[test]
    #[allow(non_snake_case)]
    fn test_wrong_pk () {
        let curve = create_secp192r1_curve();

        let sk = SSecp192r1::from_hex("0xffffffffffffffffffffffff99def836146bc9b1b4d22830");

        let v = SSecp192r1::from_hex("0xffffffffffffffffffffffff99def836146bc9b1b4d22830");
        let V = commitment(&curve, &v);

        let c = challenge(&curve, &SSecp192r1::from_hex("0x19999999999999C03200"));

        let r = respond(&v, &sk, &c);

        let wrong_pk = curve.mul(curve.generator(), &SSecp192r1::from_hex("0xffffffffffffffffffffffef6bf99dc836149b1b4d22831"));
        assert_eq!(verify(&curve, &V, &r, &wrong_pk, &c), false);
    }

    #[test]
    #[allow(non_snake_case)]
    fn test_wrong_challenge () {
        let curve = create_secp192r1_curve();

        let sk = SSecp192r1::from_hex("0xffffffffffffffffffffffff99def836146bc9b1b4d22830");
        let pk = gen_key(&curve, &sk); // public key

        let v = SSecp192r1::from_hex("0xffffffffffffffffffffffff99def836146bc9b1b4d22830");
        let V = commitment(&curve, &v);

        let c = challenge(&curve, &SSecp192r1::from_hex("0x19999999999999C03200"));

        let r = respond(&v, &sk, &c);

        let c_wrong = challenge(&curve, &SSecp192r1::from_hex("0x199C3200999999990"));
        assert_eq!(verify(&curve, &V, &r, &pk, &c_wrong), false);
    }
}