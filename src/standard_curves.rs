use crate::abstract_structures::*;
use crate::elliptic_curve::*;
use crate::point::*;
use num_bigint::BigInt;
use num_traits::ops::euclid::Euclid;

use quickcheck::{Arbitrary, Gen};
use crate::define_field;
use crate::define_scalar;

// https://neuromancer.sk/std/nist/P-192#
const SECP192R1_P_HEX: &str = "fffffffffffffffffffffffffffffffeffffffffffffffff";
const SECP192R1_N_HEX: &str = "ffffffffffffffffffffffff99def836146bc9b1b4d22831";
define_field!(FSecp192r1, BigInt::parse_bytes(SECP192R1_P_HEX.as_bytes(), 16).unwrap());
define_scalar!(SSecp192r1,BigInt::parse_bytes(SECP192R1_N_HEX.as_bytes(), 16).unwrap());

#[allow(non_snake_case)]
pub fn create_secp192r1_curve() -> EllipticCurve<FSecp192r1, SSecp192r1> {
    let a = FSecp192r1::from_hex("0xfffffffffffffffffffffffffffffffefffffffffffffffc");
    let b = FSecp192r1::from_hex("0x64210519e59c80e70fa7e9ab72243049feb8deecc146b9b1");
    let gx = FSecp192r1::from_hex("0x188da80eb03090f67cbf20eb43a18800f4ff0afd82ff1012");
    let gy = FSecp192r1::from_hex("0x07192b95ffc8da78631011ed6b24cdd573f977a11e794811");
    let h = SSecp192r1::from_hex("0x1");
    return EllipticCurve::new(a, b, Point::Affine(gx, gy), h);
}

// https://neuromancer.sk/std/secg/secp256k1
// bitcoin curve
const SECP256K1_P_HEX: &str = "fffffffffffffffffffffffffffffffffffffffffffffffffffffffefffffc2f";
const SECP256K1_N_HEX: &str = "fffffffffffffffffffffffffffffffebaaedce6af48a03bbfd25e8cd0364141";
define_field!(FSecp256k1, BigInt::parse_bytes(SECP256K1_P_HEX.as_bytes(), 16).unwrap());
define_scalar!(SSecp256k1,BigInt::parse_bytes(SECP256K1_N_HEX.as_bytes(), 16).unwrap());

#[allow(non_snake_case)]
pub fn create_secp256k1_curve() -> EllipticCurve<FSecp256k1, SSecp256k1> {
    let a = FSecp256k1::from_hex("0x0000000000000000000000000000000000000000000000000000000000000000");
    let b = FSecp256k1::from_hex("0x0000000000000000000000000000000000000000000000000000000000000007");
    let gx = FSecp256k1::from_hex("0x79be667ef9dcbbac55a06295ce870b07029bfcdb2dce28d959f2815b16f81798");
    let gy = FSecp256k1::from_hex("0x483ada7726a3c4655da4fbfc0e1108a8fd17b448a68554199c47d08ffb10d4b8");
    let h = SSecp256k1::from_hex("0x1");
    return EllipticCurve::new(a, b, Point::Affine(gx, gy), h);
}

// https://www.rfc-editor.org/rfc/rfc5639#section-3.1
const BRAINPOOL_P160R1_P_HEX: &str = "E95E4A5F737059DC60DFC7AD95B3D8139515620F";
const BRAINPOOL_P160R1_N_HEX: &str = "E95E4A5F737059DC60DF5991D45029409E60FC09";
define_field!(FP160r1, BigInt::parse_bytes(BRAINPOOL_P160R1_P_HEX.as_bytes(),16).unwrap());
define_scalar!(SP160r1, BigInt::parse_bytes(BRAINPOOL_P160R1_N_HEX.as_bytes(),16).unwrap());

#[allow(non_snake_case)]
pub fn create_brainpoolP160r1() -> EllipticCurve<FP160r1, SP160r1> {
    let a = FP160r1::from_hex("0x340E7BE2A280EB74E2BE61BADA745D97E8F7C300");
    let b = FP160r1::from_hex("0x1E589A8595423412134FAA2DBDEC95C8D8675E58");
    let gx = FP160r1::from_hex("0xBED5AF16EA3F6A4F62938C4631EB5AF7BDBCDBC3");
    let gy = FP160r1::from_hex("0x1667CB477A1A8EC338F94741669C976316DA6321");
    let h = SP160r1::from_hex("0x1");
    return EllipticCurve::new(a, b, Point::Affine(gx, gy), h);
}