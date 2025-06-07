#[macro_export]
macro_rules! define_field {
    ($name:ident, $modulus:expr) => {

        #[derive(Debug, Clone, PartialEq)]
        pub struct $name {
            v: BigInt,
        }

        impl $name {
            #[allow(dead_code)]
            pub fn new(value: BigInt) -> Self {
                $name {
                    v: value.rem_euclid(&BigInt::from($modulus)),
                }
            }

            #[allow(dead_code)]
            pub fn from(value: u32) -> Self {
                $name {
                    v: BigInt::from(value).rem_euclid(&BigInt::from($modulus)),
                }
            }

            #[allow(dead_code)]
            pub fn from_hex(value: &str) -> Self {
                $name {
                    v: BigInt::parse_bytes(value.trim_start_matches("0x").as_bytes(), 16).unwrap().rem_euclid(&BigInt::from($modulus)),
                }
                
            }
        }

        impl Field for $name {
            fn add(lhs: &Self, rhs: &Self) -> Self {
                Self { v: (&lhs.v + &rhs.v).rem_euclid(&BigInt::from($modulus)) }
            }

            fn sub(lhs: &Self, rhs: &Self) -> Self {
                Self::add(lhs, &Self::neg(rhs))
            }

            fn neg(val: &Self) -> Self {
                Self { v: (-&val.v).rem_euclid(&BigInt::from($modulus)) }
            }

            fn zero() -> Self {
                Self { v: BigInt::from(0) }
            }

            fn div(lhs: &Self, rhs: &Self) -> Self {
                Self::mul(&lhs, &Self::inv(rhs))
            }

            fn mul(lhs: &Self, rhs: &Self) -> Self {
                Self { v: (&lhs.v * &rhs.v).rem_euclid(&BigInt::from($modulus)) }
            }

            fn one() -> Self {
                Self { v: BigInt::from(1) }
            }

            fn inv(val: &Self) -> Self {
                let inv = val.v.modinv(&BigInt::from($modulus)).expect("Inverse does not exist");
                $name {
                    v: inv,
                }
            }
        }

        impl Arbitrary for $name {
            fn arbitrary(g: &mut Gen) -> Self {
                $name {
                    v: BigInt::arbitrary(g).rem_euclid(&BigInt::from($modulus)),
                }
            }
        }
    }
}

#[macro_export]
macro_rules! define_scalar {
    ($name:ident, $modulus:expr) => {
        define_field!($name, $modulus);

        impl Scalar for $name {
            fn bits(&self) -> usize {
                self.v.bits() as usize
            }

            fn bit(&self, i: usize) -> bool {
                self.v.bit(i as u64)
            }
        }

        impl PartialOrd for $name {
            fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
                self.v.partial_cmp(&other.v)
            }
        }
    }
}


#[cfg(test)]
mod test {

    use num_bigint::{BigInt};
    use num_traits::ops::euclid::Euclid;
    use crate::abstract_structures::*;

    use quickcheck::{quickcheck, TestResult};
    use quickcheck::{Arbitrary, Gen};

    const ORDER : i64 = 72057594037927931;
    define_scalar!(QcScalar, ORDER);

    quickcheck! {
        // Check range of scalar in [0, order) after operations
        fn prop_scalar_range_over_add(x: QcScalar, y: QcScalar) -> bool {
            let res = QcScalar::add(&x, &y);
            res.v >= BigInt::from(0) && res.v < BigInt::from(ORDER)
        }

        fn prop_scalar_range_over_sub(x: QcScalar, y: QcScalar) -> bool {
            let res = QcScalar::sub(&x, &y);
            res.v >= BigInt::from(0) && res.v < BigInt::from(ORDER)
        }

        fn prop_scalar_range_over_neg(x: QcScalar) -> bool {
            let res = QcScalar::neg(&x);
            res.v >= BigInt::from(0) && res.v < BigInt::from(ORDER)
        }

        fn prop_scalar_range_over_mul(x: QcScalar, y: QcScalar) -> bool {
            let res = QcScalar::mul(&x, &y);
            res.v >= BigInt::from(0) && res.v < BigInt::from(ORDER)
        }
    }

    define_field!(QcField, ORDER);

    quickcheck! {
        // Check range of field in [0, order) after operations
        fn prop_field_range_over_add(x: QcField, y: QcField) -> bool {
            let res = QcField::add(&x, &y);
            res.v >= BigInt::from(0) && res.v < BigInt::from(ORDER)
        }

        fn prop_field_range_over_sub(x: QcField, y: QcField) -> bool {
            let res = QcField::sub(&x, &y);
            res.v >= BigInt::from(0) && res.v < BigInt::from(ORDER)
        }

        fn prop_field_range_over_neg(x: QcField) -> bool {
            let res = QcField::neg(&x);
            res.v >= BigInt::from(0) && res.v < BigInt::from(ORDER)
        }

        fn prop_field_range_over_mul(x: QcField, y: QcField) -> bool {
            let res = QcField::mul(&x, &y);
            res.v >= BigInt::from(0) && res.v < BigInt::from(ORDER)
        }

        fn prop_field_range_over_div(x: QcField, y: QcField) -> TestResult {
            // Avoid division by zero
            if y.v == BigInt::from(0) {
                return TestResult::discard();
            }
            let res = QcField::div(&x, &y);
            TestResult::from_bool(res.v >= BigInt::from(0) && res.v < BigInt::from(ORDER))
        }

        fn prop_field_range_over_inv(x: QcField) -> TestResult {
            // Avoid inv of zero
            if x.v == BigInt::from(0) {
                return TestResult::discard();
            }
            let res = QcField::inv(&x);
            TestResult::from_bool(res.v >= BigInt::from(0) && res.v < BigInt::from(ORDER))
        }
    }


    quickcheck! {
        fn prop_field_add_comm (x: QcField, y: QcField) -> bool {
            QcField::add(&x, &y) == QcField::add(&y, &x)
        }

        fn prop_field_add_assoc (x: QcField, y: QcField, z: QcField) -> bool {
            QcField::add(&QcField::add(&x, &y), &z) == QcField::add(&x, &QcField::add(&y, &z))
        }

        fn prop_fied_add_zero (x: QcField) -> bool {
            QcField::add(&x, &QcField::zero()) == x
        }

        fn prop_field_add_neg (x: QcField) -> bool {
            QcField::add(&x, &QcField::neg(&x)) == QcField::zero()
        }

        fn prop_field_mul_comm (x: QcField, y: QcField) -> bool {
            QcField::mul(&x, &y) == QcField::mul(&y, &x)
        }

        fn prop_field_mul_assoc (x: QcField, y: QcField, z: QcField) -> bool {
            QcField::mul(&QcField::mul(&x, &y), &z) == QcField::mul(&x, &QcField::mul(&y, &z))
        }

        fn prop_field_mul_one (x: QcField) -> bool {
            QcField::mul(&x, &QcField::one()) == x
        }

        fn prop_field_mul_inv (x: QcField) -> TestResult {
            // Avoid inv of zero
            if x.v == BigInt::from(0) {
                return TestResult::discard();
            }
            TestResult::from_bool(QcField::mul(&x, &QcField::inv(&x)) == QcField::one())
        }

        fn prop_field_mul_distrib (x: QcField, y: QcField, z: QcField) -> bool {
            QcField::mul(&x, &QcField::add(&y, &z)) == QcField::add(&QcField::mul(&x, &y), &QcField::mul(&x, &z))
        }
    }

}