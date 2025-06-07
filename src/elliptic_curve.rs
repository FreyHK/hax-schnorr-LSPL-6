//! Implementation of an elliptic curve over a finite field.

use crate::point::Point;
use crate::abstract_structures::{
    Field,
    Scalar,
};

fn is_on_curve<F: Field>(a: &F, b: &F, p: &Point<F>) -> bool {
    match p {
        Point::Infinity => true,
        Point::Affine(x, y) => {
            let lhs = F::mul(y, y);
            let rhs = F::add(&F::add(&F::mul(x, &F::mul(x, x)),&F::mul(a, x)),b);
            lhs == rhs
        }
    }
}

fn ec_add<F: Field>(a : &F, _b: &F, p: &Point<F>, q: &Point<F>) -> Point<F> {
    match (p, q) {
        (Point::Infinity, _) => q.clone(),
        (_, Point::Infinity) => p.clone(),
        (Point::Affine(x1, y1), Point::Affine(x2, y2)) => {
            if x1 == x2 && y1 == &F::neg(y2) {
                // Point addition with opposite y-coordinates
                Point::Infinity
            } else if x1 == x2 && y1 == y2 {
                // Point doubling
                let two = F::add(&F::one(), &F::one());
                let three = F::add(&F::one(),&two);
                // m = (3 * x1^2 + a) / (2 * y1)
                let m = F::div(&F::add(&F::mul(&three, &F::mul(x1, x1)), a), &F::mul(&two, y1));
                // x3 = m^2 - x1 - x2
                let x3 = F::sub(&F::sub(&F::mul(&m, &m), &x1), &x2);
                // y3 = m * (x1 - x3) - y1
                let y3 = F::sub(&F::mul(&m, &F::sub(&x1, &x3)), &y1);
                Point::Affine(x3, y3)
            } else {
                // Point addition
                // m = (y2 - y1) / (x2 - x1)
                let m = F::div(&F::sub(y2, y1), &F::sub(x2, x1));
                // x3 = m^2 - x1 - x2
                let x3 = F::sub(&F::sub(&F::mul(&m, &m), &x1), &x2);
                // y3 = m * (x1 - x3) - y1
                let y3 = F::sub(&F::mul(&m, &F::sub(&x1, &x3)), &y1);
                Point::Affine(x3, y3)
            }
        }
    }
}

fn ec_mul<F: Field, S: Scalar>(a: &F, b: &F, p: &Point<F>, n: &S) -> Point<F> {
    let mut res = Point::Infinity;
    let bits = n.bits();
    for i in 0..bits {
        res = ec_add(a, b, &res, &res); 
        if n.bit(bits - 1 - i) {
            res = ec_add(a, b, &res, &p);
        }
    }
    res
}


#[hax_lib::attributes]
pub struct EllipticCurve<F: Field, S : Scalar> {
    a: F,
    b: F,
    //#[hax_lib::refine(is_on_curve(&a, &b, &g))]
    g: Point<F>,
    // #[hax_lib::refine(h != S::zero())]
    h: S,
}

#[hax_lib::attributes]
impl <F: Field, S : Scalar> EllipticCurve<F, S> {
    #[hax_lib::requires (
        is_on_curve(&a, &b, &g)
        && h != S::zero()
    )]
    pub fn new(a: F, b: F, g: Point<F>, h: S) -> Self {
       EllipticCurve { a, b, g, h }
    }
    
    pub fn generator(&self) -> &Point<F> {
        &self.g
    }
    
    pub fn h(&self) -> &S {
        &self.h
    }

    pub fn is_on_curve(&self, p: &Point<F>) -> bool {
        is_on_curve(&self.a, &self.b, p)
    }

    pub fn is_infinity(&self, p: &Point<F>) -> bool {
        match p {
            Point::Infinity => true,
            _ => false,
        }
    }

    pub fn add(&self, p: &Point<F>, q: &Point<F>) -> Point<F> {
        ec_add(&self.a, &self.b, p, q)
    }

    pub fn mul(&self, p: &Point<F>, n: &S) -> Point<F> {
        ec_mul(&self.a, &self.b, p, n)
    }

    pub fn neg(&self, p: &Point<F>) -> Point<F> {
        match p {
            Point::Infinity => Point::Infinity,
            Point::Affine(x, y) => Point::Affine(x.clone(), F::neg(y)),
        }
    }    
}

#[cfg(test)]
mod tests {
    use super::*;

    use quickcheck::quickcheck;

    use crate::standard_curves::{create_secp192r1_curve};
    use crate::standard_curves::{SSecp192r1};

    quickcheck!{
        // Test P + Q closed on curve
        #[allow(non_snake_case)]
        fn prop_point_add_on_curve(x: SSecp192r1, y: SSecp192r1) -> bool {
            let curve = create_secp192r1_curve();
            let P = curve.mul(&curve.generator(), &x);
            let Q = curve.mul(&curve.generator(), &y);
            let res = curve.add(&P, &Q);
            curve.is_on_curve(&res)
        }

        // Test P + P closed on curve (point doubling)
        #[allow(non_snake_case)]
        fn prop_point_double_on_curve(x: SSecp192r1) -> bool {
            let curve = create_secp192r1_curve();
            let P = curve.mul(&curve.generator(), &x);
            let res = curve.add(&P, &P);
            curve.is_on_curve(&res)
        }

        // Test P x [k] closed on curve
        #[allow(non_snake_case)]
        fn prop_point_mul_on_curve(x: SSecp192r1, k: SSecp192r1) -> bool {
            let curve = create_secp192r1_curve();
            let P = curve.mul(&curve.generator(), &x);
            let res = curve.mul(&P, &k);
            curve.is_on_curve(&res)
        }

        // Test P + Inf = P && Inf + P = P
        #[allow(non_snake_case)]
        fn prop_point_add_inf(x: SSecp192r1) -> bool {
            let curve = create_secp192r1_curve();
            let P = curve.mul(&curve.generator(), &x);
            curve.add(&P, &Point::Infinity) == P && curve.add(&Point::Infinity, &P) == P
        }

        // Test P + (-P) = Inf
        #[allow(non_snake_case)]
        fn prop_point_neg_inf(x: SSecp192r1) -> bool {
            let curve = create_secp192r1_curve();
            let P = curve.mul(&curve.generator(), &x);
            curve.add(&P, &curve.neg(&P)) == Point::Infinity && curve.add(&curve.neg(&P), &P) == Point::Infinity
        }

         // Test associativity: (P + Q) + R = P + (Q + R)
         #[allow(non_snake_case)]
         fn prop_point_add_assoc(x: SSecp192r1, y: SSecp192r1, z: SSecp192r1) -> bool {
             let curve = create_secp192r1_curve();
             let P = curve.mul(&curve.generator(), &x);
             let Q = curve.mul(&curve.generator(), &y);
             let R = curve.mul(&curve.generator(), &z);
             curve.add(&curve.add(&P, &Q), &R) == curve.add(&P, &curve.add(&Q, &R))
         }

         // Test commutativity: P + Q = Q + P
         #[allow(non_snake_case)]
         fn prop_point_add_comm(x: SSecp192r1, y: SSecp192r1) -> bool {
             let curve = create_secp192r1_curve();
             let P = curve.mul(&curve.generator(), &x);
             let Q = curve.mul(&curve.generator(), &y);
             curve.add(&P, &Q) == curve.add(&Q, &P)
         }

        // Test distributivity: (P + Q) x [k] = P x [k] + Q x [k]
        #[allow(non_snake_case)]
        fn prop_point_mul_distr(x: SSecp192r1, y: SSecp192r1, k: SSecp192r1) -> bool {
            let curve = create_secp192r1_curve();
            let P = curve.mul(&curve.generator(), &x);
            let Q = curve.mul(&curve.generator(), &y);
            curve.mul(&curve.add(&P, &Q), &k) == curve.add(&curve.mul(&P, &k), &curve.mul(&Q, &k))
        }

         // Test distributivity: P x [k + m] = P x [k] + P x [m]
        #[allow(non_snake_case)]
        fn prop_scalar_add_distr(x: SSecp192r1, k: SSecp192r1, m: SSecp192r1) -> bool {
            let curve = create_secp192r1_curve();
            let P = curve.mul(&curve.generator(), &x);
            curve.mul(&P, &SSecp192r1::add(&k, &m)) == curve.add(&curve.mul(&P, &k), &curve.mul(&P, &m))
        }

        // Test distributivity: P x [k * m] = (P x [k]) x [m]
        #[allow(non_snake_case)]
        fn prop_scalar_mul_distr(x: SSecp192r1, k: SSecp192r1, m: SSecp192r1) -> bool {
            let curve = create_secp192r1_curve();
            let P = curve.mul(&curve.generator(), &x);
            curve.mul(&P, &SSecp192r1::mul(&k, &m)) == curve.mul(&curve.mul(&P, &k), &m)
        }
    }
    
}