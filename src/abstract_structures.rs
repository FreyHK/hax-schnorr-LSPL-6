//! Defines traits for the underlying field of an elliptic curve
//! and the scalar type used for scalar multiplication.


/// Field trait representing a mathematical field. 
/// 
/// The characteristics of the field is not equal to 2
pub trait Field: Sized + PartialEq + Clone {
    fn one() -> Self;
    fn zero() -> Self;

    fn add(lhs: &Self, rhs: &Self) -> Self;
    fn sub(lhs: &Self, rhs: &Self) -> Self;
    fn neg(val: &Self) -> Self;
    fn mul(lhs: &Self, rhs: &Self) -> Self;
    fn inv(val: &Self) -> Self;
    fn div(lhs: &Self, rhs: &Self) -> Self;

    /*
    #[hax_lib::refine]
    fn add_comm (x: &Self, y: &Self) -> Proof <{
        Self::add(x, y) == Self::add(y, x)
    }>{}

    #[hax_lib::refine]
    fn add_assoc (x: &Self, y: &Self, z: &Self) -> Proof <{
        Self::add(&Self::add(x, y), z) == Self::add(x, &Self::add(y, z))
    }>{}

    #[hax_lib::refine]
    fn add_zero (x: &Self) -> Proof <{
        Self::add(x, &Self::zero()) == x
    }>{}

    #[hax_lib::refine]
    fn add_neg (x: &Self) -> Proof <{
        Self::add(x, &Self::neg(x)) == Self::zero()
    }>{}

    #[hax_lib::refine]
    fn mul_comm (x: &Self, y: &Self) -> Proof <{
        Self::mul(x, y) == Self::mul(y, x)
    }>{}

    #[hax_lib::refine]
    fn mul_assoc (x: &Self, y: &Self, z: &Self) -> Proof <{
        Self::mul(&Self::mul(x, y), z) == Self::mul(x, &Self::mul(y, z))    
    }>{}

    #[hax_lib::refine]
    fn mul_one (x: &Self) -> Proof <{
        Self::mul(x, &Self::one()) == x
    }>{}

    #[hax_lib::refine]
    fn mul_inv (x: &Self) -> Proof <{
        if x == &Self::zero() {
            return true;
        } 
        Self::mul(x, &Self::inv(x)) == Self::one()
    }>{}

    #[hax_lib::refine]
    fn add_mul_distr (x: &Self, y: &Self, z: &Self) -> Proof <{
        Self::mul(&Self::add(x, y), z) == Self::add(&Self::mul(x, z), &Self::mul(y, z))
    }>{}

    #hax_lib::refine]
    fn add_eq_sub_neg (x: &Self, y: &Self) -> Proof <{
        Self::add(x, y) == Self::sub(x, &Self::neg(y))
    }>{}

    #[hax_lib::refine]
    fn mul_eq_div (x: &Self, y: &Self) -> Proof <{
        Self::mul(x, y) == Self::div(x, &Self::inv(y))
    }>{}
    
    #[hax_lib::refine]
    fn char_neq_zero() -> Proof <{
        Self::add(&Self::one(), &Self::zero()) != Self::zero()
    }>{}

    */
}

/// Scalar trait representing a scalar field element.
/// Scalar should be implemented such that it is isomorphic to the integers modulo
/// the order of the generator point of the elliptic curve.
pub trait Scalar : Field {
    fn bits(&self) -> usize;
    fn bit(&self, i: usize) -> bool;
}
