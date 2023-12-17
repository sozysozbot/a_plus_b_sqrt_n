#![warn(clippy::pedantic)]
use fraction::{prelude::BigFraction, GenericFraction, Integer, Zero};
use num_bigint::BigUint;
use num_traits::One;
use std::ops;

#[derive(Debug, Clone)]
pub enum APlusBSqrtQ {
    Rational(BigFraction),
    Irrational {
        a: BigFraction,
        b: BigFraction, // non-zero
        q: BigUint,     // non-perfect-square
    },
}

#[must_use]
fn is_perfect_square(n: &BigUint) -> bool {
    let sqrt_n_floor = n.sqrt();
    &(sqrt_n_floor.clone() * sqrt_n_floor) == n
}

impl APlusBSqrtQ {
    /// # Panics
    /// Panics when either `a` or `b` is Infinity or NaN
    #[must_use]
    pub fn new(a: BigFraction, b: BigFraction, q: BigUint) -> Self {
        assert!(
            !(a.is_nan() || a.is_infinite() || b.is_nan() || b.is_infinite()),
            "Cannot have either Infinity or NaN in `a` or `b`"
        );

        if b == BigFraction::zero() || is_perfect_square(&q) {
            Self::Rational(a + b * q.sqrt())
        } else {
            Self::Irrational { a, b, q }
        }
    }

    #[must_use]
    /// # Panics
    /// Panics when the input is Infinity or NaN
    pub fn from_rational(a: BigFraction) -> Self {
        assert!(
            !(a.is_nan() || a.is_infinite()),
            "Cannot have either Infinity or NaN in `a` or `b`"
        );
        Self::Rational(a)
    }

    #[must_use]
    pub const fn is_rational(&self) -> bool {
        matches!(self, APlusBSqrtQ::Rational(_))
    }
}

impl PartialEq for APlusBSqrtQ {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (APlusBSqrtQ::Rational(a1), APlusBSqrtQ::Rational(a2)) => a1 == a2,
            (APlusBSqrtQ::Rational(_), APlusBSqrtQ::Irrational { .. })
            | (APlusBSqrtQ::Irrational { .. }, APlusBSqrtQ::Rational(_)) => false,
            (
                APlusBSqrtQ::Irrational {
                    a: a1,
                    b: b1,
                    q: q1,
                },
                APlusBSqrtQ::Irrational {
                    a: a2,
                    b: b2,
                    q: q2,
                },
            ) => {
                a1 == a2
                    && (b1.clone() * b1.clone() * q1.clone()
                        == b2.clone() * b2.clone() * q2.clone())
            }
        }
    }
}

impl ops::Neg for APlusBSqrtQ {
    type Output = Self;

    fn neg(self) -> Self::Output {
        match self {
            APlusBSqrtQ::Rational(a) => Self::Rational(-a),
            APlusBSqrtQ::Irrational { a, b, q } => Self::new(-a, -b, q),
        }
    }
}

impl ops::Add for APlusBSqrtQ {
    type Output = Self;
    fn add(self, other: Self) -> Self::Output {
        match (self, other) {
            (APlusBSqrtQ::Rational(a1), APlusBSqrtQ::Rational(a2)) => Self::Rational(a1 + a2),
            (APlusBSqrtQ::Irrational { a, b, q }, APlusBSqrtQ::Rational(a2))
            | (APlusBSqrtQ::Rational(a2), APlusBSqrtQ::Irrational { a, b, q }) => {
                Self::new(a + a2, b, q)
            }

            (
                APlusBSqrtQ::Irrational {
                    a: a1,
                    b: b1,
                    q: q1,
                },
                APlusBSqrtQ::Irrational {
                    a: a2,
                    b: b2,
                    q: q2,
                },
            ) => {
                if is_perfect_square(&(q1.clone() * q2.clone())) {
                    // ans = a1 + b1 sqrt(q1) + a2 + b2 sqrt(q2)
                    // Let q1 = s * s * q
                    // Let q2 = t * t * q
                    // Then q3 = gcd(q1, q2) = u * u * q
                    let q3 = q1.gcd(&q2);
                    let s_over_u_squared = q1 / q3.clone();
                    let t_over_u_squared = q2 / q3.clone();
                    assert!(is_perfect_square(&s_over_u_squared));
                    assert!(is_perfect_square(&t_over_u_squared));
                    let s_over_u = s_over_u_squared.sqrt();
                    let t_over_u = t_over_u_squared.sqrt();

                    // ans = (a1 + a2) + [b1 * (s/u) + b2 * (t/u)] sqrt(q3)
                    Self::new(a1 + a2, b1 * s_over_u + b2 * t_over_u, q3)
                } else {
                    panic!(
                        "Cannot add: sqrt({}) and sqrt({}) are incompatible",
                        &q1, &q2
                    )
                }
            }
        }
    }
}

impl ops::Sub for APlusBSqrtQ {
    type Output = Self;

    fn sub(self, rhs: Self) -> Self::Output {
        self + (-rhs)
    }
}

impl ops::Mul for APlusBSqrtQ {
    type Output = Self;

    fn mul(self, rhs: Self) -> Self::Output {
        match (self, rhs) {
            (APlusBSqrtQ::Rational(a1), APlusBSqrtQ::Rational(a2)) => Self::Rational(a1 * a2),
            (APlusBSqrtQ::Rational(multiplier), APlusBSqrtQ::Irrational { a, b, q })
            | (APlusBSqrtQ::Irrational { a, b, q }, APlusBSqrtQ::Rational(multiplier)) => {
                Self::new(a * multiplier.clone(), b * multiplier, q)
            }
            (
                APlusBSqrtQ::Irrational {
                    a: a1,
                    b: b1,
                    q: q1,
                },
                APlusBSqrtQ::Irrational {
                    a: a2,
                    b: b2,
                    q: q2,
                },
            ) => {
                if is_perfect_square(&(q1.clone() * q2.clone())) {
                    // ans = [a1 + b1 sqrt(q1)] [a2 + b2 sqrt(q2)]
                    // Let q1 = s * s * q
                    // Let q2 = t * t * q
                    // Then q3 = gcd(q1, q2) = u * u * q
                    let q3 = q1.gcd(&q2);
                    let s_over_u_squared = q1 / q3.clone();
                    let t_over_u_squared = q2 / q3.clone();
                    assert!(is_perfect_square(&s_over_u_squared));
                    assert!(is_perfect_square(&t_over_u_squared));
                    let s_over_u = s_over_u_squared.sqrt();
                    let t_over_u = t_over_u_squared.sqrt();

                    // ans = [a1 + b1 * s/u * sqrt(q3)] [a2 + b2 * t/u * sqrt(q3)]
                    //     = [a1*a2   +   b1 * s/u * q3 * b2 * t/u] + [a1 * b2 * t/u   +   a2 * b1 * s/u] sqrt(q3)
                    Self::new(
                        a1.clone() * a2.clone()
                            + b1.clone()
                                * b2.clone()
                                * s_over_u.clone()
                                * q3.clone()
                                * t_over_u.clone(),
                        a1 * b2 * t_over_u + a2 * b1 * s_over_u,
                        q3,
                    )
                } else {
                    panic!(
                        "Cannot add: sqrt({}) and sqrt({}) are incompatible",
                        &q1, &q2
                    )
                }
            }
        }
    }
}

impl APlusBSqrtQ {
    #[must_use]
    pub fn recip(self) -> Self {
        match self {
            APlusBSqrtQ::Rational(a) => Self::from_rational(GenericFraction::one() / a), /* has to check that this does not lead to infinity */
            APlusBSqrtQ::Irrational { a, b, q } => {
                // ans = 1 / [a + b * sqrt(q)]
                //     = [a - b * sqrt(q)] / [a^2 - b^2 * q]
                let dividing_factor = a.clone() * a.clone() - b.clone() * b.clone() * q.clone();
                Self::new(a / dividing_factor.clone(), -b / dividing_factor, q)
            }
        }
    }
}

impl ops::Div for APlusBSqrtQ {
    type Output = Self;

    #[allow(clippy::suspicious_arithmetic_impl)]
    fn div(self, rhs: Self) -> Self::Output {
        self * rhs.recip()
    }
}

impl APlusBSqrtQ {
    #[must_use]
    pub fn is_positive(&self) -> bool {
        match self {
            APlusBSqrtQ::Rational(a) => a > &BigFraction::zero(),
            APlusBSqrtQ::Irrational { a, b, q } => {
                if b > &BigFraction::zero() {
                    if a >= &BigFraction::zero() {
                        return true;
                    }
                    // We know that -a > 0
                    // We want to check whether b * sqrt(q) > -a > 0
                    b.clone() * b.clone() * q.clone() > a.clone() * a.clone()
                } else {
                    // b is assumed to be non-zero
                    // Thus, we know that b < 0

                    // We know that (-b) * sqrt(q) > 0
                    // We want to check whether a + b * sqrt(q) > 0
                    // Thus, we want to know whether a > (-b) * sqrt(q) > 0

                    // We first need to verify that a is indeed greater than 0
                    if a <= &BigFraction::zero() {
                        return false;
                    }

                    a.clone() * a.clone() > b.clone() * b.clone() * q.clone()
                }
            }
        }
    }
}

impl num_traits::identities::Zero for APlusBSqrtQ {
    fn zero() -> Self {
        Self::Rational(GenericFraction::zero())
    }

    fn is_zero(&self) -> bool {
        self == &Self::zero()
    }
}

impl num_traits::identities::One for APlusBSqrtQ {
    fn one() -> Self {
        Self::Rational(GenericFraction::one())
    }
}

impl num_traits::ops::inv::Inv for APlusBSqrtQ {
    type Output = Self;

    fn inv(self) -> Self::Output {
        self.recip()
    }
}

impl num_traits::ops::mul_add::MulAdd for APlusBSqrtQ {
    type Output = Self;

    fn mul_add(self, a: Self, b: Self) -> Self::Output {
        self * a + b
    }
}

impl num_traits::ops::mul_add::MulAddAssign for APlusBSqrtQ {
    fn mul_add_assign(&mut self, a: Self, b: Self) {
        *self = (self.clone() * a) + b;
    }
}

#[test]
fn eq() {
    use crate::APlusBSqrtQ;
    use fraction::prelude::BigFraction;
    use num_bigint::BigUint;
    let silver = APlusBSqrtQ::new(
        BigFraction::new(1u8, 1u8),
        BigFraction::new(1u8, 1u8),
        BigUint::new(vec![2u32]),
    );

    let silver2 = APlusBSqrtQ::new(
        BigFraction::new(1u8, 1u8),
        BigFraction::new(1u8, 2u8),
        BigUint::new(vec![8u32]),
    );
    assert_eq!(silver, silver2);
}

#[test]
fn addition() {
    use crate::APlusBSqrtQ;
    use fraction::prelude::BigFraction;
    use num_bigint::BigUint;
    let silver = APlusBSqrtQ::new(
        BigFraction::new(1u8, 1u8),
        BigFraction::new(1u8, 1u8),
        BigUint::new(vec![2u32]),
    );
    assert_eq!(
        silver.clone() + silver.clone(),
        APlusBSqrtQ::new(
            BigFraction::new(2u8, 1u8),
            BigFraction::new(2u8, 1u8),
            BigUint::new(vec![2u32]),
        )
    );
}

#[test]
fn is_positive() {
    use crate::APlusBSqrtQ;
    use fraction::prelude::BigFraction;
    use num_bigint::BigUint;
    let fourteen_minus_root_195 = APlusBSqrtQ::new(
        BigFraction::new(14u8, 1u8),
        -BigFraction::new(1u8, 1u8),
        BigUint::new(vec![195u32]),
    );

    assert!(fourteen_minus_root_195.is_positive());
}

#[test]
fn multiplication() {
    use crate::APlusBSqrtQ;
    use fraction::prelude::BigFraction;
    use num_bigint::BigUint;
    let sqrt2 = APlusBSqrtQ::new(
        BigFraction::new(0u8, 1u8),
        BigFraction::new(1u8, 1u8),
        BigUint::new(vec![2u32]),
    );
    assert_eq!(
        sqrt2.clone() * sqrt2.clone(),
        APlusBSqrtQ::new(
            BigFraction::new(2u8, 1u8),
            BigFraction::new(2u8, 1u8),
            BigUint::zero(),
        )
    );
}

#[test]
fn dividing_gives_unity() {
    use crate::APlusBSqrtQ;
    use fraction::{prelude::BigFraction, Zero};
    use num_bigint::BigUint;
    let x = APlusBSqrtQ::new(
        BigFraction::new(1u8, 1u8),
        BigFraction::new(1u8, 1u8),
        BigUint::new(vec![2u32]),
    );
    assert_eq!(
        x.clone() / x.clone(),
        APlusBSqrtQ::new(
            BigFraction::new(1u8, 1u8),
            BigFraction::new(1u8, 1u8),
            BigUint::zero()
        )
    );
}
