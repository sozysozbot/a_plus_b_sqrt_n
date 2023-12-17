#![warn(clippy::pedantic)]
use fraction::{prelude::BigFraction, GenericFraction, Integer, Zero};
use num_bigint::BigUint;
use num_traits::One;
use std::{cmp::Ordering, ops};

#[derive(Debug, Clone)]
pub enum APlusBSqrtN {
    Rational(BigFraction),
    Irrational {
        a: BigFraction,
        b: BigFraction, // non-zero
        n: BigUint,     // non-perfect-square
    },
}

#[must_use]
fn is_perfect_square(n: &BigUint) -> bool {
    let sqrt_n_floor = n.sqrt();
    &(sqrt_n_floor.clone() * sqrt_n_floor) == n
}

impl APlusBSqrtN {
    /// # Panics
    /// Panics when either `a` or `b` is Infinity or NaN
    #[must_use]
    pub fn new(a: BigFraction, b: BigFraction, n: BigUint) -> Self {
        assert!(
            !(a.is_nan() || a.is_infinite() || b.is_nan() || b.is_infinite()),
            "Cannot have either Infinity or NaN in `a` or `b`"
        );

        if b == BigFraction::zero() || is_perfect_square(&n) {
            Self::Rational(a + b * n.sqrt())
        } else {
            Self::Irrational { a, b, n }
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
        matches!(self, APlusBSqrtN::Rational(_))
    }
}

impl PartialEq for APlusBSqrtN {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (APlusBSqrtN::Rational(a1), APlusBSqrtN::Rational(a2)) => a1 == a2,
            (APlusBSqrtN::Rational(_), APlusBSqrtN::Irrational { .. })
            | (APlusBSqrtN::Irrational { .. }, APlusBSqrtN::Rational(_)) => false,
            (
                APlusBSqrtN::Irrational {
                    a: a1,
                    b: b1,
                    n: n1,
                },
                APlusBSqrtN::Irrational {
                    a: a2,
                    b: b2,
                    n: n2,
                },
            ) => {
                a1 == a2
                    && (b1.clone() * b1.clone() * n1.clone()
                        == b2.clone() * b2.clone() * n2.clone())
            }
        }
    }
}

impl Eq for APlusBSqrtN {}

impl ops::Neg for APlusBSqrtN {
    type Output = Self;

    fn neg(self) -> Self::Output {
        match self {
            APlusBSqrtN::Rational(a) => Self::Rational(-a),
            APlusBSqrtN::Irrational { a, b, n } => Self::new(-a, -b, n),
        }
    }
}

impl ops::Add for APlusBSqrtN {
    type Output = Self;
    fn add(self, other: Self) -> Self::Output {
        match (self, other) {
            (APlusBSqrtN::Rational(a1), APlusBSqrtN::Rational(a2)) => Self::Rational(a1 + a2),
            (APlusBSqrtN::Irrational { a, b, n }, APlusBSqrtN::Rational(a2))
            | (APlusBSqrtN::Rational(a2), APlusBSqrtN::Irrational { a, b, n }) => {
                Self::new(a + a2, b, n)
            }

            (
                APlusBSqrtN::Irrational {
                    a: a1,
                    b: b1,
                    n: n1,
                },
                APlusBSqrtN::Irrational {
                    a: a2,
                    b: b2,
                    n: n2,
                },
            ) => {
                if is_perfect_square(&(n1.clone() * n2.clone())) {
                    // ans = a1 + b1 sqrt(n1) + a2 + b2 sqrt(n2)
                    // Let n1 = s * s * n
                    // Let n2 = t * t * n
                    // Then n3 = gcd(n1, n2) = u * u * n
                    let n3 = n1.gcd(&n2);
                    let s_over_u_squared = n1 / n3.clone();
                    let t_over_u_squared = n2 / n3.clone();
                    assert!(is_perfect_square(&s_over_u_squared));
                    assert!(is_perfect_square(&t_over_u_squared));
                    let s_over_u = s_over_u_squared.sqrt();
                    let t_over_u = t_over_u_squared.sqrt();

                    // ans = (a1 + a2) + [b1 * (s/u) + b2 * (t/u)] sqrt(n3)
                    Self::new(a1 + a2, b1 * s_over_u + b2 * t_over_u, n3)
                } else {
                    panic!(
                        "Cannot add: sqrt({}) and sqrt({}) are incompatible",
                        &n1, &n2
                    )
                }
            }
        }
    }
}

impl ops::Sub for APlusBSqrtN {
    type Output = Self;

    fn sub(self, rhs: Self) -> Self::Output {
        self + (-rhs)
    }
}

impl ops::Mul for APlusBSqrtN {
    type Output = Self;

    fn mul(self, rhs: Self) -> Self::Output {
        match (self, rhs) {
            (APlusBSqrtN::Rational(a1), APlusBSqrtN::Rational(a2)) => Self::Rational(a1 * a2),
            (APlusBSqrtN::Rational(multiplier), APlusBSqrtN::Irrational { a, b, n })
            | (APlusBSqrtN::Irrational { a, b, n }, APlusBSqrtN::Rational(multiplier)) => {
                Self::new(a * multiplier.clone(), b * multiplier, n)
            }
            (
                APlusBSqrtN::Irrational {
                    a: a1,
                    b: b1,
                    n: n1,
                },
                APlusBSqrtN::Irrational {
                    a: a2,
                    b: b2,
                    n: n2,
                },
            ) => {
                if is_perfect_square(&(n1.clone() * n2.clone())) {
                    // ans = [a1 + b1 sqrt(n1)] [a2 + b2 sqrt(n2)]
                    // Let n1 = s * s * n
                    // Let n2 = t * t * n
                    // Then n3 = gcd(n1, n2) = u * u * n
                    let n3 = n1.gcd(&n2);
                    let s_over_u_squared = n1 / n3.clone();
                    let t_over_u_squared = n2 / n3.clone();
                    assert!(is_perfect_square(&s_over_u_squared));
                    assert!(is_perfect_square(&t_over_u_squared));
                    let s_over_u = s_over_u_squared.sqrt();
                    let t_over_u = t_over_u_squared.sqrt();

                    // ans = [a1 + b1 * s/u * sqrt(n3)] [a2 + b2 * t/u * sqrt(n3)]
                    //     = [a1*a2   +   b1 * s/u * n3 * b2 * t/u] + [a1 * b2 * t/u   +   a2 * b1 * s/u] sqrt(n3)
                    Self::new(
                        a1.clone() * a2.clone()
                            + b1.clone()
                                * b2.clone()
                                * s_over_u.clone()
                                * n3.clone()
                                * t_over_u.clone(),
                        a1 * b2 * t_over_u + a2 * b1 * s_over_u,
                        n3,
                    )
                } else {
                    panic!(
                        "Cannot add: sqrt({}) and sqrt({}) are incompatible",
                        &n1, &n2
                    )
                }
            }
        }
    }
}

impl APlusBSqrtN {
    #[must_use]
    pub fn recip(self) -> Self {
        match self {
            APlusBSqrtN::Rational(a) => Self::from_rational(GenericFraction::one() / a), /* has to check that this does not lead to infinity */
            APlusBSqrtN::Irrational { a, b, n } => {
                // ans = 1 / [a + b * sqrt(n)]
                //     = [a - b * sqrt(n)] / [a^2 - b^2 * n]
                let dividing_factor = a.clone() * a.clone() - b.clone() * b.clone() * n.clone();
                Self::new(a / dividing_factor.clone(), -b / dividing_factor, n)
            }
        }
    }
}

impl ops::Div for APlusBSqrtN {
    type Output = Self;

    #[allow(clippy::suspicious_arithmetic_impl)]
    fn div(self, rhs: Self) -> Self::Output {
        self * rhs.recip()
    }
}

impl APlusBSqrtN {
    #[must_use]
    pub fn is_positive(&self) -> bool {
        match self {
            APlusBSqrtN::Rational(a) => a > &BigFraction::zero(),
            APlusBSqrtN::Irrational { a, b, n } => {
                if b > &BigFraction::zero() {
                    if a >= &BigFraction::zero() {
                        return true;
                    }
                    // We know that -a > 0
                    // We want to check whether b * sqrt(n) > -a > 0
                    b.clone() * b.clone() * n.clone() > a.clone() * a.clone()
                } else {
                    // b is assumed to be non-zero
                    // Thus, we know that b < 0

                    // We know that (-b) * sqrt(n) > 0
                    // We want to check whether a + b * sqrt(n) > 0
                    // Thus, we want to know whether a > (-b) * sqrt(n) > 0

                    // We first need to verify that a is indeed greater than 0
                    if a <= &BigFraction::zero() {
                        return false;
                    }

                    a.clone() * a.clone() > b.clone() * b.clone() * n.clone()
                }
            }
        }
    }

    #[must_use]
    pub fn abs(self) -> Self {
        if self.is_positive() {
            self
        } else {
            -self
        }
    }
}

impl std::cmp::Ord for APlusBSqrtN {
    fn cmp(&self, other: &Self) -> Ordering {
        if self == other {
            Ordering::Equal
        } else {
            let diff = self.clone() - other.clone();
            if diff.is_positive() {
                Ordering::Greater
            } else {
                Ordering::Less
            }
        }
    }
}

impl std::cmp::PartialOrd for APlusBSqrtN {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl APlusBSqrtN {
    #[must_use]
    pub fn floor(self) -> GenericFraction<BigUint> {
        match &self {
            APlusBSqrtN::Rational(a) => a.floor(),
            APlusBSqrtN::Irrational { a, b, n } => {
                let b2n = b.clone() * b.clone() * n.clone();

                // m is an integer such that the only possible values for Self::floor() are m-1, m and m+1.
                let m = if b2n >= GenericFraction::one() {
                    // |b|√n >= 1
                    let u = b2n.sqrt(1);
                    // The square of the approximation is accurate up to 1 decimal digits.
                    // Thus
                    // |u * u - b*b*n| < 0.1
                    // | u - |b|√n | | u + |b|√n | < 0.1
                    // Since u > √0.9 and |b|√n >= 1,
                    // | u - |b|√n | < 0.1 / (1+√0.9) < 0.052

                    let approx = if b.sign() == Some(fraction::Sign::Plus) {
                        a + u
                    } else {
                        a - u
                    };

                    // let m = approx.floor();
                    // m <= approx < m+1
                    // approx is up to only 0.052 away from the true value
                    // m-1 < approx - 0.052 < a+b√q < approx + 0.052 < m+2
                    // Hence the only possible values for Self::floor() are m-1, m and m+1.

                    approx.floor()
                } else {
                    // -1 < b√q < 1
                    // let m = a.floor();
                    // m <= a < m+1
                    // m-1 < a+b√q < m+2
                    // Hence the only possible values for Self::floor() are m-1, m and m+1.
                    a.floor()
                };

                if Self::Rational(m.clone() + GenericFraction::one()) <= self.clone() {
                    if self.clone()
                        >= Self::Rational(
                            m.clone() + GenericFraction::one() + GenericFraction::one(),
                        )
                    {
                        unreachable!("oh no! there is a bug and actually self >= m+2")
                    }
                    return m + GenericFraction::one();
                } else if Self::Rational(m.clone()) <= self.clone() {
                    return m;
                } else if Self::Rational(m.clone() - GenericFraction::one()) <= self.clone() {
                    return m - GenericFraction::one();
                }
                unreachable!("oh no! there is a bug and actually self < m-1")
            }
        }
    }
}

impl num_traits::identities::Zero for APlusBSqrtN {
    fn zero() -> Self {
        Self::Rational(GenericFraction::zero())
    }

    fn is_zero(&self) -> bool {
        self == &Self::zero()
    }
}

impl num_traits::identities::One for APlusBSqrtN {
    fn one() -> Self {
        Self::Rational(GenericFraction::one())
    }
}

impl num_traits::ops::inv::Inv for APlusBSqrtN {
    type Output = Self;

    fn inv(self) -> Self::Output {
        self.recip()
    }
}

impl num_traits::ops::mul_add::MulAdd for APlusBSqrtN {
    type Output = Self;

    fn mul_add(self, a: Self, b: Self) -> Self::Output {
        self * a + b
    }
}

impl num_traits::ops::mul_add::MulAddAssign for APlusBSqrtN {
    fn mul_add_assign(&mut self, a: Self, b: Self) {
        *self = (self.clone() * a) + b;
    }
}

#[test]
fn eq() {
    use crate::APlusBSqrtN;
    use fraction::prelude::BigFraction;
    use num_bigint::BigUint;
    let silver = APlusBSqrtN::new(
        BigFraction::new(1u8, 1u8),
        BigFraction::new(1u8, 1u8),
        BigUint::new(vec![2u32]),
    );

    let silver2 = APlusBSqrtN::new(
        BigFraction::new(1u8, 1u8),
        BigFraction::new(1u8, 2u8),
        BigUint::new(vec![8u32]),
    );
    assert_eq!(silver, silver2);
}

#[test]
fn addition() {
    use crate::APlusBSqrtN;
    use fraction::prelude::BigFraction;
    use num_bigint::BigUint;
    let silver = APlusBSqrtN::new(
        BigFraction::new(1u8, 1u8),
        BigFraction::new(1u8, 1u8),
        BigUint::new(vec![2u32]),
    );
    assert_eq!(
        silver.clone() + silver.clone(),
        APlusBSqrtN::new(
            BigFraction::new(2u8, 1u8),
            BigFraction::new(2u8, 1u8),
            BigUint::new(vec![2u32]),
        )
    );
}

#[test]
fn is_positive() {
    use crate::APlusBSqrtN;
    use fraction::prelude::BigFraction;
    use num_bigint::BigUint;
    let fourteen_minus_root_195 = APlusBSqrtN::new(
        BigFraction::new(14u8, 1u8),
        -BigFraction::new(1u8, 1u8),
        BigUint::new(vec![195u32]),
    );

    assert!(fourteen_minus_root_195.is_positive());
}

#[test]
fn multiplication() {
    use crate::APlusBSqrtN;
    use fraction::prelude::BigFraction;
    use num_bigint::BigUint;
    let sqrt2 = APlusBSqrtN::new(
        BigFraction::new(0u8, 1u8),
        BigFraction::new(1u8, 1u8),
        BigUint::new(vec![2u32]),
    );
    assert_eq!(
        sqrt2.clone() * sqrt2.clone(),
        APlusBSqrtN::new(
            BigFraction::new(2u8, 1u8),
            BigFraction::new(2u8, 1u8),
            BigUint::zero(),
        )
    );
}

#[test]
fn dividing_gives_unity() {
    use crate::APlusBSqrtN;
    use fraction::{prelude::BigFraction, Zero};
    use num_bigint::BigUint;
    let x = APlusBSqrtN::new(
        BigFraction::new(1u8, 1u8),
        BigFraction::new(1u8, 1u8),
        BigUint::new(vec![2u32]),
    );
    assert_eq!(
        x.clone() / x.clone(),
        APlusBSqrtN::new(
            BigFraction::new(1u8, 1u8),
            BigFraction::new(1u8, 1u8),
            BigUint::zero()
        )
    );
}

#[test]
fn floor() {
    let small_negative = APlusBSqrtN::new(
        BigFraction::new(14142u32, 10000u32),
        -BigFraction::new(1u8, 1u8),
        BigUint::new(vec![2u32]),
    );

    let small_positive = APlusBSqrtN::new(
        BigFraction::new(14143u32, 10000u32),
        -BigFraction::new(1u8, 1u8),
        BigUint::new(vec![2u32]),
    );
    assert_eq!(-GenericFraction::one(), small_negative.floor());
    assert_eq!(GenericFraction::zero(), small_positive.floor());
}