#![warn(clippy::pedantic)]
use fraction::{prelude::BigFraction, Integer, Zero};
use num_bigint::BigUint;
use std::ops;

#[derive(Debug, Clone)]
pub struct APlusBSqrtQ {
    a: BigFraction,
    b: BigFraction,
    q: BigUint, // either 0 or non-perfect-square
}

pub fn is_perfect_square(n: &BigUint) -> bool {
    let sqrt_n_floor = n.sqrt();
    &(sqrt_n_floor.clone() * sqrt_n_floor) == n
}

impl APlusBSqrtQ {
    pub fn new(a: BigFraction, b: BigFraction, q: BigUint) -> Self {
        if b == BigFraction::zero() || is_perfect_square(&q) {
            Self {
                a: a + b * q.sqrt(),
                b: BigFraction::zero(),
                q: BigUint::zero(),
            }
        } else {
            Self { a, b, q }
        }
    }
}

impl PartialEq for APlusBSqrtQ {
    fn eq(&self, other: &Self) -> bool {
        match (self.q == BigUint::zero(), other.q == BigUint::zero()) {
            (true, true) => self.a == other.a,
            (true, false) | (false, true) => false,
            (false, false) => {
                self.a == other.a
                    && (self.b.clone() * self.b.clone() * self.q.clone()
                        == other.b.clone() * other.b.clone() * other.q.clone())
            }
        }
    }
}

impl ops::Neg for APlusBSqrtQ {
    type Output = Self;

    fn neg(self) -> Self::Output {
        Self::new(-self.a, -self.b, self.q)
    }
}

impl ops::Add for APlusBSqrtQ {
    type Output = Self;
    fn add(self, other: Self) -> Self::Output {
        if other.q == BigUint::zero() {
            Self::new(self.a + other.a, self.b, self.q)
        } else if self.q == BigUint::zero() {
            other + self
        } else if is_perfect_square(&(self.q.clone() * other.q.clone())) {
            // ans = a1 + b1 sqrt(q1) + a2 + b2 sqrt(q2)
            // Let q1 = s * s * q
            // Let q2 = t * t * q
            // Then q3 = gcd(q1, q2) = u * u * q
            let q3 = self.q.gcd(&other.q);
            let s_over_u_squared = self.q / q3.clone();
            let t_over_u_squared = other.q / q3.clone();
            assert!(is_perfect_square(&s_over_u_squared));
            assert!(is_perfect_square(&t_over_u_squared));
            let s_over_u = s_over_u_squared.sqrt();
            let t_over_u = t_over_u_squared.sqrt();

            // ans = (a1 + a2) + [b1 * (s/u) + b2 * (t/u)] sqrt(q3)
            Self::new(self.a + other.a, self.b * s_over_u + other.b * t_over_u, q3)
        } else {
            panic!(
                "Cannot add: sqrt({}) and sqrt({}) are incompatible",
                &self.q, &other.q
            )
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
        if rhs.q == BigUint::zero() {
            let multiplier = rhs.a;
            Self::new(self.a * multiplier.clone(), self.b * multiplier, self.q)
        } else if self.q == BigUint::zero() {
            rhs * self
        } else if is_perfect_square(&(self.q.clone() * rhs.q.clone())) {
            // ans = [a1 + b1 sqrt(q1)] [a2 + b2 sqrt(q2)]
            // Let q1 = s * s * q
            // Let q2 = t * t * q
            // Then q3 = gcd(q1, q2) = u * u * q
            let q3 = self.q.gcd(&rhs.q);
            let s_over_u_squared = self.q / q3.clone();
            let t_over_u_squared = rhs.q / q3.clone();
            assert!(is_perfect_square(&s_over_u_squared));
            assert!(is_perfect_square(&t_over_u_squared));
            let s_over_u = s_over_u_squared.sqrt();
            let t_over_u = t_over_u_squared.sqrt();

            // ans = [a1 + b1 * s/u * sqrt(q3)] [a2 + b2 * t/u * sqrt(q3)]
            //     = [a1*a2   +   b1 * s/u * q3 * b2 * t/u] + [a1 * b2 * t/u   +   a2 * b1 * s/u] sqrt(q3)
            Self::new(
                self.a.clone() * rhs.a.clone()
                    + self.b.clone()
                        * rhs.b.clone()
                        * s_over_u.clone()
                        * q3.clone()
                        * t_over_u.clone(),
                self.a * rhs.b * t_over_u + rhs.a * self.b * s_over_u,
                q3,
            )
        } else {
            panic!(
                "Cannot add: sqrt({}) and sqrt({}) are incompatible",
                &self.q, &rhs.q
            )
        }
    }
}

impl APlusBSqrtQ {
    pub fn recip(self) -> Self {
        if self.q == BigUint::zero() {
            Self::new(
                BigFraction::new(1u8, 1u8) / self.a,
                BigFraction::zero(),
                BigUint::zero(),
            )
        } else {
            // ans = 1 / [a + b * sqrt(q)]
            //     = [a - b * sqrt(q)] / [a^2 - b^2 * q]
            let dividing_factor =
                self.a.clone() * self.a.clone() - self.b.clone() * self.b.clone() * self.q.clone();
            Self::new(
                self.a / dividing_factor.clone(),
                -self.b / dividing_factor,
                self.q,
            )
        }
    }
}

impl ops::Div for APlusBSqrtQ {
    type Output = Self;

    fn div(self, rhs: Self) -> Self::Output {
        self * rhs.recip()
    }
}

impl APlusBSqrtQ {
    pub fn is_positive(&self) -> bool {
        if self.q == BigUint::zero() {
            self.a > BigFraction::zero()
        } else if self.b > BigFraction::zero() {
            if self.a >= BigFraction::zero() {
                return true;
            }
            // We know that -a > 0
            // We want to check whether b * sqrt(q) > -a > 0
            self.b.clone() * self.b.clone() * self.q.clone() > self.a.clone() * self.a.clone()
        } else {
            // self.b is assumed to be non-zero
            // Thus, we know that self.b < 0

            // We know that (-b) * sqrt(q) > 0
            // We want to check whether a + b * sqrt(q) > 0
            // Thus, we want to know whether a > (-b) * sqrt(q) > 0

            // We first need to verify that a is indeed greater than 0
            if self.a <= BigFraction::zero() {
                return false;
            }

            self.a.clone() * self.a.clone() >  self.b.clone() * self.b.clone() * self.q.clone()
        }
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
    assert_eq!(silver, silver2)
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
    )
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

    assert!(fourteen_minus_root_195.is_positive())
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
    )
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
    )
}
