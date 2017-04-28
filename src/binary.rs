// Copyright (c) 2016, 2017 Rouven Spreckels <n3vu0r@qu1x.org>
//
// Usage of the works is permitted provided that
// this instrument is retained with the works, so that
// any entity that uses the works is notified of this instrument.
//
// DISCLAIMER: THE WORKS ARE WITHOUT WARRANTY.

use std::convert::TryFrom;

use std::result;
use std::error;

use std::fmt;
use std::fmt::{Display, Formatter};

/// An error arising from this module's `TryFrom` trait implementation for its
/// `Signifix` type.
#[derive(Debug, Copy, Clone, PartialEq)]
pub enum Error {
	/// The given number is below the lower bound `±1.000` (`= ±1 024 ^ 0`).
	OutOfLowerBound(f64),

	/// The given number is above the upper bound `±1 023 Yi` (`≈ ±1 024 ^ 9`)
	/// of the uppermost binary prefix yobi (`Yi = 1 024 ^ 8`).
	OutOfUpperBound(f64),

	/// The given number is actually not a number (NaN).
	Nan,
}

impl Eq for Error {}

impl Display for Error {
	fn fmt(&self, f: &mut Formatter) -> fmt::Result {
		match *self {
			Error::OutOfLowerBound(number) =>
				write!(f, "{} for number {:.3E}",
					error::Error::description(self), number),
			Error::OutOfUpperBound(number) =>
				write!(f, "{} for number {:.3E}",
					error::Error::description(self), number),
			Error::Nan =>
				write!(f, "{}",
					error::Error::description(self)),
		}
	}
}

impl error::Error for Error {
	fn description(&self) -> &str {
		match *self {
			Error::OutOfLowerBound(..) =>
				"Out of lower bound ±1.000 (= ±1 024 ^ 0)",
			Error::OutOfUpperBound(..) =>
				"Out of upper bound ±1 023 Yi (≈ ±1 024 ^ 9)",
			Error::Nan =>
				"Not a Number (NaN)",
		}
	}
	fn cause(&self) -> Option<&error::Error> {
		match *self {
			Error::OutOfLowerBound(..) => None,
			Error::OutOfUpperBound(..) => None,
			Error::Nan => None,
		}
	}
}

/// The canonical `Result` type using this module's `Error` type.
pub type Result<T> = result::Result<T, Error>;

/// Intermediate implementor type of this module's `TryFrom` and `Display` trait
/// implementations. Former tries to convert a given number to this type by
/// determining the appropriate binary prefix, the normalized significand, and
/// the decimal mark position while latter uses this type's fields to format the
/// number to a string of four significant figures inclusive the binary prefix
/// symbol.
///
/// Interpreted formatting parameters are
///
///   * `+` to prefix positive numbers with a plus sign,
///   * `fill`, `alignment`, and `width` to pad or align numbers.
#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct Signifix {
	number: super::Signifix
}

/// Number of characters in default notation when no sign is prefixed.
pub const DEF_MIN_LEN: usize = 8;

/// Number of characters in default notation when a sign is prefixed.
pub const DEF_MAX_LEN: usize = 9;

/// Binary prefix symbols from `Some("Ki")` to `Some("Yi")` indexed from `1` to
/// `8`, or `None` indexed at `0`.
pub const SYMBOLS: [Option<&str>; 9] = [
	None,
	Some("Ki"), Some("Mi"), Some("Gi"), Some("Ti"),
	Some("Pi"), Some("Ei"), Some("Zi"), Some("Yi"),
];

/// Binary prefix factors from `1 024 ^ 1` to `1 024 ^ 8` indexed from `1` to
/// `8`, or `1 024 ^ 0` indexed at `0`.
pub const FACTORS: [f64; 9] = [
	(1u128 << 00) as f64,
	(1u128 << 10) as f64, (1u128 << 20) as f64,
	(1u128 << 30) as f64, (1u128 << 40) as f64,
	(1u128 << 50) as f64, (1u128 << 60) as f64,
	(1u128 << 70) as f64, (1u128 << 80) as f64,
];

impl Signifix {
	/// Signed significand normalized from `±1.000` over `±999.9` to `±1 023`.
	pub fn significand(&self) -> f64 {
		self.number.significand()
	}

	/// Signed significand numerator from `±1 000` to `±9 999`.
	pub fn numerator(&self) -> i32 {
		self.number.numerator()
	}

	/// Significand denominator of either `1`, `10`, `100`, or `1 000`.
	pub fn denominator(&self) -> i32 {
		self.number.denominator()
	}

	/// Exponent of significand denominator of either `0`, `1`, `2`, or `3`.
	pub fn exponent(&self) -> usize {
		self.number.exponent()
	}

	/// Signed integer part of significand from `±1` to `±1 023`.
	pub fn integer(&self) -> i32 {
		self.number.integer()
	}

	/// Fractional part of significand from `0` to `999`.
	pub fn fractional(&self) -> i32 {
		self.number.fractional()
	}

	/// Signed integer and fractional part at once, in given order.
	pub fn parts(&self) -> (i32, i32) {
		self.number.parts()
	}

	/// Binary prefix as `SYMBOLS` and `FACTORS` array index from `0` to `8`.
	pub fn prefix(&self) -> usize {
		self.number.prefix()
	}

	/// Symbol of binary prefix from `Some("Ki")` to `Some("Yi")`, or `None`.
	pub fn symbol(&self) -> Option<&str> {
		SYMBOLS[self.prefix()]
	}

	/// Factor of binary prefix from `1 024 ^ 1` to `1 024 ^ 8`, or `1 024 ^ 0`.
	pub fn factor(&self) -> f64 {
		FACTORS[self.prefix()]
	}
}

try_from! { i8, i16, i32, i64, i128, isize }
try_from! { u8, u16, u32, u64, u128, usize }

try_from! { f32 }

impl TryFrom<f64> for Signifix {
	type Error = Error;

	fn try_from(number: f64) -> Result<Self> {
		let (numerator, prefix) = {
			let number = number.abs();
			if number < FACTORS[1] {
				(number, 0)
			} else {
				let prefix = if number < FACTORS[5] {
					if number < FACTORS[3] {
						if number < FACTORS[2] { 1 } else { 2 }
					} else {
						if number < FACTORS[4] { 3 } else { 4 }
					}
				} else {
					if number < FACTORS[7] {
						if number < FACTORS[6] { 5 } else { 6 }
					} else {
						if number < FACTORS[8] { 7 } else { 8 }
					}
				};
				(number / FACTORS[prefix], prefix)
			}
		};
		let scaled = |pow: f64| {
			(numerator * pow).round()
		};
		let signed = |abs: f64| {
			if number.is_sign_negative() { -abs } else { abs }
		};
		let middle = scaled(1E+02);
		if middle < 1E+04 {
			let lower = scaled(1E+03);
			if lower < 1E+04 {
				if lower < 1E+03 {
					Err(Error::OutOfLowerBound(number))
				} else {
					Ok(Self {
						number: super::Signifix {
							numerator: signed(lower) as i16,
							exponent: 3,
							prefix: prefix as u8,
						}
					})
				}
			} else {
				Ok(Self {
					number: super::Signifix {
						numerator: signed(middle) as i16,
						exponent: 2,
						prefix: prefix as u8,
					}
				})
			}
		} else {
			let upper = scaled(1E+01);
			if upper < 1E+04 {
				Ok(Self {
					number: super::Signifix {
						numerator: signed(upper) as i16,
						exponent: 1,
						prefix: prefix as u8,
					}
				})
			} else {
				let above = numerator.round();
				if above < 1.024E+03 {
					Ok(Self {
						number: super::Signifix {
							numerator: signed(above) as i16,
							exponent: 0,
							prefix: prefix as u8,
						}
					})
				} else {
					let prefix = prefix + 1;
					if prefix < FACTORS.len() {
						Ok(Self {
							number: super::Signifix {
								numerator: signed(1E+03) as i16,
								exponent: 3,
								prefix: prefix as u8,
							}
						})
					} else {
						if number.is_nan() {
							Err(Error::Nan)
						} else {
							Err(Error::OutOfUpperBound(number))
						}
					}
				}
			}
		}
	}
}

impl Display for Signifix {
	fn fmt(&self, f: &mut Formatter) -> fmt::Result {
		let sign = if self.numerator().is_negative() { "-" } else
			if f.sign_plus() { "+" } else { "" };
		let symbol = self.symbol().unwrap_or("  ".into());
		if self.exponent() == 0 {
			f.pad(&format!("{}1 {:03} {}",
				sign, self.numerator().abs() - 1_000, symbol))
		} else {
			f.pad(&format!("{}{:.*} {}",
				sign, self.exponent(), self.significand().abs(), symbol))
		}
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	use std::f64;
	use std::mem::size_of;

	fn fmt(number: f64) -> Result<String> {
		Signifix::try_from(number).map(|number| format!("{}", number))
	}
	fn pos(number: f64) -> Result<String> {
		Signifix::try_from(number).map(|number| format!("{:+}", number))
	}
	fn pad(number: f64) -> Result<String> {
		Signifix::try_from(number)
			.map(|number| format!("{:>1$}", number, DEF_MAX_LEN))
	}

	#[test]
	fn factors_to_symbols() {
		assert_eq!(fmt(1_024f64.powi(0)), Ok("1.000   ".into()));
		assert_eq!(fmt(1_024f64.powi(1)), Ok("1.000 Ki".into()));
		assert_eq!(fmt(1_024f64.powi(2)), Ok("1.000 Mi".into()));
		assert_eq!(fmt(1_024f64.powi(3)), Ok("1.000 Gi".into()));
		assert_eq!(fmt(1_024f64.powi(4)), Ok("1.000 Ti".into()));
		assert_eq!(fmt(1_024f64.powi(5)), Ok("1.000 Pi".into()));
		assert_eq!(fmt(1_024f64.powi(6)), Ok("1.000 Ei".into()));
		assert_eq!(fmt(1_024f64.powi(7)), Ok("1.000 Zi".into()));
		assert_eq!(fmt(1_024f64.powi(8)), Ok("1.000 Yi".into()));
	}
	#[test]
	fn fixed_significance() {
		assert_eq!(fmt(1_024f64.powi(0) * 100.0f64), Ok("100.0   ".into()));
		assert_eq!(fmt(1_024f64.powi(0) * 123.4f64), Ok("123.4   ".into()));
		assert_eq!(fmt(1_024f64.powi(0) * 1_000f64), Ok("1 000   ".into()));
		assert_eq!(fmt(1_024f64.powi(0) * 1_002f64), Ok("1 002   ".into()));
		assert_eq!(fmt(1_024f64.powi(0) * 1_023f64), Ok("1 023   ".into()));
		assert_eq!(fmt(1_024f64.powi(1) * 1.000f64), Ok("1.000 Ki".into()));
		assert_eq!(fmt(1_024f64.powi(1) * 1.234f64), Ok("1.234 Ki".into()));
		assert_eq!(fmt(1_024f64.powi(1) * 10.00f64), Ok("10.00 Ki".into()));
		assert_eq!(fmt(1_024f64.powi(1) * 12.34f64), Ok("12.34 Ki".into()));
		assert_eq!(fmt(1_024f64.powi(1) * 100.0f64), Ok("100.0 Ki".into()));
		assert_eq!(fmt(1_024f64.powi(1) * 123.4f64), Ok("123.4 Ki".into()));
		assert_eq!(fmt(1_024f64.powi(1) * 1_000f64), Ok("1 000 Ki".into()));
		assert_eq!(fmt(1_024f64.powi(1) * 1_002f64), Ok("1 002 Ki".into()));
		assert_eq!(fmt(1_024f64.powi(1) * 1_023f64), Ok("1 023 Ki".into()));
		assert_eq!(fmt(1_024f64.powi(2) * 1.000f64), Ok("1.000 Mi".into()));
		assert_eq!(fmt(1_024f64.powi(2) * 1.234f64), Ok("1.234 Mi".into()));
	}
	#[test]
	fn formatting_options() {
		assert_eq!(fmt(-1E+00), Ok("-1.000   ".into()));
		assert_eq!(fmt( 1E+00), Ok( "1.000   ".into()));
		assert_eq!(fmt(-1E+03), Ok("-1 000   ".into()));
		assert_eq!(fmt( 1E+03), Ok( "1 000   ".into()));
		assert_eq!(pos(-1E+00), Ok("-1.000   ".into()));
		assert_eq!(pos( 1E+00), Ok("+1.000   ".into()));
		assert_eq!(pos(-1E+03), Ok("-1 000   ".into()));
		assert_eq!(pos( 1E+03), Ok("+1 000   ".into()));
		assert_eq!(pad(-1E+00), Ok("-1.000   ".into()));
		assert_eq!(pad( 1E+00), Ok(" 1.000   ".into()));
		assert_eq!(pad(-1E+03), Ok("-1 000   ".into()));
		assert_eq!(pad( 1E+03), Ok(" 1 000   ".into()));
	}
	#[test]
	fn lower_prefix_bound() {
		assert_eq!(fmt(-0.999_50E+00),
			Ok("-1.000   ".into()));
		assert_eq!(fmt(-0.999_49E+00),
			Err(Error::OutOfLowerBound(-0.999_49E+00)));
	}
	#[test]
	fn upper_prefix_bound() {
		assert_eq!(fmt(-1_237.3E+24),
			Ok("-1 023 Yi".into()));
		assert_eq!(fmt(-1_237.4E+24),
			Err(Error::OutOfUpperBound(-1_237.4E+24)));
	}
	#[test]
	fn upper_prefix_round() {
		assert_eq!(fmt(1_023.499_999_999_999_94E+00), Ok("1 023   ".into()));
		assert_eq!(fmt(1_023.499_999_999_999_95E+00), Ok("1.000 Ki".into()));
	}
	#[test]
	fn fp_category_safety() {
		assert_eq!(fmt(0f64),
			Err(Error::OutOfLowerBound(0f64)));
		assert_eq!(fmt(f64::NEG_INFINITY),
			Err(Error::OutOfUpperBound(f64::NEG_INFINITY)));
		assert_eq!(fmt(f64::INFINITY),
			Err(Error::OutOfUpperBound(f64::INFINITY)));
		assert_eq!(fmt(f64::NAN),
			Err(Error::Nan));
	}
	#[test]
	fn ord_implementation() {
		assert!(Signifix::try_from(1_024f64.powi(1)).unwrap()
			< Signifix::try_from(1_024f64.powi(2)).unwrap());
		assert!(Signifix::try_from(1E+01).unwrap()
			< Signifix::try_from(1E+02).unwrap());
		assert!(Signifix::try_from(1E+02).unwrap()
			< Signifix::try_from(1E+03).unwrap());
		assert!(Signifix::try_from(1E+02).unwrap()
			< Signifix::try_from(2E+02).unwrap());
	}
	#[test]
	fn mem_size_of_struct() {
		assert_eq!(size_of::<Signifix>(), 4);
	}
}
