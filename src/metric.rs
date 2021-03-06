// Copyright (c) 2016-2019 Rouven Spreckels <n3vu0r@qu1x.org>
//
// Usage of the works is permitted provided that
// this instrument is retained with the works, so that
// any entity that uses the works is notified of this instrument.
//
// DISCLAIMER: THE WORKS ARE WITHOUT WARRANTY.

use err_derive::Error;

use std::convert::TryFrom;

use std::result;

use std::fmt;
use std::fmt::{Display, Formatter};

use std::cmp::Ordering;

/// An error arising from this module's `TryFrom` trait implementation for its
/// `Signifix` type.
#[derive(Debug, Copy, Clone, PartialEq, Error)]
pub enum Error {
	/// The given number is below the lower bound `±1.000 y` (`= ±1E-24`) of the
	/// lowermost metric prefix yocto (`y = 1E-24`).
	#[error(display =
		"Out of lower bound ±1.000 y (= ±1E-24) for number {:.3E}", _0)]
	OutOfLowerBound(f64),
	/// The given number is above the upper bound `±999.9 Y` (`≈ ±1E+27`) of the
	/// uppermost metric prefix yotta (`Y = 1E+24`).
	#[error(display =
		"Out of upper bound ±999.9 Y (≈ ±1E+27) for number {:.3E}", _0)]
	OutOfUpperBound(f64),
	/// The given number is actually not a number (NaN).
	#[error(display = "Not a number (NaN)")]
	Nan,
}

impl Eq for Error {}

/// The canonical `Result` type using this module's `Error` type.
pub type Result<T> = result::Result<T, Error>;

/// Intermediate implementor type of this module's `TryFrom` and `Display` trait
/// implementations. Former tries to convert a given number into this type by
/// determining the appropriate metric prefix, the normalized significand, and
/// the decimal mark position while latter uses this type's fields to format the
/// number as a string of four significant figures inclusive the metric prefix
/// symbol.
///
/// Interpreted formatting parameters are
///
///   * `#` to indicate the alternate notation,
///   * `+` to prefix positive numbers with a plus sign,
///   * `fill`, `alignment`, and `width` to pad or align numbers.
#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct Signifix {
	number: super::Signifix
}

/// Number of characters in default notation when no sign is prefixed.
pub const DEF_MIN_LEN: usize = 7;

/// Number of characters in default notation when a sign is prefixed.
pub const DEF_MAX_LEN: usize = 8;

/// Number of characters in alternate notation when no sign is prefixed.
pub const ALT_MIN_LEN: usize = 5;

/// Number of characters in alternate notation when a sign is prefixed.
pub const ALT_MAX_LEN: usize = 6;

/// Metric prefix symbols from `Some("y")` to `Some("m")` indexed from `0` to
/// `7` and from `Some("k")` to `Some("Y")` indexed from `9` to `16`, or `None`
/// indexed at `8`.
pub const SYMBOLS: [Option<&str>; 17] = [
	Some("y"), Some("z"), Some("a"), Some("f"),
	Some("p"), Some("n"), Some("µ"), Some("m"),
	None,
	Some("k"), Some("M"), Some("G"), Some("T"),
	Some("P"), Some("E"), Some("Z"), Some("Y"),
];

/// Metric prefix factors from `1E-24` to `1E-03` indexed from `0` to `7` and
/// from `1E+03` to `1E+24` indexed from `9` to `16`, or `1E+00` indexed at `8`.
pub const FACTORS: [f64; 17] = [
	1E-24, 1E-21, 1E-18, 1E-15,
	1E-12, 1E-09, 1E-06, 1E-03,
	1E+00,
	1E+03, 1E+06, 1E+09, 1E+12,
	1E+15, 1E+18, 1E+21, 1E+24,
];

impl Signifix {
	/// Signed significand normalized from `±1.000` to `±999.9`.
	pub fn significand(&self) -> f64 {
		self.number.significand()
	}

	/// Signed significand numerator from `±1 000` to `±9 999`.
	pub fn numerator(&self) -> i32 {
		self.number.numerator()
	}

	/// Significand denominator of either `10`, `100`, or `1 000`.
	pub fn denominator(&self) -> i32 {
		self.number.denominator()
	}

	/// Exponent of significand denominator of either `1`, `2`, or `3`.
	pub fn exponent(&self) -> usize {
		self.number.exponent()
	}

	/// Signed integer part of significand from `±1` to `±999`.
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

	/// Metric prefix as `NAMES`, `SYMBOLS`, and `FACTORS` array index from `0`
	/// to `16`.
	pub fn prefix(&self) -> usize {
		self.number.prefix()
	}

	/// Symbol of metric prefix from `Some("y")` to `Some("Y")`, or `None`.
	pub fn symbol(&self) -> Option<&str> {
		SYMBOLS[self.prefix()]
	}

	/// Factor of metric prefix from `1E-24` to `1E+24`, or `1E+00`.
	pub fn factor(&self) -> f64 {
		FACTORS[self.prefix()]
	}

	/// Format trait implementation allowing explicit localization.
	///
	/// Until there is a recommended and possibly implicit localization system
	/// for Rust, explicit localization can be achieved by wrapping the
	/// `Signifix` type into a locale-sensitive newtype which implements the
	/// `Display` trait via this method. Used by this type's `Display` trait
	/// implementation with a decimal point as `decimal_mark`. The
	/// `decimal_mark` must be of a single character.
	pub fn fmt(&self, f: &mut Formatter,
		decimal_mark: &str)
	-> fmt::Result {
		debug_assert_eq!(decimal_mark.chars().count(), 1);
		let sign = if self.numerator().is_negative() { "-" } else
			if f.sign_plus() { "+" } else { "" };
		let (integer, fractional) = self.parts();
		if f.alternate() {
			let symbol = self.symbol().unwrap_or("#");
			f.pad(&format!("{}{}{}{:04$}",
				sign, integer.abs(), symbol, fractional,
				self.exponent()))
		} else {
			let symbol = self.symbol().unwrap_or(" ");
			f.pad(&format!("{}{}{}{:05$} {}",
				sign, integer.abs(), decimal_mark, fractional, symbol,
				self.exponent()))
		}
	}
}

impl Display for Signifix {
	fn fmt(&self, f: &mut Formatter) -> fmt::Result {
		self.fmt(f, ".")
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
			let prefix = match FACTORS[1..].binary_search_by(|factor|
				factor.partial_cmp(&number).unwrap_or(Ordering::Less)
			) { Ok(prefix) => prefix, Err(prefix) => prefix };
			(number * FACTORS[FACTORS.len() - 1 - prefix], prefix)
		};
		let scaled = |pow: f64| (numerator * pow).round();
		let signed = |abs: f64| if number.is_sign_negative()
			{ -abs } else { abs };
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

#[cfg(test)]
mod tests {
	use super::*;
	use std::f64;
	use std::mem::size_of;

	fn fmt(number: f64) -> Result<(String, String)> {
		Signifix::try_from(number).map(|number| (
			format!("{}",   number),
			format!("{:#}", number),
		))
	}
	fn pos(number: f64) -> Result<(String, String)> {
		Signifix::try_from(number).map(|number| (
			format!("{:+}",  number),
			format!("{:+#}", number),
		))
	}
	fn pad(number: f64) -> Result<(String, String)> {
		Signifix::try_from(number).map(|number| (
			format!("{:>1$}",  number, DEF_MAX_LEN),
			format!("{:>#1$}", number, ALT_MAX_LEN),
		))
	}

	#[test]
	fn factors_to_symbols() {
		assert_eq!(fmt(1E-24), Ok(("1.000 y".into(), "1y000".into())));
		assert_eq!(fmt(1E-21), Ok(("1.000 z".into(), "1z000".into())));
		assert_eq!(fmt(1E-18), Ok(("1.000 a".into(), "1a000".into())));
		assert_eq!(fmt(1E-15), Ok(("1.000 f".into(), "1f000".into())));
		assert_eq!(fmt(1E-12), Ok(("1.000 p".into(), "1p000".into())));
		assert_eq!(fmt(1E-09), Ok(("1.000 n".into(), "1n000".into())));
		assert_eq!(fmt(1E-06), Ok(("1.000 µ".into(), "1µ000".into())));
		assert_eq!(fmt(1E-03), Ok(("1.000 m".into(), "1m000".into())));
		assert_eq!(fmt(1E+00), Ok(("1.000  ".into(), "1#000".into())));
		assert_eq!(fmt(1E+03), Ok(("1.000 k".into(), "1k000".into())));
		assert_eq!(fmt(1E+06), Ok(("1.000 M".into(), "1M000".into())));
		assert_eq!(fmt(1E+09), Ok(("1.000 G".into(), "1G000".into())));
		assert_eq!(fmt(1E+12), Ok(("1.000 T".into(), "1T000".into())));
		assert_eq!(fmt(1E+15), Ok(("1.000 P".into(), "1P000".into())));
		assert_eq!(fmt(1E+18), Ok(("1.000 E".into(), "1E000".into())));
		assert_eq!(fmt(1E+21), Ok(("1.000 Z".into(), "1Z000".into())));
		assert_eq!(fmt(1E+24), Ok(("1.000 Y".into(), "1Y000".into())));
	}
	#[test]
	fn fixed_significance() {
		assert_eq!(fmt(1.000E+02), Ok(("100.0  ".into(), "100#0".into())));
		assert_eq!(fmt(1.234E+02), Ok(("123.4  ".into(), "123#4".into())));
		assert_eq!(fmt(1.000E+03), Ok(("1.000 k".into(), "1k000".into())));
		assert_eq!(fmt(1.234E+03), Ok(("1.234 k".into(), "1k234".into())));
		assert_eq!(fmt(1.000E+04), Ok(("10.00 k".into(), "10k00".into())));
		assert_eq!(fmt(1.234E+04), Ok(("12.34 k".into(), "12k34".into())));
		assert_eq!(fmt(1.000E+05), Ok(("100.0 k".into(), "100k0".into())));
		assert_eq!(fmt(1.234E+05), Ok(("123.4 k".into(), "123k4".into())));
		assert_eq!(fmt(1.000E+06), Ok(("1.000 M".into(), "1M000".into())));
		assert_eq!(fmt(1.234E+06), Ok(("1.234 M".into(), "1M234".into())));
	}
	#[test]
	fn formatting_options() {
		assert_eq!(fmt(-1E+00), Ok(("-1.000  ".into(), "-1#000".into())));
		assert_eq!(fmt( 1E+00), Ok(( "1.000  ".into(),  "1#000".into())));
		assert_eq!(pos(-1E+00), Ok(("-1.000  ".into(), "-1#000".into())));
		assert_eq!(pos( 1E+00), Ok(("+1.000  ".into(), "+1#000".into())));
		assert_eq!(pad(-1E+00), Ok(("-1.000  ".into(), "-1#000".into())));
		assert_eq!(pad( 1E+00), Ok((" 1.000  ".into(), " 1#000".into())));
	}
	#[test]
	fn lower_prefix_bound() {
		assert_eq!(fmt(-0.999_50E-24),
			Ok(("-1.000 y".into(), "-1y000".into())));
		assert_eq!(fmt(-0.999_49E-24),
			Err(Error::OutOfLowerBound(-0.999_49E-24)));
	}
	#[test]
	fn upper_prefix_bound() {
		assert_eq!(fmt(-999.949E+24),
			Ok(("-999.9 Y".into(), "-999Y9".into())));
		assert_eq!(fmt(-999.950E+24),
			Err(Error::OutOfUpperBound(-999.950E+24)));
	}
	#[test]
	fn upper_prefix_round() {
		assert_eq!(fmt(999.949_999_999_999_8E+00),
			Ok(("999.9  ".into(), "999#9".into())));
		assert_eq!(fmt(999.949_999_999_999_9E+00),
			Ok(("1.000 k".into(), "1k000".into())));
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
		assert!(Signifix::try_from(1E+03).unwrap()
			< Signifix::try_from(1E+06).unwrap());
		assert!(Signifix::try_from(1E+01).unwrap()
			< Signifix::try_from(1E+02).unwrap());
		assert!(Signifix::try_from(1E+03).unwrap()
			< Signifix::try_from(2E+03).unwrap());
	}
	#[test]
	fn mem_size_of_struct() {
		assert_eq!(size_of::<Signifix>(), 4);
	}
}
