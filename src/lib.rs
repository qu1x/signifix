// This file is part of Signifix, see <https://qu1x.org/signifix>.
//
// Copyright (c) 2016, 2017 Rouven Spreckels <n3vu0r@qu1x.org>
//
// Signifix is free software: you can redistribute it and/or modify
// it under the terms of the GNU Lesser General Public License version 3
// as published by the Free Software Foundation on 29 June 2007.
//
// Signifix is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
// GNU Lesser General Public License for more details.
//
// You should have received a copy of the GNU Lesser General Public License
// along with Signifix. If not, see <https://www.gnu.org/licenses>.

//! Number Formatter of Fixed Significance with Metric Unit Prefix
//!
//! Signifix guarantees a fixed number of significant figures and a fixed number
//! of resulting characters by automatically choosing the metric unit prefix and
//! appropriately adjusting the decimal point position.
//!
//! # Usage
//!
//! This crate is [on crates.io](https://crates.io/crates/signifix) and can be
//! used by adding `signifix` to the dependencies in your project's
//! `Cargo.toml`:
//!
//! ```toml
//! [dependencies]
//! signifix = "0.3.1"
//! ```
//!
//! and this to your crate root:
//!
//! ```
//! #![feature(try_from)] // Until stabilized. Requires nightly Rust.
//!
//! extern crate signifix;
//! ```
//!
//! # Examples
//!
//! The fixed number of significant figures and resulting characters prevent the
//! digits and prefixed units from jumping to the left or right:
//!
//! ```
//! # #![feature(try_from)]
//! use std::convert::TryFrom; // Until stabilized.
//!
//! use signifix::{Signifix, Result};
//!
//! let format = |number| -> Result<String> {
//! 	Signifix::try_from(number).map(|number| format!("{}", number))
//! };
//!
//! assert_eq!(format(1e-04), Ok("100.0 µ".into()));
//! assert_eq!(format(1e-03), Ok("1.000 m".into()));
//! assert_eq!(format(1e-02), Ok("10.00 m".into()));
//! assert_eq!(format(1e-01), Ok("100.0 m".into()));
//! assert_eq!(format(1e+00), Ok("1.000  ".into()));
//! assert_eq!(format(1e+01), Ok("10.00  ".into()));
//! assert_eq!(format(1e+02), Ok("100.0  ".into()));
//! assert_eq!(format(1e+03), Ok("1.000 k".into()));
//! assert_eq!(format(1e+04), Ok("10.00 k".into()));
//! assert_eq!(format(1e+05), Ok("100.0 k".into()));
//! assert_eq!(format(1e+06), Ok("1.000 M".into()));
//! ```
//!
//! This is useful to smoothly refresh a transfer rate within a terminal:
//!
//! ```
//! #![feature(i128_type)] // Until stabilized.
//!
//! # #![feature(try_from)]
//! use std::convert::TryFrom; // Until stabilized.
//!
//! use std::f64;
//! use signifix::{Signifix, Error, MIN_LEN};
//!
//! let format_rate = |bytes: u128, nanoseconds: u128| -> String {
//! 	let bytes_per_second = bytes as f64 / nanoseconds as f64 * 1e+09;
//! 	let unit = "B/s";
//! 	let rate = match Signifix::try_from(bytes_per_second) {
//! 		Ok(rate) => if rate.factor() < 1e+00 {
//! 			" - slow - ".into() // instead of mB/s, µB/s, ...
//! 		} else {
//! 			format!("{}{}", rate, unit) // normal rate
//! 		},
//! 		Err(case) => match case {
//! 			Error::OutOfLowerBound(rate) => if rate == 0f64 {
//! 				" - idle - " // no progress at all
//! 			} else {
//! 				" - slow - " // almost no progress
//! 			},
//! 			Error::OutOfUpperBound(rate) => if rate == f64::INFINITY {
//! 				" - ---- - " // zero nanoseconds
//! 			} else {
//! 				" - fast - " // awkwardly fast
//! 			},
//! 			Error::Nan => " - ---- - ", // zero bytes in zero nanoseconds
//! 		}.into(),
//! 	};
//! 	assert_eq!(rate.chars().count(), MIN_LEN + unit.chars().count());
//! 	rate
//! };
//!
//! assert_eq!(format_rate(42_667, 300_000_000_000), "142.2  B/s");
//! assert_eq!(format_rate(42_667, 030_000_000_000), "1.422 kB/s");
//! assert_eq!(format_rate(42_667, 003_000_000_000), "14.22 kB/s");
//! assert_eq!(format_rate(00_001, 003_000_000_000), " - slow - ");
//! assert_eq!(format_rate(00_000, 003_000_000_000), " - idle - ");
//! assert_eq!(format_rate(42_667, 000_000_000_000), " - ---- - ");
//! ```
//!
//! Or to monitor a measured quantity like an electrical current including its
//! direction with an optional space placeholder to align with negative values:
//!
//! ```
//! # #![feature(try_from)]
//! use std::convert::TryFrom; // Until stabilized.
//!
//! use signifix::{Signifix, Result, Error};
//!
//! let format_load = |current| -> Result<String> {
//! 	if let Some(current) = current {
//! 		Signifix::try_from(current).map(|c| format!("{:#}A", c))
//! 	} else {
//! 		Ok("     0  A".into())
//! 	}
//! };
//!
//! assert_eq!(format_load(Some( 1.476e-06)), Ok(" 1.476 µA".into()));
//! assert_eq!(format_load(None),             Ok("     0  A".into()));
//! assert_eq!(format_load(Some(-2.927e-06)), Ok("-2.927 µA".into()));
//! ```
//!
//! In case of displaying a file size difference after modification, a plus sign
//! might be preferred for positive values:
//!
//! ```
//! # #![feature(try_from)]
//! use std::convert::TryFrom; // Until stabilized.
//!
//! use signifix::{Signifix, Result, Error};
//!
//! let format_diff = |curr, prev| -> Result<String> {
//! 	Signifix::try_from(curr - prev).map(|diff| format!("{:+}B", diff))
//! 		.or_else(|e| if e == Error::OutOfLowerBound(0f64)
//! 			{ Ok("     0  B".into()) } else { Err(e) })
//! };
//!
//! assert_eq!(format_diff(78_346, 57_393), Ok("+20.95 kB".into()));
//! assert_eq!(format_diff(93_837, 93_837), Ok("     0  B".into()));
//! assert_eq!(format_diff(27_473, 46_839), Ok("-19.37 kB".into()));
//! ```

#![deny(missing_docs)]

#![feature(i128_type)]
#![feature(try_from)]

use std::convert::TryFrom;

use std::result;
use std::error;

use std::fmt;
use fmt::{Display, Formatter};

use std::cmp::Ordering;
use Ordering::Equal;

/// An error arising from this crate's `TryFrom` trait implementation for its
/// `Signifix` type.
#[derive(Debug, Copy, Clone, PartialEq)]
pub enum Error {
	/// The given number is below the lower bound ±1.000 y (= ±1e-24) of the
	/// lowermost metric unit prefix yocto (y = 1e-24).
	OutOfLowerBound(f64),

	/// The given number is above the upper bound ±999.9 Y (≅ ±1e+27) of the
	/// uppermost metric unit prefix yotta (Y = 1e+24).
	OutOfUpperBound(f64),

	/// The given number is actually Not a Number (NaN).
	Nan,
}

impl Eq for Error {}

impl Display for Error {
	fn fmt(&self, f: &mut Formatter) -> fmt::Result {
		match *self {
			Error::OutOfLowerBound(number) =>
				write!(f, "{} for number {:+.3e}",
					error::Error::description(self), number),
			Error::OutOfUpperBound(number) =>
				write!(f, "{} for number {:+.3e}",
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
				"Out of lower bound ±1.000 y (= ±1e-24)",
			Error::OutOfUpperBound(..) =>
				"Out of upper bound ±999.9 Y (≅ ±1e+27)",
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

/// The canonical `Result` type using this crate's `Error` type.
pub type Result<T> = result::Result<T, Error>;

/// Intermediate implementor type of this crate's `TryFrom` and `Display` trait
/// implementations. Former tries to convert a number to this type by
/// automatically choosing the metric unit prefix and appropriately adjusting
/// the decimal point position while latter uses this type's fields to format
/// the number to a string of a fixed number of significant figures and a fixed
/// number of resulting characters. The format parameter `{}` prefixes negative
/// numbers with a minus sign. The variant `{:+}` additionally prefixes positive
/// numbers with a plus sign while the variant `{:#}` uses a whitespace instead
/// to align with negative numbers. Padding via fill/alignment formatting
/// parameters like `{:>8}` is supported as well.
#[derive(Debug, Copy, Clone, PartialEq)]
pub struct Signifix {
	numerator: i16,
	exponent: u8,
	prefix: u8,
}

impl Eq for Signifix {}

impl PartialOrd for Signifix {
	fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
		Some(self.cmp(other))
	}
}

impl Ord for Signifix {
	fn cmp(&self, other: &Self) -> Ordering {
		let mut ordering = self.prefix.cmp(&other.prefix);
		if ordering == Equal {
			ordering = other.exponent.cmp(&self.exponent);
			if ordering == Equal {
				ordering = self.numerator.cmp(&other.numerator)
			}
		}
		ordering
	}
}

/// Number of resulting characters when no sign or whitespace is prefixed.
pub const MIN_LEN: usize = 7;

/// Number of resulting characters when a sign or whitespace is prefixed.
pub const MAX_LEN: usize = 8;

/// Metric unit prefix symbols from y to Y indexed from 0 to 16.
pub const SYMBOL: [char; 17] = [
	'y', 'z', 'a', 'f', 'p', 'n', 'µ', 'm',
	' ',
	'k', 'M', 'G', 'T', 'P', 'E', 'Z', 'Y',
];

/// Metric unit prefix factors from 1e-24 to 1e+24 indexed from 0 to 16.
pub const FACTOR: [f64; 17] = [
	1e-24, 1e-21, 1e-18, 1e-15, 1e-12, 1e-09, 1e-06, 1e-03,
	1e+00,
	1e+03, 1e+06, 1e+09, 1e+12, 1e+15, 1e+18, 1e+21, 1e+24,
];

impl Signifix {
	/// Metrically normalized signed significand from ±1.000 to ±999.9.
	pub fn significand(&self) -> f64 {
		self.numerator() as f64 / self.denominator() as f64
	}

	/// Signed significand numerator from ±1,000 to ±9,999.
	pub fn numerator(&self) -> i32 {
		self.numerator.into()
	}

	/// Significand denominator of either 10, 100, or 1,000.
	pub fn denominator(&self) -> i32 {
		[1, 10, 100, 1_000][self.exponent()]
	}

	/// Exponent of significand denominator of either 1, 2, or 3.
	pub fn exponent(&self) -> usize {
		self.exponent.into()
	}

	/// Metric unit prefix as `SYMBOL` and `FACTOR` array index from 0 to 16.
	pub fn prefix(&self) -> usize {
		self.prefix.into()
	}

	/// Symbol of metric unit prefix from y to Y.
	pub fn symbol(&self) -> char {
		SYMBOL[self.prefix()]
	}

	/// Factor of metric unit prefix from 1e-24 to 1e+24.
	pub fn factor(&self) -> f64 {
		FACTOR[self.prefix()]
	}
}

macro_rules! try_from {
	($($t:ty),*) => (
		$(
			impl TryFrom<$t> for Signifix {
				type Err = Error;

				fn try_from(number: $t) -> Result<Self> {
					Self::try_from(number as f64)
				}
			}
		)*
	);
}

try_from! { i8, i16, i32, i64, i128, isize }
try_from! { u8, u16, u32, u64, u128, usize }

try_from! { f32 }

impl TryFrom<f64> for Signifix {
	type Err = Error;

	fn try_from(number: f64) -> Result<Self> {
		let (numerator, prefix) = {
			let number = number.abs();
			if number < FACTOR[08] {
				let prefix = if number < FACTOR[04] {
					if number < FACTOR[02] {
						if number < FACTOR[01] { 00 } else { 01 }
					} else {
						if number < FACTOR[03] { 02 } else { 03 }
					}
				} else {
					if number < FACTOR[06] {
						if number < FACTOR[05] { 04 } else { 05 }
					} else {
						if number < FACTOR[07] { 06 } else { 07 }
					}
				};
				(number / FACTOR[prefix], prefix)
			} else
			if number < FACTOR[09] {
				(number, 08)
			} else {
				let prefix = if number < FACTOR[13] {
					if number < FACTOR[11] {
						if number < FACTOR[10] { 09 } else { 10 }
					} else {
						if number < FACTOR[12] { 11 } else { 12 }
					}
				} else {
					if number < FACTOR[15] {
						if number < FACTOR[14] { 13 } else { 14 }
					} else {
						if number < FACTOR[16] { 15 } else { 16 }
					}
				};
				(number / FACTOR[prefix], prefix)
			}
		};
		let scaled = |pow: f64| {
			(numerator * pow).round()
		};
		let signed = |abs: f64| {
			if number.is_sign_negative() { -abs } else { abs }
		};
		let middle = scaled(1e+02);
		if middle < 1e+04 {
			let lower = scaled(1e+03);
			if lower < 1e+04 {
				if lower < 1e+03 {
					Err(Error::OutOfLowerBound(number))
				} else {
					Ok(Signifix {
						numerator: signed(lower) as i16,
						exponent: 3,
						prefix: prefix as u8,
					})
				}
			} else {
				Ok(Signifix {
					numerator: signed(middle) as i16,
					exponent: 2,
					prefix: prefix as u8,
				})
			}
		} else {
			let upper = scaled(1e+01);
			if upper < 1e+04 {
				Ok(Signifix {
					numerator: signed(upper) as i16,
					exponent: 1,
					prefix: prefix as u8,
				})
			} else {
				let prefix = prefix + 1;
				if prefix < FACTOR.len() {
					Ok(Signifix {
						numerator: signed(1e+03) as i16,
						exponent: 3,
						prefix: prefix as u8,
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

impl Display for Signifix {
	fn fmt(&self, f: &mut Formatter) -> fmt::Result {
		if f.sign_plus() {
			f.pad(&format!("{:+.*} {}",
				self.exponent(), self.significand(), self.symbol()))
		} else
		if f.alternate() && self.numerator().is_positive() {
			f.pad(&format!(" {:.*} {}",
				self.exponent(), self.significand(), self.symbol()))
		} else {
			f.pad(&format!("{:.*} {}",
				self.exponent(), self.significand(), self.symbol()))
		}
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	use std::f64;
	use std::mem::size_of;

	fn def(number: f64) -> Result<String> {
		Signifix::try_from(number).map(|number| format!("{}", number))
	}
	fn pos(number: f64) -> Result<String> {
		Signifix::try_from(number).map(|number| format!("{:+}", number))
	}
	fn alt(number: f64) -> Result<String> {
		Signifix::try_from(number).map(|number| format!("{:#}", number))
	}

	#[test]
	fn metric_unit_prefix() {
		assert_eq!(def(1e-24), Ok("1.000 y".into()));
		assert_eq!(def(1e-21), Ok("1.000 z".into()));
		assert_eq!(def(1e-18), Ok("1.000 a".into()));
		assert_eq!(def(1e-15), Ok("1.000 f".into()));
		assert_eq!(def(1e-12), Ok("1.000 p".into()));
		assert_eq!(def(1e-09), Ok("1.000 n".into()));
		assert_eq!(def(1e-06), Ok("1.000 µ".into()));
		assert_eq!(def(1e-03), Ok("1.000 m".into()));
		assert_eq!(def(1e+00), Ok("1.000  ".into()));
		assert_eq!(def(1e+03), Ok("1.000 k".into()));
		assert_eq!(def(1e+06), Ok("1.000 M".into()));
		assert_eq!(def(1e+09), Ok("1.000 G".into()));
		assert_eq!(def(1e+12), Ok("1.000 T".into()));
		assert_eq!(def(1e+15), Ok("1.000 P".into()));
		assert_eq!(def(1e+18), Ok("1.000 E".into()));
		assert_eq!(def(1e+21), Ok("1.000 Z".into()));
		assert_eq!(def(1e+24), Ok("1.000 Y".into()));
	}
	#[test]
	fn fixed_significance() {
		assert_eq!(def(1.234e+02), Ok("123.4  ".into()));
		assert_eq!(def(1.234e+03), Ok("1.234 k".into()));
		assert_eq!(def(1.234e+04), Ok("12.34 k".into()));
		assert_eq!(def(1.234e+05), Ok("123.4 k".into()));
		assert_eq!(def(1.234e+06), Ok("1.234 M".into()));
	}
	#[test]
	fn formatting_options() {
		assert_eq!(def(-1e+00), Ok("-1.000  ".into()));
		assert_eq!(def( 1e+00), Ok( "1.000  ".into()));
		assert_eq!(pos(-1e+00), Ok("-1.000  ".into()));
		assert_eq!(pos( 1e+00), Ok("+1.000  ".into()));
		assert_eq!(alt(-1e+00), Ok("-1.000  ".into()));
		assert_eq!(alt( 1e+00), Ok(" 1.000  ".into()));
	}
	#[test]
	fn lower_prefix_bound() {
		assert_eq!(def(-0.99951e-24), Ok("-1.000 y".into()));
		assert_eq!(def(-0.99949e-24),
			Err(Error::OutOfLowerBound(-0.99949e-24)));
	}
	#[test]
	fn upper_prefix_bound() {
		assert_eq!(def(-0.999949e+27), Ok("-999.9 Y".into()));
		assert_eq!(def(-0.999951e+27),
			Err(Error::OutOfUpperBound(-0.999951e+27)));
	}
	#[test]
	fn upper_prefix_round() {
		assert_eq!(def(0.999949e+06), Ok("999.9 k".into()));
		assert_eq!(def(0.999951e+06), Ok("1.000 M".into()));
	}
	#[test]
	fn fp_category_safety() {
		assert_eq!(def(0f64),
			Err(Error::OutOfLowerBound(0f64)));
		assert_eq!(def(f64::NEG_INFINITY),
			Err(Error::OutOfUpperBound(f64::NEG_INFINITY)));
		assert_eq!(def(f64::INFINITY),
			Err(Error::OutOfUpperBound(f64::INFINITY)));
		assert_eq!(def(f64::NAN),
			Err(Error::Nan));
	}
	#[test]
	fn ord_implementation() {
		assert!(Signifix::try_from(1e+03).unwrap()
			< Signifix::try_from(1e+06).unwrap());
		assert!(Signifix::try_from(1e+01).unwrap()
			< Signifix::try_from(1e+02).unwrap());
		assert!(Signifix::try_from(1e+03).unwrap()
			< Signifix::try_from(2e+03).unwrap());
	}
	#[test]
	fn mem_size_of_struct() {
		assert_eq!(size_of::<Signifix>(), 4);
	}
}
