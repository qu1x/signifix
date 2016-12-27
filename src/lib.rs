// This file is part of Signifix, see <https://qu1x.org/signifix>.
//
// Copyright (c) 2016 Rouven Spreckels <n3vu0r@qu1x.org>
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

#![deny(missing_docs)]

//! Number Formatter of Fixed Significance with Metric Unit Prefix
//!
//! Signifix guarantees a fixed number of significant figures and a fixed number
//! of resulting characters by automatically choosing the metric unit prefix and
//! appropriately adjusting the floating point precision.
//!
//! # Usage
//!
//! This crate is [on crates.io](https://crates.io/crates/signifix) and can be
//! used by adding `signifix` to the dependencies in your project's
//! `Cargo.toml`:
//!
//! ```toml
//! [dependencies]
//! signifix = "0.2.0"
//! ```
//!
//! and this to your crate root:
//!
//! ```
//! #![feature(try_from)] // Until stabilized.
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
//! 	Ok(format!("{}", Signifix::try_from(number)?))
//! };
//!
//! assert_eq!(format(1e-04).ok(), Some("100.0 µ".into()));
//! assert_eq!(format(1e-03).ok(), Some("1.000 m".into()));
//! assert_eq!(format(1e-02).ok(), Some("10.00 m".into()));
//! assert_eq!(format(1e-01).ok(), Some("100.0 m".into()));
//! assert_eq!(format(1e+00).ok(), Some("1.000  ".into()));
//! assert_eq!(format(1e+01).ok(), Some("10.00  ".into()));
//! assert_eq!(format(1e+02).ok(), Some("100.0  ".into()));
//! assert_eq!(format(1e+03).ok(), Some("1.000 k".into()));
//! assert_eq!(format(1e+04).ok(), Some("10.00 k".into()));
//! assert_eq!(format(1e+05).ok(), Some("100.0 k".into()));
//! assert_eq!(format(1e+06).ok(), Some("1.000 M".into()));
//! ```
//!
//! This is useful to smoothly refresh a transfer rate inside a terminal:
//!
//! ```
//! # #![feature(try_from)]
//! use std::convert::TryFrom; // Until stabilized.
//!
//! use signifix::{Signifix, Result};
//!
//! let format_rate = |bytes, seconds| -> Result<String> {
//! 	Ok(format!("{}B/s", Signifix::try_from(bytes as f64 / seconds as f64)?))
//! };
//!
//! assert_eq!(format_rate(42_667, 300).ok(), Some("142.2  B/s".into()));
//! assert_eq!(format_rate(42_667,  30).ok(), Some("1.422 kB/s".into()));
//! assert_eq!(format_rate(42_667,   3).ok(), Some("14.22 kB/s".into()));
//! ```
//!
//! Or to monitor a measured quantity like an electrical current including its
//! direction with an optional space placeholder to align with negative values.
//!
//! ```
//! # #![feature(try_from)]
//! use std::convert::TryFrom; // Until stabilized.
//!
//! use signifix::{Signifix, Result};
//!
//! let format_load = |current| -> Result<String> {
//! 	Ok(format!("{:#}A", Signifix::try_from(current)?))
//! };
//!
//! assert_eq!(format_load( 1.476e-06).ok(), Some(" 1.476 µA".into()));
//! assert_eq!(format_load(-2.927e-06).ok(), Some("-2.927 µA".into()));
//! ```
//!
//! In case of displaying a file size difference after modification, a plus sign
//! might be preferred for positive values:
//!
//! ```
//! # #![feature(try_from)]
//! use std::convert::TryFrom; // Until stabilized.
//!
//! use signifix::{Signifix, Result};
//!
//! let format_diff = |curr, prev| -> Result<String> {
//! 	Ok(format!("{:+}B", Signifix::try_from(curr - prev)?))
//! };
//!
//! assert_eq!(format_diff(78_346, 57_393).ok(), Some("+20.95 kB".into()));
//! assert_eq!(format_diff(27_473, 46_839).ok(), Some("-19.37 kB".into()));
//! ```

#![feature(try_from)]
use std::convert::TryFrom;

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

impl std::fmt::Display for Error {
	fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
		use std::error::Error;
		match *self {
			::Error::OutOfLowerBound(number) =>
				write!(f, "{} for number {:+.3e}", self.description(), number),
			::Error::OutOfUpperBound(number) =>
				write!(f, "{} for number {:+.3e}", self.description(), number),
			::Error::Nan =>
				write!(f, "{}", self.description()),
		}
	}
}

impl std::error::Error for Error {
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
	fn cause(&self) -> Option<&std::error::Error> {
		match *self {
			Error::OutOfLowerBound(..) => None,
			Error::OutOfUpperBound(..) => None,
			Error::Nan => None,
		}
	}
}

/// The canonical `Result` type using this crate's `Error` type.
pub type Result<T> = std::result::Result<T, Error>;

/// Intermediate implementor type of this crate's `TryFrom` and `Display` trait
/// implementations. Former tries to convert a number to this type by
/// automatically choosing the metric unit prefix and appropriately adjusting
/// the floating point precision while latter uses this type's fields to format
/// the number to a string of a fixed number of significant figures and a fixed
/// number of resulting characters. The format parameter `{}` prefixes negative
/// numbers with a minus sign. The variant `{:+}` additionally prefixes positive
/// numbers with a plus sign while the variant `{:#}` uses a whitespace instead
/// to align with negative numbers.
#[derive(Debug, Copy, Clone, PartialEq)]
pub struct Signifix {
	/// Automatically chosen metric unit prefix ranging from y to Y.
	pub prefix: char,
	/// Appropriately adjusted floating point precision ranging from 1 to 3.
	pub precision: usize,
	/// Metrically normalized signed significand ranging from ±1.000 to ±999.9.
	pub significand: f64,
}

impl Eq for Signifix {}

/// Number of resulting characters when no sign or whitespace is prefixed.
pub const MINLEN: usize = 7;

/// Number of resulting characters when a sign or whitespace is prefixed.
pub const MAXLEN: usize = 8;

/// Metric unit prefix factors from 1e-24 to 1e+24 indexed from 0 to 16.
pub const FACTOR: [f64; 17] = [
	1e-24, 1e-21, 1e-18, 1e-15, 1e-12, 1e-09, 1e-06, 1e-03,
	1e+00,
	1e+03, 1e+06, 1e+09, 1e+12, 1e+15, 1e+18, 1e+21, 1e+24,
];

/// Metric unit prefix symbols from y to Y indexed from 0 to 16.
pub const SYMBOL: [char; 17] = [
	'y', 'z', 'a', 'f', 'p', 'n', 'µ', 'm',
	' ',
	'k', 'M', 'G', 'T', 'P', 'E', 'Z', 'Y',
];

impl TryFrom<i8> for Signifix {
	type Err = Error;
	fn try_from(number: i8) -> Result<Self> { Self::try_from(number as f64) }
}

impl TryFrom<i16> for Signifix {
	type Err = Error;
	fn try_from(number: i16) -> Result<Self> { Self::try_from(number as f64) }
}

impl TryFrom<i32> for Signifix {
	type Err = Error;
	fn try_from(number: i32) -> Result<Self> { Self::try_from(number as f64) }
}

impl TryFrom<i64> for Signifix {
	type Err = Error;
	fn try_from(number: i64) -> Result<Self> { Self::try_from(number as f64) }
}

impl TryFrom<u8> for Signifix {
	type Err = Error;
	fn try_from(number: u8) -> Result<Self> { Self::try_from(number as f64) }
}

impl TryFrom<u16> for Signifix {
	type Err = Error;
	fn try_from(number: u16) -> Result<Self> { Self::try_from(number as f64) }
}

impl TryFrom<u32> for Signifix {
	type Err = Error;
	fn try_from(number: u32) -> Result<Self> { Self::try_from(number as f64) }
}

impl TryFrom<u64> for Signifix {
	type Err = Error;
	fn try_from(number: u64) -> Result<Self> { Self::try_from(number as f64) }
}

impl TryFrom<isize> for Signifix {
	type Err = Error;
	fn try_from(number: isize) -> Result<Self> { Self::try_from(number as f64) }
}

impl TryFrom<usize> for Signifix {
	type Err = Error;
	fn try_from(number: usize) -> Result<Self> { Self::try_from(number as f64) }
}

impl TryFrom<f32> for Signifix {
	type Err = Error;
	fn try_from(number: f32) -> Result<Self> { Self::try_from(number as f64) }
}

impl TryFrom<f64> for Signifix {
	type Err = Error;
	fn try_from(number: f64) -> Result<Self> {
		let (significand, prefix) = {
			let number = number.abs();
			if number < FACTOR[8] {
				let prefix = if number < FACTOR[4] {
					if number < FACTOR[2] {
						if number < FACTOR[1] { 0 } else { 1 }
					} else {
						if number < FACTOR[3] { 2 } else { 3 }
					}
				} else {
					if number < FACTOR[6] {
						if number < FACTOR[5] { 4 } else { 5 }
					} else {
						if number < FACTOR[7] { 6 } else { 7 }
					}
				};
				(number / FACTOR[prefix], prefix)
			} else
			if number < FACTOR[9] {
				(number, 8)
			} else {
				let prefix = if number < FACTOR[13] {
					if number < FACTOR[11] {
						if number < FACTOR[10] { 9 } else { 10 }
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
		let scaled = |pow: f64| { (significand * pow).round() };
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
						prefix: SYMBOL[prefix],
						precision: 3,
						significand: signed(lower / 1e+03),
					})
				}
			} else {
				Ok(Signifix {
					prefix: SYMBOL[prefix],
					precision: 2,
					significand: signed(middle / 1e+02),
				})
			}
		} else {
			let upper = scaled(1e+01);
			if upper < 1e+04 {
				Ok(Signifix {
					prefix: SYMBOL[prefix],
					precision: 1,
					significand: signed(upper / 1e+01),
				})
			} else {
				if let Some(&symbol) = SYMBOL.get(prefix + 1) {
					Ok(Signifix {
						prefix: symbol,
						precision: 3,
						significand: signed(1e+00),
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

impl std::fmt::Display for Signifix {
	fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
		if f.sign_plus() {
			write!(f, "{:+.*} {}", self.precision,
				self.significand, self.prefix)
		} else
		if f.alternate() && !self.significand.is_sign_negative() {
			write!(f, " {:.*} {}", self.precision,
				self.significand, self.prefix)
		} else {
			write!(f, "{:.*} {}", self.precision,
				self.significand, self.prefix)
		}
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	fn fmt_def(number: f64) -> Result<String> {
		Ok(format!("{}", Signifix::try_from(number)?))
	}
	fn fmt_pos(number: f64) -> Result<String> {
		Ok(format!("{:+}", Signifix::try_from(number)?))
	}
	fn fmt_alt(number: f64) -> Result<String> {
		Ok(format!("{:#}", Signifix::try_from(number)?))
	}
	#[test]
	fn metric_unit_prefix() {
		assert_eq!(fmt_def(1e-24).ok(), Some("1.000 y".into()));
		assert_eq!(fmt_def(1e-21).ok(), Some("1.000 z".into()));
		assert_eq!(fmt_def(1e-18).ok(), Some("1.000 a".into()));
		assert_eq!(fmt_def(1e-15).ok(), Some("1.000 f".into()));
		assert_eq!(fmt_def(1e-12).ok(), Some("1.000 p".into()));
		assert_eq!(fmt_def(1e-09).ok(), Some("1.000 n".into()));
		assert_eq!(fmt_def(1e-06).ok(), Some("1.000 µ".into()));
		assert_eq!(fmt_def(1e-03).ok(), Some("1.000 m".into()));
		assert_eq!(fmt_def(1e+00).ok(), Some("1.000  ".into()));
		assert_eq!(fmt_def(1e+03).ok(), Some("1.000 k".into()));
		assert_eq!(fmt_def(1e+06).ok(), Some("1.000 M".into()));
		assert_eq!(fmt_def(1e+09).ok(), Some("1.000 G".into()));
		assert_eq!(fmt_def(1e+12).ok(), Some("1.000 T".into()));
		assert_eq!(fmt_def(1e+15).ok(), Some("1.000 P".into()));
		assert_eq!(fmt_def(1e+18).ok(), Some("1.000 E".into()));
		assert_eq!(fmt_def(1e+21).ok(), Some("1.000 Z".into()));
		assert_eq!(fmt_def(1e+24).ok(), Some("1.000 Y".into()));
	}
	#[test]
	fn fixed_significance() {
		assert_eq!(fmt_def(1.234e+02).ok(), Some("123.4  ".into()));
		assert_eq!(fmt_def(1.234e+03).ok(), Some("1.234 k".into()));
		assert_eq!(fmt_def(1.234e+04).ok(), Some("12.34 k".into()));
		assert_eq!(fmt_def(1.234e+05).ok(), Some("123.4 k".into()));
		assert_eq!(fmt_def(1.234e+06).ok(), Some("1.234 M".into()));
	}
	#[test]
	fn formatting_options() {
		assert_eq!(fmt_def(-1e+00).ok(), Some("-1.000  ".into()));
		assert_eq!(fmt_def( 1e+00).ok(), Some( "1.000  ".into()));
		assert_eq!(fmt_pos(-1e+00).ok(), Some("-1.000  ".into()));
		assert_eq!(fmt_pos( 1e+00).ok(), Some("+1.000  ".into()));
		assert_eq!(fmt_alt(-1e+00).ok(), Some("-1.000  ".into()));
		assert_eq!(fmt_alt( 1e+00).ok(), Some(" 1.000  ".into()));
	}
	#[test]
	fn lower_prefix_bound() {
		assert_eq!(fmt_def(-0.99951e-24).ok(), Some("-1.000 y".into()));
		assert_eq!(fmt_def(-0.99949e-24).err(),
			Some(Error::OutOfLowerBound(-0.99949e-24)));
	}
	#[test]
	fn upper_prefix_bound() {
		assert_eq!(fmt_def(-0.999949e+27).ok(), Some("-999.9 Y".into()));
		assert_eq!(fmt_def(-0.999951e+27).err(),
			Some(Error::OutOfUpperBound(-0.999951e+27)));
	}
	#[test]
	fn upper_prefix_round() {
		assert_eq!(fmt_def(999.9499999999998e+03).ok(), Some("999.9 k".into()));
		assert_eq!(fmt_def(999.9499999999999e+03).ok(), Some("1.000 M".into()));
	}
	#[test]
	fn fp_category_safety() {
		assert_eq!(fmt_def(0.0).err(),
			Some(Error::OutOfLowerBound(0.0)));
		assert_eq!(fmt_def(std::f64::NEG_INFINITY).err(),
			Some(Error::OutOfUpperBound(std::f64::NEG_INFINITY)));
		assert_eq!(fmt_def(std::f64::INFINITY).err(),
			Some(Error::OutOfUpperBound(std::f64::INFINITY)));
		assert_eq!(fmt_def(std::f64::NAN).err(),
			Some(Error::Nan));
	}
}
