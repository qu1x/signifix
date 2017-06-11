// Copyright (c) 2016, 2017 Rouven Spreckels <n3vu0r@qu1x.org>
//
// Usage of the works is permitted provided that
// this instrument is retained with the works, so that
// any entity that uses the works is notified of this instrument.
//
// DISCLAIMER: THE WORKS ARE WITHOUT WARRANTY.

//! **Number Formatter of Fixed Significance with Metric or Binary Prefix**
//!
//! Formats a given number in one of the three Signifix notations
//! [as defined below](#signifix-notations) by determining
//!
//!  1. the appropriate metric or binary prefix and
//!  2. the decimal mark position in such a way as to sustain a fixed number of
//!     four significant figures.
//!
//! # Contents
//!
//!   * [Signifix Notations](#signifix-notations)
//!       * [With Metrix Prefix](#with-metric-prefix)
//!       * [With Binary Prefix](#with-binary-prefix)
//!   * [Usage](#usage)
//!   * [Examples](#examples)
//!      1. [The Notations](#the-notations)
//!      2. [Transfer Rate](#transfer-rate)
//!      3. [Measured Amps](#measured-amps)
//!      4. [Filesize Diff](#filesize-diff)
//!      5. [Boundary Stat](#boundary-stat)
//!      6. [Localizations](#localizations)
//!
//! # Signifix Notations
//!
//! Three notations are defined,
//!
//!   * two [with metric prefix](#with-metric-prefix), a default and an
//!     alternate, and
//!   * one [with binary prefix](#with-binary-prefix), a default only.
//!
//! ## With Metric Prefix
//!
//! The two Signifix notations with metric prefix comprise
//!
//!   * a signed significand of four significant figures normalized from
//!     `±1.000` to `±999.9` to cover the three powers of ten of a particular
//!     metric prefix with the three different decimal mark positions between
//!     these four figures, and
//!   * a metric prefix symbol or its placeholder in case of no prefix
//!       - either being appended along with a whitespace as in `±1.234␣k`,
//!         that is the default notation,
//!       - or replacing the decimal mark of the significand as in `±1k234`,
//!         that is the alternate notation.
//!
//! In default notation the placeholder is another whitespace as in `±1.234␣␣`
//! to align consistently, while in alternate notation it is a number sign as in
//! `±1#234` to conspicuously separate the integer from the fractional part of
//! the significand. The decimal mark is locale-sensitive and defaults to a
//! decimal point. The plus sign of positive numbers is optional.
//!
//! ## With Binary Prefix
//!
//! The one Signifix notation with binary prefix comprises
//!
//!   * a signed significand of four significant figures normalized from
//!     `±1.000` over `±999.9` to `±1 023` to cover the four powers of ten of a
//!     particular binary prefix with the three different decimal mark positions
//!     between these four figures and a thousands separator, and
//!   * a binary prefix symbol or its placeholder in case of no prefix being
//!     appended along with a whitespace as in `±1.234␣Ki`.
//!
//! To align consistently, the placeholder is another two whitespaces as in
//! `±1.234␣␣␣` while the locale-sensitive thousands separator defaults to a
//! whitespace as in `±1␣023␣Ki`. The locale-sensitive decimal mark defaults to
//! a decimal point. The plus sign of positive numbers is optional.
//!
//! # Usage
//!
//! This crate is [on crates.io](https://crates.io/crates/signifix) and can be
//! used by adding `signifix` to the dependencies in your project's
//! `Cargo.toml`:
//!
//! ```toml
//! [dependencies]
//! signifix = "0.7.0"
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
//! ## The Notations
//!
//! The Signifix notations result in a fixed number of characters preventing
//! jumps to the left or right while making maximum use of their occupied space:
//!
//! ```
//! # #![feature(try_from)]
//! use std::convert::TryFrom; // Until stabilized.
//!
//! use signifix::{metric, binary, Result};
//!
//! let metric = |number| -> Result<(String, String)> {
//! 	let number = metric::Signifix::try_from(number)?;
//! 	Ok((format!("{}", number), format!("{:#}", number)))
//! };
//! let binary = |number| -> Result<String> {
//! 	let number = binary::Signifix::try_from(number)?;
//! 	Ok(format!("{}", number))
//! };
//!
//! // Three different decimal mark positions covering the three powers of ten
//! // of a particular metric prefix.
//! assert_eq!(metric(1E-04), Ok(("100.0 µ".into(), "100µ0".into()))); // 3rd
//! assert_eq!(metric(1E-03), Ok(("1.000 m".into(), "1m000".into()))); // 1st
//! assert_eq!(metric(1E-02), Ok(("10.00 m".into(), "10m00".into()))); // 2nd
//! assert_eq!(metric(1E-01), Ok(("100.0 m".into(), "100m0".into()))); // 3rd
//! assert_eq!(metric(1E+00), Ok(("1.000  ".into(), "1#000".into()))); // 1st
//! assert_eq!(metric(1E+01), Ok(("10.00  ".into(), "10#00".into()))); // 2nd
//! assert_eq!(metric(1E+02), Ok(("100.0  ".into(), "100#0".into()))); // 3rd
//! assert_eq!(metric(1E+03), Ok(("1.000 k".into(), "1k000".into()))); // 1st
//! assert_eq!(metric(1E+04), Ok(("10.00 k".into(), "10k00".into()))); // 2nd
//! assert_eq!(metric(1E+05), Ok(("100.0 k".into(), "100k0".into()))); // 3rd
//! assert_eq!(metric(1E+06), Ok(("1.000 M".into(), "1M000".into()))); // 1st
//!
//! // Three different decimal mark positions and a thousands separator covering
//! // the four powers of ten of a particular binary prefix.
//! assert_eq!(binary(1_024f64.powi(0) * 1E+00), Ok("1.000   ".into())); // 1st
//! assert_eq!(binary(1_024f64.powi(0) * 1E+01), Ok("10.00   ".into())); // 2nd
//! assert_eq!(binary(1_024f64.powi(0) * 1E+02), Ok("100.0   ".into())); // 3rd
//! assert_eq!(binary(1_024f64.powi(0) * 1E+03), Ok("1 000   ".into())); // 4th
//! assert_eq!(binary(1_024f64.powi(1) * 1E+00), Ok("1.000 Ki".into())); // 1st
//! assert_eq!(binary(1_024f64.powi(1) * 1E+01), Ok("10.00 Ki".into())); // 2nd
//! assert_eq!(binary(1_024f64.powi(1) * 1E+02), Ok("100.0 Ki".into())); // 3rd
//! assert_eq!(binary(1_024f64.powi(1) * 1E+03), Ok("1 000 Ki".into())); // 4th
//! assert_eq!(binary(1_024f64.powi(2) * 1E+00), Ok("1.000 Mi".into())); // 1st
//!
//! // Rounding over prefixes is safe against floating-point inaccuracies.
//! assert_eq!(metric(999.949_999_999_999_8),
//! 	Ok(("999.9  ".into(), "999#9".into())));
//! assert_eq!(metric(999.949_999_999_999_9),
//! 	Ok(("1.000 k".into(), "1k000".into())));
//! assert_eq!(binary(1_023.499_999_999_999_94),
//! 	Ok("1 023   ".into()));
//! assert_eq!(binary(1_023.499_999_999_999_95),
//! 	Ok("1.000 Ki".into()));
//! ```
//!
//! ## Transfer Rate
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
//! use signifix::metric::{Signifix, Error, DEF_MIN_LEN};
//!
//! let transfer_rate = |bytes: u128, nanoseconds: u128| -> String {
//! 	let bytes_per_second = bytes as f64 / nanoseconds as f64 * 1E+09;
//! 	let unit = "B/s";
//! 	let rate = match Signifix::try_from(bytes_per_second) {
//! 		Ok(rate) => if rate.factor() < 1E+00 {
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
//! 	debug_assert_eq!(rate.chars().count(),
//! 		DEF_MIN_LEN + unit.chars().count());
//! 	rate
//! };
//!
//! assert_eq!(transfer_rate(42_667, 300_000_000_000), "142.2  B/s");
//! assert_eq!(transfer_rate(42_667, 030_000_000_000), "1.422 kB/s");
//! assert_eq!(transfer_rate(42_667, 003_000_000_000), "14.22 kB/s");
//! assert_eq!(transfer_rate(00_001, 003_000_000_000), " - slow - ");
//! assert_eq!(transfer_rate(00_000, 003_000_000_000), " - idle - ");
//! assert_eq!(transfer_rate(42_667, 000_000_000_000), " - ---- - ");
//! ```
//!
//! ## Measured Amps
//!
//! Or to monitor a measured quantity like an electrical current including its
//! direction with positive numbers being padded to align with negative ones:
//!
//! ```
//! # #![feature(try_from)]
//! use std::convert::TryFrom; // Until stabilized.
//!
//! use signifix::metric::{Signifix, Result, DEF_MAX_LEN};
//!
//! let measured_amps = |amps| -> Result<String> {
//! 	if let Some(amps) = amps {
//! 		Signifix::try_from(amps)
//! 			.map(|amps| format!("{:>1$}A", amps, DEF_MAX_LEN))
//! 	} else {
//! 		Ok("     0  A".into())
//! 	}
//! };
//!
//! assert_eq!(measured_amps(Some( 1.476E-06)), Ok(" 1.476 µA".into()));
//! assert_eq!(measured_amps(None),             Ok("     0  A".into()));
//! assert_eq!(measured_amps(Some(-2.927E-06)), Ok("-2.927 µA".into()));
//! ```
//!
//! ## Filesize Diff
//!
//! While to visualize a change in file size, a plus sign might be preferred for
//! positive numbers:
//!
//! ```
//! # #![feature(try_from)]
//! use std::convert::TryFrom; // Until stabilized.
//!
//! use signifix::metric::{Signifix, Error, Result};
//!
//! let filesize_diff = |curr, prev| -> Result<String> {
//! 	Signifix::try_from(curr - prev).map(|diff| format!("{:+#}", diff))
//! 		.or_else(|case| if case == Error::OutOfLowerBound(0f64)
//! 			{ Ok("=const".into()) } else { Err(case) })
//! };
//!
//! assert_eq!(filesize_diff(78_346, 57_393), Ok("+20k95".into()));
//! assert_eq!(filesize_diff(93_837, 93_837), Ok("=const".into()));
//! assert_eq!(filesize_diff(27_473, 36_839), Ok("-9k366".into()));
//! ```
//!
//! ## Boundary Stat
//!
//! The binary prefix instead suits well to visualize quantities being multiples
//! of powers of two, such as memory boundaries due to binary addressing:
//!
//! ```
//! # #![feature(try_from)]
//! use std::convert::TryFrom; // Until stabilized.
//!
//! use signifix::binary::{Signifix, Error, Result};
//!
//! let boundary_stat = |used: usize, size: usize| -> Result<String> {
//! 	if used == 0 {
//! 		let size = Signifix::try_from(size)?;
//! 		return Ok(format!("    0   B (    0 %) of {}B", size));
//! 	}
//! 	let p100 = Signifix::try_from(used as f64 / size as f64 * 100.0)
//! 		.map(|p100| format!("{:.*} %", p100.exponent(), p100.significand()))
//! 		.or_else(|error| if let Error::OutOfLowerBound(_) = error
//! 			{ Ok("  < 1 %".into()) } else { Err(error) })?;
//! 	let used = Signifix::try_from(used)?;
//! 	let size = Signifix::try_from(size)?;
//! 	Ok(format!("{}B ({}) of {}B", used, p100, size))
//! };
//!
//! assert_eq!(boundary_stat(0_000usize.pow(1), 1_024usize.pow(3)),
//! 	Ok("    0   B (    0 %) of 1.000 GiB".into()));
//! assert_eq!(boundary_stat(1_024usize.pow(2), 1_024usize.pow(3)),
//! 	Ok("1.000 MiB (  < 1 %) of 1.000 GiB".into()));
//! assert_eq!(boundary_stat(3_292usize.pow(2), 1_024usize.pow(3)),
//! 	Ok("10.34 MiB (1.009 %) of 1.000 GiB".into()));
//! assert_eq!(boundary_stat(8_192usize.pow(2), 1_024usize.pow(3)),
//! 	Ok("64.00 MiB (6.250 %) of 1.000 GiB".into()));
//! assert_eq!(boundary_stat(1_000usize.pow(3), 1_024usize.pow(3)),
//! 	Ok("953.7 MiB (93.13 %) of 1.000 GiB".into()));
//! assert_eq!(boundary_stat(1_024usize.pow(3), 1_024usize.pow(3)),
//! 	Ok("1.000 GiB (100.0 %) of 1.000 GiB".into()));
//! ```
//!
//! ## Localizations
//!
//! Until there is a recommended and possible implicit localization system for
//! Rust, explicit localization can be achieved by wrapping the `Signifix` type
//! into a locale-sensitive newtype which implements the `Display` trait via the
//! `Signifix::fmt()` method:
//!
//! ```
//! # #![feature(try_from)]
//! use std::convert::TryFrom; // Until stabilized.
//!
//! use signifix::binary::{Signifix, Result};
//!
//! struct SignifixSi(Signifix); // English SI style (default)
//! struct SignifixEn(Signifix); // English locale (whitespace -> comma)
//! struct SignifixDe(Signifix); // German locale (comma <-> point)
//!
//! impl std::fmt::Display for SignifixSi {
//! 	fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
//! 		std::fmt::Display::fmt(&self.0, f)
//! 	}
//! }
//! impl std::fmt::Display for SignifixEn {
//! 	fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
//! 		self.0.fmt(f, ".", ",")
//! 	}
//! }
//! impl std::fmt::Display for SignifixDe {
//! 	fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
//! 		self.0.fmt(f, ",", ".")
//! 	}
//! }
//!
//! let localizations = |number| -> Result<(String, String, String)> {
//! 	Signifix::try_from(number).map(|number| (
//! 		format!("{}", SignifixSi(number)),
//! 		format!("{}", SignifixEn(number)),
//! 		format!("{}", SignifixDe(number)),
//! 	))
//! };
//!
//! assert_eq!(localizations(999.9f64 * 1_024f64),
//! 	Ok(("999.9 Ki".into(), "999.9 Ki".into(), "999,9 Ki".into())));
//! assert_eq!(localizations(1_000f64 * 1_024f64),
//! 	Ok(("1 000 Ki".into(), "1,000 Ki".into(), "1.000 Ki".into())));
//! ```

#![deny(missing_docs)]

#![feature(i128_type)]
#![feature(try_from)]

use std::result;
use std::error;

use std::fmt;
use std::fmt::{Display, Formatter};

use std::cmp::Ordering;

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
struct Signifix {
	numerator: i16,
	exponent: u8,
	prefix: u8,
}

impl PartialOrd for Signifix {
	fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
		Some(self.cmp(other))
	}
}

impl Ord for Signifix {
	fn cmp(&self, other: &Self) -> Ordering {
		self.prefix.cmp(&other.prefix)
			.then(self.exponent.cmp(&other.exponent).reverse())
			.then(self.numerator.cmp(&other.numerator))
	}
}

impl Signifix {
	fn significand(&self) -> f64 {
		self.numerator() as f64 * [1E-00, 1E-01, 1E-02, 1E-03][self.exponent()]
	}

	fn numerator(&self) -> i32 {
		self.numerator.into()
	}

	fn denominator(&self) -> i32 {
		[1, 10, 100, 1_000][self.exponent()]
	}

	fn exponent(&self) -> usize {
		self.exponent.into()
	}

	fn integer(&self) -> i32 {
		self.numerator() / self.denominator()
	}

	fn fractional(&self) -> i32 {
		self.numerator().abs() % self.denominator()
	}

	fn parts(&self) -> (i32, i32) {
		let trunc = self.numerator() / self.denominator();
		let fract = self.numerator() - self.denominator() * trunc;
		(trunc, fract.abs())
	}

	fn prefix(&self) -> usize {
		self.prefix.into()
	}
}

macro_rules! try_from {
	($($t:ty),*) => (
		$(
			impl TryFrom<$t> for Signifix {
				type Error = Error;

				fn try_from(number: $t) -> Result<Self> {
					Self::try_from(number as f64)
				}
			}
		)*
	);
}

/// Formatter of Signifix default and alternate notation with metric prefix.
pub mod metric;

/// Formatter of Signifix default notation with binary prefix.
pub mod binary;

/// A common error arising from this crate's modules.
#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum Error {
	/// A given number is not representable with any metric prefix.
	Metric(metric::Error),

	/// A given number is not representable with any binary prefix.
	Binary(binary::Error),
}

impl From<metric::Error> for Error {
	fn from(error: metric::Error) -> Self {
		Error::Metric(error)
	}
}

impl From<binary::Error> for Error {
	fn from(error: binary::Error) -> Self {
		Error::Binary(error)
	}
}

impl Display for Error {
	fn fmt(&self, f: &mut Formatter) -> fmt::Result {
		match *self {
			Error::Metric(_) =>
				write!(f, "{}", error::Error::description(self)),
			Error::Binary(_) =>
				write!(f, "{}", error::Error::description(self)),
		}
	}
}

impl error::Error for Error {
	fn description(&self) -> &str {
		match *self {
			Error::Metric(_) => "Not representable with metric prefix",
			Error::Binary(_) => "Not representable with binary prefix",
		}
	}
	fn cause(&self) -> Option<&error::Error> {
		match *self {
			Error::Metric(ref error) => Some(error),
			Error::Binary(ref error) => Some(error),
		}
	}
}

/// The canonical `Result` type using this crate's `Error` type.
pub type Result<T> = result::Result<T, Error>;
