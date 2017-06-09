# signifix

**Number Formatter of Fixed Significance with Metric or Binary Prefix**

[![Build Status][]](https://travis-ci.org/qu1x/signifix)
[![Version][]](https://crates.io/crates/signifix)
[![Downloads][]](https://crates.io/crates/signifix)
[![License][]](#license)
[![LoC][]](https://tokei.rs)

[Build Status]: https://travis-ci.org/qu1x/signifix.svg
[Version]: https://img.shields.io/crates/v/signifix.svg
[Downloads]: https://img.shields.io/crates/d/signifix.svg
[License]: https://img.shields.io/crates/l/signifix.svg
[LoC]: https://tokei.rs/b1/github/qu1x/signifix

[Documentation](https://docs.rs/signifix/0.7.0/signifix/)

Formats a given number in one of the three Signifix notations
[as defined below](#signifix-notations) by determining

 1. the appropriate metric or binary prefix and
 2. the decimal mark position in such a way as to sustain a fixed number of
    four significant figures.

## Signifix Notations

Three notations are defined,

  * two [with metric prefix](#with-metric-prefix), a default and an
    alternate, and
  * one [with binary prefix](#with-binary-prefix), a default only.

### With Metric Prefix

The two Signifix notations with metric prefix comprise

  * a signed significand of four significant figures normalized from
    `±1.000` to `±999.9` to cover the three powers of ten of a particular
    metric prefix with the three different decimal mark positions between
    these four figures, and
  * a metric prefix symbol or its placeholder in case of no prefix
      - either being appended along with a whitespace as in `±1.234␣k`,
        that is the default notation,
      - or replacing the decimal mark of the significand as in `±1k234`,
        that is the alternate notation.

In default notation the placeholder is another whitespace as in `±1.234␣␣`
to align consistently, while in alternate notation it is a number sign as in
`±1#234` to conspicuously separate the integer from the fractional part of
the significand. The decimal mark is locale-sensitive and defaults to a
decimal point. The plus sign of positive numbers is optional.

### With Binary Prefix

The one Signifix notation with binary prefix comprises

  * a signed significand of four significant figures normalized from
    `±1.000` over `±999.9` to `±1 023` to cover the four powers of ten of a
    particular binary prefix with the three different decimal mark positions
    between these four figures and a thousands separator, and
  * a binary prefix symbol or its placeholder in case of no prefix being
    appended along with a whitespace as in `±1.234␣Ki`.

To align consistently, the placeholder is another two whitespaces as in
`±1.234␣␣␣` while the locale-sensitive thousands separator defaults to a
whitespace as in `±1␣023␣Ki`. The locale-sensitive decimal mark defaults to
a decimal point. The plus sign of positive numbers is optional.

## Usage

This crate is [on crates.io](https://crates.io/crates/signifix) and can be
used by adding `signifix` to the dependencies in your project's
`Cargo.toml`:

```toml
[dependencies]
signifix = "0.7.0"
```

and this to your crate root:

```rust
#![feature(try_from)] // Until stabilized. Requires nightly Rust.

extern crate signifix;
```

## Examples

The Signifix notations result in a fixed number of characters preventing
jumps to the left or right while making maximum use of their occupied space:

```rust
use std::convert::TryFrom; // Until stabilized.

use signifix::{metric, binary, Result};

let metric = |number| -> Result<(String, String)> {
	let number = metric::Signifix::try_from(number)?;
	Ok((format!("{}", number), format!("{:#}", number)))
};
let binary = |number| -> Result<String> {
	let number = binary::Signifix::try_from(number)?;
	Ok(format!("{}", number))
};

// Three different decimal mark positions covering the three powers of ten
// of a particular metric prefix.
assert_eq!(metric(1E-04), Ok(("100.0 µ".into(), "100µ0".into()))); // 3rd
assert_eq!(metric(1E-03), Ok(("1.000 m".into(), "1m000".into()))); // 1st
assert_eq!(metric(1E-02), Ok(("10.00 m".into(), "10m00".into()))); // 2nd
assert_eq!(metric(1E-01), Ok(("100.0 m".into(), "100m0".into()))); // 3rd
assert_eq!(metric(1E+00), Ok(("1.000  ".into(), "1#000".into()))); // 1st
assert_eq!(metric(1E+01), Ok(("10.00  ".into(), "10#00".into()))); // 2nd
assert_eq!(metric(1E+02), Ok(("100.0  ".into(), "100#0".into()))); // 3rd
assert_eq!(metric(1E+03), Ok(("1.000 k".into(), "1k000".into()))); // 1st
assert_eq!(metric(1E+04), Ok(("10.00 k".into(), "10k00".into()))); // 2nd
assert_eq!(metric(1E+05), Ok(("100.0 k".into(), "100k0".into()))); // 3rd
assert_eq!(metric(1E+06), Ok(("1.000 M".into(), "1M000".into()))); // 1st

// Three different decimal mark positions and a thousands separator covering
// the four powers of ten of a particular binary prefix.
assert_eq!(binary(1_024f64.powi(0) * 1E+00), Ok("1.000   ".into())); // 1st
assert_eq!(binary(1_024f64.powi(0) * 1E+01), Ok("10.00   ".into())); // 2nd
assert_eq!(binary(1_024f64.powi(0) * 1E+02), Ok("100.0   ".into())); // 3rd
assert_eq!(binary(1_024f64.powi(0) * 1E+03), Ok("1 000   ".into())); // 4th
assert_eq!(binary(1_024f64.powi(1) * 1E+00), Ok("1.000 Ki".into())); // 1st
assert_eq!(binary(1_024f64.powi(1) * 1E+01), Ok("10.00 Ki".into())); // 2nd
assert_eq!(binary(1_024f64.powi(1) * 1E+02), Ok("100.0 Ki".into())); // 3rd
assert_eq!(binary(1_024f64.powi(1) * 1E+03), Ok("1 000 Ki".into())); // 4th
assert_eq!(binary(1_024f64.powi(2) * 1E+00), Ok("1.000 Mi".into())); // 1st

// Rounding over prefixes is safe against floating-point inaccuracies.
assert_eq!(metric(999.949_999_999_999_8),
	Ok(("999.9  ".into(), "999#9".into())));
assert_eq!(metric(999.949_999_999_999_9),
	Ok(("1.000 k".into(), "1k000".into())));
assert_eq!(binary(1_023.499_999_999_999_94),
	Ok("1 023   ".into()));
assert_eq!(binary(1_023.499_999_999_999_95),
	Ok("1.000 Ki".into()));
```

This is useful to smoothly refresh a transfer rate within a terminal:

```rust
#![feature(i128_type)] // Until stabilized.

use std::convert::TryFrom; // Until stabilized.

use std::f64;
use signifix::metric::{Signifix, Error, DEF_MIN_LEN};

let format_rate = |bytes: u128, nanoseconds: u128| -> String {
	let bytes_per_second = bytes as f64 / nanoseconds as f64 * 1E+09;
	let unit = "B/s";
	let rate = match Signifix::try_from(bytes_per_second) {
		Ok(rate) => if rate.factor() < 1E+00 {
			" - slow - ".into() // instead of mB/s, µB/s, ...
		} else {
			format!("{}{}", rate, unit) // normal rate
		},
		Err(case) => match case {
			Error::OutOfLowerBound(rate) => if rate == 0f64 {
				" - idle - " // no progress at all
			} else {
				" - slow - " // almost no progress
			},
			Error::OutOfUpperBound(rate) => if rate == f64::INFINITY {
				" - ---- - " // zero nanoseconds
			} else {
				" - fast - " // awkwardly fast
			},
			Error::Nan => " - ---- - ", // zero bytes in zero nanoseconds
		}.into(),
	};
	debug_assert_eq!(rate.chars().count(),
		DEF_MIN_LEN + unit.chars().count());
	rate
};

assert_eq!(format_rate(42_667, 300_000_000_000), "142.2  B/s");
assert_eq!(format_rate(42_667, 030_000_000_000), "1.422 kB/s");
assert_eq!(format_rate(42_667, 003_000_000_000), "14.22 kB/s");
assert_eq!(format_rate(00_001, 003_000_000_000), " - slow - ");
assert_eq!(format_rate(00_000, 003_000_000_000), " - idle - ");
assert_eq!(format_rate(42_667, 000_000_000_000), " - ---- - ");
```

Or to monitor a measured quantity like an electrical current including its
direction with positive numbers being padded to align with negative ones:

```rust
use std::convert::TryFrom; // Until stabilized.

use signifix::metric::{Signifix, Result, DEF_MAX_LEN};

let format_load = |amps| -> Result<String> {
	if let Some(amps) = amps {
		Signifix::try_from(amps)
			.map(|amps| format!("{:>1$}A", amps, DEF_MAX_LEN))
	} else {
		Ok("     0  A".into())
	}
};

assert_eq!(format_load(Some( 1.476E-06)), Ok(" 1.476 µA".into()));
assert_eq!(format_load(None),             Ok("     0  A".into()));
assert_eq!(format_load(Some(-2.927E-06)), Ok("-2.927 µA".into()));
```

While to visualize a change in file size, a plus sign might be preferred for
positive numbers:

```rust
use std::convert::TryFrom; // Until stabilized.

use signifix::metric::{Signifix, Error, Result};

let format_diff = |curr, prev| -> Result<String> {
	Signifix::try_from(curr - prev).map(|diff| format!("{:+#}", diff))
		.or_else(|case| if case == Error::OutOfLowerBound(0f64)
			{ Ok("=const".into()) } else { Err(case) })
};

assert_eq!(format_diff(78_346, 57_393), Ok("+20k95".into()));
assert_eq!(format_diff(93_837, 93_837), Ok("=const".into()));
assert_eq!(format_diff(27_473, 36_839), Ok("-9k366".into()));
```

The binary prefix instead suits well to visualize quantities being multiples
of powers of two, such as memory boundaries due to binary addressing:

```rust
use std::convert::TryFrom; // Until stabilized.

use signifix::binary::{Signifix, Error, Result};

let format_used = |used: usize, size: usize| -> Result<String> {
	if used == 0 {
		let size = Signifix::try_from(size)?;
		return Ok(format!("    0   B (    0 %) of {}B", size));
	}
	let p100 = Signifix::try_from(used as f64 / size as f64 * 100.0)
		.map(|p100| format!("{:.*} %", p100.exponent(), p100.significand()))
		.or_else(|error| if let Error::OutOfLowerBound(_) = error
			{ Ok("  < 1 %".into()) } else { Err(error) })?;
	let used = Signifix::try_from(used)?;
	let size = Signifix::try_from(size)?;
	Ok(format!("{}B ({}) of {}B", used, p100, size))
};

assert_eq!(format_used(0_000usize.pow(1), 1_024usize.pow(3)),
	Ok("    0   B (    0 %) of 1.000 GiB".into()));
assert_eq!(format_used(1_024usize.pow(2), 1_024usize.pow(3)),
	Ok("1.000 MiB (  < 1 %) of 1.000 GiB".into()));
assert_eq!(format_used(3_292usize.pow(2), 1_024usize.pow(3)),
	Ok("10.34 MiB (1.009 %) of 1.000 GiB".into()));
assert_eq!(format_used(8_192usize.pow(2), 1_024usize.pow(3)),
	Ok("64.00 MiB (6.250 %) of 1.000 GiB".into()));
assert_eq!(format_used(1_000usize.pow(3), 1_024usize.pow(3)),
	Ok("953.7 MiB (93.13 %) of 1.000 GiB".into()));
assert_eq!(format_used(1_024usize.pow(3), 1_024usize.pow(3)),
	Ok("1.000 GiB (100.0 %) of 1.000 GiB".into()));
```

Until there is a recommended and possible implicit localization system for
Rust, explicit localization can be achieved by wrapping the `Signifix` type
into a locale-sensitive newtype which implements the `Display` trait via the
`Signifix::fmt()` method:

```rust
use std::convert::TryFrom; // Until stabilized.

use signifix::binary::{Signifix, Result};

struct SignifixSi(Signifix); // English version of SI style (default)
struct SignifixEn(Signifix); // English locale
struct SignifixDe(Signifix); // German locale

impl std::fmt::Display for SignifixSi {
	fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
		std::fmt::Display::fmt(&self.0, f)
	}
}
impl std::fmt::Display for SignifixEn {
	fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
		self.0.fmt(f, ".", ",")
	}
}
impl std::fmt::Display for SignifixDe {
	fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
		self.0.fmt(f, ",", ".")
	}
}

let locale = |number| -> Result<(String, String, String)> {
	Signifix::try_from(number).map(|number| (
		format!("{}", SignifixSi(number)),
		format!("{}", SignifixEn(number)),
		format!("{}", SignifixDe(number)),
	))
};

assert_eq!(locale(999.9f64 * 1_024f64),
	Ok(("999.9 Ki".into(), "999.9 Ki".into(), "999,9 Ki".into())));
assert_eq!(locale(1_000f64 * 1_024f64),
	Ok(("1 000 Ki".into(), "1,000 Ki".into(), "1.000 Ki".into())));
```

## License

Copyright (c) 2016, 2017 Rouven Spreckels <n3vu0r@qu1x.org>

Usage of the works is permitted provided that
this instrument is retained with the works, so that
any entity that uses the works is notified of this instrument.

DISCLAIMER: THE WORKS ARE WITHOUT WARRANTY.

## Contribution

Unless you explicitly state otherwise, any contribution intentionally submitted
for inclusion in the works by you shall be licensed as above, without any
additional terms or conditions.
