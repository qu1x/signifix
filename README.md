# signifix

**Number Formatter of Fixed Significance with Metric Prefix**

[![Build Status](https://travis-ci.org/qu1x/signifix.svg?branch=master)](https://travis-ci.org/qu1x/signifix)
[![Version](https://img.shields.io/crates/v/signifix.svg)](https://crates.io/crates/signifix)
[![Downloads](https://img.shields.io/crates/d/signifix.svg)](https://crates.io/crates/signifix)
[![License](https://img.shields.io/crates/l/signifix.svg)](https://www.gnu.org/licenses/lgpl-3.0.en.html)
[![LoC](https://tokei.rs/b1/github/qu1x/signifix)](https://tokei.rs)

[Documentation](https://docs.rs/signifix/0.4.0/signifix/)

Formats a given number in one of the two Signifix notations
[as defined below](#definition) by

 1. selecting the appropriate metric prefix and
 2. moving the decimal point position in a way to sustain a fixed number of
    four significant figures.

## Definition

The Signifix notation comprises

  * a metrically normalized signed significand, that is a decimal of four
    significant figures from `±1.000` to `±999.9` to cover the three powers
    of ten of a particular metric prefix with the three different decimal
    point positions between these four figures, and
  * a metric prefix symbol or its placeholder in case of no prefix
      - either being appended along with a whitespace as in `±1.234␣k`,
        that is the default notation,
      - or replacing the decimal point of the significand as in `±1k234`,
        that is the alternate notation.

In default notation the placeholder is another whitespace as in `±1.234␣␣`
to align consistently, while in alternate notation it is a number sign as in
`±1#234` to conspicuously separate the integer from the fractional part of
the significand.

The plus sign of positive numbers is optional.

## Usage

This crate is [on crates.io](https://crates.io/crates/signifix) and can be
used by adding `signifix` to the dependencies in your project's
`Cargo.toml`:

```toml
[dependencies]
signifix = "0.4.0"
```

and this to your crate root:

```rust
#![feature(try_from)] // Until stabilized. Requires nightly Rust.

extern crate signifix;
```

## Examples

Both the default and alternate notation result in a fixed number of
characters preventing jumps to the left or right:

```rust
use std::convert::TryFrom; // Until stabilized.

use signifix::{Signifix, Result};

let format = |number| -> Result<(String, String)> {
	Signifix::try_from(number)
		.map(|number| (format!("{}", number), format!("{:#}", number)))
};

assert_eq!(format(1e-04), Ok(("100.0 µ".into(), "100µ0".into())));
assert_eq!(format(1e-03), Ok(("1.000 m".into(), "1m000".into())));
assert_eq!(format(1e-02), Ok(("10.00 m".into(), "10m00".into())));
assert_eq!(format(1e-01), Ok(("100.0 m".into(), "100m0".into())));
assert_eq!(format(1e+00), Ok(("1.000  ".into(), "1#000".into())));
assert_eq!(format(1e+01), Ok(("10.00  ".into(), "10#00".into())));
assert_eq!(format(1e+02), Ok(("100.0  ".into(), "100#0".into())));
assert_eq!(format(1e+03), Ok(("1.000 k".into(), "1k000".into())));
assert_eq!(format(1e+04), Ok(("10.00 k".into(), "10k00".into())));
assert_eq!(format(1e+05), Ok(("100.0 k".into(), "100k0".into())));
assert_eq!(format(1e+06), Ok(("1.000 M".into(), "1M000".into())));
```

This is useful to smoothly refresh a transfer rate within a terminal:

```rust
#![feature(i128_type)] // Until stabilized.

use std::convert::TryFrom; // Until stabilized.

use std::f64;
use signifix::{Signifix, Error, DEF_MIN_LEN};

let format_rate = |bytes: u128, nanoseconds: u128| -> String {
	let bytes_per_second = bytes as f64 / nanoseconds as f64 * 1e+09;
	let unit = "B/s";
	let rate = match Signifix::try_from(bytes_per_second) {
		Ok(rate) => if rate.factor() < 1e+00 {
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
	assert_eq!(rate.chars().count(), DEF_MIN_LEN + unit.chars().count());
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

use signifix::{Signifix, Result, DEF_MAX_LEN};

let format_load = |amps| -> Result<String> {
	if let Some(amps) = amps {
		Signifix::try_from(amps)
			.map(|amps| format!("{:>1$}A", amps, DEF_MAX_LEN))
	} else {
		Ok("     0  A".into())
	}
};

assert_eq!(format_load(Some( 1.476e-06)), Ok(" 1.476 µA".into()));
assert_eq!(format_load(None),             Ok("     0  A".into()));
assert_eq!(format_load(Some(-2.927e-06)), Ok("-2.927 µA".into()));
```

While to visualize a change in file size, a plus sign might be preferred for
positive numbers:

```rust
use std::convert::TryFrom; // Until stabilized.

use signifix::{Signifix, Result, Error};

let format_diff = |curr, prev| -> Result<String> {
	Signifix::try_from(curr - prev).map(|diff| format!("{:+#}", diff))
		.or_else(|case| if case == Error::OutOfLowerBound(0f64)
			{ Ok("=const".into()) } else { Err(case) })
};

assert_eq!(format_diff(78_346, 57_393), Ok("+20k95".into()));
assert_eq!(format_diff(93_837, 93_837), Ok("=const".into()));
assert_eq!(format_diff(27_473, 36_839), Ok("-9k366".into()));
```
