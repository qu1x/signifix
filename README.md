# signifix

Number Formatter of Fixed Significance with Metric Unit Prefix

[![Build Status](https://travis-ci.org/qu1x/signifix.svg?branch=master)](https://travis-ci.org/qu1x/signifix)

[Documentation](https://docs.rs/signifix/0.1.0/signifix/)

Signifix guarantees a fixed number of significant figures and a fixed number
of resulting characters by automatically choosing the metric unit prefix and
appropriately adjusting the floating point precision.

## Usage

This crate is [on crates.io](https://crates.io/crates/signifix) and can be
used by adding `signifix` to the dependencies in your project's
`Cargo.toml`:

```toml
[dependencies]
signifix = "0.1.0"
```

and this to your crate root:

```rust
extern crate signifix;
```

## Examples

The fixed number of significant figures and resulting characters prevent the
digits and prefixed units from jumping to the left or right:

```rust
#![feature(try_from)]
use std::convert::TryFrom;

use signifix::{Signifix, Result};

let format = |number| -> Result<String> {
	Ok(format!("{}", Signifix::try_from(number)?))
};

assert_eq!(format(1e-04).ok(), Some("100.0 µ".into()));
assert_eq!(format(1e-03).ok(), Some("1.000 m".into()));
assert_eq!(format(1e-02).ok(), Some("10.00 m".into()));
assert_eq!(format(1e-01).ok(), Some("100.0 m".into()));
assert_eq!(format(1e+00).ok(), Some("1.000  ".into()));
assert_eq!(format(1e+01).ok(), Some("10.00  ".into()));
assert_eq!(format(1e+02).ok(), Some("100.0  ".into()));
assert_eq!(format(1e+03).ok(), Some("1.000 k".into()));
assert_eq!(format(1e+04).ok(), Some("10.00 k".into()));
assert_eq!(format(1e+05).ok(), Some("100.0 k".into()));
assert_eq!(format(1e+06).ok(), Some("1.000 M".into()));
```

This is useful to smoothly refresh a transfer rate inside a terminal:

```rust
#![feature(try_from)]
use std::convert::TryFrom;

use signifix::{Signifix, Result};

let format_rate = |bytes, seconds| -> Result<String> {
	Ok(format!("{}B/s", Signifix::try_from(bytes as f64 / seconds as f64)?))
};

assert_eq!(format_rate(42_667, 300).ok(), Some("142.2  B/s".into()));
assert_eq!(format_rate(42_667,  30).ok(), Some("1.422 kB/s".into()));
assert_eq!(format_rate(42_667,   3).ok(), Some("14.22 kB/s".into()));
```

Or to monitor a measured quantity like an electrical current including its
direction with an optional space placeholder to align with negative values.

```rust
#![feature(try_from)]
use std::convert::TryFrom;

use signifix::{Signifix, Result};

let format_load = |current| -> Result<String> {
	Ok(format!("{:#}A", Signifix::try_from(current)?))
};

assert_eq!(format_load( 1.476e-06).ok(), Some(" 1.476 µA".into()));
assert_eq!(format_load(-2.927e-06).ok(), Some("-2.927 µA".into()));
```

In case of displaying a file size difference after modification, a plus sign
might be preferred for positive values:

```rust
#![feature(try_from)]
use std::convert::TryFrom;

use signifix::{Signifix, Result};

let format_diff = |curr, prev| -> Result<String> {
	Ok(format!("{:+}B", Signifix::try_from(curr - prev)?))
};

assert_eq!(format_diff(78_346, 57_393).ok(), Some("+20.95 kB".into()));
assert_eq!(format_diff(27_473, 46_839).ok(), Some("-19.37 kB".into()));
```
