# Version 0.5.0 (2017-02-27)

* Added common `Error`/`Result` types for the `metric`/`binary` modules.
* Refactored crate into `metric`/`binary` modules.
* Defined Signifix default notation with binary prefix (`1.234 Ki`, `1 023 Ki`).
* Replaced `f64` divisions by multiplications whenever the inverse is known.

# Version 0.4.1 (2017-02-17)

* Changed license from LGPL-3.0 to Fair.

# Version 0.4.0 (2017-02-14)

* Refactored examples and documentation.
* Reassigned alternate flag to alternate notation, thanks to padding support.
* Complemented `DEF_MIN_LEN`/`DEF_MAX_LEN` with `ALT_MIN_LEN`/`ALT_MAX_LEN`.
* Renamed `MAX_LEN` to `DEF_MAX_LEN` and `MIN_LEN` to `DEF_MAX_LEN`.
* Wrapped return value of `symbol()` method in `Option`.
* Wrapped elements of `SYMBOLS` in `Option` with `' '` becoming `None`.
* Renamed `SYMBOL` to `SYMBOLS` and `FACTOR` to `FACTORS`.
* Defined Signifix default (`1.234 k`) and alternate (`1k234`) notation with
  metric prefix.
* Added `integer()`, `fractional()`, and `parts()` methods.
* Fixed missing padding support via fill/alignment formatting parameters.

# Version 0.3.0 (2017-01-31)

* Covered `i128`/`u128`.
* Replaced public fields by methods.
* Shrank `Signifix` type from 24 to 4 B.
* Implemented `Ord` trait.
* Added public constants `MIN_LEN` and `MAX_LEN`.
* Added public constants `SYMBOL` and `FACTOR`.

# Version 0.2.0 (2016-12-17)

* Covered `isize`/`usize` and `i64`/`u64`.
* Replaced methods by public fields.
* Added `Error::Nan` variant.

# Version 0.1.0 (2016-12-04)

* Initial release
