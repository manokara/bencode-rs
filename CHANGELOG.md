# Changelog

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [Unreleased]

### Changed

- Allow index to be equal to length in Value::insert

## [0.9.1]

### Changed

- Implement `Display` for `UpdateError`
- Expose `UpdateError` in the crate root

## [0.9.0] - 2020-12-31

### Added

- `Value::insert` and `Value::remove` methods
- `Value::has` to check if a dictionary has a key
- `"."` selector as an alias for the root value in `Value::select`.

## [0.8.1] - 2020-11-12

### Changed

- json: Fixed valid strings being considered bytes
- parser: Throw syntax error if there are trailing data

## [0.8.0] - 2020-11-11

### Added

- Make ValueAccessor public so it can show in the docs
- Add load_prim() function
- Add conversions from stdlib types to Values
- Allow comparing primitive Values to stdlib types
- Add Value::encode() function
- Add a test for Value::traverse()
- Add README
- JSON serialization with nanoserde
- Allow Value references to be compared to owned integer
- Comparing Values with byte slices and vecs
- Benchmarks
- Stream wrapper
- Recursion limit if the stream has no known size

### Changed

- Split library into different modules
- Use byte slices in load_str() functions
- Change the concept of "context" in traverse() and select()
- The `value` argument of the `Value::traverse` closure is now optional.
- Now `load()` handles both `Read`able types and slices.

### Removed

- `Dict` and `Done` states in the parser.
- `load_str`, `load_dict_str`, `load_list_str` and `load_prim_str` functions.

## [0.7.0] - 2020-11-06

### Added

- Missing documentation
- Add load_dict and load_list functions
- Add Value::get() and Value::get_mut()
- Add Value::select_mut()

### Changed

- Rename Error to ParserError
- Move LocalValue out of load()
- Make Value::traverse() use get()
- Refactor Value::select() to not use traverse() anymore

### Removed

- Unnecessary variants in Error

## [0.6.0] - 2020-10-26

`0.6.0` is somewhat arbitrary as originally this library used to be a part of another project.

### Added

- Load bencode files
- Display Values
- Value::select() method
- Customizable ValueDisplay
- Show bytes left in repr_bytes()
- Bencode samples
- Value::traverse() method
- Value::len() method

### Changed

- Limit stack depth in ValueDisplay
- Fixed empty dicts causing syntax errors
- Decrease stack count when popping containers in ValueDisplay
- Truncate long lists in ValueDisplay
- Dict iterators do not need to be peekable in ValueDisplay
- Use a builder pattern to change parameters in ValueDisplay
- Use container stacks with last/last_mut() instead of indexing
- Make dict keys Strings
- Make Value::select() and ValueDisplay::fmt() use Value::traverse()
- Fixed list remainder in ValueDisplay being off by 10. Turns out I was using the iterator to get the number of items.

### Removed

- Ref variants from Value
- Debug prints

[Unreleased]: https://github.com/manokara/bencode-rs/compare/v0.9.1...HEAD
[0.9.1]: https://github.com/manokara/bencode-rs/compare/v0.9.0...v0.9.1
[0.9.0]: https://github.com/manokara/bencode-rs/compare/v0.8.1...v0.9.0
[0.8.1]: https://github.com/manokara/bencode-rs/compare/v0.8.0...v0.8.1
[0.8.0]: https://github.com/manokara/bencode-rs/compare/v0.7.0...v0.8.0
[0.7.0]: https://github.com/manokara/bencode-rs/compare/v0.6.0...v0.7.0
[0.6.0]: https://github.com/manokara/bencode-rs/releases/tag/v0.6.0

