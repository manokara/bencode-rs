# Changelog

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [0.8.0] - 2020-11-08

### Added

- Make ValueAccessor public so it can show in the docs
- Add load_prim() function
- Add functions to convert stdlib types to Values
- Allow comparing primitive Values to stdlib types
- Add Value::encode() function
- Add a test for Value::traverse()
- Add README

### Changed

- Split library into different modules
- Use byte slices in load_str() functions
- Change the concept of "context" in traverse() and select()

### Removed

- `Dict` and `Done` states in the parser.

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

[Unreleased]: https://github.com/manokara/bencode-rs/compare/v0.8.0...HEAD
[0.8.0]: https://github.com/manokara/bencode-rs/compare/v0.7.0...v0.8.0
[0.7.0]: https://github.com/manokara/bencode-rs/compare/v0.6.0...v0.7.0
[0.6.0]: https://github.com/manokara/bencode-rs/releases/tag/v0.6.0
