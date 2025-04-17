# Changelog
All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [Unreleased]

### Added

### Changed

### Deprecated

### Removed

### Fixed

## [0.2.2] - 2025-04-17

### Fixed

- Add explicit import of `Coq.Setoid`, for compatibility with MathComp 2.4.0.

## [0.2.1] - 2024-12-02

### Changed

- Use new display type for `orderType`, as in MathComp 2.3.0.  The generated
  instances now use the default display.

### Fixed

- Simplify the type of derived isFinite instances to avoid a non-forgetful
  inheritance warning.

## [0.2.0] - 2023-09-22

### Changed
- Make Deriving compatible with Hierarchy Builder and MathComp 2.0.0.

- Following the changes of terminology in MathComp, the syntax for deriving the
  base mixins has now the form `[derive [<flag>] <mixin> for <type>]`, where
  + `<flag>` is one of `red`, `nored` or `lazy`.
  + `<mixin>` is one of `hasDecEq`, `hasChoice`, `isCountable`, `isFinite` or
    `isOrder`.

### Deprecated

- The derivation forms `[derive ...]` that mention the old MathComp mixin names
  `eqMixin`, `choiceMixin`, `countMixin`, `finMixin` and `orderMixin` are
  deprecated.  Use the new names for those mixins, as explained in the previous
  section.

## [0.1.1] - 2023-03-10
### Fixed
- Add `global` locality annotations to comply with newer versions of Coq

## [0.1.0] - 2020-02-24
### Added
- First version supporting inductive types.

[Unreleased]: https://github.com/arthuraa/deriving/compare/v0.2.2...HEAD
[0.2.2]: https://github.com/arthuraa/deriving/releases/tag/v0.2.2
[0.2.1]: https://github.com/arthuraa/deriving/releases/tag/v0.2.1
[0.2.0]: https://github.com/arthuraa/deriving/releases/tag/v0.2.0
[0.1.1]: https://github.com/arthuraa/deriving/releases/tag/v0.1.1
[0.1.0]: https://github.com/arthuraa/deriving/releases/tag/v0.1.0

