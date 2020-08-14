# Deriving ─ Generic instances for Coq inductive types

[![arthuraa](https://circleci.com/gh/arthuraa/deriving.svg?style=shield)](https://circleci.com/gh/arthuraa/deriving/tree/master)

The Deriving library builds instances of basic MathComp classes for inductive
data types with little boilerplate, akin to Haskell's `deriving` functionality.
To define an `eqType` instance for a type `foo`, just write:

    From mathcomp Require Import ssreflect ssrnat eqtype.
    From deriving Require Import deriving.

    Inductive foo := Foo of nat.

    Definition foo_indMixin := Eval simpl in [indMixin for foo_rect].
    Canonical foo_indType := IndType _ foo foo_indMixin.

    Definition foo_eqMixin := Eval simpl in [derive eqMixin for foo].
    Canonical foo_eqType := EqType foo foo_eqMixin.

## Usage and limitations

Besides `eqType`, there are predefined generic instances for `choiceType`,
`countType` and `finType`.  Check out the examples in `theories/examples.v`.
You can also write generic instances for your own classes (though this currently
requires some non-trivial dependently typed hacking).  Currently, the library
does not support nested inductive types, mutual inductive types or indexed
types.

## Requirements

- Coq 8.10

- `coq-mathcomp-ssreflect` 1.10

## Build instructions

To compile, do

```shell
make
```

To install, do

```shell
make install
```
