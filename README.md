# Deriving ─ Generic instances for Coq inductive types

The Deriving library builds instances of basic MathComp classes for inductive
data types with little boilerplate, akin to Haskell's `deriving` functionality.
To define an `eqType` instance for a type `foo`, just write:

    From mathcomp Require Import ssreflect eqtype.
    From deriving Require Import deriving.

    Inductive foo := Foo of nat.

    Definition foo_coqIndMixin := Eval simpl in [coqIndMixin for foo_rect].
    Canonical foo_coqIndType := CoqIndType _ foo foo_coqIndMixin.

    Definition foo_eqMixin := Eval simpl in [indEqMixin for foo].
    Canonical foo_eqType := EqType foo foo_eqMixin.

## Usage and limitations

Besides `eqType`, there are predefined generic instances for `choiceType`,
`countType` and `finType`.  Check out the examples in `theories/examples.v`.
You can also write generic instances for your own classes (though this currently
requires some non-trivial dependently typed hacking).  Currently, the library
does not support nested inductive types, mutual inductive types or indexed
types.

## Requirements

- Coq 8.9

- `coq-mathcomp-ssreflect` 1.9

- `coq-void` (https://github.com/arthuraa/coq-void)

## Build instructions

To compile, do

```shell
make
```

To install, do

```shell
make install
```

## TODO

- Documentation

- Clean up code

- Support mutually inductive types
