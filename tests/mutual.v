From HB Require Import structures.

From mathcomp Require Import
  ssreflect ssrfun ssrbool ssrnat eqtype seq choice fintype finset order.

From deriving Require Import deriving.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Unset Elimination Schemes.
Inductive foo :=
| Foo1 of nat
| Foo2 of bool & bar

with bar :=
| Bar1 of foo & foo
| Bar2 of nat & foo

with baz :=
| Baz of foo & baz.
Set Elimination Schemes.

Scheme foo_rect := Induction for foo Sort Type
with   bar_rect := Induction for bar Sort Type
with   baz_rect := Induction for baz Sort Type.

Combined Scheme foo_bar_baz_rect from foo_rect, bar_rect, baz_rect.

Definition foo_bar_baz_indDef := [indDef for foo_bar_baz_rect].
Canonical foo_indType := IndType foo foo_bar_baz_indDef.
Canonical bar_indType := IndType bar foo_bar_baz_indDef.
Canonical baz_indType := IndType baz foo_bar_baz_indDef.

Definition foo_eqMixin := [derive lazy eqMixin for foo].
HB.instance Definition _ := foo_eqMixin.
Definition bar_eqMixin := [derive lazy eqMixin for bar].
HB.instance Definition _ := bar_eqMixin.
Definition baz_eqMixin := [derive lazy eqMixin for baz].
HB.instance Definition _ := baz_eqMixin.
Definition foo_choiceMixin := [derive choiceMixin for foo].
HB.instance Definition _ := foo_choiceMixin.
Definition bar_choiceMixin := [derive choiceMixin for bar].
HB.instance Definition _ := bar_choiceMixin.
Definition baz_choiceMixin := [derive choiceMixin for baz].
HB.instance Definition _ := baz_choiceMixin.
Definition foo_countMixin := [derive countMixin for foo].
HB.instance Definition _ := foo_countMixin.
Definition bar_countMixin := [derive countMixin for bar].
HB.instance Definition _ := bar_countMixin.
Definition baz_countMixin := [derive countMixin for baz].
HB.instance Definition _ := baz_countMixin.
Definition foo_orderMixin := [derive lazy orderMixin for foo].
HB.instance Definition _ := foo_orderMixin.
Definition bar_orderMixin := [derive lazy orderMixin for bar].
HB.instance Definition _ := bar_orderMixin.
Definition baz_orderMixin := [derive lazy orderMixin for baz].
HB.instance Definition _ := baz_orderMixin.
