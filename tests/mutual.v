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
Canonical foo_indType := IndType _ foo foo_bar_baz_indDef.
Canonical bar_indType := IndType _ bar foo_bar_baz_indDef.
Canonical baz_indType := IndType _ baz foo_bar_baz_indDef.

Definition foo_eqMixin := [derive lazy eqMixin for foo].
Canonical foo_eqType := EqType foo foo_eqMixin.
Definition bar_eqMixin := [derive lazy eqMixin for bar].
Canonical bar_eqType := EqType bar bar_eqMixin.
Definition baz_eqMixin := [derive lazy eqMixin for baz].
Canonical baz_eqType := EqType baz baz_eqMixin.
Definition foo_choiceMixin := [derive choiceMixin for foo].
Canonical foo_choiceType := Eval hnf in ChoiceType foo foo_choiceMixin.
Definition bar_choiceMixin := [derive choiceMixin for bar].
Canonical bar_choiceType := Eval hnf in ChoiceType bar bar_choiceMixin.
Definition baz_choiceMixin := [derive choiceMixin for baz].
Canonical baz_choiceType := Eval hnf in ChoiceType baz baz_choiceMixin.
Definition foo_countMixin := [derive countMixin for foo].
Canonical foo_countType := Eval hnf in CountType foo foo_countMixin.
Definition bar_countMixin := [derive countMixin for bar].
Canonical bar_countType := Eval hnf in CountType bar bar_countMixin.
Definition baz_countMixin := [derive countMixin for baz].
Canonical baz_countType := Eval hnf in CountType baz baz_countMixin.
Definition foo_orderMixin := [derive lazy orderMixin for foo].
Canonical foo_porderType := Eval hnf in POrderType tt foo foo_orderMixin.
Canonical foo_latticeType := Eval hnf in LatticeType foo foo_orderMixin.
Canonical foo_distrLatticeType := Eval hnf in DistrLatticeType foo foo_orderMixin.
Canonical foo_orderType := Eval hnf in OrderType foo foo_orderMixin.
Definition bar_orderMixin := [derive lazy orderMixin for bar].
Canonical bar_porderType := Eval hnf in POrderType tt bar bar_orderMixin.
Canonical bar_latticeType := Eval hnf in LatticeType bar bar_orderMixin.
Canonical bar_distrLatticeType := Eval hnf in DistrLatticeType bar bar_orderMixin.
Canonical bar_orderType := Eval hnf in OrderType bar bar_orderMixin.
Definition baz_orderMixin := [derive lazy orderMixin for baz].
Canonical baz_porderType := Eval hnf in POrderType tt baz baz_orderMixin.
Canonical baz_latticeType := Eval hnf in LatticeType baz baz_orderMixin.
Canonical baz_distrLatticeType := Eval hnf in DistrLatticeType baz baz_orderMixin.
Canonical baz_orderType := Eval hnf in OrderType baz baz_orderMixin.
