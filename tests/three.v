From HB Require Import structures.

From mathcomp Require Import
  ssreflect ssrfun ssrbool ssrnat eqtype seq choice fintype finset order.

From deriving Require Import deriving.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Inductive three := A of bool & bool | B | C.

Definition three_indDef :=
  [indDef for three_rect].
Canonical three_indType :=
  Eval hnf in IndType three three_indDef.

Definition three_eqMixin :=
  [derive eqMixin for three].
HB.instance Definition _ := three_eqMixin.
Definition three_choiceMixin :=
  [derive choiceMixin for three].
HB.instance Definition _ := three_choiceMixin.
Definition three_countMixin :=
  [derive countMixin for three].
HB.instance Definition _ := three_countMixin.
Definition three_finMixin :=
  [derive finMixin for three].
HB.instance Definition _ := three_finMixin.
Definition three_orderMixin :=
  [derive orderMixin for three].
HB.instance Definition _ := three_orderMixin.
