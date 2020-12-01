From mathcomp Require Import
  ssreflect ssrfun ssrbool ssrnat eqtype seq choice fintype finset order.

From deriving Require Import deriving.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Inductive three := A of bool & bool | B | C.

Definition three_indMixin :=
  [indMixin for three_rect].
Canonical three_indType :=
  Eval hnf in IndType three three_indMixin.

Definition three_eqMixin :=
  [derive eqMixin for three].
Canonical three_eqType :=
  Eval hnf in EqType three three_eqMixin.
Definition three_choiceMixin :=
  [derive choiceMixin for three].
Canonical three_choiceType :=
  Eval hnf in ChoiceType three three_choiceMixin.
Definition three_countMixin :=
  [derive countMixin for three].
Canonical three_countType :=
  Eval hnf in CountType three three_countMixin.
Definition three_finMixin :=
  [derive finMixin for three].
Canonical three_finType :=
  Eval hnf in FinType three three_finMixin.
Definition three_orderMixin :=
  [derive lazy orderMixin for three].
Canonical three_porderType :=
  Eval hnf in POrderType tt three three_orderMixin.
Canonical three_latticeType :=
  Eval hnf in LatticeType three three_orderMixin.
Canonical three_distrLatticeType :=
  Eval hnf in DistrLatticeType three three_orderMixin.
Canonical three_orderType :=
  Eval hnf in OrderType three three_orderMixin.
