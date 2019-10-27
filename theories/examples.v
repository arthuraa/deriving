From mathcomp Require Import
  ssreflect ssrfun ssrbool ssrnat eqtype seq choice fintype.

From void Require Import void.

From deriving Require Import deriving.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module RecursiveExample.

Inductive tree (T : Type) :=
| Leaf of nat
| Node of T & tree T & tree T.
Arguments Leaf {_} _.

Definition tree_indMixin T :=
  Eval simpl in [indMixin for @tree_rect T].
Canonical tree_indType T :=
  Eval hnf in IndType _ _ (tree_indMixin T).

Definition tree_eqMixin (T : eqType) :=
  Eval simpl in [derive eqMixin for tree T].
Canonical tree_eqType (T : eqType) :=
  Eval hnf in EqType (tree T) (tree_eqMixin T).
Definition tree_choiceMixin (T : choiceType) :=
  [derive choiceMixin for tree T].
Canonical tree_choiceType (T : choiceType) :=
  Eval hnf in ChoiceType (tree T) (tree_choiceMixin T).
Definition tree_countMixin (T : countType) :=
  [derive countMixin for tree T].
Canonical tree_countType (T : countType) :=
  Eval hnf in CountType (tree T) (tree_countMixin T).

End RecursiveExample.

Module FiniteExample.

Inductive three := A of unit & bool | B | C.

Definition three_indMixin :=
  Eval simpl in [indMixin for three_rect].
Canonical three_indType :=
  Eval hnf in IndType _ _ three_indMixin.

Definition three_eqMixin :=
  Eval simpl in [derive eqMixin for three].
Canonical three_eqType :=
  Eval hnf in EqType three three_eqMixin.
Definition three_choiceMixin := [derive choiceMixin for three].
Canonical three_choiceType :=
  Eval hnf in ChoiceType three three_choiceMixin.
Definition three_countMixin := [derive countMixin for three].
Canonical three_countType :=
  Eval hnf in CountType three three_countMixin.
Definition three_finMixin :=
  Eval simpl in [derive finMixin for three].
Canonical three_finType :=
  Eval hnf in FinType three three_finMixin.

End FiniteExample.
