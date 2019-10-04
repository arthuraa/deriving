From mathcomp Require Import
  ssreflect ssrfun ssrbool ssrnat eqtype seq choice fintype.

Require Import deriving.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module RecursiveExample.

Inductive tree (T : Type) :=
| Leaf of nat
| Node of T & tree T & tree T.
Arguments Leaf {_} _.

Definition tree_coqIndMixin T :=
  Eval simpl in [coqIndMixin for @tree_rect T].
Canonical tree_coqIndType T :=
  Eval hnf in CoqIndType _ _ (tree_coqIndMixin T).

Definition tree_eqMixin (T : eqType) :=
  Eval simpl in [indEqMixin for tree T].
Canonical tree_eqType (T : eqType) :=
  Eval hnf in EqType (tree T) (tree_eqMixin T).
Definition tree_choiceMixin (T : choiceType) :=
  [indChoiceMixin for tree T].
Canonical tree_choiceType (T : choiceType) :=
  Eval hnf in ChoiceType (tree T) (tree_choiceMixin T).
Definition tree_countMixin (T : countType) :=
  [indCountMixin for tree T].
Canonical tree_countType (T : countType) :=
  Eval hnf in CountType (tree T) (tree_countMixin T).

End RecursiveExample.

Module FiniteExample.

Inductive three := A of unit & bool | B | C.

Definition three_coqIndMixin :=
  Eval simpl in [coqIndMixin for three_rect].
Canonical three_coqIndType :=
  Eval hnf in CoqIndType _ _ three_coqIndMixin.

Definition three_eqMixin :=
  Eval simpl in [indEqMixin for three].
Canonical three_eqType :=
  Eval hnf in EqType three three_eqMixin.
Definition three_choiceMixin := [indChoiceMixin for three].
Canonical three_choiceType :=
  Eval hnf in ChoiceType three three_choiceMixin.
Definition three_countMixin := [indCountMixin for three].
Canonical three_countType :=
  Eval hnf in CountType three three_countMixin.
Definition three_finMixin :=
  Eval simpl in [indFinMixin for three].
Canonical three_finType :=
  Eval hnf in FinType three three_finMixin.

End FiniteExample.
