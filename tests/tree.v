From mathcomp Require Import
  ssreflect ssrfun ssrbool ssrnat eqtype seq choice fintype finset order.

From deriving Require Import deriving.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Inductive tree (T : Type) :=
| Leaf of {set 'I_10}
| Node of T & tree T & tree T.
Arguments Leaf {_} _.

Definition tree_indDef T :=
  [indDef for @tree_rect T].
Canonical tree_indType T :=
  Eval hnf in IndType (tree T) (tree_indDef T).

Definition tree_eqMixin (T : eqType) :=
  [derive eqMixin for tree T].
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
