From HB Require Import structures.

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

Section TreeEqType.
Variable T : eqType.
Definition tree_eqMixin := [derive eqMixin for tree T].
HB.instance Definition _ := tree_eqMixin.
End TreeEqType.

Section TreeChoiceType.
Variable T : choiceType.
Definition tree_choiceMixin := [derive choiceMixin for tree T].
HB.instance Definition _ := tree_choiceMixin.
End TreeChoiceType.

Section TreeCountType.
Variable T : countType.
Definition tree_countMixin := [derive countMixin for tree T].
HB.instance Definition _ := tree_countMixin.
End TreeCountType.
