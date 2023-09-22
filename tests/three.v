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

Definition three_hasDecEq :=
  [derive hasDecEq for three].
HB.instance Definition _ := three_hasDecEq.
Definition three_hasChoice :=
  [derive hasChoice for three].
HB.instance Definition _ := three_hasChoice.
Definition three_isCountable :=
  [derive isCountable for three].
HB.instance Definition _ := three_isCountable.
Definition three_isFinite :=
  [derive isFinite for three].
HB.instance Definition _ := three_isFinite.
Definition three_isOrder :=
  [derive isOrder for three].
HB.instance Definition _ := three_isOrder.
