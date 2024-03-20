From HB Require Import structures.
From mathcomp Require Import
  ssreflect ssrfun ssrbool ssrnat eqtype seq choice fintype order.

From deriving Require Import base ind tactics infer.
From deriving.instances Require Export eqtype tree_of_ind fintype order.

From Coq Require Import ZArith NArith String Ascii.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Open Scope deriving_scope.

Definition unit_indDef :=
  [indDef for unit_rect].
Canonical unit_indType :=
  IndType unit unit_indDef.

Definition void_indDef :=
  [indDef for Empty_set_rect].
Canonical void_indType :=
  IndType void void_indDef.

Definition bool_indDef :=
  [indDef for bool_rect].
Canonical bool_indType :=
  IndType bool bool_indDef.

Definition nat_indDef :=
  [indDef for nat_rect].
Canonical nat_indType :=
  IndType nat nat_indDef.

Definition option_indDef T :=
  [indDef for @option_rect T].
Canonical option_indType T :=
  IndType (option T) (option_indDef T).
Section OptionOrderType.
Variable Tord : orderType Order.default_display.
Definition option_isOrder :=
  Eval hnf in [derive isOrder for option Tord].
HB.instance Definition _ := option_isOrder.
End OptionOrderType.

Definition sum_indDef T1 T2 :=
  [indDef for @sum_rect T1 T2].
Canonical sum_indType T1 T2 :=
  IndType (T1 + T2) (sum_indDef T1 T2).

Definition prod_indDef T1 T2 :=
  [indDef for @prod_rect T1 T2].
Canonical prod_indType T1 T2 :=
  IndType (T1 * T2) (prod_indDef T1 T2).

Definition seq_indDef T :=
  [indDef for @list_rect T].
Canonical seq_indType T :=
  IndType (seq T) (seq_indDef T).

Definition comparison_indDef :=
  [indDef for comparison_rect].
Canonical comparison_indType :=
  IndType comparison comparison_indDef.
Definition comparison_hasDecEq :=
  [derive hasDecEq for comparison].
HB.instance Definition _ := comparison_hasDecEq.
Definition comparison_hasChoice :=
  [derive hasChoice for comparison].
HB.instance Definition _ := comparison_hasChoice.
Definition comparison_isCountable :=
  [derive isCountable for comparison].
HB.instance Definition _ := comparison_isCountable.
Definition comparison_isFinite :=
  [derive isFinite for comparison].
HB.instance Definition _ := comparison_isFinite.

Definition positive_indDef :=
  [indDef for positive_rect].
Canonical positive_indType :=
  IndType positive positive_indDef.
Definition positive_hasDecEq :=
  [derive hasDecEq for positive].
HB.instance Definition _ := positive_hasDecEq.
Definition positive_hasChoice :=
  [derive hasChoice for positive].
HB.instance Definition _ := positive_hasChoice.
Definition positive_isCountable :=
  [derive isCountable for positive].
HB.instance Definition _ := positive_isCountable.

Definition bin_nat_indDef :=
  [indDef for N_rect].
Canonical bin_nat_indType :=
  IndType N bin_nat_indDef.
Definition bin_nat_hasChoice :=
  [derive hasChoice for N].
HB.instance Definition _ := bin_nat_hasChoice.
Definition bin_nat_isCountable :=
  [derive isCountable for N].
HB.instance Definition _ := bin_nat_isCountable.

Definition Z_indDef :=
  [indDef for Z_rect].
Canonical Z_indType :=
  IndType Z Z_indDef.
Definition Z_hasDecEq :=
  [derive hasDecEq for Z].
HB.instance Definition _ := Z_hasDecEq.
Definition Z_hasChoice :=
  [derive hasChoice for Z].
HB.instance Definition _ := Z_hasChoice.
Definition Z_isCountable :=
  [derive isCountable for Z].
HB.instance Definition _ := Z_isCountable.

Definition ascii_indDef :=
  [indDef for ascii_rect].
Canonical ascii_indType :=
  IndType ascii ascii_indDef.
Definition ascii_hasDecEq :=
  [derive hasDecEq for ascii].
HB.instance Definition _ := ascii_hasDecEq.
Definition ascii_hasChoice :=
  [derive hasChoice for ascii].
HB.instance Definition _ := ascii_hasChoice.
Definition ascii_isCountable :=
  [derive isCountable for ascii].
HB.instance Definition _ := ascii_isCountable.
Definition ascii_isFinite :=
  [derive isFinite for ascii].
HB.instance Definition _ := ascii_isFinite.
Definition ascii_isOrder :=
  [derive isOrder for ascii].
HB.instance Definition _ := ascii_isOrder.

Definition string_indDef :=
  [indDef for string_rect].
Canonical string_indType :=
  IndType string string_indDef.
Definition string_hasDecEq :=
  [derive hasDecEq for string].
HB.instance Definition _ := string_hasDecEq.
Definition string_hasChoice :=
  [derive hasChoice for string].
HB.instance Definition _ := string_hasChoice.
Definition string_isCountable :=
  [derive isCountable for string].
HB.instance Definition _ := string_isCountable.
Definition string_isOrder :=
  [derive isOrder for string].
HB.instance Definition _ := string_isOrder.
