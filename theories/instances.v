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
Variable Tord : orderType tt.
Definition option_orderMixin :=
  Eval hnf in [derive orderMixin for option Tord].
HB.instance Definition _ := option_orderMixin.
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
Definition comparison_eqMixin :=
  [derive eqMixin for comparison].
HB.instance Definition _ := comparison_eqMixin.
Definition comparison_choiceMixin :=
  [derive choiceMixin for comparison].
HB.instance Definition _ := comparison_choiceMixin.
Definition comparison_countMixin :=
  [derive countMixin for comparison].
HB.instance Definition _ := comparison_countMixin.
Definition comparison_finMixin :=
  [derive finMixin for comparison].
HB.instance Definition _ := comparison_finMixin.

Definition positive_indDef :=
  [indDef for positive_rect].
Canonical positive_indType :=
  IndType positive positive_indDef.
Definition positive_eqMixin :=
  [derive eqMixin for positive].
HB.instance Definition _ := positive_eqMixin.
Definition positive_choiceMixin :=
  [derive choiceMixin for positive].
HB.instance Definition _ := positive_choiceMixin.
Definition positive_countMixin :=
  [derive countMixin for positive].
HB.instance Definition _ := positive_countMixin.

Definition bin_nat_indDef :=
  [indDef for N_rect].
Canonical bin_nat_indType :=
  IndType N bin_nat_indDef.
Definition bin_nat_choiceMixin :=
  [derive choiceMixin for N].
HB.instance Definition _ := bin_nat_choiceMixin.
Definition bin_nat_countMixin :=
  [derive countMixin for N].
HB.instance Definition _ := bin_nat_countMixin.

Definition Z_indDef :=
  [indDef for Z_rect].
Canonical Z_indType :=
  IndType Z Z_indDef.
Definition Z_eqMixin :=
  [derive eqMixin for Z].
HB.instance Definition _ := Z_eqMixin.
Definition Z_choiceMixin :=
  [derive choiceMixin for Z].
HB.instance Definition _ := Z_choiceMixin.
Definition Z_countMixin :=
  [derive countMixin for Z].
HB.instance Definition _ := Z_countMixin.

Definition ascii_indDef :=
  [indDef for ascii_rect].
Canonical ascii_indType :=
  IndType ascii ascii_indDef.
Definition ascii_eqMixin :=
  [derive eqMixin for ascii].
HB.instance Definition _ := ascii_eqMixin.
Definition ascii_choiceMixin :=
  [derive choiceMixin for ascii].
HB.instance Definition _ := ascii_choiceMixin.
Definition ascii_countMixin :=
  [derive countMixin for ascii].
HB.instance Definition _ := ascii_countMixin.
Definition ascii_finMixin :=
  [derive finMixin for ascii].
HB.instance Definition _ := ascii_finMixin.
Definition ascii_orderMixin :=
  [derive orderMixin for ascii].
HB.instance Definition _ := ascii_orderMixin.

Definition string_indDef :=
  [indDef for string_rect].
Canonical string_indType :=
  IndType string string_indDef.
Definition string_eqMixin :=
  [derive eqMixin for string].
HB.instance Definition _ := string_eqMixin.
Definition string_choiceMixin :=
  [derive choiceMixin for string].
HB.instance Definition _ := string_choiceMixin.
Definition string_countMixin :=
  [derive countMixin for string].
HB.instance Definition _ := string_countMixin.
Definition string_orderMixin :=
  [derive orderMixin for string].
HB.instance Definition _ := string_orderMixin.
