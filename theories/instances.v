From mathcomp Require Import
  ssreflect ssrfun ssrbool ssrnat eqtype seq choice fintype order.

From deriving Require Import base ind tactics infer.
From deriving.instances Require Export eqtype tree_of_ind fintype order.

From Coq Require Import ZArith NArith String Ascii.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Open Scope deriving_scope.

Section Instances.

Implicit Types T : Type.
Implicit Types Teq : eqType.
Implicit Types Tord : orderType tt.

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
Definition option_orderMixin Tord :=
  [derive orderMixin for option Tord].
Canonical option_porderType Tord :=
  Eval hnf in POrderType tt (option Tord) (option_orderMixin Tord).
Canonical option_latticeType Tord :=
  Eval hnf in LatticeType (option Tord) (option_orderMixin Tord).
Canonical option_distrLatticeType Tord :=
  Eval hnf in DistrLatticeType (option Tord) (option_orderMixin Tord).
Canonical option_orderType Tord :=
  Eval hnf in OrderType (option Tord) (option_orderMixin Tord).

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
Canonical comparison_eqType :=
  Eval hnf in EqType comparison comparison_eqMixin.
Definition comparison_choiceMixin :=
  [derive choiceMixin for comparison].
Canonical comparison_choiceType :=
  Eval hnf in ChoiceType comparison comparison_choiceMixin.
Definition comparison_countMixin :=
  [derive countMixin for comparison].
Canonical comparison_countType :=
  Eval hnf in CountType comparison comparison_countMixin.
Definition comparison_finMixin :=
  [derive finMixin for comparison].
Canonical comparison_finType :=
  Eval hnf in FinType comparison comparison_finMixin.

Definition positive_indDef :=
  [indDef for positive_rect].
Canonical positive_indType :=
  IndType positive positive_indDef.
Definition positive_eqMixin :=
  [derive eqMixin for positive].
Canonical positive_eqType :=
  Eval hnf in EqType positive positive_eqMixin.
Definition positive_choiceMixin :=
  [derive choiceMixin for positive].
Canonical positive_choiceType :=
  Eval hnf in ChoiceType positive positive_choiceMixin.
Definition positive_countMixin :=
  [derive countMixin for positive].
Canonical positive_countType :=
  Eval hnf in CountType positive positive_countMixin.

Definition bin_nat_indDef :=
  [indDef for N_rect].
Canonical bin_nat_indType :=
  IndType N bin_nat_indDef.
Definition bin_nat_choiceMixin :=
  [derive choiceMixin for N].
Canonical bin_nat_choiceType :=
  Eval hnf in ChoiceType N bin_nat_choiceMixin.
Definition bin_nat_countMixin :=
  [derive countMixin for N].
Canonical bin_nat_countType :=
  Eval hnf in CountType N bin_nat_countMixin.

Definition Z_indDef :=
  [indDef for Z_rect].
Canonical Z_indType :=
  IndType Z Z_indDef.
Definition Z_eqMixin :=
  [derive eqMixin for Z].
Canonical Z_eqType :=
  Eval hnf in EqType Z Z_eqMixin.
Definition Z_choiceMixin :=
  [derive choiceMixin for Z].
Canonical Z_choiceType :=
  Eval hnf in ChoiceType Z Z_choiceMixin.
Definition Z_countMixin :=
  [derive countMixin for Z].
Canonical Z_countType :=
  Eval hnf in CountType Z Z_countMixin.

Definition ascii_indDef :=
  [indDef for ascii_rect].
Canonical ascii_indType :=
  IndType ascii ascii_indDef.
Definition ascii_eqMixin :=
  [derive eqMixin for ascii].
Canonical ascii_eqType :=
  Eval hnf in EqType ascii ascii_eqMixin.
Definition ascii_choiceMixin :=
  [derive choiceMixin for ascii].
Canonical ascii_choiceType :=
  Eval hnf in ChoiceType ascii ascii_choiceMixin.
Definition ascii_countMixin :=
  [derive countMixin for ascii].
Canonical ascii_countType :=
  Eval hnf in CountType ascii ascii_countMixin.
Definition ascii_finMixin :=
  [derive finMixin for ascii].
Canonical ascii_finType :=
  Eval hnf in FinType ascii ascii_finMixin.
Definition ascii_orderMixin :=
  [derive orderMixin for ascii].
Canonical ascii_porderType :=
  Eval hnf in POrderType tt ascii ascii_orderMixin.
Canonical ascii_latticeType :=
  Eval hnf in LatticeType ascii ascii_orderMixin.
Canonical ascii_distrLatticeType :=
  Eval hnf in DistrLatticeType ascii ascii_orderMixin.
Canonical ascii_orderType :=
  Eval hnf in OrderType ascii ascii_orderMixin.

Definition string_indDef :=
  [indDef for string_rect].
Canonical string_indType :=
  IndType string string_indDef.
Definition string_eqMixin :=
  [derive eqMixin for string].
Canonical string_eqType :=
  Eval hnf in EqType string string_eqMixin.
Definition string_choiceMixin :=
  [derive choiceMixin for string].
Canonical string_choiceType :=
  Eval hnf in ChoiceType string string_choiceMixin.
Definition string_countMixin :=
  [derive countMixin for string].
Canonical string_countType :=
  Eval hnf in CountType string string_countMixin.
Definition string_orderMixin :=
  [derive orderMixin for string].
Canonical string_porderType :=
  Eval hnf in POrderType tt string string_orderMixin.
Canonical string_latticeType :=
  Eval hnf in LatticeType string string_orderMixin.
Canonical string_distrLatticeType :=
  Eval hnf in DistrLatticeType string string_orderMixin.
Canonical string_orderType :=
  Eval hnf in OrderType string string_orderMixin.

End Instances.
