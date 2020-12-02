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

Definition unit_indMixin :=
  Eval simpl in [indMixin for unit_rect].
Canonical unit_indType :=
  Eval hnf in IndType unit unit_indMixin.

Definition void_indMixin :=
  Eval simpl in [indMixin for Empty_set_rect].
Canonical void_indType :=
  Eval hnf in IndType void void_indMixin.

Definition bool_indMixin :=
  Eval simpl in [indMixin for bool_rect].
Canonical bool_indType :=
  Eval hnf in IndType bool bool_indMixin.

Definition nat_indMixin :=
  Eval simpl in [indMixin for nat_rect].
Canonical nat_indType :=
  Eval hnf in IndType nat nat_indMixin.

Definition option_indMixin T :=
  Eval simpl in [indMixin for @option_rect T].
Canonical option_indType T :=
  Eval hnf in IndType (option T) (option_indMixin T).
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

Definition sum_indMixin T1 T2 :=
  Eval simpl in [indMixin for @sum_rect T1 T2].
Canonical sum_indType T1 T2 :=
  Eval hnf in IndType (T1 + T2) (sum_indMixin T1 T2).

Definition prod_indMixin T1 T2 :=
  Eval simpl in [indMixin for @prod_rect T1 T2].
Canonical prod_indType T1 T2 :=
  Eval hnf in IndType (T1 * T2) (prod_indMixin T1 T2).

Definition seq_indMixin T :=
  Eval simpl in [indMixin for @list_rect T].
Canonical seq_indType T :=
  Eval hnf in IndType (seq T) (seq_indMixin T).

Definition comparison_indMixin :=
  [indMixin for comparison_rect].
Canonical comparison_indType :=
  Eval hnf in IndType comparison comparison_indMixin.
Definition comparison_eqMixin :=
  [derive eqMixin for comparison].
Canonical comparison_eqType :=
  Eval hnf in EqType comparison comparison_eqMixin.
Definition comparison_choiceMixin :=
  Eval simpl in [derive choiceMixin for comparison].
Canonical comparison_choiceType :=
  Eval hnf in ChoiceType comparison comparison_choiceMixin.
Definition comparison_countMixin :=
  Eval simpl in [derive countMixin for comparison].
Canonical comparison_countType :=
  Eval hnf in CountType comparison comparison_countMixin.
Definition comparison_finMixin :=
  Eval simpl in [derive finMixin for comparison].
Canonical comparison_finType :=
  Eval hnf in FinType comparison comparison_finMixin.

Definition positive_indMixin :=
  Eval simpl in [indMixin for positive_rect].
Canonical positive_indType :=
  Eval hnf in IndType positive positive_indMixin.
Definition positive_eqMixin :=
  Eval simpl in [derive eqMixin for positive].
Canonical positive_eqType :=
  Eval hnf in EqType positive positive_eqMixin.
Definition positive_choiceMixin :=
  Eval simpl in [derive choiceMixin for positive].
Canonical positive_choiceType :=
  Eval hnf in ChoiceType positive positive_choiceMixin.
Definition positive_countMixin :=
  Eval simpl in [derive countMixin for positive].
Canonical positive_countType :=
  Eval hnf in CountType positive positive_countMixin.

Definition bin_nat_indMixin :=
  Eval simpl in [indMixin for N_rect].
Canonical bin_nat_indType :=
  Eval hnf in IndType N bin_nat_indMixin.
Definition bin_nat_choiceMixin :=
  Eval simpl in [derive choiceMixin for N].
Canonical bin_nat_choiceType :=
  Eval hnf in ChoiceType N bin_nat_choiceMixin.
Definition bin_nat_countMixin :=
  Eval simpl in [derive countMixin for N].
Canonical bin_nat_countType :=
  Eval hnf in CountType N bin_nat_countMixin.

Definition Z_indMixin :=
  Eval simpl in [indMixin for Z_rect].
Canonical Z_indType :=
  Eval hnf in IndType Z Z_indMixin.
Definition Z_eqMixin :=
  Eval simpl in [derive eqMixin for Z].
Canonical Z_eqType :=
  Eval hnf in EqType Z Z_eqMixin.
Definition Z_choiceMixin :=
  Eval simpl in [derive choiceMixin for Z].
Canonical Z_choiceType :=
  Eval hnf in ChoiceType Z Z_choiceMixin.
Definition Z_countMixin :=
  Eval simpl in [derive countMixin for Z].
Canonical Z_countType :=
  Eval hnf in CountType Z Z_countMixin.

Definition ascii_indMixin :=
  Eval simpl in [indMixin for ascii_rect].
Canonical ascii_indType :=
  Eval hnf in IndType ascii ascii_indMixin.
Definition ascii_eqMixin :=
  Eval simpl in [derive eqMixin for ascii].
Canonical ascii_eqType :=
  Eval hnf in EqType ascii ascii_eqMixin.
Definition ascii_choiceMixin :=
  Eval simpl in [derive choiceMixin for ascii].
Canonical ascii_choiceType :=
  Eval hnf in ChoiceType ascii ascii_choiceMixin.
Definition ascii_countMixin :=
  Eval simpl in [derive countMixin for ascii].
Canonical ascii_countType :=
  Eval hnf in CountType ascii ascii_countMixin.
Definition ascii_finMixin :=
  Eval simpl in [derive finMixin for ascii].
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

Definition string_indMixin :=
  Eval simpl in [indMixin for string_rect].
Canonical string_indType :=
  Eval hnf in IndType string string_indMixin.
Definition string_eqMixin :=
  Eval simpl in [derive eqMixin for string].
Canonical string_eqType :=
  Eval hnf in EqType string string_eqMixin.
Definition string_choiceMixin :=
  Eval simpl in [derive choiceMixin for string].
Canonical string_choiceType :=
  Eval hnf in ChoiceType string string_choiceMixin.
Definition string_countMixin :=
  Eval simpl in [derive countMixin for string].
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
