From mathcomp Require Import
  ssreflect ssrfun ssrbool ssrnat eqtype seq choice fintype finset order.

From deriving Require Import deriving.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module RecursiveExample.

Inductive tree (T : Type) :=
| Leaf of {set 'I_10}
| Node of T & tree T & tree T.
Arguments Leaf {_} _.

Definition tree_indMixin T :=
  [indMixin for @tree_rect T].
Canonical tree_indType T :=
  Eval hnf in IndType _ (tree T) (tree_indMixin T).

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

End RecursiveExample.

Module FiniteExample.

Inductive three := A of bool & bool | B | C.

Definition three_indMixin :=
  [indMixin for three_rect].
Canonical three_indType :=
  Eval hnf in IndType _ three three_indMixin.

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

End FiniteExample.

Section MutualExample.

Unset Elimination Schemes.
Inductive foo :=
| Foo1 of nat
| Foo2 of bool & bar

with bar :=
| Bar1 of foo & foo
| Bar2 of nat & foo.
Set Elimination Schemes.

Scheme foo_rect := Induction for foo Sort Type
with   bar_rect := Induction for bar Sort Type.

Combined Scheme foo_bar_rect from foo_rect, bar_rect.

Definition foo_bar_mutIndMixin := [mutIndType for foo_bar_rect].
Canonical foo_indType := IndType _ foo foo_bar_mutIndMixin.
Canonical bar_indType := IndType _ bar foo_bar_mutIndMixin.

Definition foo_eqMixin := [derive lazy eqMixin for foo].
Canonical foo_eqType := EqType foo foo_eqMixin.
Definition bar_eqMixin := [derive lazy eqMixin for bar].
Canonical bar_eqType := EqType bar bar_eqMixin.
Definition foo_choiceMixin := [derive choiceMixin for foo].
Canonical foo_choiceType := Eval hnf in ChoiceType foo foo_choiceMixin.
Definition bar_choiceMixin := [derive choiceMixin for bar].
Canonical bar_choiceType := Eval hnf in ChoiceType bar bar_choiceMixin.
Definition foo_countMixin := [derive countMixin for foo].
Canonical foo_countType := Eval hnf in CountType foo foo_countMixin.
Definition bar_countMixin := [derive countMixin for bar].
Canonical bar_countType := Eval hnf in CountType bar bar_countMixin.
Definition foo_orderMixin := [derive lazy orderMixin for foo].
Canonical foo_porderType := Eval hnf in POrderType tt foo foo_orderMixin.
Canonical foo_latticeType := Eval hnf in LatticeType foo foo_orderMixin.
Canonical foo_distrLatticeType := Eval hnf in DistrLatticeType foo foo_orderMixin.
Canonical foo_orderType := Eval hnf in OrderType foo foo_orderMixin.
Definition bar_orderMixin := [derive lazy orderMixin for bar].
Canonical bar_porderType := Eval hnf in POrderType tt bar bar_orderMixin.
Canonical bar_latticeType := Eval hnf in LatticeType bar bar_orderMixin.
Canonical bar_distrLatticeType := Eval hnf in DistrLatticeType bar bar_orderMixin.
Canonical bar_orderType := Eval hnf in OrderType bar bar_orderMixin.

End MutualExample.

Module SyntaxExample.

(* An example of syntax trees for a lambda calculus.  Adapted from Iris's heap
lang
(https://gitlab.mpi-sws.org/iris/iris/blob/master/theories/heap_lang/lang.v). *)

Inductive base_lit : Set :=
  | LitInt (n : nat) | LitBool (b : bool) | LitUnit | LitPoison
  | LitLoc (l : nat) | LitProphecy (p: nat).
Definition base_lit_indMixin :=
  [indMixin for base_lit_rect].
Canonical base_lit_indType :=
  IndType _ base_lit base_lit_indMixin.
Definition base_lit_eqMixin :=
  [derive lazy eqMixin for base_lit].
Canonical base_lit_eqType :=
  EqType base_lit base_lit_eqMixin.
Definition base_lit_choiceMixin :=
  [derive choiceMixin for base_lit].
Canonical base_lit_choiceType :=
  Eval hnf in ChoiceType base_lit base_lit_choiceMixin.
Definition base_lit_countMixin :=
  [derive countMixin for base_lit].
Canonical base_lit_countType :=
  Eval hnf in CountType base_lit base_lit_countMixin.
Definition base_lit_orderMixin :=
  [derive lazy orderMixin for base_lit].
Canonical base_lit_porderType :=
  Eval hnf in POrderType tt base_lit base_lit_orderMixin.
Canonical base_lit_latticeType :=
  Eval hnf in LatticeType base_lit base_lit_orderMixin.
Canonical base_lit_distrLatticeType :=
  Eval hnf in DistrLatticeType base_lit base_lit_orderMixin.
Canonical base_lit_orderType :=
  Eval hnf in OrderType base_lit base_lit_orderMixin.

Inductive un_op : Set :=
  | NegOp | MinusUnOp.
Definition un_op_indMixin :=
  [indMixin for un_op_rect].
Canonical un_op_indType :=
  IndType _ un_op un_op_indMixin.
Definition un_op_eqMixin :=
  [derive eqMixin for un_op].
Canonical un_op_eqType :=
  EqType un_op un_op_eqMixin.
Definition un_op_choiceMixin :=
  [derive choiceMixin for un_op].
Canonical un_op_choiceType :=
  Eval hnf in ChoiceType un_op un_op_choiceMixin.
Definition un_op_countMixin :=
  [derive countMixin for un_op].
Canonical un_op_countType :=
  Eval hnf in CountType un_op un_op_countMixin.
Definition un_op_finMixin :=
  [derive finMixin for un_op].
Canonical un_op_finType :=
  Eval hnf in FinType un_op un_op_finMixin.
Definition un_op_orderMixin :=
  [derive orderMixin for un_op].
Canonical un_op_porderType :=
  Eval hnf in POrderType tt un_op un_op_orderMixin.
Canonical un_op_latticeType :=
  Eval hnf in LatticeType un_op un_op_orderMixin.
Canonical un_op_distrLatticeType :=
  Eval hnf in DistrLatticeType un_op un_op_orderMixin.
Canonical un_op_orderType :=
  Eval hnf in OrderType un_op un_op_orderMixin.

Inductive bin_op : Set :=
  | PlusOp | MinusOp | MultOp | QuotOp | RemOp
  | AndOp | OrOp | XorOp
  | ShiftLOp | ShiftROp
  | LeOp | LtOp | EqOp
  | OffsetOp.
Definition bin_op_indMixin :=
  [indMixin for bin_op_rect].
Canonical bin_op_indType :=
  IndType _ bin_op bin_op_indMixin.
Definition bin_op_eqMixin :=
  [derive lazy eqMixin for bin_op].
Canonical bin_op_eqType :=
  EqType bin_op bin_op_eqMixin.
Definition bin_op_choiceMixin :=
  [derive choiceMixin for bin_op].
Canonical bin_op_choiceType :=
  Eval hnf in ChoiceType bin_op bin_op_choiceMixin.
Definition bin_op_countMixin :=
  [derive countMixin for bin_op].
Canonical bin_op_countType :=
  Eval hnf in CountType bin_op bin_op_countMixin.
Definition bin_op_finMixin :=
  [derive finMixin for bin_op].
Canonical bin_op_finType :=
  Eval hnf in FinType bin_op bin_op_finMixin.
Definition bin_op_orderMixin :=
  [derive lazy orderMixin for bin_op].
Canonical bin_op_porderType :=
  Eval hnf in POrderType tt bin_op bin_op_orderMixin.
Canonical bin_op_latticeType :=
  Eval hnf in LatticeType bin_op bin_op_orderMixin.
Canonical bin_op_distrLatticeType :=
  Eval hnf in DistrLatticeType bin_op bin_op_orderMixin.
Canonical bin_op_orderType :=
  Eval hnf in OrderType bin_op bin_op_orderMixin.

Inductive expr :=
  | Var (x : nat)
  | Rec (f x : nat) (e : expr)
  | App (e1 e2 : expr)
  | UnOp (op : un_op) (e : expr)
  | BinOp (op : bin_op) (e1 e2 : expr)
  | If (e0 e1 e2 : expr)
  | Pair (e1 e2 : expr)
  | Fst (e : expr)
  | Snd (e : expr)
  | InjL (e : expr)
  | InjR (e : expr)
  | Case (e0 : expr) (e1 : expr) (e2 : expr)
  | Fork (e : expr)
  | AllocN (e1 e2 : expr)
  | Load (e : expr)
  | Store (e1 : expr) (e2 : expr)
  | CmpXchg (e0 : expr) (e1 : expr) (e2 : expr)
  | FAA (e1 : expr) (e2 : expr)
  | NewProph
  | Resolve (e0 : expr) (e1 : expr) (e2 : expr)
  | Lit (l : base_lit).
Definition expr_indMixin :=
  [indMixin for expr_rect].
Canonical expr_indType :=
  IndType _ expr expr_indMixin.
Definition expr_eqMixin :=
  [derive lazy eqMixin for expr].
Canonical expr_eqType :=
  EqType expr expr_eqMixin.
Definition expr_choiceMixin :=
  [derive choiceMixin for expr].
Canonical expr_choiceType :=
  Eval hnf in ChoiceType expr expr_choiceMixin.
Definition expr_countMixin :=
  [derive countMixin for expr].
Canonical expr_countType :=
  Eval hnf in CountType expr expr_countMixin.
Definition expr_orderMixin :=
  [derive lazy orderMixin for expr].
Canonical expr_porderType :=
  Eval hnf in POrderType tt expr expr_orderMixin.
Canonical expr_latticeType :=
  Eval hnf in LatticeType expr expr_orderMixin.
Canonical expr_distrLatticeType :=
  Eval hnf in DistrLatticeType expr expr_orderMixin.
Canonical expr_orderType :=
  Eval hnf in OrderType expr expr_orderMixin.

End SyntaxExample.
