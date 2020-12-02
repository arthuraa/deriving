From mathcomp Require Import
  ssreflect ssrfun ssrbool ssrnat eqtype seq choice fintype finset order.

From deriving Require Import deriving.

Require Import Coq.Strings.String.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* An example of syntax trees for a lambda calculus.  Adapted from Iris's heap
lang
(https://gitlab.mpi-sws.org/iris/iris/blob/master/theories/heap_lang/lang.v). *)

Inductive base_lit : Set :=
  | LitInt (n : nat) | LitBool (b : bool) | LitUnit | LitPoison
  | LitLoc (l : nat) | LitProphecy (p: nat).
Definition base_lit_indDef :=
  [indDef for base_lit_rect].
Canonical base_lit_indType :=
  IndType base_lit base_lit_indDef.
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
Definition un_op_indDef :=
  [indDef for un_op_rect].
Canonical un_op_indType :=
  IndType un_op un_op_indDef.
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
Definition bin_op_indDef :=
  [indDef for bin_op_rect].
Canonical bin_op_indType :=
  IndType bin_op bin_op_indDef.
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

Unset Elimination Schemes.
Inductive expr :=
  (* Values *)
  | Val (v : val)
  (* Base lambda calculus *)
  | Var (x : string)
  | Rec (f x : string) (e : expr)
  | App (e1 e2 : expr)
  (* Base types and their operations *)
  | UnOp (op : un_op) (e : expr)
  | BinOp (op : bin_op) (e1 e2 : expr)
  | If (e0 e1 e2 : expr)
  (* Products *)
  | Pair (e1 e2 : expr)
  | Fst (e : expr)
  | Snd (e : expr)
  (* Sums *)
  | InjL (e : expr)
  | InjR (e : expr)
  | Case (e0 : expr) (e1 : expr) (e2 : expr)
  (* Concurrency *)
  | Fork (e : expr)
  (* Heap *)
  | AllocN (e1 e2 : expr) (* array length (positive number), initial value *)
  | Free (e : expr)
  | Load (e : expr)
  | Store (e1 : expr) (e2 : expr)
  | CmpXchg (e0 : expr) (e1 : expr) (e2 : expr) (* Compare-exchange *)
  | FAA (e1 : expr) (e2 : expr) (* Fetch-and-add *)
  (* Prophecy *)
  | NewProph
  | Resolve (e0 : expr) (e1 : expr) (e2 : expr) (* wrapped expr, proph, val *)
with val :=
  | LitV (l : base_lit)
  | RecV (f x : string) (e : expr)
  | PairV (v1 v2 : val)
  | InjLV (v : val)
  | InjRV (v : val).
Set Elimination Schemes.

Scheme expr_rect := Induction for expr Sort Type
with   val_rect  := Induction for val  Sort Type.

Combined Scheme expr_val_rect from expr_rect, val_rect.

Definition expr_val_indDef :=
  [indDef for expr_val_rect].
Canonical expr_indType :=
  IndType expr expr_val_indDef.
Canonical val_indType :=
  IndType val expr_val_indDef.
Definition expr_eqMixin :=
  [derive lazy eqMixin for expr].
Canonical expr_eqType :=
  EqType expr expr_eqMixin.
Definition val_eqMixin :=
  [derive lazy eqMixin for val].
Canonical val_eqType :=
  EqType val val_eqMixin.
Definition expr_choiceMixin :=
  [derive choiceMixin for expr].
Canonical expr_choiceType :=
  Eval hnf in ChoiceType expr expr_choiceMixin.
Definition val_choiceMixin :=
  [derive choiceMixin for val].
Canonical val_choiceType :=
  Eval hnf in ChoiceType val val_choiceMixin.
Definition expr_countMixin :=
  [derive countMixin for expr].
Canonical expr_countType :=
  Eval hnf in CountType expr expr_countMixin.
Definition val_countMixin :=
  [derive countMixin for val].
Canonical val_countType :=
  Eval hnf in CountType val val_countMixin.
Definition expr_orderMixin : leOrderMixin expr_choiceType.
Proof. exact [derive nored orderMixin for expr]. Qed.
Canonical expr_porderType :=
  Eval hnf in POrderType tt expr expr_orderMixin.
Canonical expr_latticeType :=
  Eval hnf in LatticeType expr expr_orderMixin.
Canonical expr_distrLatticeType :=
  Eval hnf in DistrLatticeType expr expr_orderMixin.
Canonical expr_orderType :=
  Eval hnf in OrderType expr expr_orderMixin.
Definition val_orderMixin : leOrderMixin val_choiceType.
Proof. exact [derive nored orderMixin for val]. Qed.
Canonical val_porderType :=
  Eval hnf in POrderType tt val val_orderMixin.
Canonical val_latticeType :=
  Eval hnf in LatticeType val val_orderMixin.
Canonical val_distrLatticeType :=
  Eval hnf in DistrLatticeType val val_orderMixin.
Canonical val_orderType :=
  Eval hnf in OrderType val val_orderMixin.
