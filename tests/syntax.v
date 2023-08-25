From HB Require Import structures.

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
HB.instance Definition _ := base_lit_eqMixin.
Definition base_lit_choiceMixin :=
  [derive choiceMixin for base_lit].
HB.instance Definition _ := base_lit_choiceMixin.
Definition base_lit_countMixin :=
  [derive countMixin for base_lit].
HB.instance Definition _ := base_lit_countMixin.
Definition base_lit_orderMixin :=
  [derive orderMixin for base_lit].
HB.instance Definition _ := base_lit_orderMixin.

Inductive un_op : Set :=
  | NegOp | MinusUnOp.
Definition un_op_indDef :=
  [indDef for un_op_rect].
Canonical un_op_indType :=
  IndType un_op un_op_indDef.
Definition un_op_eqMixin :=
  [derive eqMixin for un_op].
HB.instance Definition _ := un_op_eqMixin.
Definition un_op_choiceMixin :=
  [derive choiceMixin for un_op].
HB.instance Definition _ := un_op_choiceMixin.
Definition un_op_countMixin :=
  [derive countMixin for un_op].
HB.instance Definition _ := un_op_countMixin.
Definition un_op_finMixin :=
  [derive finMixin for un_op].
HB.instance Definition _ := un_op_finMixin.
Definition un_op_orderMixin :=
  [derive orderMixin for un_op].
HB.instance Definition _ := un_op_orderMixin.

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
  [derive eqMixin for bin_op].
HB.instance Definition _ := bin_op_eqMixin.
Definition bin_op_choiceMixin :=
  [derive choiceMixin for bin_op].
HB.instance Definition _ := bin_op_choiceMixin.
Definition bin_op_countMixin :=
  [derive countMixin for bin_op].
HB.instance Definition _ := bin_op_countMixin.
Definition bin_op_finMixin :=
  [derive finMixin for bin_op].
HB.instance Definition _ := bin_op_finMixin.
Definition bin_op_orderMixin :=
  [derive orderMixin for bin_op].
HB.instance Definition _ := bin_op_orderMixin.

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
(* FIXME: can we remove nored from here? *)
Definition expr_eqMixin :=
  [derive nored eqMixin for expr].
HB.instance Definition _ := expr_eqMixin.
(* FIXME: can we remove nored from here? *)
Definition val_eqMixin :=
  [derive nored eqMixin for val].
HB.instance Definition _ := val_eqMixin.
Definition expr_choiceMixin :=
  [derive choiceMixin for expr].
HB.instance Definition _ := expr_choiceMixin.
Definition val_choiceMixin :=
  [derive choiceMixin for val].
HB.instance Definition _ := val_choiceMixin.
Definition expr_countMixin :=
  [derive countMixin for expr].
HB.instance Definition _ := expr_countMixin.
Definition val_countMixin :=
  [derive countMixin for val].
HB.instance Definition _ := val_countMixin.
Definition expr_orderMixin :
  Order.isOrder.axioms_ tt expr (Choice.on expr) (Equality.on expr).
Proof. exact: [derive nored orderMixin for expr]. Qed.
HB.instance Definition _ := expr_orderMixin.
Definition val_orderMixin :
  Order.isOrder.axioms_ tt val (Choice.on val) (Equality.on val).
Proof. exact: [derive nored orderMixin for val]. Qed.
HB.instance Definition _ := val_orderMixin.
