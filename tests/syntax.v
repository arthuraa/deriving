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
Definition base_lit_hasDecEq :=
  [derive lazy hasDecEq for base_lit].
HB.instance Definition _ := base_lit_hasDecEq.
Definition base_lit_hasChoice :=
  [derive hasChoice for base_lit].
HB.instance Definition _ := base_lit_hasChoice.
Definition base_lit_isCountable :=
  [derive isCountable for base_lit].
HB.instance Definition _ := base_lit_isCountable.
Definition base_lit_isOrder :=
  [derive isOrder for base_lit].
HB.instance Definition _ := base_lit_isOrder.

Inductive un_op : Set :=
  | NegOp | MinusUnOp.
Definition un_op_indDef :=
  [indDef for un_op_rect].
Canonical un_op_indType :=
  IndType un_op un_op_indDef.
Definition un_op_hasDecEq :=
  [derive hasDecEq for un_op].
HB.instance Definition _ := un_op_hasDecEq.
Definition un_op_hasChoice :=
  [derive hasChoice for un_op].
HB.instance Definition _ := un_op_hasChoice.
Definition un_op_isCountable :=
  [derive isCountable for un_op].
HB.instance Definition _ := un_op_isCountable.
Definition un_op_isFinite :=
  [derive isFinite for un_op].
HB.instance Definition _ := un_op_isFinite.
Definition un_op_isOrder :=
  [derive isOrder for un_op].
HB.instance Definition _ := un_op_isOrder.

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
Definition bin_op_hasDecEq :=
  [derive hasDecEq for bin_op].
HB.instance Definition _ := bin_op_hasDecEq.
Definition bin_op_hasChoice :=
  [derive hasChoice for bin_op].
HB.instance Definition _ := bin_op_hasChoice.
Definition bin_op_isCountable :=
  [derive isCountable for bin_op].
HB.instance Definition _ := bin_op_isCountable.
Definition bin_op_isFinite :=
  [derive isFinite for bin_op].
HB.instance Definition _ := bin_op_isFinite.
Definition bin_op_isOrder :=
  [derive isOrder for bin_op].
HB.instance Definition _ := bin_op_isOrder.

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
(* FIXME: can we make these definitions transparent? *)
Definition expr_hasDecEq : Equality.mixin_of expr.
Proof. exact: [derive nored hasDecEq for expr]. Qed.
HB.instance Definition _ := expr_hasDecEq.
(* FIXME: can we make these definitions transparent? *)
Definition val_hasDecEq : Equality.mixin_of val.
Proof. exact: [derive nored hasDecEq for val]. Qed.
HB.instance Definition _ := val_hasDecEq.
Definition expr_hasChoice :=
  [derive hasChoice for expr].
HB.instance Definition _ := expr_hasChoice.
Definition val_hasChoice :=
  [derive hasChoice for val].
HB.instance Definition _ := val_hasChoice.
Definition expr_isCountable :=
  [derive isCountable for expr].
HB.instance Definition _ := expr_isCountable.
Definition val_isCountable :=
  [derive isCountable for val].
HB.instance Definition _ := val_isCountable.
Definition expr_isOrder : Order.isOrder Order.default_display expr.
Proof. exact: [derive nored isOrder for expr]. Qed.
HB.instance Definition _ := expr_isOrder.
Definition val_isOrder : Order.isOrder Order.default_display val.
Proof. exact: [derive nored isOrder for val]. Qed.
HB.instance Definition _ := val_isOrder.
