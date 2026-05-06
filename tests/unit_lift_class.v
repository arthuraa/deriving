(** Unit tests for [theories/lift_class.v].

    Each test pins down the reduction behaviour of one [lift_class.v]
    function against a concrete fixture, with no [[indDef for ...]]
    involvement.  The tests cover three layers:

    - [fun_split] / [fun_split1] / [fsE1] / [fsE2]: the per-step
      head/tail decomposition of a function [fin n.+1 -> R].
    - [arity_rec]: the recursion principle on a class-decorated arity,
      one test per shape ([::], [NonRec _ :: _], [Rec _ :: _]).
    - [arg_class_map]: re-decorating an [arg] from one class to another,
      one test per [arg] shape.

    [arity_rec] is universe-polymorphic; we pick a single concrete class
    parameter ([Equality.type] / [Equality.sort]) for these tests.  The
    parameters are named at each lemma rather than at section level so
    that each occurrence gets a fresh universe instance — section-level
    [Variable]s for the eliminator branches force a single universe
    assignment that can clash with [arity_rec]'s call-site universes. *)

From HB Require Import structures.
From mathcomp Require Import
  ssreflect ssrfun ssrbool ssrnat eqtype seq choice fintype.
Set SsrOldRewriteGoalsOrder.

From deriving Require Import base shape lift_class.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Open Scope deriving_scope.

(** ** [fun_split1] / [fsE1] / [fsE2] / [fs_fun]: the canonical splitter
    is the trivial one — [fsE1] / [fsE2] are [erefl] and [fs_fun]
    recovers the original function. *)

Lemma fsE1_canonical n R (f : fin n.+1 -> R) :
  fsE1 (fun_split1 f) = erefl.
Proof. by []. Qed.

Lemma fsE2_canonical n R (f : fin n.+1 -> R) i :
  fsE2 (fun_split1 f) i = erefl.
Proof. by []. Qed.

Lemma fs_fun_canonical n R (f : fin n.+1 -> R) :
  fs_fun (fun_split1 f) = f.
Proof. by []. Qed.

(** ** [arity_rec] reduction: one test per arity-shape branch. *)

Lemma arity_rec_nil n (P : arity n -> Type)
  (Pnil : P PolyType.nil)
  (PNonRec : forall (sX : Equality.type) (As : arity n),
                P As -> P (PolyType.cons (NonRec (Equality.sort sX)) As))
  (PRec : forall i (As : arity n),
                P As -> P (PolyType.cons (Rec i) As)) :
  arity_rec Equality.sort P Pnil PNonRec PRec PolyType.nil tt = Pnil.
Proof. by []. Qed.

Lemma arity_rec_NonRec_cons n (P : arity n -> Type)
  (Pnil : P PolyType.nil)
  (PNonRec : forall (sX : Equality.type) (As : arity n),
                P As -> P (PolyType.cons (NonRec (Equality.sort sX)) As))
  (PRec : forall i (As : arity n),
                P As -> P (PolyType.cons (Rec i) As))
  (sX : Equality.type)
  (As : arity n) (cAs : arity_class Equality.sort As) :
  arity_rec Equality.sort P Pnil PNonRec PRec
    (PolyType.cons (NonRec (Equality.sort sX)) As)
    (PolyType.exist _ sX erefl ::: cAs) =
  PNonRec sX As (arity_rec Equality.sort P Pnil PNonRec PRec As cAs).
Proof. by []. Qed.

Lemma arity_rec_Rec_cons n (P : arity n -> Type)
  (Pnil : P PolyType.nil)
  (PNonRec : forall (sX : Equality.type) (As : arity n),
                P As -> P (PolyType.cons (NonRec (Equality.sort sX)) As))
  (PRec : forall i (As : arity n),
                P As -> P (PolyType.cons (Rec i) As))
  (i : fin n)
  (As : arity n) (cAs : arity_class Equality.sort As) :
  arity_rec Equality.sort P Pnil PNonRec PRec
    (PolyType.cons (Rec i) As) (tt ::: cAs) =
  PRec i As (arity_rec Equality.sort P Pnil PNonRec PRec As cAs).
Proof. by []. Qed.

(** ** [arg_class_map] reduction, one test per [arg] shape. *)

Lemma arg_class_map_NonRec
  n (K1 K2 : Type) (sort1 : K1 -> Type) (sort2 : K2 -> Type)
  (f : K1 -> K2) (p : forall cT, sort2 (f cT) = sort1 cT)
  (X : Type) (cT : eq_class sort1 X) :
  @arg_class_map n K1 K2 sort1 sort2 f p (NonRec X) cT =
  PolyType.exist _ (f (PolyType.sval cT))
                 (p (PolyType.sval cT) * PolyType.svalP cT).
Proof. by []. Qed.

Lemma arg_class_map_Rec
  n (K1 K2 : Type) (sort1 : K1 -> Type) (sort2 : K2 -> Type)
  (f : K1 -> K2) (p : forall cT, sort2 (f cT) = sort1 cT)
  (i : fin n) (cT : arg_class sort1 (Rec i)) :
  @arg_class_map n K1 K2 sort1 sort2 f p (Rec i) cT = tt.
Proof. by []. Qed.
