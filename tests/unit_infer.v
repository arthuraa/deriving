(** Unit tests for [theories/infer.v].

    Smoke tests for the inference typeclasses behind [[indDef for rect]].
    The deriving framework's existing top-level tests
    ([tests/syntax.v], [tests/mutual.v], [tests/nested.v], etc.)
    already verify that [[indDef for rect]] resolves correctly on a
    representative cross-section of inputs.  These tests are simpler
    smoke checks that the underlying typeclass machinery is reachable
    and that resolution produces the expected number of types and the
    expected declaration. *)

From mathcomp Require Import
  ssreflect ssrfun ssrbool ssrnat eqtype seq choice fintype.
Set SsrOldRewriteGoalsOrder.

From deriving Require Import base shape lift_class ind tactics infer.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Open Scope deriving_scope.

(** ** F1.  Single inductive: [[indDef for T0_rect]] resolves and the
    resulting [Ind.Def.n] is [1] (single type) with two constructors at
    index [None]. *)

Inductive T0 := C0_0 of nat | C0_1 of nat & T0.
Definition T0_indDef := [indDef for T0_rect].

Lemma T0_indDef_n : Ind.Def.n T0_indDef = 1.
Proof. by []. Qed.

Lemma T0_indDef_decl_size :
  PolyType.size (Ind.Def.decl T0_indDef None) = 2.
Proof. by []. Qed.

(** ** F2.  Per-constructor arities have the expected shape: [C0_0] has
    one [NonRec] argument and [C0_1] has one [NonRec] and one [Rec]. *)

Lemma T0_indDef_C0_0_arity :
  PolyType.size (nth_fin (None : Ind.Cidx (Ind.Def.decl T0_indDef) None)) = 1.
Proof. by []. Qed.

Lemma T0_indDef_C0_1_arity :
  PolyType.size
    (nth_fin (Some None : Ind.Cidx (Ind.Def.decl T0_indDef) None)) = 2.
Proof. by []. Qed.

(** ** F3.  The registered constructors agree with [C0_0] / [C0_1] on
    concrete arguments. *)

(** [Ind.Def.Cons] takes the class as its sole explicit "structure" arg,
    then [Ci]; [Ti] is implicit (inferred from [Ci]'s type). *)

Lemma T0_indDef_Cons_C0_0 (n : nat) :
  Ind.Def.Cons T0_indDef
               (None : Ind.Cidx (Ind.Def.decl T0_indDef) None) n = C0_0 n.
Proof. by []. Qed.

Lemma T0_indDef_Cons_C0_1 (n : nat) (t : T0) :
  Ind.Def.Cons T0_indDef
               (Some None : Ind.Cidx (Ind.Def.decl T0_indDef) None) n t =
  C0_1 n t.
Proof. by []. Qed.

(** ** F4.  Mutual block: two trivially-mutual types resolve to
    [Ind.Def.n = 2].  This exercises [read_rect_type]'s
    motive-prefix-stripping for genuinely mutual recursors. *)

Inductive M0 := M0A | M0B of M1
with M1 := M1A of M0.

Scheme M0_rect_ := Induction for M0 Sort Type
with   M1_rect_ := Induction for M1 Sort Type.

Combined Scheme M01_rect from M0_rect_, M1_rect_.

Definition M01_indDef := [indDef for M01_rect].

Lemma M01_indDef_n : Ind.Def.n M01_indDef = 2.
Proof. by []. Qed.

Lemma M01_indDef_decl_M0_size :
  PolyType.size (Ind.Def.decl M01_indDef None) = 2.
Proof. by []. Qed.

Lemma M01_indDef_decl_M1_size :
  PolyType.size (Ind.Def.decl M01_indDef (Some None)) = 1.
Proof. by []. Qed.
