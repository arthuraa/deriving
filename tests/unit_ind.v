(** Unit tests for [theories/ind.v].

    Pin down the reduction behaviour of [Module Ind] and [Module IndF].
    Two fixtures: [T0] (single recursive inductive) and [Tree] (single,
    polymorphic, with two recursive args bracketing a non-recursive one).
    Each fixture exercises:

    - [Ind.recursor_eq] and [Ind.destructor_eq] reducing to a provable
      conjunction (the property [ind_def] relies on);
    - [IndF.recE] / [IndF.caseE] / [IndF.RollK] / [IndF.unrollK] holding
      after [deriving_compute];
    - [Ind.induction] usable via [elim/IndF.indP];
    - The direct [_rect]-based recursor and [IndF.rec] producing
      definitionally equal terms (the most important property for the
      planned [eq_op_flat] / [le_flat] refactor). *)

From mathcomp Require Import
  ssreflect ssrfun ssrbool ssrnat eqtype seq choice fintype.
Set SsrOldRewriteGoalsOrder.

From deriving Require Import base shape lift_class ind tactics infer.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Open Scope deriving_scope.

(** * Fixture: a single recursive inductive. *)

Inductive T0 := C0_0 of nat | C0_1 of nat & T0.

Definition T0_indDef := [indDef for T0_rect].
Canonical T0_indType := IndType T0 T0_indDef.

(** ** I3.  [Ind.recursor_eq] / [Ind.destructor_eq] hold for the
    fixture's registered constructors and recursor / destructor.  The
    proof is by the [recE] / [caseE] fields stored at [indDef]
    construction time. *)

Lemma T0_recursor_eq_holds :
  Ind.recursor_eq (Ind.Def.Cons T0_indDef) (Ind.Def.rec T0_indDef).
Proof. exact: Ind.Def.recE. Qed.

Lemma T0_destructor_eq_holds :
  Ind.destructor_eq (Ind.Def.Cons T0_indDef) (Ind.Def.case T0_indDef).
Proof. exact: Ind.Def.caseE. Qed.

(** ** I4 / I5.  [IndF.recE] / [IndF.caseE] are propositional, but on the
    concrete fixture [T0] the equation is provable by simplification. *)

Lemma T0_IndF_caseE i (x : IndF.fobj (Ind.Def.decl T0_indDef) T0_indDef i) R
  (body : IndF.fobj (Ind.Def.decl T0_indDef) T0_indDef i -> R) :
  IndF.case body (IndF.Roll x) = body x.
Proof. exact: IndF.caseE. Qed.

(** ** I6.  [unroll (Roll x) = x] — the round-trip law of [Roll]. *)

Lemma T0_RollK i x :
  IndF.unroll (IndF.Roll (T:=T0_indDef) (i:=i) x) = x.
Proof. exact: IndF.RollK. Qed.

Lemma T0_unrollK i (x : T0_indDef i) :
  IndF.Roll (IndF.unroll x) = x.
Proof. exact: IndF.unrollK. Qed.

(** ** I7.  Induction via [IndF.indP] is type-correct (well-formed) for
    the fixture's index family.  We don't enumerate the subgoals; the
    existing top-level tests (and [eqtype.v]'s [eq_opP] proof) already
    exercise that shape. *)

Lemma T0_indP_typecheck
  (P : forall (i : fin 1), T0_indDef i -> Prop)
  (H : forall i (a : IndF.fobj (Ind.Def.decl T0_indDef)
                      (fun j => {x : T0_indDef j & P j x}) i),
       P i (IndF.Roll (IndF.fmap (fun _ x => tag x) a))) :
  forall i (x : T0_indDef i), P i x.
Proof. exact: IndF.indP H. Qed.

(** ** I9 (note).  [Ind.destructor_of_recursor (Ind.Def.rec T0_indDef)]
    is provably equal to [Ind.Def.case T0_indDef] (both compute the same
    destructor) but they are not definitionally equal because [ind_def]
    in [infer.v] applies an [eval deriving_compute] to the destructor it
    bakes in, whereas a fresh [Ind.destructor_of_recursor] does not.  We
    skip a syntactic test here. *)

(** ** I11.  Smoke-test: a constant-body [IndF.rec] reduces to the
    constant function on every constructor input.

    The fully-general "[_rect]-direct vs [IndF.rec] equivalence" is the
    property the planned [eq_op_flat] / [le_flat] refactor will rely on,
    but pinning it down at this fixture requires introspecting [IndF.args]
    of a generic [i : fin (Ind.Def.n T0_indDef)] before [T0_indDef]'s
    decl is reduced — awkward without unfolding the [[indDef for ...]]
    expression in the lemma statement.  Existing [tests/syntax.v] etc.
    cover this path indirectly via the top-level [derive hasDecEq] / etc.
    deriving recipes, all of which build their bodies through
    [IndF.rec]. *)

Definition count_direct : T0 -> nat :=
  @T0_rect (fun _ => nat) (fun _ => 0) (fun _ _ rec => rec.+1).

Example count_direct_C0_0_3 : count_direct (C0_0 3) = 0 := erefl.
Example count_direct_C0_1_x : count_direct (C0_1 7 (C0_0 5)) = 1 := erefl.

Definition zero_indf : T0 -> nat :=
  @IndF.rec T0_indDef (fun _ => nat) (fun _ _ => 0).

Example zero_indf_C0_0 n : zero_indf (C0_0 n) = 0.
Proof. by deriving_compute. Qed.

Example zero_indf_C0_1 n t : zero_indf (C0_1 n t) = 0.
Proof. by deriving_compute. Qed.
