From mathcomp Require Import
  ssreflect ssrfun ssrbool ssrnat eqtype seq choice fintype order.
Set SsrOldRewriteGoalsOrder.  (* change Set to Unset when porting the file, then remove the line when requiring MathComp >= 2.6 *)

From deriving Require Import base ind tactics.

From Coq Require Import ZArith NArith String Ascii.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Open Scope deriving_scope.

(* Use `eval red` (one-step delta on the head constant, then beta)
   to inline recursor constants into their underlying fix, falling
   back to `eval hnf` when the head is already a fix or lambda.
   This matters for mutual types: Combined Scheme produces a wrapper
   that calls the per-type recursors (M0_rect, M1_rect, ...) as
   constants.  eval hnf refuses to delta-unfold a recursor whose
   structurally recursive argument is not yet supplied, so the
   destructor baked into Ind.Def.case would contain stuck terms
   like `M0_rect ... (M0A n)`.  Because deriving_compute uses cbv
   with a fixed delta-whitelist that does not include user-defined
   recursor names, it cannot reduce these stuck terms, and derived
   definitions (eq_op, le, ...) carry unreduced recursor calls that
   blow up at simplification time.  eval red does not have this
   restriction: it always unfolds the head constant, exposing the
   mutual fix so that iota reduction can proceed normally. *)
Ltac head_red rec :=
  match constr:(tt) with
  | _ => let r := eval red in rec in r
  | _ => let r := eval hnf in rec in r
  end.

Ltac unwind_recursor rec :=
  try red;
  match goal with
  | |- ?F -> ?G =>
    let X := fresh "X" in
    intros X; unwind_recursor (rec X)
  | |- prod ?T1 ?T2 =>
    let rec1 := head_red (rec.1) in
    let rec2 := head_red (rec.2) in
    split; [unwind_recursor rec1|unwind_recursor rec2]
  | |- forall x, _ =>
    let rec' := head_red rec in
    intros x; destruct x; apply rec'
  end.

Ltac ind_def rec :=
  let Rec := eval red in rec in
  let H   := constr:((fun n Ts D Cs RecT' Rec' Rec'' =>
                      fun (H : infer_ind _ Rec n Ts D Cs RecT' Rec' Rec'') => H)
                     _ _ _ _ _ _ _ _) in
  match type of H with
  | infer_ind _ _ ?n ?Ts ?D ?Cs ?RecT' ?Rec' ?Rec'' =>
    let case := constr:(ltac:(intros P; deriving_compute; unwind_recursor (Rec' P))
                        : forall P, RecT' P) in
    let case := constr:(fun S : fin n -> Type => case (fun i _ => S i)) in
    let case := constr:(@Ind.destructor_of_recursor n D Ts case) in
    let case := eval deriving_compute in case in
    refine (IndDef (@Ind.Def.Class n Ts D Cs (fun S => Rec' (fun i _ => S i)) case _ _ rec));
    abstract (deriving_compute; intuition)
  end.

Notation "[ 'indDef' 'for' rect ]" :=
  (ltac:(ind_def rect))
  (at level 0) : form_scope.

(** In these two notations, we force the indType instance to be unfolded before
    returning it, so that it can be simplified. *)

Notation "[ 'infer' 'indType' 'of' T 'as' sT n sorts D 'in' e ]" :=
  (fun (sT' : indType) & phant_id T%type (Ind.sort sT') =>
   fun n (sorts : fin n -> Type) (D : declaration n) =>
   fun (def : Ind.Def.class_of sorts D) (i : fin n) (iE : T%type = sorts i) =>
   let sT := Ind.Pack (@Ind.Mixin T (@Ind.Def.Pack n sorts D def) i iE) in
   fun & phant_id sT' sT => e)
  (at level 0, sT ident, n ident, sorts ident, D ident)
  : form_scope.

Notation "[ 'infer' 'indType' 'of' T 'with' proj 'as' sT n sorts D cD 'in' e ]" :=
  ([infer indType of T as sT n sorts D in
    fun (sD : decl_inst n proj n) & phant_id D (untag_decl sD) =>
    fun (cD : forall i : fin n, sig_class proj (D i)) =>
    fun & phant_id (decl_inst_class sD) cD => e])
  (at level 0, sT ident, n ident, sorts ident, D ident, cD ident)
  : form_scope.
