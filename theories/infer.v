From mathcomp Require Import
  ssreflect ssrfun ssrbool ssrnat eqtype seq choice fintype order.

From deriving Require Import base ind tactics.

From Coq Require Import ZArith NArith String Ascii.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Open Scope deriving_scope.

Ltac unwind_recursor rec :=
  try red;
  match goal with
  | |- ?F -> ?G =>
    let X := fresh "X" in
    intros X; unwind_recursor (rec X)
  | |- prod ?T1 ?T2 =>
    let rec1 := eval hnf in rec.1 in
    let rec2 := eval hnf in rec.2 in
    split; [unwind_recursor rec1|unwind_recursor rec2]
  | |- forall x, _ =>
    let rec' := eval hnf in rec in
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

(** Compatibility *)
Notation "[ 'indMixin' 'for' rect ]" :=
  [indDef for rect] (at level 0) : form_scope.

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
