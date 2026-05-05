(** * Inferring an [indDef] from a [Scheme]-derived recursor

    The user's entry point is [[indDef for rect]]: given a recursor
    [rect : forall (P : T -> Type), …branches… -> forall x, P x] (typically
    produced by [Scheme]/[Combined Scheme]), this file produces an
    [indDef] for [T] (or for the whole mutual block).  It also provides
    [[infer indType of T as …]] / [[infer indType of T with proj as …]]
    notations for use in deriving recipes that need to recover the
    [indDef] structure of a user-supplied type.

    The work splits into two layers:

    - A typeclass backbone (see [Section InferInstances] below):
      [infer_arity], [infer_decl], [read_rect], [bless_rect], [infer_ind].
      These walk the syntactic shape of [rect]'s type to extract the
      number [n] of mutual types, their [declaration] [D], and the
      [constructors Cs] / [recursor Rec'] in deriving form.

    - An Ltac driver: [head_red], [unwind_recursor], [ind_def].  Once
      the typeclass resolution has produced an [infer_ind] instance,
      the Ltac extracts [D], [Cs], [Rec'] and uses
      [Ind.destructor_of_recursor] (plus a per-branch reduction of
      [Rec']) to assemble the [Ind.Def.class_of] record.

    To break a dependency cycle with [tactics.v]: the typeclass instances
    in this file would naturally have their [Hint Unfold]s emitted into
    [tactics.v]'s [deriving_compute] whitelist, but [infer.v] needs to
    *call* [deriving_compute] inside its Ltac, so [tactics.v] cannot
    depend on [infer.v].  We resolve this by defining an internal
    [infer_compute] reduction here (a focused [cbv] that unfolds only the
    inference-typeclass instances) and applying it inside [ind_def]
    *before* [deriving_compute].  The inference instances therefore stay
    out of the global [deriving_compute] whitelist, where they don't
    belong anyway — they're local to this one workflow. *)

From HB Require Import structures.
From mathcomp Require Import
  ssreflect ssrfun ssrbool ssrnat eqtype seq choice fintype order.
Set SsrOldRewriteGoalsOrder.  (* change Set to Unset when porting the file, then remove the line when requiring MathComp >= 2.6 *)

From deriving Require Import base shape lift_class ind ind_class tactics.

From Coq Require Import ZArith NArith String Ascii.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Open Scope deriving_scope.

(** ** Inference typeclass backbone

    The four classes below cooperate to read a [Scheme]-derived recursor's
    type and extract the inductive's declaration and recursor in the form
    needed by [Ind.Def].

    - [infer_arity n T P branchT As i C] : [branchT] is the type of one
      branch of the recursor, of arity [As], for the constructor
      [C : hfun' (type_of_arg T) As (T i)].  The instances [infer_arity_end],
      [infer_arity_rec], [infer_arity_nonrec] read the shape of [branchT]
      from left to right.

    - [infer_decl n T P elimT D Cs] : [elimT] is the type of the rest of
      the recursor (after fixing the motive [P]), and [D]/[Cs] the
      corresponding declaration and constructors.

    - [read_rect rectT rect n Ts rectT' rect'] : reformulates a recursor
      [rect : forall P, rectT P] over a single inductive into its
      mutual-block analogue [rect'] over a [fin n.+1]-indexed motive,
      driven by the prefix of universally-quantified motives.

    - [bless_rect n Ts D Cs rectT' rect' rect''] : packages [rect'] (which
      takes a per-index motive [P : fin n -> ?]) into a [recursor] (which
      takes a single hlist-indexed motive [S : fin n -> Type]).

    The umbrella [infer_ind] glues these three together. *)

Section InferInstances.

Import PolyType.

Class infer_arity
  n (T : fin n -> Type) (P : forall i, T i -> Type)
  (branchT : Type) (As : arity n) (i : fin n)
  (C : hfun' (type_of_arg T) As (T i)) : Type.
Arguments infer_arity : clear implicits.

Instance infer_arity_end
  n T P i (x : T i) :
  infer_arity n T P (P i x) [::] i x.
Defined.

Instance infer_arity_rec
  n Ts P j
  (branchT : Ts j -> Type)
  i (As : arity n)
  (C : Ts j -> hfun' (type_of_arg Ts) As (Ts i))
  (_ : forall x, infer_arity n Ts P (branchT x) As i (C x)) :
  infer_arity n Ts P (forall x, P j x -> branchT x) (Rec j :: As) i C.
Defined.

Instance infer_arity_nonrec
  n T P S
  (branchT : S -> Type) i As (C : S -> hfun' (type_of_arg T) As (T i))
  (_ : forall x, infer_arity n T P (branchT x) As i (C x)) :
  infer_arity n T P (forall x, branchT x) (NonRec S :: As) i C.
Defined.

Class infer_decl
  n T (P : forall i, T i -> Type)
  (elimT : Type) (D : declaration n) (Cs : Ind.constructors D T) : Type.
Arguments infer_decl : clear implicits.

Global Instance infer_decl_end n T P :
  infer_decl n T P
             (hlist1 (fun i => forall (x : T i), P i x))
             empty_decl
             (@Ind.empty_cons _ _).
Defined.

Global Instance infer_decl_cons n T P
  (branchT : Type) Ti As C
  (_ : infer_arity n T P branchT As Ti C)
  (elimT : Type) D Cs
  (_ : infer_decl n T P elimT D Cs)
  : infer_decl n T P (branchT -> elimT) (add_arity D Ti As) (Ind.add_cons Cs C).
Defined.

Class read_rect (rectT : Type) (rect : rectT)
  (n : nat) (Ts : fin n -> Type)
  (rectT' : (forall i, Ts i -> Type) -> Type)
  (rect' : forall Ps, rectT' Ps).
Arguments read_rect : clear implicits.

Global Instance read_rect_type
  (T : Type) (rectT : (T -> Type) -> Type) (rect : forall P, rectT P)
  n Ts rectT' rect'
  (_ : forall P, read_rect (rectT P) (rect P) n Ts (rectT' P) (rect' P))
  : read_rect (forall P, rectT P) rect n.+1
              (fcons T Ts)
              (fun Ps => rectT' (Ps None) (fun i => Ps (Some i)))
              (fun Ps => rect' (Ps None) (fun i => Ps (Some i))) | 1.
Defined.

Global Instance read_rect_done rectT rect :
  read_rect rectT rect 0 (fnil Type) (fun _ => rectT) (fun _ => rect) | 2.
Defined.

Class bless_rect
  n Ts (D : declaration n) (Cs : Ind.constructors D Ts)
  (rectT : (forall i, Ts i -> Type) -> Type)
  (rect  : forall P, rectT P)
  (rect' : Ind.recursor D Ts).
Arguments bless_rect : clear implicits.

Class infer_ind rectT (rect : rectT)
  n Ts (D : declaration n) (Cs : Ind.constructors D Ts)
  (rectT' : (forall i, Ts i -> Type) -> Type) (rect' : forall P, rectT' P)
  (rect'' : Ind.recursor D Ts).
Arguments infer_ind : clear implicits.

Global Instance do_infer_ind rectT rect
  n Ts rectT' rect'
  (_ : read_rect rectT rect n Ts rectT' rect')
  D Cs
  (_ : forall P, infer_decl n Ts P (rectT' P) D Cs)
  rect''
  (_ : bless_rect n Ts D Cs rectT' rect' rect'')
  : infer_ind rectT rect n Ts D Cs rectT' rect' rect''.
Defined.

End InferInstances.

Arguments infer_arity : clear implicits.
Arguments infer_decl : clear implicits.
Arguments read_rect : clear implicits.
Arguments bless_rect : clear implicits.
Arguments infer_ind : clear implicits.

(** Local reduction that unfolds only the inference-typeclass instances.
    Applied inside [ind_def] before [deriving_compute] so that the
    instance terms are normalised to their underlying [Ind.*] form
    *before* the global cbv runs.  Keeping these constants out of
    [deriving_compute]'s whitelist avoids a circular dependency between
    [tactics.v] and this file. *)

Ltac infer_compute :=
  cbv [infer_arity_end infer_arity_rec infer_arity_nonrec
       infer_decl_end infer_decl_cons
       read_rect_type read_rect_done
       do_infer_ind].

(** ** Search hooks

    The [Hint Extern]s below replace pure [Hint Resolve] for the inference
    instances because we need pattern-matching on the goal shape (e.g. to
    decide between [infer_decl_cons] and [infer_decl_end]).  The Ltac
    helpers do that case analysis. *)

Ltac infer_arity :=
  cbv beta;
  match goal with
  | |- infer_arity ?n ?Ts ?Ps (?Ps ?i ?x) _ _ _ =>
    exact (@infer_arity_end n Ts Ps i x)
  | |- infer_arity ?n ?Ts ?Ps (forall x, ?Ps ?j x -> @?branchT x) _ _ _ =>
    eapply (@infer_arity_rec n Ts Ps j branchT)
  | |- infer_arity ?n ?Ts ?Ps (forall x : ?S, @?branchT x) _ _ _ =>
    eapply (@infer_arity_nonrec n Ts Ps S branchT)
  end.

#[global]
Hint Extern 0 (infer_arity _ _ _ _ _ _ _) => infer_arity : typeclass_instances.

Ltac infer_decl :=
  cbv beta;
  match goal with
  | |- infer_decl ?n ?Ts ?Ps (?branchT -> ?rectT) _ _ =>
    eapply (@infer_decl_cons n Ts Ps branchT _ _ _ _ rectT)
  | |- infer_decl ?n ?Ts ?Ps _ _ _ =>
    eapply (@infer_decl_end n Ts Ps)
  end.

#[global]
Hint Extern 0 (infer_decl _ _ _ _ _ _) => infer_decl : typeclass_instances.

Ltac bless_rect :=
  cbv beta;
  match goal with
  | |- bless_rect ?n ?Ts ?D ?Cs ?rectT ?rect _ =>
     exact (@Build_bless_rect n Ts D Cs rectT rect
                             (fun P => rect (fun i _ => P i)))
  end.

#[global]
Hint Extern 0 (bless_rect _ _ _ _ _ _ _) => bless_rect : typeclass_instances.

(** ** Ltac driver: [[indDef for rect]]

    [head_red] inlines a constant by one [delta] step (preferred over
    [hnf]'s "reduce until you see a constructor or lambda" because the
    [Combined Scheme] wrapper for mutual blocks is itself a constant whose
    body is a fix; [hnf] won't unfold it without an applied recursor).

    [unwind_recursor] walks the rendered recursor type and case-splits on
    each input variable until it bottoms out at a constructor application,
    matching the shape that [Ind.Def.case] expects.

    [ind_def] ties everything together: it extracts [n], [Ts], [D], [Cs],
    [Rec'], [Rec''] via the [infer_ind] typeclass; constructs [case] from
    [Rec'] using [Ind.destructor_of_recursor]; and refines into
    [IndDef (Ind.Def.Class …)] with [recE] / [caseE] obligations
    discharged by the [deriving_compute; intuition] tactic combination
    (they collapse to [erefl] chains after reduction). *)

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
    let case := constr:(ltac:(intros P; infer_compute; deriving_compute;
                              unwind_recursor (Rec' P))
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

(** ** [[infer indType of T …]]: recovering the indDef of a user type

    Used inside deriving recipes (e.g. [DerEqType.pack],
    [DerOrderType.pack]) to canonically resolve the [indDef] of a
    user-supplied type [T], optionally also resolving the per-index
    class projections via [decl_inst] / [lift_class].

    We force the [indType] instance to be unfolded before returning it,
    so that downstream cbv passes see the constructor structure
    rather than an abstract [Ind.Pack]. *)

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
