(** * Class-decorated views of declarations

    This file builds the machinery that lets the deriving framework recover
    a typeclass instance for every non-recursive argument of every
    constructor of a mutual inductive block.  It has three layers, in
    order of generality:

    - The [fun_split] primitive splits a function [fin n.+1 -> R] into a
      head element and a tail function [fin n -> R].  It is the per-step
      tool for peeling a mutual block one type at a time, and is
      registered as a canonical structure so that Coq can synthesise
      these splits during instance inference.

    - [lift_class] packages, for a sequence of [n] types
      [Ts : fin n -> Type], the data that each [Ts i] has an instance of a
      chosen typeclass [K] (witnessed by an [eq_class] for a class
      projection [sort : K -> Type]).  Canonical instances [nil_lift_class]
      and [cons_lift_class] let Coq synthesise a [lift_class n] for any
      family of types whose individual instances are already known.

    - The [arg_class] / [arity_class] / [sig_class] / [decl_inst]
      hierarchy decorates a [shape.v]-style [declaration n] with class
      instances on the non-recursive arguments — used to find, for each
      constructor argument, the [eqType] / [choiceType] / [orderType]
      instance that the deriving framework will rely on to compose the
      derived operation.

    The eliminator [arity_rec] from this file is the recursion principle
    over a class-decorated arity, used by every deriving recipe to build
    up a per-constructor body. *)

From HB Require Import structures.

From mathcomp Require Import
  ssreflect ssrfun ssrbool ssrnat eqtype seq choice fintype.
Set SsrOldRewriteGoalsOrder.

From deriving Require Import base shape.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Backwards compatibility for hint locality attributes *)
Set Warnings "-unsupported-attributes".

Open Scope deriving_scope.

(** ** [fun_split]: peeling a function on [fin n.+1] into head and tail

    A [fun_split n R T Ts] is a function [TTs : fin n.+1 -> R] together
    with proofs that [TTs None = T] (the head element) and
    [TTs (Some i) = Ts i] for each tail index.  The canonical instance
    [fun_split1] makes this trivially available for any [TTs], so that
    Coq's canonical structure inference can decompose mutual-block
    families during typeclass resolution. *)

Record fun_split n (R : Type) (T : R) (Ts : fin n -> R) := FunSplit {
  fs_fun :> fin n.+1 -> R;
  _      :  T = fs_fun None;
  _      :  forall i, Ts i = fs_fun (Some i);
}.

Definition fsE1 n R T Ts (TTs : @fun_split n R T Ts) : T = TTs None :=
  let: FunSplit _ e _ := TTs in e.

Definition fsE2 n R T Ts (TTs : @fun_split n R T Ts) :
  forall i, Ts i = TTs (Some i) :=
  let: FunSplit _ _ e := TTs in e.

Canonical fun_split1 n R (TTs : fin n.+1 -> R) :=
  @FunSplit n R (TTs None) (fun i => TTs (Some i)) TTs erefl (fun=> erefl).

#[global]
Hint Unfold fs_fun : deriving.
#[global]
Hint Unfold fsE1 : deriving.
#[global]
Hint Unfold fsE2 : deriving.
#[global]
Hint Unfold fun_split1 : deriving.

(** ** [lift_class]: per-index class instances along a type family

    Given a class projection [sort : K -> Type] (e.g.
    [Equality.sort : eqType -> Type]), a [lift_class n] is a family
    [Ts : fin n -> Type] together with, for each [i], an [eq_class]
    witness that some [sX : K] has [sort sX = Ts i].  In practice this is
    "for each type in the mutual block, an instance of the chosen
    MathComp class".

    [tagged_sort] interposes a level of indirection so that the canonical
    inference can backtrack between the empty (tail) case and the cons
    (head + tail) case without ambiguity. *)

Section LiftClass.

Import PolyType.

Variables (K : Type) (sort : K -> Type).

Definition eq_class X := {sX : K | sort sX = X}.

Record tagged_sort n := TaggedSort {
  untag_sort :> fin n -> Type;
}.

Definition ts_nil_tag n Ts := @TaggedSort n Ts.
Canonical ts_cons_tag n Ts := @ts_nil_tag n Ts.

Record lift_class n := LiftClass {
  lift_class_sort  :> tagged_sort n;
  _ :  forall i, eq_class (lift_class_sort i);
}.

Definition lift_class_class n (sTs : lift_class n) :=
  let: LiftClass _ cTs := sTs return forall i, eq_class (sTs i) in cTs.

Canonical nil_lift_class f :=
  @LiftClass 0 (ts_nil_tag f) (fun i => match i with end).

Canonical cons_lift_class n
  (sT : K) (f : lift_class n) (g : fun_split (sort sT) f) :=
  @LiftClass n.+1 (ts_cons_tag g)
             (fun i =>
                match i with
                | None   => cast eq_class (fsE1 g)   (exist _ sT erefl)
                | Some i => cast eq_class (fsE2 g i) (lift_class_class f i)
                end).

(** [lift_class_proj] uses an [eq_class] witness to transport a class
    instance along the equality [sort sX = sTs i], producing the per-index
    instance for any user-supplied projection [class : forall sT, cK (sort sT)]
    (e.g. [Equality.class] mapping [sX : eqType] to its mixin). *)

Definition lift_class_proj n cK
           (class : forall sT, cK (sort sT))
           (sTs : lift_class n) (i : fin n)
  : cK (sTs i) :=
  cast cK (svalP (lift_class_class sTs i)) (class _).

End LiftClass.

#[global]
Hint Unfold eq_class : deriving.
#[global]
Hint Unfold untag_sort : deriving.
#[global]
Hint Unfold ts_nil_tag : deriving.
#[global]
Hint Unfold ts_cons_tag : deriving.
#[global]
Hint Unfold lift_class_sort : deriving.
#[global]
Hint Unfold lift_class_class : deriving.
#[global]
Hint Unfold nil_lift_class : deriving.
#[global]
Hint Unfold cons_lift_class : deriving.
#[global]
Hint Unfold lift_class_proj : deriving.

Arguments lift_class_proj {K sort n cK} class sTs i.

(** ** Class-decorated declaration views

    Given a declaration [D : declaration n] and a class projection [sort],
    the [arg_class]/[arity_class]/[sig_class]/[decl_inst] hierarchy
    answers the question: for each non-recursive argument [NonRec X],
    what is the class instance of [X]?

    - [arg_class A] is the data attached to one [arg]: an [eq_class]
      witness if [A] is a [NonRec X], and [unit] otherwise.
    - [arg_inst]/[arity_inst]/[sig_inst]/[decl_inst] are records bundling
      a syntactic shape with its decorations, used as canonical-structure
      hooks for inference.
    - The [Canonical] declarations below tell Coq how to compose these
      decorations along [::] and [_ :: _]: roughly, an empty arity has
      [tt] decoration; a cons arity has its head and tail decorations
      side by side; and so on up to whole declarations.

    The end result is that the user just writes [decl_inst n sort n] and
    Coq fills it in, producing [D] together with [forall i, sig_class (D i)]. *)

Set Universe Polymorphism.

Section ShapeClass.

Import PolyType.

Variable n : nat.
Variables (K : Type) (sort : K -> Type).

Implicit Types (T S : fin n -> Type).
Implicit Types (A : arg n) (As : arity n) (Σ : signature n).

Definition arg_class A :=
  if A is NonRec T then eq_class sort T else unit.

Record arg_inst := ArgInst {
  arg_inst_sort  :> arg n;
  arg_inst_class :  arg_class arg_inst_sort
}.
Arguments ArgInst : clear implicits.

Definition arity_class (As : arity n) :=
  hlist' arg_class As.

Record arity_inst := ArityInst {
  arity_inst_sort  :> arity n;
  arity_inst_class :  arity_class arity_inst_sort;
}.
Arguments ArityInst : clear implicits.

Definition sig_class (Σ : signature n) :=
  hlist' arity_class Σ.

Record sig_inst := SigInst {
  sig_inst_sort  :> signature n;
  sig_inst_class :  sig_class sig_inst_sort;
}.
Arguments SigInst : clear implicits.

Record tagged_decl k := TaggedDecl {
  untag_decl :> fin k -> signature n;
}.

Record decl_inst k := DeclInst {
  decl_inst_sort  :> tagged_decl k;
  _               :  forall i, sig_class (decl_inst_sort i)
}.
Arguments DeclInst : clear implicits.

Definition decl_inst_class k (d : decl_inst k) :
  forall i, sig_class (@decl_inst_sort k d i) :=
  let: DeclInst _ d := d in d.

Implicit Types (Ai : arg_inst) (Asi : arity_inst) (Σi : sig_inst).

(** Canonical instances for inferring [arg_inst] / [arity_inst] / [sig_inst]
    / [decl_inst] from concrete shapes. *)

Canonical NonRec_arg_inst sX :=
  ArgInst (NonRec (sort sX)) (exist _ sX erefl).

Canonical Rec_arg_inst i :=
  ArgInst (Rec i) tt.

Canonical nth_fin_arg_inst Asi (i : fin (size Asi)) :=
  ArgInst (nth_fin i) (arity_inst_class Asi i).

Canonical nil_arity_inst :=
  ArityInst nil tt.

Canonical cons_arity_inst Ai Asi :=
  ArityInst (arg_inst_sort Ai :: arity_inst_sort Asi)
            (arg_inst_class Ai ::: arity_inst_class Asi).

Canonical nth_fin_arity_inst Σi (i : fin (size Σi)) :=
  ArityInst (nth_fin i) (sig_inst_class Σi i).

Canonical nil_sig_inst :=
  SigInst nil tt.

Canonical cons_sig_inst Asi Σi :=
  SigInst (arity_inst_sort Asi :: sig_inst_sort Σi)
          (arity_inst_class Asi ::: sig_inst_class Σi).

Definition nil_decl_tag k (D : fin k -> signature n) := TaggedDecl D.
Canonical cons_decl_tag k (D : fin k -> signature n) := nil_decl_tag D.

Canonical nil_decl_inst f :=
  DeclInst 0 (nil_decl_tag f) (fun i => match i with end).

Canonical cons_decl_inst k Σi Di
  (D : fun_split (sig_inst_sort Σi) (untag_decl (@decl_inst_sort k Di))) :=
  DeclInst k.+1
           (cons_decl_tag (fs_fun D))
           (fun i =>
              match i with
              | None => cast sig_class (fsE1 D) (sig_inst_class Σi)
              | Some i => cast sig_class (fsE2 D i) (@decl_inst_class k Di i)
              end).

(** [arity_rec] is the recursion principle on a class-decorated arity:
    given a base case [Pnil] and step cases [PNonRec] (carrying the
    underlying class element) and [PRec] (carrying the recursive index),
    it produces a [P As] for any [As : arity n] paired with its
    [arity_class] decoration.  Every deriving recipe (eqtype, order, ...)
    builds its per-constructor body via this fold. *)

Definition arity_rec (P : arity n -> Type)
  (Pnil    : P [::])
  (PNonRec : forall (sX : K) (As : arity n), P As -> P (NonRec (sort sX) :: As))
  (PRec    : forall i        (As : arity n), P As -> P (Rec i            :: As)) :=
  fix arity_rec As : arity_class As -> P As :=
    match As with
    | [::]               => fun cAs =>
      Pnil
    | NonRec X :: As => fun cAs =>
      cast (fun X => P (NonRec X :: As)) (svalP cAs.(hd))
           (PNonRec (sval cAs.(hd)) As (arity_rec As cAs.(tl)))
    | Rec i :: As    => fun cAs =>
      PRec i As (arity_rec As cAs.(tl))
    end.

(** [arity_ind] is the matching induction principle: it lets a user prove
    a [Prop]-valued claim by induction on the arity, using the same shape
    of cases as [arity_rec]. *)

Lemma arity_ind (P : forall As, hlist' arg_class As -> Type)
  (Pnil : P [::] tt)
  (PNonRec : forall sX As cAs,
      P As cAs -> P (NonRec (sort sX) :: As) (exist _ sX erefl ::: cAs))
  (PRec : forall i As cAs,
      P As cAs -> P (Rec i :: As) (tt ::: cAs))
  As cAs : P As cAs.
Proof.
elim: As cAs=> [|[X|i] As IH] => /= [[]|[[xS e] cAs]|[[] cAs]] //.
  by case: X / e cAs => ?; apply: PNonRec.
by apply: PRec.
Qed.

End ShapeClass.

#[global]
Hint Unfold arg_class : deriving.
#[global]
Hint Unfold arg_inst_sort : deriving.
#[global]
Hint Unfold arg_inst_class : deriving.
#[global]
Hint Unfold arity_class : deriving.
#[global]
Hint Unfold arity_inst_sort : deriving.
#[global]
Hint Unfold arity_inst_class : deriving.
#[global]
Hint Unfold sig_class : deriving.
#[global]
Hint Unfold sig_inst_sort : deriving.
#[global]
Hint Unfold sig_inst_class : deriving.
#[global]
Hint Unfold untag_decl : deriving.
#[global]
Hint Unfold decl_inst_sort : deriving.
#[global]
Hint Unfold decl_inst_class : deriving.
#[global]
Hint Unfold NonRec_arg_inst : deriving.
#[global]
Hint Unfold Rec_arg_inst : deriving.
#[global]
Hint Unfold nth_fin_arg_inst : deriving.
#[global]
Hint Unfold nil_arity_inst : deriving.
#[global]
Hint Unfold cons_arity_inst : deriving.
#[global]
Hint Unfold nil_sig_inst : deriving.
#[global]
Hint Unfold cons_sig_inst : deriving.
#[global]
Hint Unfold nil_decl_tag : deriving.
#[global]
Hint Unfold cons_decl_tag : deriving.
#[global]
Hint Unfold nil_decl_inst : deriving.
#[global]
Hint Unfold cons_decl_inst : deriving.
#[global]
Hint Unfold arity_rec : deriving.

(** [arg_class_map] re-decorates an [arg] from one class to another along a
    proof that the second class's projection factors through the first.
    Used by recipes that lift [eqType] decorations to [choiceType] or
    [orderType]. *)

Definition arg_class_map
  n K1 K2 (sort1 : K1 -> Type) (sort2 : K2 -> Type)
  (f : K1 -> K2) (p : forall cT, sort2 (f cT) = sort1 cT) (A : arg n) :
  arg_class sort1 A -> arg_class sort2 A :=
  match A with
  | NonRec T => fun cT =>
    PolyType.exist _
      (f (PolyType.sval cT)) (p (PolyType.sval cT) * PolyType.svalP cT)
  | Rec i    => fun _  => tt
  end.

#[global]
Hint Unfold arg_class_map : deriving.

(** [pack_decl_inst] is the inference hook that lets a notation say "find
    me a [decl_inst] for this declaration"; the [phant_id] argument lines
    up the user-supplied declaration with the canonical-structure
    inferred one. *)

Definition pack_decl_inst
  n (D : declaration n) (Di : decl_inst n Equality.sort n)
  & phant_id D (untag_decl (decl_inst_sort Di)) := Di.

Unset Universe Polymorphism.

Arguments arity_rec {n K} _ _ _ _ _.
