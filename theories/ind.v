(** * Recursors, destructors, and the [indType] class

    This file gives the deriving framework's view of an inductive type as a
    bundle of:

    - Constructors [Cons : constructors D T] (one [hfun']-curried function
      per constructor of each mutually-defined type),
    - A primitive recursor [rec : recursor D T] and destructor
      [case : destructor D T] (the [Scheme]-style elimination principles
      reformulated to take heterogeneous-list-curried branches),
    - The equational laws [recE]/[caseE] and the induction principle [indP]
      that tie the constructors, recursor, and destructor together.

    These are packaged in [Ind.Def.class_of].  The [indType] class then
    bundles a [Ind.Def.type] (a mutual block) with an index [i : fin n]
    picking which of the mutual types the user actually wants.

    The bottom of the file provides:

    - [find_idx], [pack_indType], and the [IndType] notation: the
      canonical-structure inference that locates a single type [T] within a
      mutual [Ind.Def.type].

    - [Module IndF]: a functor view of an [indType].  Where [Ind.Def] takes
      branches as nested [hfun']s, [IndF] presents each constructor
      application as a single record [Cons constr args] (the constructor
      tag plus an [hlist'] of arguments), gives a [fmap] over those
      arguments, and lifts the primitive [Ind.Def.rec]/[Ind.Def.case] to
      user-friendly [rec]/[case] combinators that operate on this
      flat-record view.

    The [IndF] equations [recE]/[caseE] are propositional lemmas, not
    definitional reductions.  This matters for the [tactics.v] /
    [deriving_compute] pipeline: simplification has to step through the
    underlying [Ind.Def.rec]/[Ind.Def.case] rather than rewriting with
    [recE]/[caseE]. *)

From HB Require Import structures.

From mathcomp Require Import
  ssreflect ssrfun ssrbool ssrnat eqtype seq choice fintype.
Set SsrOldRewriteGoalsOrder.

From deriving Require Import base shape.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Set Warnings "-unsupported-attributes".

Open Scope deriving_scope.

Module Ind.

Section Basic.

Variable n : nat.
Implicit Types (A : arg n) (As : arity n) (Σ : signature n).
Implicit Types (D : declaration n).
Implicit Types (T S : fin n -> Type).

Import PolyType.

(** [Cidx D i] is the index type of the constructors of the [i]-th
    inductive type — finite of size [size (D i)].  [args] gives the
    arguments tuple as an [hlist'] over the [arg]s in [nth_fin Ci]. *)

Definition Cidx D i := fin (size (D i)).
Arguments Cidx : clear implicits.

Definition args D T i (j : Cidx D i) : Type :=
  hlist' (type_of_arg T) (nth_fin j).

Definition args_map D T S (f : T -F> S) i j (xs : @args D T i j) :
  args S j :=
  hmap' (type_of_arg_map f) xs.

(** [constructors D T] : the family of constructors, one per
    [(i, j) : (fin n, Cidx D i)], curried as an [hfun']. *)

Definition constructors D T :=
  forall (Ti : fin n) (Ci : Cidx D Ti),
    hfun' (type_of_arg T) (nth_fin Ci) (T Ti).

Definition empty_cons T : constructors empty_decl T :=
  fun Ti Ci => match Ci with end.

Definition add_cons D T (Cs : constructors D T) Ti As
  (C : hfun' (type_of_arg T) As (T Ti))
  : constructors (add_arity D Ti As) T :=
  fun Ti' =>
    add_arity_ind
      (fun Ti' Σ =>
         forall Ci : fin (size Σ),
           hfun' (type_of_arg T) (nth_fin Ci) (T Ti'))
      D Ti As Ti'
      (fun Ci => if Ci is Some Ci then Cs Ti Ci else C)
      (Cs Ti').

(** [rec_branch'] is the type of one recursor branch, expressed as a
    nested function over the arity.  At each [NonRec] argument [X] we
    abstract over an [X]; at each [Rec j] we abstract over both the
    recursive subterm [T j] and the result of recursing on it [S j]. *)

Fixpoint rec_branch' T S i As : Type :=
  match As with
  | NonRec X :: As => X          -> rec_branch' T S i As
  | Rec    j :: As => T j -> S j -> rec_branch' T S i As
  | [::]           => S i
  end.

Definition rec_branch D T S i (j : Cidx D i) : Type :=
  rec_branch' T S i (nth_fin j).

(** [recursor D T] is the type of the primitive recursor: an [hfun2]
    taking one branch per [(i, j)] and returning, for each [i], a
    function [T i -> S i]. *)

Definition recursor D T :=
  forall S, hfun2 (@rec_branch D T S) (hlist1 (fun i => T i -> S i)).

(** Conversion between [rec_branch'] (the curried per-arity branch shape)
    and [hfun'] over [type_of_arg (T *F S)] (the branch shape used by
    [IndF.rec]).  These are mutual inverses up to [hcurryK]/[hcurry];
    [rec_branch_of_hfunK] expresses the round-trip identity. *)

Fixpoint rec_branch'_of_hfun' T S i As :
  hfun' (type_of_arg (T *F S)) As (S i) -> rec_branch' T S i As :=
  match As with
  | NonRec R :: As => fun f x   => rec_branch'_of_hfun' (f x)
  | Rec    j :: As => fun f x y => rec_branch'_of_hfun' (f (x, y))
  | [::]           => fun f     => f
  end.

Fixpoint hfun'_of_rec_branch' T S i As :
  rec_branch' T S i As -> hfun' (type_of_arg (T *F S)) As (S i) :=
  match As with
  | NonRec R :: As => fun f x => hfun'_of_rec_branch' (f x)
  | Rec    j :: As => fun f p => hfun'_of_rec_branch' (f p.1 p.2)
  | [::]           => fun f   => f
  end.

Coercion hfun'_of_rec_branch' : rec_branch' >-> hfun'.

Lemma rec_branch_of_hfunK T S i As f xs :
  @rec_branch'_of_hfun' T S i As f xs = f xs.
Proof. by elim: As f xs => [|[R|j] As IH] f //= [[x y] xs]. Qed.

(** [recursor_eq] is the equational law: applied to a constructor [Cs i j],
    the recursor returns the corresponding branch evaluated on the
    arguments paired with their recursive results. *)

Definition recursor_eq D T (Cs : constructors D T) (r : recursor D T) :=
  forall S,
  all_hlist2 (fun bs : hlist2 (rec_branch T S) =>
  all_fin    (fun i  : fin n                   =>
  all_fin    (fun j  : Cidx D i                =>
  all_hlist  (fun xs : args T j                =>
    r S bs _ (Cs i j xs) =
    bs i j (args_map (fun k x => (x, r S bs k x)) xs))))).

Definition des_branch D T S i (j : Cidx D i) :=
  hfun' (type_of_arg T) (nth_fin j) (S i).

Definition destructor D T :=
  forall S, hfun2 (@des_branch D T S) (hlist1 (fun i => T i -> S i)).

Definition destructor_eq D T (Cs : constructors D T) (d : destructor D T) :=
  forall S,
  all_hlist2 (fun bs : hlist2 (des_branch T S) =>
  all_fin    (fun i  : fin n                   =>
  all_fin    (fun j  : Cidx D i                =>
  all_hlist  (fun xs : args T j                =>
    d S bs _ (Cs i j xs) = bs i j xs)))).

(** A destructor can be constructed from a recursor by ignoring the
    recursive results; we use this in [infer.v] to derive [case] from
    the user-supplied [Scheme]-style recursor. *)

Definition rec_of_des_branch D T S i (j : Cidx D i) (b : des_branch T S j) :
  rec_branch T S j :=
  rec_branch'_of_hfun' (hcurry (fun xs => b (args_map (fun _ => fst) xs))).

Definition destructor_of_recursor D T (r : recursor D T) : destructor D T :=
  fun S => hcurry2 (fun bs : hlist2 (@des_branch D T S) =>
    r S (hmap2 (@rec_of_des_branch D T S) bs)).

(** [ind_branch'] is the per-arity shape of an induction-principle
    branch: at each [NonRec R] we abstract over an [R]; at each [Rec j]
    we abstract over the subterm and an induction-hypothesis [P j]. *)

Fixpoint ind_branch' T (P : forall i, T i -> Type) i As :
  hfun' (type_of_arg T) As (T i) -> Type :=
  match As with
  | NonRec R :: As => fun C => forall x : R,            ind_branch' P (C x)
  | Rec    j :: As => fun C => forall x : T j, P j x -> ind_branch' P (C x)
  | [::]           => fun C => P i C
  end.

Definition ind_branch D T P (Cs : constructors D T) i (j : Cidx D i) :=
  @ind_branch' T P i (nth_fin j) (Cs i j).

Definition induction D T (Cs : constructors D T) :=
  @hdfun n (fun i => T i -> Type) (fun P : hlist (fun i => T i -> Type) =>
  hfun2 (@ind_branch D T P Cs) (hlist1 (fun i => forall x, P i x))).

End Basic.

(** ** [Ind.Def]: bundling the recursor/destructor data

    [Ind.Def.class_of n sorts decl] is the record packaging the
    constructors, the primitive [rec]/[case], their equations, and the
    induction principle.  [Ind.Def.type] is its sigma counterpart, with
    [n], [sorts], and [decl] existentially packed.  The user obtains an
    [Ind.Def.type] via [[indDef for rect]] in [infer.v]. *)

Module Def.

Set Primitive Projections.
Record class_of n sorts (decl : declaration n) := Class {
  Cons      : constructors decl sorts;
  rec       : recursor decl sorts;
  case      : destructor decl sorts;
  recE      : recursor_eq Cons rec;
  caseE     : destructor_eq Cons case;
  indP      : induction Cons;
}.

Record type := Pack {
  n : nat;
  sorts : fin n -> Type;
  decl : declaration n;
  class : class_of sorts decl;
}.
Unset Primitive Projections.

End Def.

(** ** [indType]: a single Coq type within a mutual block

    [Ind.type] picks a specific carrier [T] out of an [Ind.Def.type] by
    storing the index [i : fin (Def.n def)] and a transport [T = Def.sorts i].
    [Ind.clone] is the [[indType of T]] resolver. *)

Section ClassDef.

Set Primitive Projections.
Record mixin_of T := Mixin {
  def  : Def.type;
  idx  : fin (Def.n def);
  idxE : T = Def.sorts idx;
}.
Unset Primitive Projections.

Record type := Pack {sort : Type; _ : mixin_of sort}.
Local Coercion sort : type >-> Sortclass.
Local Notation class_of := mixin_of.

Variables (T : Type) (cT : type).
Definition class := let: Pack _ c as cT' := cT return class_of cT' in c.
Definition clone n Ts D cTs i iE :=
  let sTs := @Mixin T (@Def.Pack n Ts D cTs) i iE in
  fun & phant_id class sTs => @Pack T sTs.
Let xT := let: Pack T _ := cT in T.
Notation xclass := (class : class_of xT).

End ClassDef.

Notation class_of := mixin_of.

Module Exports.
Identity Coercion hdfun_of_induction : induction >-> hdfun.
Coercion Def.sorts : Def.type >-> Funclass.
Coercion Def.class : Def.type >-> Def.class_of.
Notation indDef := Def.type.
Notation IndDef := Def.Pack.
Coercion sort : type >-> Sortclass.
Coercion class : type >-> class_of.
Coercion def : class_of >-> indDef.
Notation indType := type.
Notation "[ 'indType' 'of' T ]" := (@clone T _ _ _ _ _ _ _ id)
  (at level 0, format "[ 'indType'  'of'  T ]") : form_scope.
End Exports.

End Ind.
Export Ind.Exports.

Arguments Ind.Def.decl : clear implicits.

(** ** [find_idx]: locating [T] within a mutual [Def.type]

    [find_idx n Ts T i e] is a typeclass that asserts [T = Ts i] and
    pinpoints the index [i].  The two [Hint Extern]s implement the search
    by case-analysing on [n]: at [n.+1], either match the head ([Ts None])
    or recurse on the tail ([fun i => Ts (Some i)]).

    Used by [pack_indType] / [IndType T Ts] to canonically associate a
    user type [T] with its position in a mutual block. *)

Class find_idx n (Ts : fin n -> Type) (T : Type) i (e : T = Ts i) :=
  make_find_idx { }.
Arguments find_idx : clear implicits.
Arguments make_find_idx {_ _ _ _ _}.

Definition find_idx_here n (Ts : fin n.+1 -> Type) :
  find_idx n.+1 Ts (Ts None) None erefl := make_find_idx.

Definition find_idx_there n (Ts : fin n.+1 -> Type) T i e
  (_ : find_idx n (fun i => Ts (Some i)) T i e) :
  find_idx n.+1 Ts T (Some i) e :=
  make_find_idx.

#[global]
Hint Extern 1 (find_idx ?m ?Ts ?T _ _) =>
  match eval hnf in m with
  | ?n.+1 => eapply (@find_idx_here n Ts)
  end : typeclass_instances.

#[global]
Hint Extern 2 (find_idx ?m ?Ts ?T _ _) =>
  match eval hnf in m with
  | ?n.+1 => eapply (@find_idx_there n Ts)
  end : typeclass_instances.

Definition pack_indType
  T (Ts : indDef) i e
  & find_idx (Ind.Def.n Ts) Ts T i e :=
  Ind.Pack (@Ind.Mixin T Ts i e).

Notation IndType T Ts := (@pack_indType T Ts _ _ _).

#[global]
Hint Unfold Ind.Cidx : deriving.
#[global]
Hint Unfold Ind.args : deriving.
#[global]
Hint Unfold Ind.args_map : deriving.
#[global]
Hint Unfold Ind.constructors : deriving.
#[global]
Hint Unfold Ind.empty_cons : deriving.
#[global]
Hint Unfold Ind.add_cons : deriving.
#[global]
Hint Unfold Ind.rec_branch' : deriving.
#[global]
Hint Unfold Ind.rec_branch : deriving.
#[global]
Hint Unfold Ind.recursor : deriving.
#[global]
Hint Unfold Ind.rec_branch'_of_hfun' : deriving.
#[global]
Hint Unfold Ind.hfun'_of_rec_branch' : deriving.
#[global]
Hint Unfold Ind.recursor_eq : deriving.
#[global]
Hint Unfold Ind.des_branch : deriving.
#[global]
Hint Unfold Ind.destructor : deriving.
#[global]
Hint Unfold Ind.destructor_eq : deriving.
#[global]
Hint Unfold Ind.rec_of_des_branch : deriving.
#[global]
Hint Unfold Ind.destructor_of_recursor : deriving.
#[global]
Hint Unfold Ind.ind_branch' : deriving.
#[global]
Hint Unfold Ind.ind_branch : deriving.
#[global]
Hint Unfold Ind.induction : deriving.
#[global]
Hint Unfold Ind.Def.Cons : deriving.
#[global]
Hint Unfold Ind.Def.rec : deriving.
#[global]
Hint Unfold Ind.Def.case : deriving.
#[global]
Hint Unfold Ind.Def.n : deriving.
#[global]
Hint Unfold Ind.Def.sorts : deriving.
#[global]
Hint Unfold Ind.Def.decl : deriving.
#[global]
Hint Unfold Ind.Def.class : deriving.
#[global]
Hint Unfold Ind.class : deriving.
#[global]
Hint Unfold Ind.def : deriving.
#[global]
Hint Unfold Ind.idx : deriving.
#[global]
Hint Unfold Ind.idxE : deriving.
#[global]
Hint Unfold Ind.sort : deriving.
#[global]
Hint Unfold Ind.clone : deriving.
#[global]
Hint Unfold find_idx_here : deriving.
#[global]
Hint Unfold find_idx_there : deriving.
#[global]
Hint Unfold pack_indType : deriving.

(** ** [IndF]: a functor view of an [indType]

    [Ind.Def] presents constructor application as nested [hfun']s; that
    shape is convenient for stating [recursor_eq], but inconvenient for
    user code that wants to talk about a single inductive value as
    "the constructor tag plus the hlist of its arguments".  [IndF.fobj T i]
    is exactly that record, with [Roll]/[unroll] as the round-trip with
    the underlying [T i].

    On top of this, [IndF.rec] / [IndF.case] are user-friendly recursor /
    destructor combinators (taking a single function over [F T] rather
    than an [hfun2] of branches), and [recE]/[caseE]/[indP]/[Roll_inj]
    state the equational laws and induction principle. *)

Module IndF.

Section FunctorDef.

Variables (n : nat) (D : declaration n).

Implicit Types (T S : fin n -> Type).

Notation size := PolyType.size.

Record fobj T (i : fin n) := Cons {
  constr : Ind.Cidx D i;
  args : hlist' (type_of_arg T) (nth_fin constr)
}.

Arguments Cons {_ i} _ _.

Local Notation F := fobj.

Definition fmap T S (f : T -F> S) i (x : F T i) : F S i :=
  Cons (constr x) (hmap' (type_of_arg_map f) (args x)).

Lemma fmap_eq T S (f g : T -F> S) :
  (forall i x, f i x = g i x) ->
  (forall i (x : F T i), fmap f x = fmap g x).
Proof.
move=> e i [j args]; congr Cons; apply: hmap_eq => /= k.
by case: (nth_fin k).
Qed.

Lemma fmap1 T i : @fmap T T (fun _ => id) i =1 id.
Proof.
move=> [j args] /=; congr Cons; rewrite -[RHS]hmap1.
by apply: hmap_eq=> /= k; case: (nth_fin k).
Qed.

Lemma fmap_comp T S R (f : T -F> S) (g : S -F> R) i :
  @fmap _ _ (fun j x => g j (f j x)) i =1
  @fmap _ _ g i \o @fmap _ _ f i.
Proof.
move=> [j args] /=; congr Cons; rewrite /= /hmap' hmap_comp.
by apply: hmap_eq=> /= k; case: (nth_fin k).
Qed.

Lemma inj T (i : fin n) (j : Ind.Cidx D i)
  (a b : hlist' (type_of_arg T) (nth_fin j)) :
  Cons j a = Cons j b -> a = b.
Proof.
pose get x :=
  if leq_fin (constr x) j is inl e then
    cast (fun j : Ind.Cidx D i =>
            hlist' (type_of_arg T) (nth_fin j)) e (args x)
  else a.
by move=> /(congr1 get); rewrite /get /= leq_finii /=.
Qed.

End FunctorDef.

Section TypeDef.

Variable (T : indDef).

Notation D := (Ind.Def.decl T).
Notation F := (@fobj _ D).

Arguments Cons {n D T i} _ _.

Definition Roll i (x : F T i) : T i :=
  @Ind.Def.Cons _ _ _ T i (constr x) (args x).

Definition rec_branches_of_fun S (body : F (T *F S) -F> S) :
  hlist2 (@Ind.rec_branch _ D T S) :=
  hlist_of_fun (fun i =>
  hlist_of_fun (fun j : Ind.Cidx D i =>
    Ind.rec_branch'_of_hfun'
      (hcurry
         (fun l => body i (Cons j l))))).

Definition rec S (body : F (T *F S) -F> S) :=
  @Ind.Def.rec _ _ _ T S (rec_branches_of_fun body).

(** [lift_type]/[lift_typeE]/[lift_type_of] — bookkeeping that lets the
    destructor [case] return a result type that depends on the index [i]
    being matched, while still factoring through the index-uniform
    [Ind.Def.case]. *)

Definition lift_type R i : fin (Ind.Def.n T) -> Type :=
  fun j => if leq_fin i j is inl e then R else unit.

Definition lift_typeE R i : lift_type R i i = R :=
  congr1 (fun r => if r is inl e then R else unit) (leq_finii i).

Definition lift_type_of R i j (f : i = j -> R) : lift_type R i j :=
  match leq_fin i j
  as r
  return if r is inl e then R else unit
  with
  | inl e => f e
  | inr _ => tt
  end.

Definition des_branches_of_fun i R (body : F T i -> R) :
  hlist2 (@Ind.des_branch _ D T (lift_type R i)) :=
  hlist_of_fun (fun i' =>
  hlist_of_fun (fun j : Ind.Cidx D i' =>
    hcurry (fun l => @lift_type_of R i i' (fun e => body (cast (F T) e^-1 (Cons j l)))))).

Definition case i R (body : F T i -> R) x :=
  cast id (lift_typeE R i)
    (@Ind.Def.case _ _ _ T _ (des_branches_of_fun body) i x).

Lemma recE S f i (a : F T i) :
  @rec S f i (Roll a) =
  f i (fmap (fun j (x : T j) => (x, rec f j x)) a).
Proof.
case: a=> [j args]; have := Ind.Def.recE T S.
move/all_hlist2P/(_ (rec_branches_of_fun f)).
move/all_finP/(_ i).
move/all_finP/(_ j).
move/all_hlistP/(_ args).
rewrite /rec_branches_of_fun hnth_of_fun.
rewrite /rec /Roll => -> /=.
by rewrite /= hnth_of_fun Ind.rec_branch_of_hfunK hcurryK.
Qed.

Lemma caseE i R f (a : F T i) : case f (Roll a) = f a :> R.
Proof.
case: a => [j args]; have := Ind.Def.caseE T (lift_type R i).
move/all_hlist2P/(_ (des_branches_of_fun f)).
move/all_finP/(_ i).
move/all_finP/(_ j).
move/all_hlistP/(_ args).
rewrite /des_branches_of_fun hnth_of_fun.
rewrite /case /Roll => -> /=.
rewrite /lift_type /lift_typeE /lift_type_of hnth_of_fun hcurryK /=.
case: (leq_fin i i) (leq_finii i)=> // e.
rewrite (eq_axiomK e) => {}e.
by rewrite (eq_axiomK e) /=.
Qed.

Lemma indP P :
  (forall i (a : F (fun j => {x & P j x}) i),
    P i (Roll (fmap (fun _ => tag) a))) ->
  forall i x, P i x.
Proof.
move=> IH.
pose Q := hlist_of_fun P.
pose Q_of_P i a : P i a -> Q i a :=
  cast id (congr1 (fun F => F a) (hnth_of_fun P i))^-1.
pose P_of_Q i a : Q i a -> P i a :=
  cast id (congr1 (fun F => F a) (hnth_of_fun P i)).
pose TP_of_TQ i x := Tagged (P i) (P_of_Q i (tag x) (tagged x)).
have Q_of_PK i a : cancel (Q_of_P i a) (P_of_Q i a) := castKV _.
have P_of_QK i a : cancel (P_of_Q i a) (Q_of_P i a) := castK  _.
have {}IH i (a : F (fun j => {x & Q j x}) i) :
    Q i (Roll (fmap (fun _ => tag) a)).
  rewrite (_ : fmap _ a = fmap (fun _ => tag) (fmap TP_of_TQ a)); last first.
    by rewrite -[RHS]fmap_comp; apply: fmap_eq=> ? [].
  by apply: (Q_of_P); apply: IH.
move=> i x {P_of_QK Q_of_PK Q_of_P TP_of_TQ}; apply: P_of_Q.
move: {P} Q IH i x.
rewrite /Roll; case: (T) => n S D [/= Cs _ _ _ _ indP] P.
have {}indP :
    (forall i j, Ind.ind_branch' P (Cs i j)) ->
    (forall i x, P i x).
  move=> hyps i x.
  pose bs : hlist2 (Ind.ind_branch P Cs) :=
    hlist_of_fun (fun i => hlist_of_fun (fun j => hyps i j)).
  exact: (hdapp indP P bs i x).
move=> hyps; apply: indP=> i j.
have {}hyps:
  forall args : hlist' (type_of_arg (fun k => {x & P k x})) (nth_fin j),
    P i (Cs i j (hmap' (type_of_arg_map (fun _ => tag)) args)).
  by move=> args; move: (hyps i (Cons j args)).
move: (Cs i j) hyps; rewrite /fnth.
elim: (nth_fin j)=> [|[R|k] As IH] /=.
- by move=> C /(_ tt).
- move=> C hyps x; apply: IH=> args; exact: (hyps (x ::: args)).
- move=> constr hyps x H; apply: IH=> args.
  exact: (hyps (existT _ x H ::: args)).
Qed.

Definition unroll i := @case i _ id.

Lemma RollK i : cancel (@Roll i) (@unroll i).
Proof. by move=> x; rewrite /unroll caseE. Qed.

Lemma Roll_inj i : injective (@Roll i).
Proof. exact: can_inj (@RollK i). Qed.

Lemma unrollK i : cancel (@unroll i) (@Roll i).
Proof. by elim/indP: i / => i a; rewrite RollK. Qed.

Lemma unroll_inj i : injective (@unroll i).
Proof. exact: can_inj (@unrollK i). Qed.

End TypeDef.

End IndF.

#[global]
Hint Unfold IndF.constr : deriving.
#[global]
Hint Unfold IndF.args : deriving.
#[global]
Hint Unfold IndF.fmap : deriving.
#[global]
Hint Unfold IndF.Roll : deriving.
#[global]
Hint Unfold IndF.rec_branches_of_fun : deriving.
#[global]
Hint Unfold IndF.rec : deriving.
#[global]
Hint Unfold IndF.lift_type : deriving.
#[global]
Hint Unfold IndF.lift_typeE : deriving.
#[global]
Hint Unfold IndF.lift_type_of : deriving.
#[global]
Hint Unfold IndF.des_branches_of_fun : deriving.
#[global]
Hint Unfold IndF.case : deriving.
#[global]
Hint Unfold IndF.unroll : deriving.
