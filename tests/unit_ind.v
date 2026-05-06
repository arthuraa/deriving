(** Unit tests for [theories/ind.v].

    Each test pins down the reduction behaviour of one [Ind] / [IndF]
    function against a hand-written fixture.  No [[indDef for ...]] is
    used: the declaration, constructor table, recursor, and destructor
    are all written out directly, and the [Ind.Def.class_of] record is
    assembled from these manually-proved building blocks at the end of
    the file.

    The fixture is the single-type inductive

      [Inductive T0 := C0_0 of nat | C0_1 of nat & T0]

    chosen because it exercises both kinds of constructor argument
    ([NonRec] for the [nat]s, [Rec] for the recursive [T0] in [C0_1])
    while staying small enough to write each [Ind.Cidx] / [Ind.args]
    instance by hand. *)

From mathcomp Require Import
  ssreflect ssrfun ssrbool ssrnat eqtype seq choice fintype.
Set SsrOldRewriteGoalsOrder.

From deriving Require Import base shape ind tactics.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Open Scope deriving_scope.

(** * Fixture *)

Inductive T0 := C0_0 of nat | C0_1 of nat & T0.

Definition T0_sorts : fin 1 -> Type := fun _ => T0.

(** [T0_decl] is a [Notation] (not a [Definition]) so each use site
    re-elaborates it in context, picking up the universe instantiation
    its consumer expects.  A [Definition T0_decl : declaration 1 := ...]
    would freeze the second universe at the [Set] forced by [nat]
    appearing in [NonRec nat], and downstream uses ([Ind.Cidx],
    [Ind.constructors]) — whose universes are fixed at compile time of
    [theories/ind.v] — would refuse it. *)

(** The most-recently-added arity sits at the head (index [None]) of
    the resulting sequence.  To match [T0_rect]'s natural order
    (C0_0 first, C0_1 second), we add C0_1 first and C0_0 second, so
    that C0_0's arity ends up at index [None]. *)

Notation T0_decl :=
  (add_arity (add_arity (@empty_decl 1) (None : fin 1)
                        (PolyType.cons (NonRec nat)
                        (PolyType.cons (Rec (None : fin 1))
                         PolyType.nil)))
             (None : fin 1)
             (PolyType.cons (NonRec nat) PolyType.nil)).

(** Constructor table, recursor, and destructor — all written out by
    hand in terms of [T0_rect] / [match].  Building [T0_Cs] via
    [Ind.add_cons] (instead of a nested pattern match) lets Coq's
    elaborator infer the universes from [Ind.add_cons]'s expected type,
    avoiding the [Set]-locking issue described above. *)

Definition T0_Cs : Ind.constructors T0_decl T0_sorts :=
  Ind.add_cons
    (Ind.add_cons (@Ind.empty_cons 1 T0_sorts)
                  (Ti := None)
                  (As := PolyType.cons (NonRec nat)
                        (PolyType.cons (Rec (None : fin 1)) PolyType.nil))
                  C0_1)
    (Ti := None)
    (As := PolyType.cons (NonRec nat) PolyType.nil)
    C0_0.

Definition T0_recursor : Ind.recursor T0_decl T0_sorts :=
  fun S (b1 : nat -> S None) (b2 : nat -> T0 -> S None -> S None) (x : T0) =>
    @T0_rect (fun _ => S None) b1 b2 x.

Definition T0_destructor : Ind.destructor T0_decl T0_sorts :=
  fun S (b1 : nat -> S None) (b2 : nat -> T0 -> S None) (x : T0) =>
    match x with
    | C0_0 n   => b1 n
    | C0_1 n t => b2 n t
    end.

(** * Tests for [Ind] *)

(** ** [Ind.empty_cons]: vacuous on [fin 0]. *)

Lemma empty_cons_void T (i : fin 0) (j : Ind.Cidx empty_decl i) :
  @Ind.empty_cons 0 T i j = match j with end.
Proof. by case: i. Qed.

(** ** [Ind.add_cons]: at the freshly-added head ([Ci = None] after the
    extra cons), returns the new constructor [C]; on a [Some Ci'] it
    falls through to [Cs].  We pin the test on the concrete [T0_decl]
    fixture, where the relevant [Ind.Cidx] reduces enough for [None]
    and [Some None] to typecheck without explicit casts. *)

Lemma add_cons_head_T0 :
  @Ind.add_cons 1 _ _ (@Ind.empty_cons 1 T0_sorts)
                None
                (PolyType.cons (NonRec nat) PolyType.nil)
                C0_0
                None None = C0_0.
Proof. by []. Qed.

Lemma add_cons_skew_T0 :
  @Ind.add_cons 1 _ _
                (Ind.add_cons (@Ind.empty_cons 1 T0_sorts)
                              (Ti := None)
                              (As := PolyType.cons (NonRec nat) PolyType.nil)
                              C0_0)
                None
                (PolyType.cons (NonRec nat)
                (PolyType.cons (Rec (None : fin 1)) PolyType.nil))
                C0_1
                None (Some None) =
  C0_0.
Proof. by []. Qed.

(** ** [Ind.recursor_eq]: for our manually-built [T0_Cs] / [T0_recursor],
    the universally-quantified equation simplifies to a finite
    conjunction of [erefl]-provable equations.  This is the property
    that [ind_def] in [infer.v] discharges by [deriving_compute;
    intuition].

    The [/=] reduction step is the load-bearing one: it unfolds
    [all_hlist2], [all_fin], [all_hlist], the curried [happ] / [happ2]
    coercions on [T0_Cs] / [T0_recursor], and the [args_map] over each
    [hlist'].  After it, every conjunct closes by [erefl]. *)

Lemma T0_recursor_eq : Ind.recursor_eq T0_Cs T0_recursor.
Proof. by move=> S /=; do !split=> //=. Qed.

(** ** [Ind.destructor_eq]: same property for the destructor. *)

Lemma T0_destructor_eq : Ind.destructor_eq T0_Cs T0_destructor.
Proof. by move=> S /=; do !split=> //=. Qed.

(** ** [Ind.rec_branch'_of_hfun']: reduction on each constructor's
    argument shape.  At [NonRec X :: As] it strips an [X], at [Rec j ::
    As] it strips a pair, and at [[::]] it returns its argument. *)

Lemma rec_branch'_of_hfun'_C0_0 S (f : nat -> S None) (n : nat) :
  Ind.rec_branch'_of_hfun' (n:=1) (T:=T0_sorts) (S:=S) (i:=None)
                           (As := PolyType.cons (NonRec nat) PolyType.nil)
                           f n = f n.
Proof. by []. Qed.

Lemma rec_branch'_of_hfun'_C0_1 S
  (f : nat -> (T0 * S None) -> S None)
  (n : nat) (t : T0) (r : S None) :
  Ind.rec_branch'_of_hfun' (n:=1) (T:=T0_sorts) (S:=S) (i:=None)
                           (As := PolyType.cons (NonRec nat)
                                 (PolyType.cons (Rec (None : fin 1))
                                  PolyType.nil))
                           f n t r = f n (t, r).
Proof. by []. Qed.

(** * Manually-built [Ind.Def.type] for [IndF] tests

    [Ind.induction T0_Cs] reduces (after [hdfun] / [hfun2] / [hlist1]
    expansion at [n = 1]) to the [T0_rect]-shaped induction principle,
    so [T0_rect] inhabits it directly. *)

Definition T0_indP : Ind.induction T0_Cs := T0_rect.

Definition T0_indClass : Ind.Def.class_of T0_sorts T0_decl :=
  Ind.Def.Class T0_recursor_eq T0_destructor_eq T0_indP.

Definition T0_indDef : Ind.Def.type :=
  Ind.Def.Pack T0_indClass.

(** * Tests for [IndF]

    These exercise [IndF]'s reductions and propositional laws against
    our manually-bundled [T0_indDef].  The [::: ] notation does not
    declare an associativity, so all [hlist] literals are written with
    explicit right-associative parens. *)

(** ** [IndF.fmap] reductions, one per constructor. *)

Lemma fmap_C0_0 (T S : fin 1 -> Type) (f : T -F> S) (n : nat) :
  IndF.fmap f (@IndF.Cons _ T0_decl T None None (n ::: tt)) =
  @IndF.Cons _ T0_decl S None None (n ::: tt).
Proof. by []. Qed.

Lemma fmap_C0_1
  (T S : fin 1 -> Type) (f : T -F> S) (n : nat) (t : T None) :
  IndF.fmap f
    (@IndF.Cons _ T0_decl T None (Some None) (n ::: (t ::: tt))) =
  @IndF.Cons _ T0_decl S None (Some None) (n ::: (f None t ::: tt)).
Proof. by []. Qed.

(** ** [IndF.RollK] / [IndF.unrollK]: round-trip identities. *)

Lemma RollK_C0_0 (n : nat) :
  IndF.unroll
    (IndF.Roll (T:=T0_indDef) (i:=None)
       (@IndF.Cons _ (Ind.Def.decl T0_indDef) T0_indDef None None
                   (n ::: tt))) =
  @IndF.Cons _ (Ind.Def.decl T0_indDef) T0_indDef None None (n ::: tt).
Proof. exact: IndF.RollK. Qed.

Lemma unrollK_T0 (x : T0_indDef None) :
  IndF.Roll (IndF.unroll x) = x.
Proof. exact: IndF.unrollK. Qed.

(** ** [IndF.recE] / [IndF.caseE] on each constructor.

    These are propositional laws (not definitional), but on our manual
    [T0_indDef] they hold for any [body] / [n] by [IndF.recE] /
    [IndF.caseE]. *)

Lemma recE_C0_0
  S (body : IndF.fobj (Ind.Def.decl T0_indDef) (T0_indDef *F S) -F> S)
  (n : nat) :
  hnth1 (IndF.rec body) None
    (IndF.Roll (T:=T0_indDef) (i:=None)
       (@IndF.Cons _ (Ind.Def.decl T0_indDef) T0_indDef None None
                   (n ::: tt))) =
  body None
    (@IndF.Cons _ (Ind.Def.decl T0_indDef) (T0_indDef *F S) None None
                (n ::: tt)).
Proof. exact: IndF.recE. Qed.

Lemma caseE_C0_0
  R (body : IndF.fobj (Ind.Def.decl T0_indDef) T0_indDef None -> R)
  (n : nat) :
  IndF.case body
    (IndF.Roll (T:=T0_indDef) (i:=None)
       (@IndF.Cons _ (Ind.Def.decl T0_indDef) T0_indDef None None
                   (n ::: tt))) =
  body
    (@IndF.Cons _ (Ind.Def.decl T0_indDef) T0_indDef None None
                (n ::: tt)).
Proof. exact: IndF.caseE. Qed.

(** ** [IndF.indP]: the induction principle is type-correct.  We don't
    enumerate the subgoals here; existing top-level tests
    ([tests/syntax.v], [tests/tree.v]) and the [eqtype] / [order]
    recipes already exercise the substantive shape of [indP]. *)

Lemma indP_typecheck
  (P : forall i, T0_indDef i -> Prop)
  (H : forall i (a : IndF.fobj (Ind.Def.decl T0_indDef)
                      (fun j => {x : T0_indDef j & P j x}) i),
       P i (IndF.Roll (IndF.fmap (fun _ x => tag x) a))) :
  forall i (x : T0_indDef i), P i x.
Proof. exact: IndF.indP H. Qed.
