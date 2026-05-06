(** Unit tests for [theories/infer.v].

    Each test pins down the resolution behaviour of one inference
    typeclass on a hand-picked branch / recursor shape, *without* going
    through [[indDef for ...]] (which exercises the whole pipeline at
    once: a failure in any one component breaks every test).

    The fixture is a single, recursive inductive

      [Inductive T0 := C0_0 of nat | C0_1 of nat & T0]

    which gives us one [NonRec]-only constructor branch, one branch
    mixing [NonRec] and [Rec], and one recursor type with a single
    motive — covering every instance of [infer_arity] /
    [infer_decl] / [read_rect].

    A separate (small) end-to-end test at the bottom checks
    [[indDef for T0_rect]] against the manually-spelled-out values
    of [n], [decl], etc. — so a regression in the [ind_def] Ltac driver
    is still caught, but not via the per-component tests. *)

From HB Require Import structures.
From mathcomp Require Import
  ssreflect ssrfun ssrbool ssrnat eqtype seq choice fintype.
Set SsrOldRewriteGoalsOrder.

From deriving Require Import base shape lift_class ind ind_class tactics infer.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Open Scope deriving_scope.

(** * Fixture *)

Inductive T0 := C0_0 of nat | C0_1 of nat & T0.

(** * [infer_arity] resolution

    Each branch shape exercises a different instance.  The
    universally-quantified [P] keeps the branchT abstract enough that
    only the [Hint Extern] for [infer_arity] (which pattern-matches on
    the [forall x, P j x -> _] / [forall x : S, _] / [P i x] shapes) can
    drive resolution. *)

(** ** [infer_arity_end]: terminal branch [P i x]. *)

Definition test_infer_arity_end
  (P : forall i : fin 1, (fun _ => T0) i -> Type) (x : T0) :
  infer_arity 1 (fun _ => T0) P
              (P None x)
              PolyType.nil
              None x := _.

(** ** [infer_arity_nonrec] then [infer_arity_end]: the C0_0 branch. *)

Definition test_infer_arity_C0_0
  (P : forall i : fin 1, (fun _ => T0) i -> Type) :
  infer_arity 1 (fun _ => T0) P
              (forall n : nat, P None (C0_0 n))
              (PolyType.cons (NonRec nat) PolyType.nil)
              None C0_0 := _.

(** ** [infer_arity_nonrec] then [infer_arity_rec]: the C0_1 branch. *)

Definition test_infer_arity_C0_1
  (P : forall i : fin 1, (fun _ => T0) i -> Type) :
  infer_arity 1 (fun _ => T0) P
              (forall (n : nat) (t : T0), P None t -> P None (C0_1 n t))
              (PolyType.cons (NonRec nat)
              (PolyType.cons (Rec (None : fin 1)) PolyType.nil))
              None C0_1 := _.

(** * [infer_decl] resolution

    [infer_decl_end] terminates at [hlist1 (fun i => forall x, P i x)].
    [infer_decl_cons] strips a [branchT -> _] and recurses on the tail. *)

(** ** [infer_decl_end]: empty recursor (no constructors). *)

Definition test_infer_decl_empty
  (P : forall i : fin 1, (fun _ => T0) i -> Type) :
  infer_decl 1 (fun _ => T0) P
             (hlist1 (fun i : fin 1 => forall x, P i x))
             empty_decl
             (Ind.empty_cons _) := _.

(** ** [infer_decl_cons] applied twice: the full T0 recursor. *)

Definition test_infer_decl_T0
  (P : forall i : fin 1, (fun _ => T0) i -> Type) :
  infer_decl 1 (fun _ => T0) P
    ((forall n : nat, P None (C0_0 n)) ->
     (forall (n : nat) (t : T0), P None t -> P None (C0_1 n t)) ->
     hlist1 (fun i : fin 1 => forall x, P i x))
    (add_arity (add_arity (@empty_decl 1) None
                          (PolyType.cons (NonRec nat)
                          (PolyType.cons (Rec (None : fin 1)) PolyType.nil)))
               None
               (PolyType.cons (NonRec nat) PolyType.nil))
    (Ind.add_cons (Ind.add_cons (Ind.empty_cons _)
                                (Ti := (None : fin 1))
                                (As := PolyType.cons (NonRec nat)
                                      (PolyType.cons (Rec (None : fin 1))
                                       PolyType.nil))
                                C0_1)
                  (Ti := (None : fin 1))
                  (As := PolyType.cons (NonRec nat) PolyType.nil)
                  C0_0) := _.

(** * [read_rect_done]: terminal case for [read_rect].

    Built by direct application of [read_rect_done] rather than [_]:
    the instance is non-polymorphic and keyed on the specific universe
    of [fnil Type] in [infer.v], which a fresh [Definition] in this
    file would not match.  [read_rect_type] (the inductive case) and
    [bless_rect] are not unit-tested here — they only resolve when
    paired with a concrete recursor whose [rectT] reduces to the
    expected [hfun2] form, i.e. essentially at integration with the
    [ind_def] Ltac driver, which is what the end-to-end test below
    exercises. *)

Definition test_read_rect_done (rectT : Type) (rect : rectT) :=
  @read_rect_done rectT rect.

(** * Integration: [[indDef for T0_rect]]

    A minimal end-to-end check that the [ind_def] Ltac driver, given
    the components above, produces an [indDef] whose [n] / [decl] /
    [Cons] match the manually-built ones from [unit_ind.v].  This is
    the *only* test in the file that exercises [[indDef for ...]]. *)

Definition T0_indDef_via_indDef := [indDef for T0_rect].

Lemma indDef_n_T0 : Ind.Def.n T0_indDef_via_indDef = 1.
Proof. by []. Qed.

Lemma indDef_decl_size_T0 :
  PolyType.size (Ind.Def.decl T0_indDef_via_indDef None) = 2.
Proof. by []. Qed.

Lemma indDef_C0_0_arity :
  PolyType.size
    (nth_fin (None : Ind.Cidx (Ind.Def.decl T0_indDef_via_indDef) None)) = 1.
Proof. by []. Qed.

Lemma indDef_C0_1_arity :
  PolyType.size
    (nth_fin (Some None : Ind.Cidx (Ind.Def.decl T0_indDef_via_indDef) None)) = 2.
Proof. by []. Qed.

Lemma indDef_Cons_C0_0 (n : nat) :
  Ind.Def.Cons T0_indDef_via_indDef
               (None : Ind.Cidx (Ind.Def.decl T0_indDef_via_indDef) None) n =
  C0_0 n.
Proof. by []. Qed.

Lemma indDef_Cons_C0_1 (n : nat) (t : T0) :
  Ind.Def.Cons T0_indDef_via_indDef
               (Some None
                  : Ind.Cidx (Ind.Def.decl T0_indDef_via_indDef) None) n t =
  C0_1 n t.
Proof. by []. Qed.

(** A mutual-block end-to-end check: [read_rect_type] must strip two
    motives, and the resulting decl has [n = 2]. *)

Inductive M0 := M0A | M0B of M1
with M1 := M1A of M0.

Scheme M0_rect_ := Induction for M0 Sort Type
with   M1_rect_ := Induction for M1 Sort Type.

Combined Scheme M01_rect from M0_rect_, M1_rect_.

Definition M01_indDef := [indDef for M01_rect].

Lemma indDef_n_M01 : Ind.Def.n M01_indDef = 2.
Proof. by []. Qed.

Lemma indDef_decl_size_M0 :
  PolyType.size (Ind.Def.decl M01_indDef None) = 2.
Proof. by []. Qed.

Lemma indDef_decl_size_M1 :
  PolyType.size (Ind.Def.decl M01_indDef (Some None)) = 1.
Proof. by []. Qed.
