From mathcomp Require Import
  ssreflect ssrfun ssrbool ssrnat eqtype seq choice fintype.

From void Require Import void.

From deriving Require Import base.

From Coq Require Import ZArith NArith String Ascii.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope deriving_scope.

(* The SSReflect definition is opaque, which interferes with certain reductions
   below. *)
Local Notation svalP := proj2_sig.

Record functor := Functor {
  fobj      :> Type -> Type;
  fmap      :  forall T S, (T -> S) -> (fobj T -> fobj S);
  fmap_eq   :  forall T S (f g : T -> S), f =1 g -> fmap f =1 fmap g;
  fmap1     :  forall T, fmap (@id T) =1 id;
  fmap_comp :  forall T S R (f : T -> S) (g : S -> R),
                 fmap (g \o f) =1 fmap g \o fmap f
}.

Module Ind.

Section ClassDef.

Record mixin_of T (F : functor) := Mixin {
  Roll     :  F T -> T;
  case     :  forall S, (F T -> S) -> T -> S;
  rec      :  forall S, (F (T * S)%type -> S) -> T -> S;
  _        :  forall S f a, rec f (Roll a) =
                            f (fmap (fun x => (x, rec f x)) a) :> S;
  _        :  forall S f a, case f (Roll a) = f a :> S;
  _        :  forall P,
                (forall (a : F {x & P x}), P (Roll (fmap tag a))) ->
                forall x, P x
}.
Notation class_of := mixin_of (only parsing).

Record type F := Pack {sort : Type; _ : class_of sort F}.
Local Coercion sort : type >-> Sortclass.
Variables (F : functor) (T : Type) (cT : type F).
Definition class := let: Pack _ c as cT' := cT return class_of cT' F in c.
Definition clone c of phant_id class c := @Pack F T c.
Let xT := let: Pack T _ := cT in T.
Notation xclass := (class : class_of xT).

Definition pack c := @Pack F T c.

End ClassDef.

Module Exports.
Coercion sort : type >-> Sortclass.
Notation indType := type.
Notation IndMixin := Mixin.
Notation IndType F T m := (@pack F T m).
Notation "[ 'indMixin' 'of' T ]" := (class _ : mixin_of T)
  (at level 0, format "[ 'indMixin'  'of'  T ]") : form_scope.
Notation "[ 'indType' 'of' T 'for' C ]" := (@clone T C _ idfun id)
  (at level 0, format "[ 'indType'  'of'  T  'for'  C ]") : form_scope.
Notation "[ 'indType' 'of' T ]" := (@clone T _ _ id id)
  (at level 0, format "[ 'indType'  'of'  T ]") : form_scope.
End Exports.

End Ind.
Export Ind.Exports.

Section IndTheory.

Variable F : functor.
Variable T : indType F.

Definition Roll := (Ind.Roll (Ind.class T)).
Definition case := (Ind.case (Ind.class T)).
Definition rec  := (Ind.rec  (Ind.class T)).

Lemma recE S f a : rec f (Roll a) =
                   f (fmap (fun x => (x, rec f x)) a) :> S.
Proof. by rewrite /Roll /rec; case: (T) f a=> [? []]. Qed.

Lemma caseE S f a : case f (Roll a) = f a :> S.
Proof. by rewrite /Roll /case; case: (T) f a=> [? []]. Qed.

Lemma indP P :
  (forall (a : F {x & P x}), P (Roll (fmap tag a))) ->
  forall x, P x.
Proof. by rewrite /Roll /rec; case: (T) P => [? []]. Qed.

Definition unroll := case id.

Lemma RollK : cancel Roll unroll.
Proof. by move=> x; rewrite /unroll caseE. Qed.

Lemma Roll_inj : injective Roll.
Proof. exact: can_inj RollK. Qed.

Lemma unrollK : cancel unroll Roll.
Proof. by elim/indP=> a; rewrite RollK. Qed.

Lemma unroll_inj : injective unroll.
Proof. exact: can_inj unrollK. Qed.

End IndTheory.

Variant arg := NonRec of Type | Rec.

Definition is_rec A := if A is Rec then true else false.

Definition arity := seq arg.
Definition signature := seq arity.

Identity Coercion seq_of_arity : arity >-> seq.
Identity Coercion seq_of_sig : signature >-> seq.

Section ClassLifting.

Variables (K : Type) (sort : K -> Type).

Definition arg_class A :=
  if A is NonRec T then {sT : K | sort sT = T} else unit.

Record arg_inst := ArgInst {
  arg_inst_sort  :> arg;
  arg_inst_class :  arg_class arg_inst_sort
}.
Arguments ArgInst : clear implicits.

Record arity_inst := ArityInst {
  arity_inst_sort  :> arity;
  arity_inst_class :  hlist arg_class arity_inst_sort;
}.
Arguments ArityInst : clear implicits.

Record sig_inst := SigInst {
  sig_inst_sort  :> signature;
  sig_inst_class :  hlist (hlist arg_class) sig_inst_sort;
}.
Arguments SigInst : clear implicits.

Implicit Types (A : arg) (As : arity) (Σ : signature).
Implicit Types (Ai : arg_inst) (Asi : arity_inst) (Σi : sig_inst).

Canonical NonRec_arg_inst T :=
  ArgInst (NonRec (sort T)) (exist _ T erefl).

Canonical Rec_arg_inst :=
  ArgInst Rec tt.

Canonical nth_fin_arg_inst Asi (i : fin (size Asi)) :=
  ArgInst (nth_fin i) (nth_hlist (arity_inst_class Asi) i).

Canonical nil_arity_inst :=
  ArityInst nil tt.

Canonical cons_arity_inst Ai Asi :=
  ArityInst (arg_inst_sort Ai :: arity_inst_sort Asi)
            (arg_inst_class Ai, arity_inst_class Asi).

Canonical nth_fin_arity_inst Σi (i : fin (size Σi)) :=
  ArityInst (nth_fin i) (nth_hlist (sig_inst_class Σi) i).

Canonical nil_sig_inst :=
  SigInst nil tt.

Canonical cons_sig_inst Asi Σi :=
  SigInst (arity_inst_sort Asi :: sig_inst_sort Σi)
          (arity_inst_class Asi, sig_inst_class Σi).

Definition arity_rec (T : arity -> Type)
  (Tnil    : T [::])
  (TNonRec : forall (S : K) (As : arity), T As -> T (NonRec (sort S) :: As))
  (TRec    : forall         (As : arity), T As -> T (Rec :: As)) :=
  fix arity_rec As : hlist arg_class As -> T As :=
    match As with
    | [::]               => fun cAs =>
      Tnil
    | NonRec Ssort :: As => fun cAs =>
      cast (fun Ssort => T (NonRec Ssort :: As)) (svalP cAs.1)
           (TNonRec (sval cAs.1) As (arity_rec As cAs.2))
    | Rec :: As          => fun cAs =>
      TRec As (arity_rec As cAs.2)
    end.

Lemma arity_ind (T : forall As, hlist arg_class As -> Type)
  (Tnil : T [::] tt)
  (TNonRec : forall S As cAs,
      T As cAs -> T (NonRec (sort S) :: As) (exist _ S erefl, cAs))
  (TRec : forall As cAs,
      T As cAs -> T (Rec :: As) (tt, cAs))
  As cAs : T As cAs.
Proof.
elim: As cAs=> [|[Ssort|] As IH] => /= [[]|[[S e] cAs]|[[] cAs]] //.
  by case: Ssort / e; apply: TNonRec.
by apply: TRec.
Qed.

End ClassLifting.

Arguments arity_rec {_} _ _ _ _ _.

Definition type_of_arg T (A : arg) : Type :=
  if A is NonRec T' then T' else T.

Definition type_of_arg_map T S (f : T -> S) A :
  type_of_arg T A -> type_of_arg S A :=
  if A is Rec then f else id.

Module CoqInd.

Section Basic.

Variable (T : Type).

Implicit Types (A : arg) (As : arity) (Σ : signature).

Definition constructors Σ :=
  hlist (fun As => hfun (type_of_arg T) As T) Σ.

Fixpoint branch S As : Type :=
  match As with
  | NonRec R :: As => R      -> branch S As
  | Rec      :: As => T -> S -> branch S As
  | [::]           => S
  end.

Definition recursor Σ := forall S, hfun (branch S) Σ (T -> S).

Fixpoint branch_of_hfun S As :
  hfun (type_of_arg (T * S)) As S -> branch S As :=
  match As with
  | NonRec R :: As => fun f x   => branch_of_hfun (f x)
  | Rec      :: As => fun f x y => branch_of_hfun (f (x, y))
  | [::]           => fun f     => f
  end.

Fixpoint hfun_of_branch S As :
  branch S As -> hfun (type_of_arg (T * S)) As S :=
  match As with
  | NonRec R :: As => fun f x => hfun_of_branch (f x)
  | Rec      :: As => fun f p => hfun_of_branch (f p.1 p.2)
  | [::]           => fun f   => f
  end.

Lemma branch_of_hfunK S As f xs :
  hfun_of_branch (@branch_of_hfun S As f) xs = f xs.
Proof. by elim: As f xs=> [|[R|] As IH] f //= [[x y] xs]. Qed.

Definition recursor_eq Σ (Cs : constructors Σ) (r : recursor Σ) :=
  forall S,
  all_hlist (fun bs : hlist (branch S) Σ =>
  all_fin   (fun i  : fin (size Σ) =>
  all_hlist (fun xs : hlist (type_of_arg T) (nth_fin i) =>
    r S bs (nth_hlist Cs i xs) =
    hfun_of_branch (nth_hlist bs i)
                   (hmap (type_of_arg_map (fun x => (x, r S bs x))) xs)))).

Definition destructor Σ :=
  forall S, hfun (fun As => hfun (type_of_arg T) As S) Σ (T -> S).

Definition destructor_eq s (cs : constructors s) (d : destructor s) :=
  forall S,
  all_hlist (fun bs : hlist (fun ks => hfun (type_of_arg T) ks S) s =>
  all_fin   (fun i  : fin (size s) =>
  all_hlist (fun xs : hlist (type_of_arg T) (nth_fin i) =>
    d S bs (nth_hlist cs i xs) = nth_hlist bs i xs))).

Definition destructor_of_recursor Σ (r : recursor Σ) : destructor Σ :=
  fun S => hcurry (
  fun bs : hlist (fun As => hfun (type_of_arg T) As S) Σ =>
    r S (hmap (fun As (b : hfun (type_of_arg T) As S) =>
           branch_of_hfun (hcurry (fun xs => b (hmap (type_of_arg_map fst) xs)))) bs)
).

Fixpoint ind_branch (P : T -> Type) As : hfun (type_of_arg T) As T -> Type :=
  match As with
  | NonRec R :: As => fun C => forall x : R,        ind_branch P (C x)
  | Rec      :: As => fun C => forall x : T, P x -> ind_branch P (C x)
  | [::]           => fun C => P C
  end.

Fixpoint ind_at (P : T -> Type) Σ : constructors Σ -> Type :=
  match Σ with
  | As :: Σ => fun Cs => ind_branch P Cs.1 -> ind_at P Cs.2
  | [::]    => fun Cs => forall x, P x
  end.

End Basic.

Section ClassDef.

Variables (Σ : signature).

Record mixin_of T := Mixin {
  Cons      : constructors T Σ;
  rec       : recursor T Σ;
  case      : destructor T Σ;
  _         : recursor_eq Cons rec;
  _         : destructor_eq Cons case;
  _         : forall P, ind_at P Cons;
}.

Record type := Pack {sort : Type; class : mixin_of sort}.
Variables (T : Type).
Definition recE (m : mixin_of T) : recursor_eq (Cons m) (rec m) :=
  let: Mixin _ _ _ recE _ _ := m in recE.
Definition caseE (m : mixin_of T) : destructor_eq (Cons m) (case m) :=
  let: Mixin _ _ _ _ caseE _ := m in caseE.
Definition indP (m : mixin_of T) :=
  let: Mixin _ _ _ _ _ indP := m
  return forall P : T -> Type, ind_at P (Cons m)
  in indP.

End ClassDef.

Module Exports.
Coercion sort : type >-> Sortclass.
Coercion class : type >-> mixin_of.
Notation coqIndType := type.
Notation CoqIndType s T m := (@Pack s T m).
Notation CoqIndMixin := Mixin.
End Exports.

End CoqInd.
Export CoqInd.Exports.

Class infer_arity
  T (P : T -> Type)
  (branchT : Type) (As : arity) (C : hfun (type_of_arg T) As T) : Type.
Arguments infer_arity : clear implicits.

Instance infer_arity_end
  T (P : T -> Type) (x : T) :
  infer_arity T P (P x) [::] x.

Instance infer_arity_rec
  T (P : T -> Type)
  (branchT : T -> Type) (As : arity) (C : T -> hfun (type_of_arg T) As T)
  (_ : forall x, infer_arity T P (branchT x) As (C x)) :
  infer_arity T P (forall x, P x -> branchT x) (Rec :: As) C.

Instance infer_arity_nonrec
  T (P : T -> Type)
  S (branchT : S -> Type) As (C : S -> hfun (type_of_arg T) As T)
  (_ : forall x, infer_arity T P (branchT x) As (C x)) :
  infer_arity T P (forall x, branchT x) (NonRec S :: As) C.

Class infer_sig
  T (P : T -> Type) (elimT : Type) Σ (Cs : CoqInd.constructors T Σ).
Arguments infer_sig : clear implicits.

Instance infer_sig_end T (P : T -> Type) :
  infer_sig T P (forall x : T, P x) [::] tt.

Instance infer_sig_branch
  T (P : T -> Type)
  (branchT : Type) As C (_ : infer_arity T P branchT As C)
  (elimT : Type) (Σ : signature) Cs (_ : infer_sig T P elimT Σ Cs) :
  infer_sig T P (branchT -> elimT) (As :: Σ) (C, Cs).

Ltac unwind_recursor rec :=
  match goal with
  | |- ?F -> ?G =>
    let X := fresh "X" in
    intros X; unwind_recursor (rec X)
  | |- _ => case; intros; apply rec
  end.

Ltac coq_ind_mixin rec :=
  match type of rec with
  | forall (P : ?T -> Type), @?elimT P =>
    let Rec  := eval compute in rec in
    let ΣCs  := constr:((fun Σ Cs (_ : forall P, infer_sig T P (elimT P) Σ Cs) => (Σ, Cs)) _ _ _) in
    let Σ    := eval simpl in ΣCs.1 in
    let Cs   := eval simpl in ΣCs.2 in
    let case := constr:(ltac:(intros P; simpl; unwind_recursor (Rec P)) : forall P, elimT P) in
    let case := eval compute in (@CoqInd.destructor_of_recursor T Σ (fun S => case (fun _ => S))) in
    refine (@CoqInd.Mixin Σ T Cs (fun S => Rec (fun _ => S)) case _ _ _);
    try by [abstract done|exact rec]
  end.

Notation "[ 'coqIndMixin' 'for' rect ]" :=
  (ltac:(coq_ind_mixin rect))
  (at level 0) : form_scope.

Module CoqIndFunctor.

Section TypeDef.

Import CoqInd.

Variables (Σ : signature).

Record type T := CoqInd {
  constr : fin (size Σ);
  args : hlist (type_of_arg T) (nth_fin constr)
}.

Arguments CoqInd {_} _ _.

Local Notation F := type.

Definition fmap T S (f : T -> S) (x : F T) : F S :=
  CoqInd (constr x) (hmap (type_of_arg_map f) (args x)).

Lemma fmap_eq T S (f g : T -> S) : f =1 g -> fmap f =1 fmap g.
Proof.
by move=> e [i args]; congr CoqInd; apply: hmap_eq; case.
Qed.

Lemma fmap1 T : @fmap T T id =1 id.
Proof.
move=> [i args] /=; congr CoqInd; rewrite -[RHS]hmap1.
by apply: hmap_eq; case.
Qed.

Lemma fmap_comp T S R (f : T -> S) (g : S -> R) :
  fmap (g \o f) =1 fmap g \o fmap f.
Proof.
move=> [i args] /=; congr CoqInd; rewrite /= hmap_comp.
by apply: hmap_eq; case.
Qed.

Canonical coqInd_functor := Functor fmap_eq fmap1 fmap_comp.

Lemma inj T (i : fin (size Σ)) (a b : hlist (type_of_arg T) (nth_fin i)) :
  CoqInd i a = CoqInd i b -> a = b.
Proof.
pose get x :=
  if leq_fin (constr x) i is inl e then
    cast (fun j : fin (size Σ) => hlist (type_of_arg T) (nth_fin j)) e (args x)
  else a.
by move=> /(congr1 get); rewrite /get /= leq_finii /=.
Qed.

Variable T : coqIndType Σ.

Definition Roll (x : F T) : T :=
  nth_hlist (@Cons _ _ T) (constr x) (args x).

Definition branches_of_fun S (body : F (T * S)%type -> S) :=
  hlist_of_fun (fun i =>
    branch_of_hfun
      (hcurry
         (fun l => body (CoqInd i l)))).

Definition rec S (body : F (T * S)%type -> S) :=
  happ (@CoqInd.rec _ _ T S) (branches_of_fun body).

Definition case S (body : F T -> S) :=
  happ (@CoqInd.case _ _ T S)
       (hlist_of_fun
          (fun i =>
             hcurry
               (fun l =>
                  body (CoqInd i l)))).

Lemma recE S f a : @rec S f (Roll a) =
                   f (fmap (fun x => (x, rec f x)) a).
Proof.
case: a=> [i args]; have := CoqInd.recE T S.
move/all_hlistP/(_ (branches_of_fun f)).
move/all_finP/(_ i).
move/all_hlistP/(_ args).
rewrite /rec /Roll => -> /=.
by rewrite /= nth_hlist_of_fun branch_of_hfunK hcurryK.
Qed.

Lemma caseE S f a : case f (Roll a) = f a :> S.
Proof.
case: a => [i args]; have := CoqInd.caseE T S.
move/all_hlistP.
move/(_ (hlist_of_fun (fun i => hcurry (fun l => f (CoqInd i l))))).
move/all_finP/(_ i).
move/all_hlistP/(_ args).
rewrite /case /Roll => -> /=.
by rewrite nth_hlist_of_fun hcurryK.
Qed.

Lemma indP P :
  (forall (a : F {x & P x}), P (Roll (fmap tag a))) ->
  forall x, P x.
Proof.
rewrite /Roll; case: (T) P => S [/= Cons _ _ _ _ indP] P.
have {indP} indP:
    (forall i, CoqInd.ind_branch P (nth_hlist Cons i)) ->
    (forall x, P x).
  elim: (Σ) Cons {indP} (indP P) => //= As Σ' IH [C Cs] /= indP hyps.
  move/indP/IH: (hyps None); apply=> i; exact: (hyps (Some i)).
move=> hyps; apply: indP=> j.
have {hyps} hyps:
  forall args : hlist (type_of_arg {x : S & P x}) (nth_fin j),
    P (nth_hlist Cons j (hmap (type_of_arg_map tag) args)).
  by move=> args; move: (hyps (CoqInd j args)).
elim: (nth_fin j) (nth_hlist Cons j) hyps=> [|[R|] As IH] //=.
- by move=> ? /(_ tt).
- move=> C hyps x; apply: IH=> args; exact: (hyps (x, args)).
- move=> constr hyps x H; apply: IH=> args.
  exact: (hyps (existT _ x H, args)).
Qed.

Canonical indType :=
  Eval hnf in IndType coqInd_functor T (IndMixin recE caseE indP).

End TypeDef.

End CoqIndFunctor.

Canonical CoqIndFunctor.coqInd_functor.
Canonical CoqIndFunctor.indType.
Coercion CoqIndFunctor.indType : coqIndType >-> indType.

Module IndEqType.

Local Notation arg_class := (arg_class Equality.sort).
Local Notation arg_inst := (arg_inst Equality.sort).
Local Notation arity_inst := (arity_inst Equality.sort).
Local Notation sig_inst := (sig_inst Equality.sort).

Section EqType.

Variable (Σ : sig_inst).
Let F := CoqIndFunctor.coqInd_functor Σ.
Variable (T : indType F).

Let eq_op_branch As (cAs : hlist arg_class As) :
  hlist (type_of_arg (T * (T -> bool))) As ->
  hlist (type_of_arg T)                 As ->
  bool :=
  arity_rec _ (fun As => hlist _ As -> hlist _ As -> bool)
    (fun _ _ => true)
    (fun R As rec x y => (x.1 == y.1) && rec x.2 y.2)
    (fun   As rec x y => x.1.2 y.1 && rec x.2 y.2) As cAs.

Let eq_op : T -> T -> bool :=
  rec  (fun args1 =>
  case (fun args2 =>
          match leq_fin (CoqIndFunctor.constr args2) (CoqIndFunctor.constr args1) with
          | inl e =>
            eq_op_branch
              (nth_hlist (sig_inst_class Σ) (CoqIndFunctor.constr args1))
              (CoqIndFunctor.args args1)
              (cast (hlist (type_of_arg T) \o @nth_fin _ _) e (CoqIndFunctor.args args2))
          | inr _ => false
          end)).

Lemma eq_opP : Equality.axiom eq_op.
Proof.
elim/indP=> [[xi xargs]] y.
rewrite /eq_op recE /= -[rec _]/(eq_op) /=.
rewrite -[y]unrollK caseE; move: {y} (unroll y)=> [yi yargs] /=.
case le: (leq_fin yi xi)=> [e|b]; last first.
  constructor=> /Roll_inj /= [] e _.
  by move: le; rewrite e leq_finii.
case: xi / e xargs {le} => /= xargs.
apply/(@iffP (hmap (type_of_arg_map tag) xargs = yargs)); first last.
- by move=> /Roll_inj /CoqIndFunctor.inj.
- by move=> <-.
elim/arity_ind: {yi} _ / (nth_hlist _ _) xargs yargs=> //=.
- by move=> _ []; constructor.
- move=> S As cAs IH [x xs] [y ys] /=.
  apply/(iffP andP)=> [[/eqP ? /IH ?]|[/eqP ? /IH]];
  intuition (eauto; congruence).
- move=> As cAs IH [[x xP] xs] [y ys] /=.
  apply/(iffP andP)=> [[/xP ? /IH ?]|[/xP ? /IH ?]];
  intuition (eauto; congruence).
Qed.

End EqType.

Record type (F : functor) := Pack {
  sort      : Type;
  eq_class  : Equality.class_of sort;
  ind_class : Ind.mixin_of sort F;
}.

Definition eqType F (T : type F) := Equality.Pack (eq_class T).
Definition indType F (T : type F) := Ind.Pack (ind_class T).

Definition pack :=
  fun (T : Type) =>
  fun Σ (sT : coqIndType Σ) & phant_id (CoqInd.sort sT) T =>
  fun (sΣ : sig_inst) & phant_id Σ (sig_inst_sort sΣ) =>
  fun (cT : CoqInd.mixin_of sΣ T) & phant_id (CoqInd.class sT) cT =>
    ltac:(
      let ax := constr:(@eq_opP sΣ (CoqInd.Pack cT)) in
      match type of ax with
      | Equality.axiom ?e =>
        let e' := eval compute -[eq_op Equality.sort andb] in e in
        exact: @EqMixin T e' ax
      end).

Module Import Exports.
Notation "[ 'indEqMixin' 'for' T ]" :=
  (let m := @pack T _ _ id _ id _ id in
   ltac:(
     let x := eval hnf in m in
     exact x))
  (at level 0, format "[ 'indEqMixin'  'for'  T ]") : form_scope.
Notation indEqType := type.
Coercion sort : type >-> Sortclass.
Coercion eqType : type >-> Equality.type.
Canonical eqType.
Coercion indType : type >-> Ind.type.
Canonical indType.
End Exports.

End IndEqType.

Export IndEqType.Exports.

Section TreeOfCoqInd.

Variables (Σ : signature).
Let F := CoqIndFunctor.coqInd_functor Σ.
Variables (T : indType F).

Import GenTree.

Definition coq_ind_arg := hsum (hsum (type_of_arg void)) Σ.

Definition mk_coq_ind_arg (i : fin (size Σ)) (j : fin (size (nth_fin i))) :
  type_of_arg void (nth_fin j) -> coq_ind_arg :=
  fun x => hin (hin x).

Definition proj_coq_ind_arg
  (i : fin (size Σ)) (j : fin (size (nth_fin i))) (x : coq_ind_arg) :
  option (type_of_arg void (nth_fin j)) :=
  hcase (fun i' =>
    if leq_fin i' i is inl e then
      match e^-1 in _ = i'
      return (hsum (fun k => type_of_arg void k) (nth_fin i') -> option _) with
      | erefl =>
        hcase (fun j' =>
          if leq_fin j' j is inl e then
            match e^-1 in _ = j'
            return (type_of_arg void (nth_fin j') -> option _)
            with
            | erefl => fun x => Some x
            end
          else fun _ => None)
      end
    else fun _ => None) x.

Lemma mk_coq_ind_argK i j : pcancel (@mk_coq_ind_arg i j) (@proj_coq_ind_arg i j).
Proof.
by move=> x; rewrite /proj_coq_ind_arg hcaseE leq_finii /= hcaseE leq_finii.
Qed.

Let wrap (i : fin (size Σ)) (j : fin (size (nth_fin i))) :
  type_of_arg (tree coq_ind_arg) (nth_fin j) -> tree coq_ind_arg :=
  match nth_fin j as k
  return (type_of_arg void k -> coq_ind_arg) ->
         type_of_arg (tree coq_ind_arg) k -> tree coq_ind_arg
  with
  | NonRec R => fun c x => Leaf (c x)
  | Rec     => fun c x => x
  end (@mk_coq_ind_arg i j).

Definition tree_of_coq_ind (x : T) : tree coq_ind_arg :=
  rec (fun x =>
         let i := CoqIndFunctor.constr x in
         Node (nat_of_fin i)
           (list_of_seq (seq_of_hlist_in (@wrap i)
              (hmap (type_of_arg_map snd) (CoqIndFunctor.args x))))) x.

Fixpoint coq_ind_of_tree (x : tree coq_ind_arg) : option T :=
  match x with
  | Leaf _ => None
  | Node c xs =>
    if fin_of_nat (size Σ) c is Some i then
      let xs := seq_of_list [seq (t, coq_ind_of_tree t) | t <- xs] in
      if hlist_of_seq_in (fun j ts =>
                            match nth_fin j as k
                                  return (coq_ind_arg -> option (type_of_arg void k)) ->
                                         option (type_of_arg T k) with
                            | NonRec R => fun f => if ts.1 is Leaf x then f x else None
                            | Rec => fun _ => ts.2
                            end (@proj_coq_ind_arg i j)) xs is Some args then
        Some (Roll (CoqIndFunctor.CoqInd args))
      else None
    else None
  end.

Lemma tree_of_coq_indK : pcancel tree_of_coq_ind coq_ind_of_tree.
Proof.
elim/indP=> [[i xs]].
rewrite /tree_of_coq_ind recE /= -[rec _]/(tree_of_coq_ind).
rewrite nat_of_finK !hmap_comp /=.
set xs' := hlist_of_seq_in _ _.
suffices -> : xs' = Some (hmap (type_of_arg_map tag) xs) by [].
rewrite {}/xs' seq_of_list_map list_of_seqK hlist_of_seq_in_map /= /wrap.
move: (@mk_coq_ind_arg i) (@proj_coq_ind_arg i) (@mk_coq_ind_argK i).
elim: {i} (nth_fin i) xs=> //= - [S|] As IH /= xs C p CK.
  by rewrite CK IH //= => j x; rewrite CK.
case: xs=> [[x xP] xs] /=; rewrite xP IH //.
by move=> j ?; rewrite CK.
Qed.

End TreeOfCoqInd.

Definition pack_tree_of_coq_indK :=
  fun (T : Type) =>
  fun Σ (sT_ind : coqIndType Σ) & phant_id (CoqInd.sort sT_ind) T =>
  @tree_of_coq_indK _ sT_ind.

Notation "[ 'indChoiceMixin' 'for' T ]" :=
  (PcanChoiceMixin (@pack_tree_of_coq_indK T _ _ id))
  (at level 0, format "[ 'indChoiceMixin'  'for'  T ]") : form_scope.

Notation "[ 'indCountMixin' 'for' T ]" :=
  (PcanCountMixin (@pack_tree_of_coq_indK T _ _ id))
  (at level 0, format "[ 'indCountMixin'  'for'  T ]") : form_scope.

Module IndFinType.

Section FinType.

Fixpoint allP T (P : pred T) (xs : seq T) : all P xs -> forall i : fin (size xs), P (nth_fin i) :=
  match xs with
  | [::] => fun H i => match i with end
  | x :: xs => match P x as b return (P x = b -> b && all P xs ->
                                      forall i : fin (size (x :: xs)), P (nth_fin i)) with
               | true => fun e H i => match i with
                                      | None => e
                                      | Some j => allP H j
                                      end
               | false => ltac:(done)
               end erefl
  end.

Variable (Σ : sig_inst Finite.sort).
Let F := CoqIndFunctor.coqInd_functor Σ.
Variable (T : indEqType F).

Hypothesis not_rec : all (all (negb \o is_rec)) Σ.

Definition enum_branch :=
  arity_rec
    _ (fun As => all (negb \o is_rec) As -> seq.seq (hlist (type_of_arg T) As))
    (fun _ => [:: tt]%SEQ)
    (fun S As rec P => allpairs pair (Finite.enum S) (rec P))
    (fun   As rec P => ltac:(done)).

Definition enum_ind :=
  flatten [seq [seq Roll (CoqIndFunctor.CoqInd args)
               | args <- enum_branch (nth_hlist (sig_inst_class Σ) i) (allP not_rec i)]
          | i <- list_of_seq (enum_fin (size Σ))].

Lemma enum_indP : Finite.axiom enum_ind.
Proof.
move=> x; rewrite -[x]unrollK; case: {x} (unroll x)=> i xs.
rewrite /enum_ind count_flatten -!map_comp /comp /=.
have <- : sumn [seq i == j : nat | j <- list_of_seq (enum_fin (size Σ))] = 1.
  elim: (size Σ) i {xs}=> [|n IH] //= [i|] /=.
    by rewrite list_of_seq_map -map_comp /comp /= -(IH i) add0n.
  rewrite list_of_seq_map -map_comp /comp /=; congr addn; apply/eqP/natnseq0P.
  by elim: (enum_fin n)=> {IH} // m ms /= <-.
congr sumn; apply/eq_map=> j /=; rewrite count_map.
have [<- {j}|ne] /= := altP (i =P j).
  set P := preim _ _.
  have PP : forall ys, reflect (xs = ys) (P ys).
    move=> ys; rewrite /P /=; apply/(iffP idP); last by move=> ->.
    by move=> /eqP/Roll_inj/CoqIndFunctor.inj ->.
  move: P PP.
  elim/arity_ind: {i} _ / (nth_hlist _ i) xs (allP _ _)=> //=.
    by move=> [] _ P /(_ tt); case.
  move=> S As cAs IH [x xs] As_not_rec P PP.
  elim: (Finite.enum S) (enumP x)=> //= y ys IHys.
  have [-> {y} [e]|ne] := altP (y =P x).
    rewrite count_cat count_map (IH xs); last first.
      move=> zs; apply/(iffP (PP (x, zs))); congruence.
    congr succn.
    elim: ys e {IHys} => //= y ys; case: (altP eqP) => //= ne H /H.
    rewrite count_cat => ->; rewrite addn0.
    elim: (enum_branch _ _)=> //= zs e ->; rewrite addn0.
    apply/eqP; rewrite eqb0; apply/negP=> /PP [] /esym/eqP.
    by rewrite (negbTE ne).
  rewrite count_cat; move=> /IHys ->; rewrite addn1; congr succn.
  elim: (enum_branch _ _) {IHys}=> //= zs e ->; rewrite addn0.
  apply/eqP; rewrite eqb0; apply/negP=> /PP [] /esym/eqP.
  by rewrite (negbTE ne).
set P := preim _ _.
rewrite (@eq_count _ _ pred0) ?count_pred0 //.
move=> ys /=; apply/negbTE; apply: contra ne.
by move=> /eqP/Roll_inj/(congr1 (@CoqIndFunctor.constr _ _)) /= ->.
Qed.

End FinType.

Definition pack :=
  fun (T : Type) =>
  fun (b : Countable.class_of T) bT & phant_id (Countable.class bT) b =>
  fun Σ (sT : coqIndType Σ) & phant_id (CoqInd.sort sT) T =>
  fun (sΣ : sig_inst Finite.sort) & phant_id Σ (sig_inst_sort sΣ) =>
  fun (cT : CoqInd.mixin_of sΣ T) & phant_id (CoqInd.class sT) cT =>
  fun (not_rec : all (all (negb \o is_rec)) sΣ) =>
    ltac:(
      let ax := constr:(@enum_indP sΣ (IndEqType.Pack b (Ind.class (CoqInd.Pack cT))) not_rec) in
      match type of ax with
      | Finite.axiom ?e =>
        let e' := (eval compute -[Finite.sort Equality.sort allpairs cat map] in e) in
        exact (@FinMixin (Countable.Pack b) e' ax)
      end).

Module Import Exports.
Notation "[ 'indFinMixin' 'for' T ]" :=
  (let m := @pack T _ _ id _ _ id _ id _ id erefl in
   ltac:(
     let x := eval hnf in m in
     exact x))
  (at level 0, format "[ 'indFinMixin'  'for'  T ]") : form_scope.
End Exports.

End IndFinType.
Export IndFinType.Exports.

Section Instances.

Variables (T T1 T2 : Type).

Definition unit_coqIndMixin :=
  Eval simpl in [coqIndMixin for unit_rect].
Canonical unit_coqIndType :=
  Eval hnf in CoqIndType _ unit unit_coqIndMixin.

Definition void_coqIndMixin :=
  Eval simpl in [coqIndMixin for Empty_set_rect].
Canonical void_coqIndType :=
  Eval hnf in CoqIndType _ void void_coqIndMixin.

Definition bool_coqIndMixin :=
  Eval simpl in [coqIndMixin for bool_rect].
Canonical bool_coqIndType :=
  Eval hnf in CoqIndType _ bool bool_coqIndMixin.

Definition nat_coqIndMixin :=
  Eval simpl in [coqIndMixin for nat_rect].
Canonical nat_coqIndType :=
  Eval hnf in CoqIndType _ nat nat_coqIndMixin.

Definition option_coqIndMixin :=
  Eval simpl in [coqIndMixin for @option_rect T].
Canonical option_coqIndType :=
  Eval hnf in CoqIndType _ (option T) option_coqIndMixin.

Definition sum_coqIndMixin :=
  Eval simpl in [coqIndMixin for @sum_rect T1 T2].
Canonical sum_coqIndType :=
  Eval hnf in CoqIndType _ _ sum_coqIndMixin.

Definition prod_coqIndMixin :=
  Eval simpl in [coqIndMixin for @prod_rect T1 T2].
Canonical prod_coqIndType :=
  Eval hnf in CoqIndType _ _ prod_coqIndMixin.

Definition seq_coqIndMixin :=
  Eval simpl in [coqIndMixin for @list_rect T].
Canonical seq_coqIndType :=
  Eval hnf in CoqIndType _ _ seq_coqIndMixin.

Definition comparison_coqIndMixin :=
  Eval simpl in [coqIndMixin for comparison_rect].
Canonical comparison_coqIndType :=
  Eval hnf in CoqIndType _ comparison comparison_coqIndMixin.
Definition comparison_eqMixin :=
  Eval simpl in [indEqMixin for comparison].
Canonical comparison_eqType :=
  Eval hnf in EqType comparison comparison_eqMixin.
Definition comparison_choiceMixin :=
  Eval simpl in [indChoiceMixin for comparison].
Canonical comparison_choiceType :=
  Eval hnf in ChoiceType comparison comparison_choiceMixin.
Definition comparison_countMixin :=
  Eval simpl in [indCountMixin for comparison].
Canonical comparison_countType :=
  Eval hnf in CountType comparison comparison_countMixin.
Definition comparison_finMixin :=
  Eval simpl in [indFinMixin for comparison].
Canonical comparison_finType :=
  Eval hnf in FinType comparison comparison_finMixin.

Definition positive_coqIndMixin :=
  Eval simpl in [coqIndMixin for positive_rect].
Canonical positive_coqIndType :=
  Eval hnf in CoqIndType _ positive positive_coqIndMixin.
Definition positive_eqMixin :=
  Eval simpl in [indEqMixin for positive].
Canonical positive_eqType :=
  Eval hnf in EqType positive positive_eqMixin.
Definition positive_choiceMixin :=
  Eval simpl in [indChoiceMixin for positive].
Canonical positive_choiceType :=
  Eval hnf in ChoiceType positive positive_choiceMixin.
Definition positive_countMixin :=
  Eval simpl in [indCountMixin for positive].
Canonical positive_countType :=
  Eval hnf in CountType positive positive_countMixin.

Definition bin_nat_coqIndMixin :=
  Eval simpl in [coqIndMixin for N_rect].
Canonical bin_nat_coqIndType :=
  Eval hnf in CoqIndType _ N bin_nat_coqIndMixin.
Definition bin_nat_choiceMixin :=
  Eval simpl in [indChoiceMixin for N].
Canonical bin_nat_choiceType :=
  Eval hnf in ChoiceType N bin_nat_choiceMixin.
Definition bin_nat_countMixin :=
  Eval simpl in [indCountMixin for N].
Canonical bin_nat_countType :=
  Eval hnf in CountType N bin_nat_countMixin.

Definition Z_coqIndMixin :=
  Eval simpl in [coqIndMixin for Z_rect].
Canonical Z_coqIndType :=
  Eval hnf in CoqIndType _ Z Z_coqIndMixin.
Definition Z_eqMixin :=
  Eval simpl in [indEqMixin for Z].
Canonical Z_eqType :=
  Eval hnf in EqType Z Z_eqMixin.
Definition Z_choiceMixin :=
  Eval simpl in [indChoiceMixin for Z].
Canonical Z_choiceType :=
  Eval hnf in ChoiceType Z Z_choiceMixin.
Definition Z_countMixin :=
  Eval simpl in [indCountMixin for Z].
Canonical Z_countType :=
  Eval hnf in CountType Z Z_countMixin.

Definition ascii_coqIndMixin :=
  Eval simpl in [coqIndMixin for ascii_rect].
Canonical ascii_coqIndType :=
  Eval hnf in CoqIndType _ ascii ascii_coqIndMixin.
Definition ascii_eqMixin :=
  Eval simpl in [indEqMixin for ascii].
Canonical ascii_eqType :=
  Eval hnf in EqType ascii ascii_eqMixin.
Definition ascii_choiceMixin :=
  Eval simpl in [indChoiceMixin for ascii].
Canonical ascii_choiceType :=
  Eval hnf in ChoiceType ascii ascii_choiceMixin.
Definition ascii_countMixin :=
  Eval simpl in [indCountMixin for ascii].
Canonical ascii_countType :=
  Eval hnf in CountType ascii ascii_countMixin.
Definition ascii_finMixin :=
  Eval simpl in [indFinMixin for ascii].
Canonical ascii_finType :=
  Eval hnf in FinType ascii ascii_finMixin.

Definition string_coqIndMixin :=
  Eval simpl in [coqIndMixin for string_rect].
Canonical string_coqIndType :=
  Eval hnf in CoqIndType _ string string_coqIndMixin.
Definition string_eqMixin :=
  Eval simpl in [indEqMixin for string].
Canonical string_eqType :=
  Eval hnf in EqType string string_eqMixin.
Definition string_choiceMixin :=
  Eval simpl in [indChoiceMixin for string].
Canonical string_choiceType :=
  Eval hnf in ChoiceType string string_choiceMixin.
Definition string_countMixin :=
  Eval simpl in [indCountMixin for string].
Canonical string_countType :=
  Eval hnf in CountType string string_countMixin.

End Instances.
