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

Module InitAlg.

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
Notation initAlgType := type.
Notation InitAlgMixin := Mixin.
Notation InitAlgType F T m := (@pack F T m).
Notation "[ 'initAlgMixin' 'of' T ]" := (class _ : mixin_of T)
  (at level 0, format "[ 'initAlgMixin'  'of'  T ]") : form_scope.
Notation "[ 'initAlgType' 'of' T 'for' C ]" := (@clone T C _ idfun id)
  (at level 0, format "[ 'initAlgType'  'of'  T  'for'  C ]") : form_scope.
Notation "[ 'initAlgType' 'of' T ]" := (@clone T _ _ id id)
  (at level 0, format "[ 'initAlgType'  'of'  T ]") : form_scope.
End Exports.

End InitAlg.
Export InitAlg.Exports.

Section InitAlgTheory.

Variable F : functor.
Variable T : initAlgType F.

Definition Roll := (InitAlg.Roll (InitAlg.class T)).
Definition case := (InitAlg.case (InitAlg.class T)).
Definition rec  := (InitAlg.rec  (InitAlg.class T)).

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

End InitAlgTheory.

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

Module Ind.

Section Basic.

Implicit Types (A : arg) (As : arity) (Σ : signature) (T S : Type).

Definition constructors Σ T :=
  hlist (fun As => hfun (type_of_arg T) As T) Σ.

Fixpoint branch T S As : Type :=
  match As with
  | NonRec R :: As => R      -> branch T S As
  | Rec      :: As => T -> S -> branch T S As
  | [::]           => S
  end.

Definition recursor Σ T := forall S, hfun (branch T S) Σ (T -> S).

Fixpoint branch_of_hfun T S As :
  hfun (type_of_arg (T * S)) As S -> branch T S As :=
  match As with
  | NonRec R :: As => fun f x   => branch_of_hfun (f x)
  | Rec      :: As => fun f x y => branch_of_hfun (f (x, y))
  | [::]           => fun f     => f
  end.

Fixpoint hfun_of_branch T S As :
  branch T S As -> hfun (type_of_arg (T * S)) As S :=
  match As with
  | NonRec R :: As => fun f x => hfun_of_branch (f x)
  | Rec      :: As => fun f p => hfun_of_branch (f p.1 p.2)
  | [::]           => fun f   => f
  end.

Lemma branch_of_hfunK T S As f xs :
  hfun_of_branch (@branch_of_hfun T S As f) xs = f xs.
Proof. by elim: As f xs=> [|[R|] As IH] f //= [[x y] xs]. Qed.

Definition recursor_eq Σ T (Cs : constructors Σ T) (r : recursor Σ T) :=
  forall S,
  all_hlist (fun bs : hlist (branch T S) Σ =>
  all_fin   (fun i  : fin (size Σ) =>
  all_hlist (fun xs : hlist (type_of_arg T) (nth_fin i) =>
    r S bs (nth_hlist Cs i xs) =
    hfun_of_branch (nth_hlist bs i)
                   (hmap (type_of_arg_map (fun x => (x, r S bs x))) xs)))).

Definition destructor Σ T :=
  forall S, hfun (fun As => hfun (type_of_arg T) As S) Σ (T -> S).

Definition destructor_eq Σ T (Cs : constructors Σ T) (d : destructor Σ T) :=
  forall S,
  all_hlist (fun bs : hlist (fun ks => hfun (type_of_arg T) ks S) Σ =>
  all_fin   (fun i  : fin (size Σ) =>
  all_hlist (fun xs : hlist (type_of_arg T) (nth_fin i) =>
    d S bs (nth_hlist Cs i xs) = nth_hlist bs i xs))).

Definition destructor_of_recursor Σ T (r : recursor Σ T) : destructor Σ T :=
  fun S => hcurry (
  fun bs : hlist (fun As => hfun (type_of_arg T) As S) Σ =>
    r S (hmap (fun As (b : hfun (type_of_arg T) As S) =>
           branch_of_hfun
             (hcurry (fun xs => b (hmap (type_of_arg_map fst) xs)))) bs)
).

Fixpoint ind_branch T (P : T -> Type) As : hfun (type_of_arg T) As T -> Type :=
  match As with
  | NonRec R :: As => fun C => forall x : R,        ind_branch P (C x)
  | Rec      :: As => fun C => forall x : T, P x -> ind_branch P (C x)
  | [::]           => fun C => P C
  end.

Fixpoint induction T (P : T -> Type) Σ : constructors Σ T -> Type :=
  match Σ with
  | As :: Σ => fun Cs => ind_branch P Cs.1 -> induction P Cs.2
  | [::]    => fun Cs => forall x, P x
  end.

End Basic.

Section ClassDef.

Variables (Σ : signature).

Record mixin_of T := Mixin {
  Cons      : constructors Σ T;
  rec       : recursor Σ T;
  case      : destructor Σ T;
  _         : recursor_eq Cons rec;
  _         : destructor_eq Cons case;
  _         : forall P, induction P Cons;
}.

Record type := Pack {sort : Type; class : mixin_of sort}.
Variables (T : Type).
Definition recE (m : mixin_of T) : recursor_eq (Cons m) (rec m) :=
  let: Mixin _ _ _ recE _ _ := m in recE.
Definition caseE (m : mixin_of T) : destructor_eq (Cons m) (case m) :=
  let: Mixin _ _ _ _ caseE _ := m in caseE.
Definition indP (m : mixin_of T) :=
  let: Mixin _ _ _ _ _ indP := m
  return forall P : T -> Type, induction P (Cons m)
  in indP.

End ClassDef.

Module Exports.
Coercion sort : type >-> Sortclass.
Coercion class : type >-> mixin_of.
Notation indType := type.
Notation IndType Σ T m := (@Pack Σ T m).
Notation IndMixin := Mixin.
End Exports.

End Ind.
Export Ind.Exports.

Class infer_arity
  T (P : T -> Type)
  (branchT : Type) (As : arity) (C : hfun (type_of_arg T) As T) : Type.
Arguments infer_arity : clear implicits.

Instance infer_arity_end
  T (P : T -> Type) (x : T) :
  infer_arity T P (P x) [::] x.
Defined.

Instance infer_arity_rec
  T (P : T -> Type)
  (branchT : T -> Type) (As : arity) (C : T -> hfun (type_of_arg T) As T)
  (_ : forall x, infer_arity T P (branchT x) As (C x)) :
  infer_arity T P (forall x, P x -> branchT x) (Rec :: As) C.
Defined.

Instance infer_arity_nonrec
  T (P : T -> Type)
  S (branchT : S -> Type) As (C : S -> hfun (type_of_arg T) As T)
  (_ : forall x, infer_arity T P (branchT x) As (C x)) :
  infer_arity T P (forall x, branchT x) (NonRec S :: As) C.
Defined.

Class infer_sig
  T (P : T -> Type) (elimT : Type) Σ (Cs : Ind.constructors Σ T).
Arguments infer_sig : clear implicits.

Instance infer_sig_end T (P : T -> Type) :
  infer_sig T P (forall x : T, P x) [::] tt.
Defined.

Instance infer_sig_branch
  T (P : T -> Type)
  (branchT : Type) As C (_ : infer_arity T P branchT As C)
  (elimT : Type) (Σ : signature) Cs (_ : infer_sig T P elimT Σ Cs) :
  infer_sig T P (branchT -> elimT) (As :: Σ) (C, Cs).
Defined.

Ltac unwind_recursor rec :=
  match goal with
  | |- ?F -> ?G =>
    let X := fresh "X" in
    intros X; unwind_recursor (rec X)
  | |- _ => case; intros; apply rec
  end.

Ltac ind_mixin rec :=
  match type of rec with
  | forall (P : ?T -> Type), @?elimT P =>
    let Rec  := eval compute in rec in
    let ΣCs  := constr:((fun Σ Cs (_ : forall P, infer_sig T P (elimT P) Σ Cs) => (Σ, Cs)) _ _ _) in
    let Σ    := eval simpl in ΣCs.1 in
    let Cs   := eval simpl in ΣCs.2 in
    let case := constr:(ltac:(intros P; simpl; unwind_recursor (Rec P)) : forall P, elimT P) in
    let case := eval compute in (@Ind.destructor_of_recursor Σ T (fun S => case (fun _ => S))) in
    refine (@IndMixin Σ T Cs (fun S => Rec (fun _ => S)) case _ _ _);
    try by [abstract done|exact rec]
  end.

Notation "[ 'indMixin' 'for' rect ]" :=
  (ltac:(ind_mixin rect))
  (at level 0) : form_scope.

Module IndF.

Section TypeDef.

Variables (Σ : signature).

Record fobj T := Cons {
  constr : fin (size Σ);
  args : hlist (type_of_arg T) (nth_fin constr)
}.

Arguments Cons {_} _ _.

Local Notation F := fobj.

Definition fmap T S (f : T -> S) (x : F T) : F S :=
  Cons (constr x) (hmap (type_of_arg_map f) (args x)).

Lemma fmap_eq T S (f g : T -> S) : f =1 g -> fmap f =1 fmap g.
Proof.
by move=> e [i args]; congr Cons; apply: hmap_eq; case.
Qed.

Lemma fmap1 T : @fmap T T id =1 id.
Proof.
move=> [i args] /=; congr Cons; rewrite -[RHS]hmap1.
by apply: hmap_eq; case.
Qed.

Lemma fmap_comp T S R (f : T -> S) (g : S -> R) :
  fmap (g \o f) =1 fmap g \o fmap f.
Proof.
move=> [i args] /=; congr Cons; rewrite /= hmap_comp.
by apply: hmap_eq; case.
Qed.

Canonical functor := Functor fmap_eq fmap1 fmap_comp.

Lemma inj T (i : fin (size Σ)) (a b : hlist (type_of_arg T) (nth_fin i)) :
  Cons i a = Cons i b -> a = b.
Proof.
pose get x :=
  if leq_fin (constr x) i is inl e then
    cast (fun j : fin (size Σ) => hlist (type_of_arg T) (nth_fin j)) e (args x)
  else a.
by move=> /(congr1 get); rewrite /get /= leq_finii /=.
Qed.

Variable T : indType Σ.

Definition Roll (x : F T) : T :=
  nth_hlist (@Ind.Cons _ _ T) (constr x) (args x).

Definition branches_of_fun S (body : F (T * S)%type -> S) :=
  hlist_of_fun (fun i =>
    Ind.branch_of_hfun
      (hcurry
         (fun l => body (Cons i l)))).

Definition rec S (body : F (T * S)%type -> S) :=
  happ (@Ind.rec _ _ T S) (branches_of_fun body).

Definition case S (body : F T -> S) :=
  @Ind.case _ _ T S
     (hlist_of_fun
        (fun i =>
           hcurry
             (fun l => body (Cons i l)))).

Lemma recE S f a : @rec S f (Roll a) =
                   f (fmap (fun x => (x, rec f x)) a).
Proof.
case: a=> [i args]; have := Ind.recE T S.
move/all_hlistP/(_ (branches_of_fun f)).
move/all_finP/(_ i).
move/all_hlistP/(_ args).
rewrite /rec /Roll => -> /=.
by rewrite /= nth_hlist_of_fun Ind.branch_of_hfunK hcurryK.
Qed.

Lemma caseE S f a : case f (Roll a) = f a :> S.
Proof.
case: a => [i args]; have := Ind.caseE T S.
move/all_hlistP.
move/(_ (hlist_of_fun (fun i => hcurry (fun l => f (Cons i l))))).
move/all_finP/(_ i).
move/all_hlistP/(_ args).
rewrite /case /Roll => -> /=.
by rewrite nth_hlist_of_fun hcurryK.
Qed.

Lemma indP P :
  (forall (a : F {x & P x}), P (Roll (fmap tag a))) ->
  forall x, P x.
Proof.
rewrite /Roll; case: (T) P => S [/= Cs _ _ _ _ indP] P.
have {indP} indP:
    (forall i, Ind.ind_branch P (nth_hlist Cs i)) ->
    (forall x, P x).
  elim: (Σ) Cs {indP} (indP P) => //= As Σ' IH [C Cs] /= indP hyps.
  move/indP/IH: (hyps None); apply=> i; exact: (hyps (Some i)).
move=> hyps; apply: indP=> j.
have {hyps} hyps:
  forall args : hlist (type_of_arg {x : S & P x}) (nth_fin j),
    P (nth_hlist Cs j (hmap (type_of_arg_map tag) args)).
  by move=> args; move: (hyps (Cons j args)).
elim: (nth_fin j) (nth_hlist Cs j) hyps=> [|[R|] As IH] //=.
- by move=> ? /(_ tt).
- move=> C hyps x; apply: IH=> args; exact: (hyps (x, args)).
- move=> constr hyps x H; apply: IH=> args.
  exact: (hyps (existT _ x H, args)).
Qed.

Canonical initAlgType :=
  Eval hnf in InitAlgType functor T (InitAlgMixin recE caseE indP).

End TypeDef.

End IndF.

Canonical IndF.functor.
Canonical IndF.initAlgType.
Coercion IndF.initAlgType : indType >-> initAlgType.

Module IndEqType.

Local Notation arg_class := (arg_class Equality.sort).
Local Notation arg_inst := (arg_inst Equality.sort).
Local Notation arity_inst := (arity_inst Equality.sort).
Local Notation sig_inst := (sig_inst Equality.sort).

Section EqType.

Variable (Σ : sig_inst).
Let F := IndF.functor Σ.
Variable (T : initAlgType F).

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
          match leq_fin (IndF.constr args2) (IndF.constr args1) with
          | inl e =>
            eq_op_branch
              (nth_hlist (sig_inst_class Σ) (IndF.constr args1))
              (IndF.args args1)
              (cast (hlist (type_of_arg T) \o @nth_fin _ _) e (IndF.args args2))
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
- by move=> /Roll_inj /IndF.inj.
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
  sort           : Type;
  eq_class       : Equality.class_of sort;
  init_alg_class : InitAlg.mixin_of sort F;
}.

Definition eqType F (T : type F) := Equality.Pack (eq_class T).
Definition initAlgType F (T : type F) := InitAlg.Pack (init_alg_class T).

Definition pack :=
  fun (T : Type) =>
  fun Σ (sT : indType Σ) & phant_id (Ind.sort sT) T =>
  fun (sΣ : sig_inst) & phant_id Σ (sig_inst_sort sΣ) =>
  fun (cT : Ind.mixin_of sΣ T) & phant_id (Ind.class sT) cT =>
    ltac:(
      let ax := constr:(@eq_opP sΣ (Ind.Pack cT)) in
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
Notation initAlgEqType := type.
Notation InitAlgEqType := Pack.
Coercion sort : type >-> Sortclass.
Coercion eqType : type >-> Equality.type.
Canonical eqType.
Coercion initAlgType : type >-> InitAlg.type.
Canonical initAlgType.
End Exports.

End IndEqType.

Export IndEqType.Exports.

Section TreeOfInd.

Variables (Σ : signature).
Let F := IndF.functor Σ.
Variables (T : initAlgType F).

Import GenTree.

Definition ind_arg := hsum (hsum (type_of_arg void)) Σ.

Definition mk_ind_arg (i : fin (size Σ)) (j : fin (size (nth_fin i))) :
  type_of_arg void (nth_fin j) -> ind_arg :=
  fun x => hin (hin x).

Definition proj_ind_arg
  (i : fin (size Σ)) (j : fin (size (nth_fin i))) (x : ind_arg) :
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

Lemma mk_ind_argK i j : pcancel (@mk_ind_arg i j) (@proj_ind_arg i j).
Proof.
by move=> x; rewrite /proj_ind_arg hcaseE leq_finii /= hcaseE leq_finii.
Qed.

Let wrap (i : fin (size Σ)) (j : fin (size (nth_fin i))) :
  type_of_arg (tree ind_arg) (nth_fin j) -> tree ind_arg :=
  match nth_fin j as k
  return (type_of_arg void k -> ind_arg) ->
         type_of_arg (tree ind_arg) k -> tree ind_arg
  with
  | NonRec R => fun c x => Leaf (c x)
  | Rec     => fun c x => x
  end (@mk_ind_arg i j).

Definition tree_of_coq_ind (x : T) : tree ind_arg :=
  rec (fun x =>
         let i := IndF.constr x in
         Node (nat_of_fin i)
           (list_of_seq (seq_of_hlist_in (@wrap i)
              (hmap (type_of_arg_map snd) (IndF.args x))))) x.

Fixpoint coq_ind_of_tree (x : tree ind_arg) : option T :=
  match x with
  | Leaf _ => None
  | Node c xs =>
    if fin_of_nat (size Σ) c is Some i then
      let xs := seq_of_list [seq (t, coq_ind_of_tree t) | t <- xs] in
      if hlist_of_seq_in (fun j ts =>
                            match nth_fin j as k
                                  return (ind_arg -> option (type_of_arg void k)) ->
                                         option (type_of_arg T k) with
                            | NonRec R => fun f => if ts.1 is Leaf x then f x else None
                            | Rec => fun _ => ts.2
                            end (@proj_ind_arg i j)) xs is Some args then
        Some (Roll (IndF.Cons args))
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
move: (@mk_ind_arg i) (@proj_ind_arg i) (@mk_ind_argK i).
elim: {i} (nth_fin i) xs=> //= - [S|] As IH /= xs C p CK.
  by rewrite CK IH //= => j x; rewrite CK.
case: xs=> [[x xP] xs] /=; rewrite xP IH //.
by move=> j ?; rewrite CK.
Qed.

End TreeOfInd.

Definition pack_tree_of_indK :=
  fun (T : Type) =>
  fun Σ (sT_ind : indType Σ) & phant_id (Ind.sort sT_ind) T =>
  @tree_of_coq_indK _ sT_ind.

Notation "[ 'indChoiceMixin' 'for' T ]" :=
  (PcanChoiceMixin (@pack_tree_of_indK T _ _ id))
  (at level 0, format "[ 'indChoiceMixin'  'for'  T ]") : form_scope.

Notation "[ 'indCountMixin' 'for' T ]" :=
  (PcanCountMixin (@pack_tree_of_indK T _ _ id))
  (at level 0, format "[ 'indCountMixin'  'for'  T ]") : form_scope.

Module IndFinType.

Section FinType.

Fixpoint allP T (P : pred T) (xs : seq T) :
  all P xs -> forall i : fin (size xs), P (nth_fin i) :=
  match xs with
  | [::] =>
    fun H i => match i with end
  | x :: xs =>
    match P x as b
    return (P x = b -> b && all P xs ->
            forall i : fin (size (x :: xs)), P (nth_fin i))
    with
    | true => fun e H i => match i with
                           | None => e
                           | Some j => allP H j
                           end
    | false => ltac:(done)
    end erefl
  end.

Variable (Σ : sig_inst Finite.sort).
Let F := IndF.functor Σ.
Variable (T : initAlgEqType F).

Hypothesis not_rec : all (all (negb \o is_rec)) Σ.

Definition enum_branch :=
  arity_rec
    _ (fun As => all (negb \o is_rec) As -> seq.seq (hlist (type_of_arg T) As))
    (fun _ => [:: tt]%SEQ)
    (fun S As rec P => allpairs pair (Finite.enum S) (rec P))
    (fun   As rec P => ltac:(done)).

Definition enum_ind :=
  flatten [seq [seq Roll (IndF.Cons args)
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
    by move=> /eqP/Roll_inj/IndF.inj ->.
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
by move=> /eqP/Roll_inj/(congr1 (@IndF.constr _ _)) /= ->.
Qed.

End FinType.

Definition pack :=
  fun (T : Type) =>
  fun (b : Countable.class_of T) bT & phant_id (Countable.class bT) b =>
  fun Σ (sT : indType Σ) & phant_id (Ind.sort sT) T =>
  fun (sΣ : sig_inst Finite.sort) & phant_id Σ (sig_inst_sort sΣ) =>
  fun (cT : Ind.mixin_of sΣ T) & phant_id (Ind.class sT) cT =>
  fun (not_rec : all (all (negb \o is_rec)) sΣ) =>
    ltac:(
      let ax := constr:(@enum_indP sΣ (InitAlgEqType b (InitAlg.class (Ind.Pack cT))) not_rec) in
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

Definition unit_indMixin :=
  Eval simpl in [indMixin for unit_rect].
Canonical unit_indType :=
  Eval hnf in IndType _ unit unit_indMixin.

Definition void_indMixin :=
  Eval simpl in [indMixin for Empty_set_rect].
Canonical void_indType :=
  Eval hnf in IndType _ void void_indMixin.

Definition bool_indMixin :=
  Eval simpl in [indMixin for bool_rect].
Canonical bool_indType :=
  Eval hnf in IndType _ bool bool_indMixin.

Definition nat_indMixin :=
  Eval simpl in [indMixin for nat_rect].
Canonical nat_indType :=
  Eval hnf in IndType _ nat nat_indMixin.

Definition option_indMixin :=
  Eval simpl in [indMixin for @option_rect T].
Canonical option_indType :=
  Eval hnf in IndType _ (option T) option_indMixin.

Definition sum_indMixin :=
  Eval simpl in [indMixin for @sum_rect T1 T2].
Canonical sum_indType :=
  Eval hnf in IndType _ _ sum_indMixin.

Definition prod_indMixin :=
  Eval simpl in [indMixin for @prod_rect T1 T2].
Canonical prod_indType :=
  Eval hnf in IndType _ _ prod_indMixin.

Definition seq_indMixin :=
  Eval simpl in [indMixin for @list_rect T].
Canonical seq_indType :=
  Eval hnf in IndType _ _ seq_indMixin.

Definition comparison_indMixin :=
  Eval simpl in [indMixin for comparison_rect].
Canonical comparison_indType :=
  Eval hnf in IndType _ comparison comparison_indMixin.
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

Definition positive_indMixin :=
  Eval simpl in [indMixin for positive_rect].
Canonical positive_indType :=
  Eval hnf in IndType _ positive positive_indMixin.
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

Definition bin_nat_indMixin :=
  Eval simpl in [indMixin for N_rect].
Canonical bin_nat_indType :=
  Eval hnf in IndType _ N bin_nat_indMixin.
Definition bin_nat_choiceMixin :=
  Eval simpl in [indChoiceMixin for N].
Canonical bin_nat_choiceType :=
  Eval hnf in ChoiceType N bin_nat_choiceMixin.
Definition bin_nat_countMixin :=
  Eval simpl in [indCountMixin for N].
Canonical bin_nat_countType :=
  Eval hnf in CountType N bin_nat_countMixin.

Definition Z_indMixin :=
  Eval simpl in [indMixin for Z_rect].
Canonical Z_indType :=
  Eval hnf in IndType _ Z Z_indMixin.
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

Definition ascii_indMixin :=
  Eval simpl in [indMixin for ascii_rect].
Canonical ascii_indType :=
  Eval hnf in IndType _ ascii ascii_indMixin.
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

Definition string_indMixin :=
  Eval simpl in [indMixin for string_rect].
Canonical string_indType :=
  Eval hnf in IndType _ string string_indMixin.
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
