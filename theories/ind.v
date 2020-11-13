From mathcomp Require Import
  ssreflect ssrfun ssrbool ssrnat eqtype seq choice fintype.

From deriving Require Import base.

From Coq Require Import ZArith NArith String Ascii.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Open Scope deriving_scope.

Notation "T -F> S" :=
  (forall i, T i -> S i)
  (at level 30, no associativity)
  : deriving_scope.

Notation "T *F S"  :=
  (fun i => T i * S i)%type
  (at level 20, no associativity)
  : deriving_scope.

Record functor I := Functor {
  fobj      :> (I -> Type) -> I -> Type;
  fmap      :  forall T S, (T -F> S) -> fobj T -F> fobj S;
  fmap_eq   :  forall T S (f g : T -F> S),
                 (forall i, f i =1 g i) ->
                 (forall i (x : fobj T i), fmap f x = fmap g x);
  fmap1     :  forall T i (x : fobj T i),
                 fmap (fun i => @id (T i)) x = x;
  fmap_comp :  forall T S R (f : T -F> S) (g : S -F> R) i (x : fobj T i),
                 fmap (fun i => g i \o f i) x = fmap g (fmap f x);
}.

Module InitAlg.

Section ClassDef.

Record mixin_of I T (F : functor I) := Mixin {
  Roll     :  F T -F> T;
  case     :  forall S, (F T -F> S) -> T -F> S;
  rec      :  forall S, (F (T *F S) -F> S) -> T -F> S;
  _        :  forall S f i a,
                rec f (Roll a) =
                f i (fmap (fun i x => (x, rec f x)) a) :> S i;
  _        :  forall S f i a, case f (Roll a) = f i a :> S i;
  _        :  forall (P : forall i, T i -> Type),
                (forall i (a : F (fun i => {x & P i x}) i),
                   P i (Roll (fmap (fun i x => tag x) a))) ->
                forall i (x : T i), P i x
}.
Notation class_of := mixin_of (only parsing).

Record type I F := Pack {sort : I -> Type; _ : class_of sort F}.
Local Coercion sort : type >-> Funclass.
Variables (I : Type) (F : functor I) (T : I -> Type) (cT : type F).
Definition class := let: Pack _ c as cT' := cT return class_of cT' F in c.
Definition clone c of phant_id class c := @Pack I F T c.
Let xT := let: Pack T _ := cT in T.
Notation xclass := (class : class_of xT).

Definition pack c := @Pack I F T c.

End ClassDef.

Module Exports.
Coercion sort : type >-> Funclass.
Notation initAlgType := type.
Notation InitAlgMixin := Mixin.
Notation InitAlgType F T m := (@pack _ F T m).
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

Variable I : Type.
Variable F : functor I.
Variable T : initAlgType F.

Definition Roll := (InitAlg.Roll (InitAlg.class T)).
Definition case := (InitAlg.case (InitAlg.class T)).
Definition rec  := (InitAlg.rec  (InitAlg.class T)).

Lemma recE S f i a : rec f (Roll a) =
                     f i (fmap (fun i x => (x, rec f x)) a) :> S i.
Proof. by rewrite /Roll /rec; case: (T) f a=> [? []]. Qed.

Lemma caseE S f i a : case f (Roll a) = f i a :> S i.
Proof. by rewrite /Roll /case; case: (T) f a=> [? []]. Qed.

Lemma indP P :
  (forall i (a : F (fun i => {x & P i x}) i),
      P i (Roll (fmap (fun i x => tag x) a))) ->
  forall i (x : T i), P i x.
Proof. by rewrite /Roll /rec; case: (T) P => [? []]. Qed.

Definition unroll := case (fun _ => id).

Lemma RollK i : cancel (@Roll i) (@unroll i).
Proof. by move=> x; rewrite /unroll caseE. Qed.

Lemma Roll_inj i : injective (@Roll i).
Proof. exact: can_inj (@RollK i). Qed.

Lemma unrollK i : cancel (@unroll i) (@Roll i).
Proof. by elim/indP: i / => i a; rewrite RollK. Qed.

Lemma unroll_inj i : injective (@unroll i).
Proof. exact: can_inj (@unrollK i). Qed.

End InitAlgTheory.

Hint Unfold
  InitAlg.Roll
  InitAlg.case
  InitAlg.rec
  InitAlg.class
  InitAlg.sort
  Roll
  case
  rec
  unroll
  : deriving.

Set Universe Polymorphism.

Section Signature.

Import PolyType.

Variable n : nat.
Implicit Types (T S : fin n -> Type).

Variant arg := NonRec of Type | Rec of fin n.

Definition type_of_arg T (A : arg) : Type :=
  match A with
  | NonRec X => X
  | Rec i => T i
  end.

Definition type_of_arg_map T S (f : T -F> S) A :
  type_of_arg T A -> type_of_arg S A :=
  match A with
  | NonRec X => id
  | Rec i => f i
  end.

Definition is_rec A := if A is Rec _ then true else false.

Definition arity       := seq arg.
Definition signature   := seq arity.
Definition declaration := ilist signature n.

Identity Coercion seq_of_arity : arity >-> seq.
Identity Coercion seq_of_sig   : signature >-> seq.

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

Record decl_inst := DeclInst {
  decl_inst_len   :  nat;
  decl_inst_sort  :> ilist signature decl_inst_len;
  decl_inst_class :  hlist (hlist (hlist arg_class)) (seq_of_ilist decl_inst_sort);
}.
Arguments DeclInst : clear implicits.

Implicit Types (A : arg) (As : arity) (Σ : signature).
Implicit Types (Ai : arg_inst) (Asi : arity_inst) (Σi : sig_inst).

Canonical NonRec_arg_inst sX :=
  ArgInst (NonRec (sort sX)) (exist _ sX erefl).

Canonical Rec_arg_inst i :=
  ArgInst (Rec i) tt.

Canonical nth_fin_arg_inst Asi (i : fin (size Asi)) :=
  ArgInst (nth_fin i) (hnth (arity_inst_class Asi) i).

Canonical nil_arity_inst :=
  ArityInst nil tt.

Canonical cons_arity_inst Ai Asi :=
  ArityInst (arg_inst_sort Ai :: arity_inst_sort Asi)
            (arg_inst_class Ai ::: arity_inst_class Asi).

Canonical nth_fin_arity_inst Σi (i : fin (size Σi)) :=
  ArityInst (nth_fin i) (hnth (sig_inst_class Σi) i).

Canonical nil_sig_inst :=
  SigInst nil tt.

Canonical cons_sig_inst Asi Σi :=
  SigInst (arity_inst_sort Asi :: sig_inst_sort Σi)
          (arity_inst_class Asi ::: sig_inst_class Σi).

Canonical nil_decl_inst :=
  DeclInst 0 tt tt.

Canonical cons_decl_inst Σi Di :=
  DeclInst (decl_inst_len Di).+1
           (sig_inst_sort Σi  ::: decl_inst_sort Di)
           (sig_inst_class Σi ::: decl_inst_class Di).

Definition arity_rec (P : arity -> Type)
  (Pnil    : P [::])
  (PNonRec : forall (sX : K) (As : arity), P As -> P (NonRec (sort sX) :: As))
  (PRec    : forall i        (As : arity), P As -> P (Rec i            :: As)) :=
  fix arity_rec As : hlist arg_class As -> P As :=
    match As with
    | [::]               => fun cAs =>
      Pnil
    | NonRec X :: As => fun cAs =>
      cast (fun X => P (NonRec X :: As)) (svalP cAs.(hd))
           (PNonRec (sval cAs.(hd)) As (arity_rec As cAs.(tl)))
    | Rec i :: As    => fun cAs =>
      PRec i As (arity_rec As cAs.(tl))
    end.

Lemma arity_ind (P : forall As, hlist arg_class As -> Type)
  (Pnil : P [::] tt)
  (PNonRec : forall sX As cAs,
      P As cAs -> P (NonRec (sort sX) :: As) (exist _ sX erefl ::: cAs))
  (PRec : forall i As cAs,
      P As cAs -> P (Rec i :: As) (tt ::: cAs))
  As cAs : P As cAs.
Proof.
elim: As cAs=> [|[X|i] As IH] => /= [[]|[[sX e] cAs]|[[] cAs]] //.
  by case: X / e; apply: PNonRec.
by apply: PRec.
Qed.

End Signature.

Hint Unfold
  type_of_arg
  type_of_arg_map
  is_rec
  arity
  signature
  arg_class
  arg_inst_sort
  arg_inst_class
  arity_inst_sort
  arity_inst_class
  sig_inst_sort
  sig_inst_class
  NonRec_arg_inst
  Rec_arg_inst
  nth_fin_arg_inst
  nil_arity_inst
  cons_arity_inst
  nil_sig_inst
  cons_sig_inst
  arity_rec
  : deriving.

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

Hint Unfold arg_class_map : deriving.

Unset Universe Polymorphism.

Arguments arity_rec {n K} _ _ _ _ _.

Unset Elimination Schemes.
Inductive foo := Foo of bar
with bar := Bar of foo.
Set Elimination Schemes.

Scheme foo_rect := Induction for foo Sort Type
with   bar_rect := Induction for bar Sort Type.

Combined Scheme foo_bar_rect from foo_rect, bar_rect.

Module Ind.

Section Basic.

Variable n : nat.
Implicit Types (A : arg n.+1) (As : arity n.+1) (Σ : signature n.+1).
Implicit Types (D : declaration n.+1).
Implicit Types (T S : fin n.+1 -> Type).

Import PolyType.

Definition constructors D T :=
  hlist (fun Σ => hlist (fun As => hfun (type_of_arg T) As (T i)) Σ).

Fixpoint branch T S i As : Type :=
  match As with
  | NonRec X :: As => X          -> branch T S i As
  | Rec    j :: As => T j -> S j -> branch T S i As
  | [::]           => S i
  end.

Fixpoint recursor_res_aux m acc :
  forall (T : fin m -> Type) (P : forall i : fin m, T i -> Type), Type :=
  match m with
  | 0 =>
    fun _ _ => acc
  | m.+1 =>
    fun (T : fin m.+1 -> Type) (P : forall i : fin m.+1, T i -> Type) =>
      recursor_res_aux (prod acc (forall x : T None, P None x))
                       (fun i x => P (Some i) x)
  end.

Fixpoint acc_of_recursor_res_aux m acc :
  forall (T : fin m -> Type) (P : forall i, T i -> Type),
    recursor_res_aux acc P -> acc :=
  match m with
  | 0    =>
    fun (T : fin 0 -> Type) _ => id
  | m.+1 =>
    fun (T : fin m.+1 -> Type) P fs =>
      Datatypes.fst (@acc_of_recursor_res_aux m _ _ _ fs)
  end.

Fixpoint fun_of_recursor_res_aux m acc :
  forall (T : fin m -> Type) (P : forall i, T i -> Type),
    recursor_res_aux acc P ->
    forall (i : fin m) (x : T i), P i x :=
  match m with
  | 0    => fun (T : fin 0 -> Type) P fs i => match i with end
  | m.+1 => fun (T : fin m.+1 -> Type) P fs i =>
    match i with
    | None   => Datatypes.snd (@acc_of_recursor_res_aux m _ _ _ fs)
    | Some i => fun x => @fun_of_recursor_res_aux m _ _ _ fs i x
    end
  end.

Definition recursor_res T (P : forall i, T i -> Type) : Type :=
  recursor_res_aux (forall x : T None, P None x)
                   (fun i x => P (Some i) x).

Definition fun_of_recursor_res
  T (P : forall i, T i -> Type) (f : recursor_res P) (i : fin n.+1) :
  forall (x : T i), P i x :=
  match i with
  | None   => acc_of_recursor_res_aux f
  | Some i => fun x => fun_of_recursor_res_aux f x
  end.

Fixpoint recursor_for m : forall (D : ilist (signature n.+1) m) T S, Type :=
  match m with
  | 0    => fun _ T S => @recursor_res T (fun i _ => S i)
  | m.+1 => fun (D : ilist (signature n.+1) m) T S =>
              hfun


Definition recursor Σ T :=
  forall S, hfun (branch T S) Σ (@recursor_res T (fun i _ => S i)).

Fixpoint branch_of_hfun T S As :
  hfun (type_of_arg (Datatypes.prod T S)) As S -> branch T S As :=
  match As with
  | NonRec R :: As => fun f x   => branch_of_hfun (f x)
  | Rec      :: As => fun f x y => branch_of_hfun (f (Datatypes.pair x y))
  | [::]           => fun f     => f
  end.

Fixpoint hfun_of_branch T S As :
  branch T S As -> hfun (type_of_arg (Datatypes.prod T S)) As S :=
  match As with
  | NonRec R :: As => fun f x => hfun_of_branch (f x)
  | Rec      :: As => fun f p => hfun_of_branch (f (Datatypes.fst p) (Datatypes.snd p))
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
    r S bs (hnth Cs i xs) =
    hfun_of_branch (hnth bs i)
                   (hmap (type_of_arg_map (fun x => Datatypes.pair x (r S bs x))) xs)))).

Definition destructor Σ T :=
  forall S, hfun (fun As => hfun (type_of_arg T) As S) Σ (T -> S).

Definition destructor_eq Σ T (Cs : constructors Σ T) (d : destructor Σ T) :=
  forall S,
  all_hlist (fun bs : hlist (fun ks => hfun (type_of_arg T) ks S) Σ =>
  all_fin   (fun i  : fin (size Σ) =>
  all_hlist (fun xs : hlist (type_of_arg T) (nth_fin i) =>
    d S bs (hnth Cs i xs) = hnth bs i xs))).

Definition destructor_of_recursor Σ T (r : recursor Σ T) : destructor Σ T :=
  fun S => hcurry (
  fun bs : hlist (fun As => hfun (type_of_arg T) As S) Σ =>
    r S (hmap (fun As (b : hfun (type_of_arg T) As S) =>
           branch_of_hfun
             (hcurry (fun xs => b (hmap (type_of_arg_map Datatypes.fst) xs)))) bs)
).

Fixpoint ind_branch T (P : T -> Type) As : hfun (type_of_arg T) As T -> Type :=
  match As with
  | NonRec R :: As => fun C => forall x : R,        ind_branch P (C x)
  | Rec      :: As => fun C => forall x : T, P x -> ind_branch P (C x)
  | [::]           => fun C => P C
  end.

Fixpoint induction T (P : T -> Type) Σ : constructors Σ T -> Type :=
  match Σ with
  | As :: Σ => fun Cs => ind_branch P Cs.(hd) -> induction P Cs.(tl)
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

Hint Unfold
  Ind.constructors
  Ind.branch
  Ind.recursor
  Ind.branch_of_hfun
  Ind.hfun_of_branch
  Ind.recursor_eq
  Ind.destructor
  Ind.destructor_eq
  Ind.destructor_of_recursor
  Ind.ind_branch
  Ind.induction
  Ind.Cons
  Ind.rec
  Ind.case
  Ind.sort
  Ind.class
  : deriving.

Module IndF.

Section TypeDef.

Variables (Σ : signature).

Notation size := PolyType.size.

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
  hnth (@Ind.Cons _ _ T) (constr x) (args x).

Definition branches_of_fun S (body : F (T * S) -> S) :=
  hlist_of_fun (fun i =>
    Ind.branch_of_hfun
      (hcurry
         (fun l => body (Cons i l)))).

Definition rec S (body : F (T * S) -> S) :=
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
by rewrite /= hnth_of_fun Ind.branch_of_hfunK hcurryK.
Qed.

Lemma caseE S f a : case f (Roll a) = f a :> S.
Proof.
case: a => [i args]; have := Ind.caseE T S.
move/all_hlistP.
move/(_ (hlist_of_fun (fun i => hcurry (fun l => f (Cons i l))))).
move/all_finP/(_ i).
move/all_hlistP/(_ args).
rewrite /case /Roll => -> /=.
by rewrite hnth_of_fun hcurryK.
Qed.

Lemma indP P :
  (forall (a : F {x & P x}), P (Roll (fmap tag a))) ->
  forall x, P x.
Proof.
rewrite /Roll; case: (T) P => S [/= Cs _ _ _ _ indP] P.
have {}indP:
    (forall i, Ind.ind_branch P (hnth Cs i)) ->
    (forall x, P x).
  elim: (Σ) Cs {indP} (indP P) => //= As Σ' IH [C Cs] /= indP hyps.
  move/indP/IH: (hyps None); apply=> i; exact: (hyps (Some i)).
move=> hyps; apply: indP=> j.
have {}hyps:
  forall args : hlist (type_of_arg {x : S & P x}) (nth_fin j),
    P (hnth Cs j (hmap (type_of_arg_map tag) args)).
  by move=> args; move: (hyps (Cons j args)).
elim: (nth_fin j) (hnth Cs j) hyps=> [|[R|] As IH] //=.
- by move=> ? /(_ tt).
- move=> C hyps x; apply: IH=> args; exact: (hyps (x ::: args)).
- move=> constr hyps x H; apply: IH=> args.
  exact: (hyps (existT _ x H ::: args)).
Qed.

Canonical initAlgType :=
  Eval hnf in InitAlgType functor T (InitAlgMixin recE caseE indP).

End TypeDef.

End IndF.

Hint Unfold
  IndF.constr
  IndF.args
  IndF.fmap
  IndF.functor
  IndF.Roll
  IndF.branches_of_fun
  IndF.rec
  IndF.case
  IndF.initAlgType
  : deriving.

Canonical IndF.functor.
Canonical IndF.initAlgType.
Coercion IndF.initAlgType : indType >-> initAlgType.

Section InferInstances.

Import PolyType.

Class infer_arity
  T (P : T -> Type)
  (branchT : Type) (As : arity) (C : hfun (type_of_arg T) As T) : Type.
Arguments infer_arity : clear implicits.

Global Instance infer_arity_end
  T (P : T -> Type) (x : T) :
  infer_arity T P (P x) [::] x.
Defined.

Global Instance infer_arity_rec
  T (P : T -> Type)
  (branchT : T -> Type) (As : arity) (C : T -> hfun (type_of_arg T) As T)
  (_ : forall x, infer_arity T P (branchT x) As (C x)) :
  infer_arity T P (forall x, P x -> branchT x) (Rec :: As) C.
Defined.

Global Instance infer_arity_nonrec
  T (P : T -> Type)
  S (branchT : S -> Type) As (C : S -> hfun (type_of_arg T) As T)
  (_ : forall x, infer_arity T P (branchT x) As (C x)) :
  infer_arity T P (forall x, branchT x) (NonRec S :: As) C.
Defined.

Class infer_sig
  T (P : T -> Type) (elimT : Type) Σ (Cs : Ind.constructors Σ T).
Arguments infer_sig : clear implicits.

Global Instance infer_sig_end T (P : T -> Type) :
  infer_sig T P (forall x : T, P x) [::] tt.
Defined.

Global Instance infer_sig_branch
  T (P : T -> Type)
  (branchT : Type) As C (_ : infer_arity T P branchT As C)
  (elimT : Type) (Σ : signature) Cs (_ : infer_sig T P elimT Σ Cs) :
  infer_sig T P (branchT -> elimT) (As :: Σ) (C ::: Cs).
Defined.

End InferInstances.

Arguments infer_arity : clear implicits.
Arguments infer_sig : clear implicits.

Hint Unfold
  infer_arity_end
  infer_arity_rec
  infer_arity_nonrec
  infer_sig_end
  infer_sig_branch
  : deriving.

Module InitAlgEqType.

Record type (F : functor) := Pack {
  sort           : Type;
  eq_class       : Equality.class_of sort;
  init_alg_class : InitAlg.mixin_of sort F;
}.

Definition eqType F (T : type F) := Equality.Pack (eq_class T).
Definition initAlgType F (T : type F) := InitAlg.Pack (init_alg_class T).

Module Import Exports.
Notation initAlgEqType := type.
Notation InitAlgEqType := Pack.
Coercion sort : type >-> Sortclass.
Coercion eqType : type >-> Equality.type.
Canonical eqType.
Coercion initAlgType : type >-> InitAlg.type.
Canonical initAlgType.
End Exports.

End InitAlgEqType.

Export InitAlgEqType.Exports.

Hint Unfold
  InitAlgEqType.sort
  InitAlgEqType.eq_class
  InitAlgEqType.init_alg_class
  InitAlgEqType.eqType
  InitAlgEqType.initAlgType
  : deriving.

Module InitAlgChoiceType.

Record type (F : functor) := Pack {
  sort           : Type;
  choice_class   : Choice.class_of sort;
  init_alg_class : InitAlg.mixin_of sort F;
}.

Definition eqType F (T : type F) := Equality.Pack (choice_class T).
Definition choiceType F (T : type F) := Choice.Pack (choice_class T).
Definition initAlgType F (T : type F) := InitAlg.Pack (init_alg_class T).

Module Import Exports.
Notation initAlgChoiceType := type.
Notation InitAlgChoiceType := Pack.
Coercion sort : type >-> Sortclass.
Coercion eqType : type >-> Equality.type.
Canonical eqType.
Coercion choiceType : type >-> Choice.type.
Canonical choiceType.
Coercion initAlgType : type >-> InitAlg.type.
Canonical initAlgType.
End Exports.

End InitAlgChoiceType.

Export InitAlgChoiceType.Exports.

Hint Unfold
  InitAlgChoiceType.sort
  InitAlgChoiceType.choice_class
  InitAlgChoiceType.init_alg_class
  InitAlgChoiceType.eqType
  InitAlgChoiceType.choiceType
  InitAlgChoiceType.initAlgType
  : deriving.
