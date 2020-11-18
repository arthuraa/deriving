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

Definition arity_class (As : arity) :=
  hlist' arg_class As.

Record arity_inst := ArityInst {
  arity_inst_sort  :> arity;
  arity_inst_class :  arity_class arity_inst_sort;
}.
Arguments ArityInst : clear implicits.

Definition sig_class (Σ : signature) :=
  hlist' arity_class Σ.

Record sig_inst := SigInst {
  sig_inst_sort  :> signature;
  sig_inst_class :  sig_class sig_inst_sort;
}.
Arguments SigInst : clear implicits.

Record decl_inst := DeclInst {
  decl_inst_len   :  nat;
  decl_inst_sort  :> ilist signature decl_inst_len;
  decl_inst_class :  hlist' sig_class (seq_of_ilist decl_inst_sort);
}.
Arguments DeclInst : clear implicits.

Implicit Types (A : arg) (As : arity) (Σ : signature).
Implicit Types (Ai : arg_inst) (Asi : arity_inst) (Σi : sig_inst).

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
  arity_class
  arity_inst_sort
  arity_inst_class
  sig_class
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

Definition idx D := fin (sumn_fin (fun i => size (inth D i))).

Definition Tidx D (i : idx D) := tag (tag_of_fin _ i).
Arguments Tidx : clear implicits.

Definition Cidx D (i : idx D) := tagged (tag_of_fin _ i).
Arguments Cidx : clear implicits.

Definition sig_of D (i : idx D) : signature n.+1 :=
  inth D (Tidx D i).

Definition arity_of D (i : idx D) : arity n.+1 :=
  nth_fin (Cidx D i).

Definition args D T (i : idx D) : Type :=
  hlist' (type_of_arg T) (arity_of i).

Definition args_map D T S (f : T -F> S) (i : idx D) (xs : args T i) : args S i :=
  hmap' (type_of_arg_map f) xs.

Definition constructors D T :=
  hlist (fun i =>
    hfun' (type_of_arg T) (arity_of i) (T (Tidx D i))).

Fixpoint rec_branch' T S i As : Type :=
  match As with
  | NonRec X :: As => X          -> rec_branch' T S i As
  | Rec    j :: As => T j -> S j -> rec_branch' T S i As
  | [::]           => S i
  end.

Definition rec_branch D T S i : Type :=
  rec_branch' T S (Tidx D i) (arity_of i).

Fixpoint hlist1V' m acc : (fin m -> Type) -> Type :=
  match m with
  | 0    => fun _ => acc
  | m.+1 => fun X => hlist1V' (acc * (X None)) (fun i => X (Some i))
  end%type.

Fixpoint hd_hlist1V' m acc :
  forall (X : fin m -> Type), hlist1V' acc X -> acc :=
  match m with
  | 0    => fun X l => l
  | m.+1 => fun X l => (@hd_hlist1V' m _ (fun i => X (Some i)) l).1
  end.

Fixpoint tl_hlist1V' m acc :
  forall (X : fin m -> Type), hlist1V' acc X -> forall i, X i :=
  match m with
  | 0    => fun X l i => match i with end
  | m.+1 => fun X l i =>
    match i with
    | None => (@hd_hlist1V' m _ _ l).2
    | Some i => @tl_hlist1V' m _ _ l i
    end
  end.

Definition hlist1V T := hlist1V' (T None) (fun i => T (Some i)).

Definition hnth1V T (l : hlist1V T) i : T i :=
  match i with
  | None => hd_hlist1V' l
  | Some i => tl_hlist1V' l i
  end.

Coercion hnth1V : hlist1V >-> Funclass.

Definition recursor D T :=
  forall S, hfun (@rec_branch D T S) (hlist1V (fun i => T i -> S i)).

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

Definition recursor_eq D T (Cs : constructors D T) (r : recursor D T) :=
  forall S,
  all_hlist (fun bs : hlist (rec_branch T S) =>
  all_fin   (fun i  : idx D                  =>
  all_hlist (fun xs : args T i               =>
    r S bs _ (Cs i xs) =
    bs i (args_map (fun j x => (x, r S bs j x)) xs)))).

Definition des_branch D T S i :=
  hfun' (type_of_arg T) (arity_of i) (S (Tidx D i)).

Definition destructor D T :=
  forall S, hfun (@des_branch D T S) (hlist1V (fun i => T i -> S i)).

Definition destructor_eq D T (Cs : constructors D T) (d : destructor D T) :=
  forall S,
  all_hlist (fun bs : hlist (des_branch T S) =>
  all_fin   (fun i  : idx D                  =>
  all_hlist (fun xs : args T i               =>
    d S bs _ (Cs i xs) = bs i xs))).

Definition rec_of_des_branch D T S (i : idx D) (b : des_branch T S i) :
  rec_branch T S i :=
  rec_branch'_of_hfun' (hcurry (fun xs => b (args_map (fun _ => fst) xs))).

Definition destructor_of_recursor D T (r : recursor D T) : destructor D T :=
  fun S => hcurry (fun bs : hlist (@des_branch D T S) =>
    r S (hmap (@rec_of_des_branch D T S) bs)).

Fixpoint ind_branch' T (P : hlist (fun i => T i -> Type)) i As :
  hfun' (type_of_arg T) As (T i) -> Type :=
  match As with
  | NonRec R :: As => fun C => forall x : R,            ind_branch' P (C x)
  | Rec    j :: As => fun C => forall x : T j, P j x -> ind_branch' P (C x)
  | [::]           => fun C => P i C
  end.

Definition ind_branch D T P (Cs : constructors D T) i :=
  @ind_branch' T P (Tidx D i) (arity_of i) (Cs i).

Definition induction D T (Cs : constructors D T) :=
  @hdfun n.+1 (fun i => T i -> Type) (fun P =>
  hfun (@ind_branch D T P Cs)
       (hlist1V (fun i => forall x, P i x))).

End Basic.

Section ClassDef.

Variables (n : nat) (D : declaration n.+1).

Record mixin_of T := Mixin {
  Cons      : constructors D T;
  rec       : recursor D T;
  case      : destructor D T;
  _         : recursor_eq Cons rec;
  _         : destructor_eq Cons case;
  _         : induction Cons;
}.

Record type := Pack {sort : fin n.+1 -> Type; class : mixin_of sort}.
Variables (T : fin n.+1 -> Type).
Definition recE (m : mixin_of T) : recursor_eq (Cons m) (rec m) :=
  let: Mixin _ _ _ recE _ _ := m in recE.
Definition caseE (m : mixin_of T) : destructor_eq (Cons m) (case m) :=
  let: Mixin _ _ _ _ caseE _ := m in caseE.
Definition indP (m : mixin_of T) :=
  let: Mixin _ _ _ _ _ indP := m
  return induction (Cons m) in indP.

End ClassDef.

Module Exports.
Coercion sort : type >-> Funclass.
Coercion class : type >-> mixin_of.
Notation indType := type.
Notation IndType m := (@Pack _ _ _ m).
Notation IndMixin := Mixin.
End Exports.

End Ind.
Export Ind.Exports.

Hint Unfold
  Ind.constructors
  Ind.rec_branch'
  Ind.rec_branch
  Ind.recursor
  Ind.rec_branch'_of_hfun'
  Ind.hfun'_of_rec_branch'
  Ind.recursor_eq
  Ind.des_branch
  Ind.destructor
  Ind.destructor_eq
  Ind.rec_of_des_branch
  Ind.destructor_of_recursor
  Ind.ind_branch'
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

Variables (n : nat) (D : declaration n.+1).

Implicit Types (T S : fin n.+1 -> Type).

Notation size := PolyType.size.

Record fobj T (i : fin n.+1) := Cons {
  constr : fin (size (inth D i));
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

Canonical functor := Functor fmap_eq fmap1 fmap_comp.

Lemma inj T (i : fin n.+1) (j : fin (size (inth D i))) (a b : hlist' (type_of_arg T) (nth_fin j)) :
  Cons j a = Cons j b -> a = b.
Proof.
pose get x :=
  if leq_fin (constr x) j is inl e then
    cast (fun j : fin (size (inth D i)) => hlist' (type_of_arg T) (nth_fin j)) e (args x)
  else a.
by move=> /(congr1 get); rewrite /get /= leq_finii /=.
Qed.

Variable T : indType D.

Definition Roll i (x : F T i) : T i :=
  @Ind.Cons _ _ _ T (@fin_of_tag' _ _ i (constr x)) (args x).

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
  forall args : hlist' (type_of_arg {x : S & P x}) (nth_fin j),
    P (hnth Cs j (hmap' (type_of_arg_map tag) args)).
  by move=> args; move: (hyps (Cons j args)).
move: (hnth Cs j) hyps; rewrite /fnth.
elim: (nth_fin j)=> [|[R|] As IH] //=.
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
  (branchT : Type) (As : arity) (C : hfun' (type_of_arg T) As T) : Type.
Arguments infer_arity : clear implicits.

Global Instance infer_arity_end
  T (P : T -> Type) (x : T) :
  infer_arity T P (P x) [::] x.
Defined.

Global Instance infer_arity_rec
  T (P : T -> Type)
  (branchT : T -> Type) (As : arity) (C : T -> hfun' (type_of_arg T) As T)
  (_ : forall x, infer_arity T P (branchT x) As (C x)) :
  infer_arity T P (forall x, P x -> branchT x) (Rec :: As) C.
Defined.

Global Instance infer_arity_nonrec
  T (P : T -> Type)
  S (branchT : S -> Type) As (C : S -> hfun' (type_of_arg T) As T)
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
