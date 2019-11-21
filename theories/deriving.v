From mathcomp Require Import
  ssreflect ssrfun ssrbool ssrnat eqtype seq choice fintype.

From void Require Import void.

From deriving Require Import base.

From Coq Require Import ZArith NArith String Ascii.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Open Scope deriving_scope.

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

Set Universe Polymorphism.

Section Signature.

Import PolyType.

Definition arity := seq bool.
Definition signature := seq arity.

Definition argT K b := fin (~~ b) -> K.
Definition arityT K (A : arity) :=
  forall i : fin (size A), argT K (nth_fin i).
Definition signatureT K (Σ : signature) :=
  forall c : fin (size Σ), arityT K (nth_fin c).

Identity Coercion fun_of_argT : argT >-> Funclass.
Identity Coercion fun_of_arityT : arityT >-> Funclass.
Identity Coercion fun_of_signatureT : signatureT >-> Funclass.

Definition argF T b : argT Type b -> Type :=
  match b with
  | true  => fun _ => T
  | false => fun S => S None
  end.

Definition argF_map T1 T2 (f : T1 -> T2) b :
  forall S : argT Type b, argF T1 S -> argF T2 S :=
  match b with
  | true  => fun A x => f x
  | false => fun A x => x
  end.

Definition argF_eq T b :
  forall (S1 S2 : argT Type b) (e : forall P, S1 P = S2 P),
  argF T S1 = argF T S2 :=
  match b with
  | true  => fun S1 S2 e => erefl
  | false => fun S1 S2 e => e None
  end.

Lemma argF_eqV T b S1 S2 e : (@argF_eq T b S1 S2 e)^-1 = argF_eq T (fun P => (e P)^-1).
Proof. by case: b S1 S2 e. Qed.

Variables (K : Type) (sort : K -> Type).

Definition arity_rec
  (T       : forall A, arityT K A -> Type)
  (Tnil    : forall   f, T [::] f)
  (TNonRec : forall A f, T A (fun i => f (Some i)) -> T (false :: A) f)
  (TRec    : forall A f, T A (fun i => f (Some i)) -> T (true  :: A) f) :=
  fix arity_rec A : forall f, T A f :=
    match A with
    | [::]       => fun f => Tnil f
    | false :: A => fun f => TNonRec A f (arity_rec A _)
    | true  :: A => fun f => TRec    A f (arity_rec A _)
    end.

End Signature.

(** We would like the inference of canonical structures to work with functions
    of finite domain.  *)

Record preorder_tag := PreorderTag { po_untag :> Type }.

Record preorder := Preorder {
  po_sort  :> preorder_tag;
  po_order :  po_sort -> po_sort -> Prop;
  po_refl  :  forall x, po_order x x;
  po_trans :  forall x y z, po_order x y -> po_order y z -> po_order x z;
}.

Declare Scope preorder_scope.

Notation "1" := (po_refl _) : preorder_scope.
Notation "p * q" := (po_trans p q) : preorder_scope.
Notation "x ≡ y" := (po_order x y) (at level 70): preorder_scope.

Section ClassLift.

Import PolyType.

Local Open Scope preorder_scope.

Definition eq_preorder_tag T := PreorderTag T.
Canonical fun_preorder_tag := eq_preorder_tag.

Canonical eq_preorder T :=
  @Preorder (eq_preorder_tag T) (@eq T) (@erefl T) (@etrans T).

Canonical fun_preorder T (S : T -> preorder) :=
  @Preorder (fun_preorder_tag (forall x, S x))
    (fun f g => forall x, f x ≡ g x)
    (fun f x => 1)
    (fun f g h p q x => p x * q x).

Record cl_tag n (S : fin n -> Type) := ClTag { cl_untag :> forall i, S i }.

Definition class_lift0_tag n S T := @ClTag n S T.
Definition class_lift1_tag n S T := @class_lift0_tag n S T.
Canonical class_lift1_tag.

Record class_lift n K (S : fin n -> preorder) (sort : forall i, K i -> S i) := ClassLift {
  cl_fun :> cl_tag S;
  _      :  {sT : forall i, K i | forall i, sort i (sT i) ≡ cl_fun i}
}.

Definition cl_funL n K S sort (T : @class_lift n K S sort) :
  forall i, K i :=
  let: ClassLift _ e := T in sval e.

Definition cl_funP n K S sort (T : @class_lift n K S sort) :
  forall i, sort i (cl_funL T i) ≡ T i :=
  let: ClassLift _ e := T in svalP e.

Canonical class_lift0 K S sort T :=
  @ClassLift 0 K S sort (@class_lift0_tag 0 S T)
    (exist _ (fun i : void => match i with end)
             (fun i : void => match i with end)).

(*
Record fun_split n (R : Type) (T : R) (Ts : fin n -> R) := FunSplit {
  fs_fun :> fin n.+1 -> R;
  _      :  T = fs_fun None;
  _      :  forall i, Ts i = fs_fun (Some i);
}.

Definition fsE1 n R T Ts (TTs : @fun_split n R T Ts) : T ≡ TTs None :=
  let: FunSplit _ e _ := TTs in e.

Definition fsE2 n R T Ts (TTs : @fun_split n R T Ts) : forall i, Ts i ≡ TTs (Some i) :=
  let: FunSplit _ _ e := TTs in e.

Canonical fun_split1 n R (TTs : fin n.+1 -> R) :=
  @FunSplit n R (TTs None) (fun i => TTs (Some i)) TTs erefl (fun=> erefl).
*)

Record fun_split n (Ss : fin n.+1 -> preorder) (T : Ss None) (Ts : forall i : fin n, Ss (Some i)) := FunSplit {
  fs_fun :> forall i, Ss i;
  _      :  T ≡ fs_fun None;
  _      :  forall i, Ts i ≡ fs_fun (Some i);
}.

Definition fsE1 n Ss T Ts (TTs : @fun_split n Ss T Ts) : T ≡ TTs None :=
  let: FunSplit _ e _ := TTs in e.

Definition fsE2 n Ss T Ts (TTs : @fun_split n Ss T Ts) : forall i, Ts i ≡ TTs (Some i) :=
  let: FunSplit _ _ e := TTs in e.

Canonical fun_split1 n (Ss : fin n.+1 -> preorder) (TTs : forall i, Ss i) :=
  @FunSplit n Ss (TTs None) (fun i => TTs (Some i)) TTs 1 (fun=> 1).

Canonical class_lift1 n
  (KKs : fin n.+1 -> Type) (SSs : fin n.+1 -> preorder)
  (sorts : forall i, KKs i -> SSs i)
  (T : KKs None) (Ts : class_lift (fun i : fin n => sorts (Some i)))
  (TTs : @fun_split n SSs (sorts None T) (cl_fun Ts)) :=
  let RRs (i : fin n.+1) : KKs i :=
    if i is Some j then cl_funL Ts j else T in
  let RRsP (i : fin n.+1) : sorts i (RRs i) ≡ TTs i :=
    if i is Some j then cl_funP Ts j * @fsE2 _ _ _ _ TTs j else fsE1 TTs in
  @ClassLift n.+1 KKs SSs sorts (class_lift1_tag TTs) (exist _ RRs RRsP).

End ClassLift.

Unset Universe Polymorphism.

Arguments arity_rec {_} _ _ _ _ _.

Module Ind.

Section Basic.

Implicit Types (A : arity) (Σ : signature) (T S : Type).

Import PolyType.

Definition constructors Σ (ΣT : signatureT Type Σ) T :=
  hlist (fun c => hfun (fun i => argF T (ΣT c i)) T).

Definition constructors_eq Σ (ΣT1 ΣT2 : signatureT Type Σ)
  (e : forall i j ijP, @ΣT1 i j ijP = @ΣT2 i j ijP) T :
  constructors ΣT1 T = constructors ΣT2 T :=
  hlist_eq (fun c => hfun_eq (fun i => argF_eq T (e c i)) T).

Fixpoint branch T S A : arityT Type A -> Type :=
  match A with
  | [::]       => fun AT => S
  | false :: A => fun AT => AT None None -> branch T S (fun i => AT (Some i))
  | true  :: A => fun AT => T -> S       -> branch T S (fun i => AT (Some i))
  end.

Fixpoint branch_eq T S A :
  forall (AT1 AT2 : arityT Type A) (e : forall i iP, AT1 i iP = AT2 i iP),
  branch T S AT1 = branch T S AT2 :=
  match A with
  | [::]       => fun AT1 AT2 e => erefl
  | false :: A => fun AT1 AT2 e => congr2 (fun X Y => X -> Y) (e None None) (branch_eq T S (fun i => e (Some i)))
  | true  :: A => fun AT1 AT2 e => congr1 (fun   Y => T -> S -> Y) (branch_eq T S (fun i => e (Some i)))
  end.

Lemma branch_eqV T S A AT1 AT2 e :
  (@branch_eq T S A AT1 AT2 e)^-1 = branch_eq T S (fun i iP => (e i iP)^-1).
Proof.
elim: A AT1 AT2 e=> //= [] [] A IH AT1 AT2 /= e.
  by rewrite congr1V IH.
rewrite /congr2 etransV !congr1V IH.
case: _ / (e None _) => /=; by rewrite etrans1p.
Qed.

Definition recursor Σ (ΣT : signatureT Type Σ) T :=
  forall S, hfun (fun c => branch T S (ΣT c)) (T -> S).

Definition recursor_eq Σ (ΣT1 ΣT2 : signatureT Type Σ)
  (e : forall i j ijP, ΣT1 i j ijP = ΣT2 i j ijP) T :=
  fun S => hfun_eq (fun c => branch_eq T S (e c)) (T -> S).

Fixpoint branch_of_hfun T S A : forall (AT : arityT Type A),
  hfun (fun i => argF (prod T S) (AT i)) S -> branch T S AT :=
  match A with
  | [::]       => fun AT f     => f
  | false :: A => fun AT f x   => branch_of_hfun (f x)
  | true  :: A => fun AT f x y => branch_of_hfun (f (x, y))
  end.

Fixpoint hfun_of_branch T S A : forall (AT : arityT Type A),
  branch T S AT -> hfun (fun i => argF (prod T S) (AT i)) S :=
  match A with
  | [::]       => fun AT f   => f
  | false :: A => fun AT f x => hfun_of_branch (f x)
  | true  :: A => fun AT f p => hfun_of_branch (f p.1 p.2)
  end.

Lemma branch_of_hfunK T S A AT f xs :
  hfun_of_branch (@branch_of_hfun T S A AT f) xs = f xs.
Proof. by elim: A AT f xs=> [|[] A IH] //= AT f [[x y] xs]. Qed.

Lemma hfun_of_branch_eq T S A AT1 AT2 e f xs :
  hfun_of_branch (cast id (@branch_eq T S A AT1 AT2 e) f) xs =
  hfun_of_branch f (cast id (hlist_eq (fun i => argF_eq _ (e i)))^-1 xs).
Proof.
elim: A AT1 AT2 e f xs=> // [] [] A IH /= AT1 AT2 e f.
- case=> [[x y] xs]; rewrite /congr2 /= cast_idE !(castFE, castCE) IH.
  by congr (hfun_of_branch _ _); case: _ / (hlist_eq _) xs.
- case=> x xs; rewrite /congr2 /= castD !cast_idE !(castFE, castCE) IH.
  rewrite etransV !congr1V castD.
  by case: _ / (e None _) x=> /= x; case: _ / (hlist_eq _) xs=> /=.
Qed.

Definition recursorE Σ ΣT T (Cs : @constructors Σ ΣT T) (r : recursor ΣT T) :=
  forall S,
  all_hlist (fun bs : hlist (fun c => branch T S (ΣT c)) =>
  all_fin   (fun c  : fin (size Σ) =>
  all_hlist (fun xs : hlist (fun i => argF T (ΣT c i)) =>
    r S bs (hnth Cs c xs) =
    hfun_of_branch (hnth bs c)
      (hmap (fun i x => argF_map (fun x => (x, r S bs x)) x) xs)))).

Lemma recursorE_eq Σ (ΣT1 ΣT2 : signatureT Type Σ) T (Cs : @constructors Σ ΣT1 T) (r : recursor ΣT1 T)
  (e : forall i j ijP, ΣT1 i j ijP = ΣT2 i j ijP) (rP : recursorE Cs r) :
  recursorE (cast id (constructors_eq e T) Cs) (fun S => cast id (recursor_eq e T S) (r S)).
Proof.
move=> S; move: (r S) (rP S)=> {}r {}rP.
apply/all_hlistP=> bs.
move/all_hlistP/(_ (cast id (hlist_eq (fun c => branch_eq T S (e c)))^-1 bs)) in rP.
apply/all_finP=> c.
move/all_finP/(_ c) in rP.
apply/all_hlistP=> xs.
move/all_hlistP/(_ (cast id (hlist_eq (fun i => argF_eq T (e c i)))^-1 xs)) in rP.
rewrite /recursor_eq happ_eq hlist_eq_hmap hnth_hmap happ_eq rP hlist_eqV.
rewrite hlist_eq_hmap hnth_hmap branch_eqV hfun_of_branch_eq.
rewrite hlist_eqV hlist_eq_hmap hmap_comp; congr (hfun_of_branch _ _).
rewrite hlist_eqV hlist_eq_hmap hmap_comp; apply: hmap_eq=> i x /=.
rewrite -argF_eqV esymK.
case: (nth_fin i) (ΣT1 c i) (ΣT2 c i) (e c i) x=> //= ????.
by rewrite -castD etransVp.
Qed.

Definition destructor Σ (ΣT : signatureT Type Σ) T :=
  forall S, hfun (fun c => hfun (fun i => argF T (ΣT c i)) S) (T -> S).

Definition destructor_eq Σ (ΣT1 ΣT2 : signatureT Type Σ)
  (e : forall i j ijP, ΣT1 i j ijP = ΣT2 i j ijP) T :=
  fun S => hfun_eq (fun c => hfun_eq (fun i => argF_eq T (e c i)) S) (T -> S).

Definition destructorE Σ ΣT T (Cs : @constructors Σ ΣT T) (d : destructor ΣT T) :=
  forall S,
  all_hlist (fun bs : hlist (fun c => hfun (fun i => argF T (ΣT c i)) S) =>
  all_fin   (fun c  : fin (size Σ) =>
  all_hlist (fun xs : hlist (fun i => argF T (ΣT c i)) =>
    d S bs (hnth Cs c xs) = hnth bs c xs))).

Lemma destructorE_eq Σ (ΣT1 ΣT2 : signatureT Type Σ) T (Cs : @constructors Σ ΣT1 T) (d : destructor ΣT1 T)
  (e : forall i j ijP, ΣT1 i j ijP = ΣT2 i j ijP) (dP : destructorE Cs d) :
  destructorE (cast id (constructors_eq e T) Cs) (fun S => cast id (destructor_eq e T S) (d S)).
Proof.
move=> S; move: (d S) (dP S)=> {}d {}dP.
apply/all_hlistP=> bs.
pose p := hlist_eq (fun c => hfun_eq (fun i => argF_eq T (e c i)) S).
move/all_hlistP/(_ (cast id p^-1 bs)) in dP.
apply/all_finP=> c.
move/all_finP/(_ c) in dP.
apply/all_hlistP=> xs.
move/all_hlistP/(_ (cast id (hlist_eq (fun i => argF_eq T (e c i)))^-1 xs)) in dP.
rewrite /destructor_eq happ_eq hlist_eq_hmap hnth_hmap happ_eq {}dP hlist_eqV.
rewrite /p hlist_eq_hmap !hlist_eqV hlist_eq_hmap hnth_hmap hfun_eqV happ_eq.
rewrite -hlist_eqV esymK hlist_eq_hmap hmap_comp; congr (hnth bs c _).
by rewrite -[RHS]hmap1; apply: hmap_eq=> i x /=; rewrite -castD etransVp.
Qed.

Definition destructor_of_recursor Σ ΣT T (r : @recursor Σ ΣT T) : destructor ΣT T :=
  fun S => hcurry (
  fun bs : hlist (fun c => hfun (fun i => argF T (ΣT c i)) S) =>
    r S (hmap (fun _ (b : hfun (fun i => argF T (ΣT _ i)) S) =>
           branch_of_hfun
             (hcurry (fun xs => b (hmap (fun _ x => argF_map fst x) xs)))) bs)
).

Fixpoint ind_branch T (P : T -> Type) A : forall AT : arityT Type A,
  hfun (fun i => argF T (AT i)) T -> Type :=
  match A with
  | [::]       => fun AT C => P C
  | false :: A => fun AT C => forall x : _,        ind_branch P (C x)
  | true  :: A => fun AT C => forall x : T, P x -> ind_branch P (C x)
  end.

Fixpoint induction T (P : T -> Type) Σ : forall ΣT : signatureT Type Σ,
  constructors ΣT T -> Type :=
  match Σ with
  | A :: Σ => fun ΣT Cs => ind_branch P Cs.(hd) -> induction P Cs.(tl)
  | [::]   => fun ΣT Cs => forall x, P x
  end.

Lemma induction_eq Σ (ΣT1 ΣT2 : signatureT Type Σ) T (Cs : @constructors Σ ΣT1 T)
  (e : forall i j ijP, ΣT1 i j ijP = ΣT2 i j ijP) P :
  @induction T P Σ ΣT1 Cs -> induction P (cast id (constructors_eq e T) Cs).
Proof.
elim: Σ ΣT1 ΣT2 Cs e=> //= A Σ IH ΣT1 ΣT2 Cs e indP.
set e_None := hfun_eq (fun i => argF_eq T (e None i)) T.
rewrite (_ : (cast id _ Cs).(hd) = cast id e_None Cs.(hd)); last first.
  by rewrite /constructors_eq hlist_eq_hmap /=.
move=> b; have /indP {}b: ind_branch P Cs.(hd).
  move: b; rewrite {}/e_None.
  elim: {IH ΣT1 ΣT2 e Cs indP} A (ΣT1 None) (ΣT2 None) (e None) Cs.(hd)=> //=.
  move=> [] A IH AT1 AT2 e f b x => [xP|]; apply: (IH _ _ (fun i=> e (Some i))).
  - by move/(_ _ xP): b; rewrite /congr2 castD !cast_idE !castFE !castCE.
  - move/(_ (cast id (argF_eq T (e None)) x)): b.
    by rewrite /congr2 castD !cast_idE !castFE !castCE -castD etranspV /=.
move/(_ _ _ _ (fun i => e (Some i)) b): IH=> {b e_None indP}.
move: Cs; rewrite /constructors /= -[hlist _]/(constructors _ _); case=> C Cs /=.
set Cs' := cast id (constructors_eq _ T) Cs.
rewrite (_ : (cast id _ (C ::: Cs)).(tl) = Cs') // {}/Cs'.
move: Cs; rewrite /constructors_eq /= /constructors.
case: _ / (hlist_eq _) => /= Cs.
by case: _ / (hfun_eq _ _) C.
Qed.

End Basic.

Section ClassDef.

Variables (Σ : signature) (ΣT : signatureT Type Σ).

Record mixin_of T := Mixin {
  Cons      : constructors ΣT T;
  rec       : recursor ΣT T;
  case      : destructor ΣT T;
  _         : recursorE Cons rec;
  _         : destructorE Cons case;
  _         : forall P, induction P Cons;
}.

Record type := Pack {sort : Type; class : mixin_of sort}.
Variables (T : Type).
Definition recE (m : mixin_of T) : recursorE (Cons m) (rec m) :=
  let: Mixin _ _ _ recE _ _ := m in recE.
Definition caseE (m : mixin_of T) : destructorE (Cons m) (case m) :=
  let: Mixin _ _ _ _ caseE _ := m in caseE.
Definition indP (m : mixin_of T) :=
  let: Mixin _ _ _ _ _ indP := m
  return forall P : T -> Type, induction P (Cons m)
  in indP.

End ClassDef.

Definition cast Σ ΣT1 ΣT2 e (T : type ΣT1) : type ΣT2 :=
  @Pack Σ ΣT2 (sort T)
    (Mixin (@recursorE_eq Σ ΣT1 ΣT2 _ _ _ e (recE (class T)))
           (destructorE_eq e (caseE (class T)))
           (fun P => induction_eq e (indP (class T) P))).

Module Exports.
Coercion sort : type >-> Sortclass.
Coercion class : type >-> mixin_of.
Notation indType := type.
Notation IndType T m := (@Pack _ _ _ T m).
Notation IndMixin := Mixin.
End Exports.

End Ind.
Export Ind.Exports.

Section InferInstances.

Import PolyType.

Class infer_arity
  T (P : T -> Type)
  (branchT : Type) (A : arity) (AT : arityT Type A)
  (C : hfun (fun i => argF T (AT i)) T) : Type.
Arguments infer_arity : clear implicits.

Global Instance infer_arity_end
  T (P : T -> Type) (x : T) :
  infer_arity T P (P x) [::] (fun i => match i with end) x.
Defined.

Global Instance infer_arity_rec
  T (P : T -> Type)
  (branchT : T -> Type) (A : arity) (AT : arityT Type A)
  (C : T -> hfun (fun i => argF T (AT i)) T)
  (_ : forall x, infer_arity T P (branchT x) A AT (C x)) :
  infer_arity T P (forall x, P x -> branchT x)
  (true :: A) (fun i => if i is Some j then AT j else fun _ => unit) C.
Defined.

Global Instance infer_arity_nonrec
  T (P : T -> Type)
  S (branchT : S -> Type) A (AT : arityT Type A)
  (C : S -> hfun (fun i => argF T (AT i)) T)
  (_ : forall x, infer_arity T P (branchT x) A AT (C x)) :
  infer_arity T P (forall x, branchT x)
  (false :: A) (fun i => if i is Some j then AT j else fun _ => S) C.
Defined.

Class infer_sig
  T (P : T -> Type) (elimT : Type) Σ ΣT (Cs : @Ind.constructors Σ ΣT T) : Type.
Arguments infer_sig : clear implicits.

Global Instance infer_sig_end T (P : T -> Type) :
  infer_sig T P (forall x : T, P x) [::] (fun i => match i as j return arityT Type (nth_fin i) with end) tt.
Defined.

Global Instance infer_sig_branch
  T (P : T -> Type)
  (branchT : Type) A (AT : arityT Type A) C (_ : infer_arity T P branchT A AT C)
  (elimT : Type) (Σ : signature) ΣT Cs (_ : infer_sig T P elimT Σ ΣT Cs) :
  infer_sig T P (branchT -> elimT) (A :: Σ) (fun i => if i is Some j then ΣT j else AT) (C ::: Cs).
Defined.

End InferInstances.

Arguments infer_arity : clear implicits.
Arguments infer_sig : clear implicits.

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
    let ΣCs  := constr:((fun Σ ΣT Cs (_ : forall P : T -> Type, infer_sig T P (elimT P) Σ ΣT Cs) => (Σ, (ΣT, Cs))) _ _ _ _) in
    let Σ    := eval simpl in ΣCs.1 in
    let ΣT   := eval simpl in ΣCs.2.1 in
    let Cs   := eval simpl in ΣCs.2.2 in
    let case := constr:(ltac:(intros P; simpl; unwind_recursor (Rec P)) : forall P, elimT P) in
    let case := eval compute in (@Ind.destructor_of_recursor Σ ΣT T (fun S => case (fun _ => S))) in
    refine (@IndMixin Σ ΣT T Cs (fun S => Rec (fun _ => S)) case _ _ _);
    try by [abstract done|exact rec]
  end.

Notation "[ 'indMixin' 'for' rect ]" :=
  (ltac:(ind_mixin rect))
  (at level 0) : form_scope.

Set Typeclasses Debug.
Set Typeclasses Debug Verbosity 2.

Definition baz:= (fun P =>
  @infer_sig_branch unit P (P tt) _ _ _ _ (forall x, P x) _ _ _ _).

Definition bar := ((fun A AT C & (forall (P : unit -> Type), infer_arity unit P (P tt) A AT C) => C) _ _ _ _).

Unset Printing All.

Check
(fun Σ ΣT Cs & (forall P : unit -> Type, infer_sig unit P (P tt -> forall c : unit, P c) Σ ΣT Cs) => Cs) _ _ _ _.

Check (fun P => erefl : infer_sig _ _ (forall x : _, _ x) PolyType.nil
   (fun i : fin (PolyType.size PolyType.nil) => match i as i0 return (arityT Type (nth_fin i0)) with
                                                end) tt = infer_sig unit P (forall c : unit, P c)
                                                                _
                                                                (fun c : fin (PolyType.size _) => [eta _ c])
                                                                _).



Definition foo :=
(fun Σ ΣT Cs & (forall P : unit -> Type, infer_sig unit P (P tt -> forall c : unit, P c) Σ ΣT Cs) => Cs) _ _ _ _.

Definition foo := ((fun Σ ΣT Cs (_ : forall P : comparison -> Type, infer_sig comparison P (P Eq -> P Lt -> P Gt -> forall c : comparison, P c) Σ ΣT Cs) => (Σ, (ΣT, Cs))) _ _ _ _).

Unset Ltac Debug.

Definition comparison_indMixin :=
  Eval simpl in [indMixin for comparison_rect].
Canonical comparison_indType :=
  Eval hnf in IndType _ comparison comparison_indMixin.

Module IndF.

Section TypeDef.

Variables (Σ : signature) (ΣT : signatureT Type Σ).

Notation size := PolyType.size.

Record fobj T := Cons {
  constr : fin (size Σ);
  args : hlist (fun i => argF T (@ΣT constr i));
}.
Arguments Cons {_} _ _.

Local Notation F := fobj.

Definition fmap T S (f : T -> S) (x : F T) : F S :=
  Cons (constr x) (hmap (fun _ x => argF_map f x) (args x)).

Lemma fmap_eq T S (f g : T -> S) : f =1 g -> fmap f =1 fmap g.
Proof.
move=> e [i xs]; congr Cons; apply: hmap_eq=> /= j x.
by case: (nth_fin j) (@ΣT _ j) x.
Qed.

Lemma fmap1 T : @fmap T T id =1 id.
Proof.
move=> [i args] /=; congr Cons; rewrite -[RHS]hmap1.
apply: hmap_eq=> /= j x; by case: (nth_fin j) (@ΣT _ j) x.
Qed.

Lemma fmap_comp T S R (f : T -> S) (g : S -> R) :
  fmap (g \o f) =1 fmap g \o fmap f.
Proof.
move=> [i args] /=; congr Cons; rewrite /= hmap_comp.
apply: hmap_eq=> /= j x; by case: (nth_fin j) (@ΣT _ j) x.
Qed.

Canonical functor := Functor fmap_eq fmap1 fmap_comp.

Lemma inj T (i : fin (size Σ)) (a b : hlist (fun i => argF T (@ΣT _ i))) :
  Cons i a = Cons i b -> a = b.
Proof.
pose get x :=
  if leq_fin (constr x) i is inl e then
    cast (fun j : fin (size Σ) => hlist (fun i => argF T (@ΣT j i))) e (args x)
  else a.
by move=> /(congr1 get); rewrite /get /= leq_finii /=.
Qed.

Variable T : indType ΣT.

Definition Roll (x : F T) : T :=
  hnth (@Ind.Cons _ _ _ T) (constr x) (args x).

Definition branches_of_fun S (body : F (T * S) -> S) :=
  hlist_of_fun (fun i =>
    Ind.branch_of_hfun
      (hcurry
         (fun l => body (Cons i l)))).

Definition rec S (body : F (T * S) -> S) :=
  happ (@Ind.rec _ _ _ T S) (branches_of_fun body).

Definition case S (body : F T -> S) :=
  @Ind.case _ _ _ T S
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
  elim: (Σ) (ΣT) Cs {indP} (indP P) => //= As Σ' IH ΣT' [C Cs] /= indP hyps.
  move/indP/IH: (hyps None); apply=> i; exact: (hyps (Some i)).
move=> hyps; apply: indP=> j.
have {}hyps:
  forall args : hlist (fun i => argF {x : S & P x} (@ΣT _ i)),
    P (hnth Cs j (hmap (fun _ x => argF_map tag x) args)).
  by move=> args; move: (hyps (Cons j args)).
move: (hnth Cs j) hyps=> /=; elim: (nth_fin j) (@ΣT j) => [|[] /= A IH] AT //=.
- by move=> ? /(_ tt).
- move=> C hyps x H; apply: IH=> args.
  exact: (hyps (existT _ x H ::: args)).
- move=> C hyps x; apply: IH=> args; exact: (hyps (x ::: args)).
Qed.

Canonical initAlgType :=
  Eval hnf in InitAlgType functor T (InitAlgMixin recE caseE indP).

End TypeDef.

End IndF.

Canonical IndF.functor.
Canonical IndF.initAlgType.
Coercion IndF.initAlgType : indType >-> initAlgType.

Module DerEqType.

Section EqType.

Variable (Σ : signature) (ΣT : signatureT eqType Σ).
Let F := IndF.functor ΣT.
Variable (T : initAlgType F).

Import PolyType.

Fixpoint eq_op_branch A :
  forall (AT : arityT eqType A),
  hlist (fun i => argF (T * (T -> bool)) (AT i)) ->
  hlist (fun i => argF  T                (AT i)) ->
  bool :=
  match A with
  | [::]       => fun AT _ _ => true
  | true  :: A => fun AT x y =>  x.(hd).2  y.(hd)  && eq_op_branch x.(tl) y.(tl)
  | false :: A => fun AT x y => (x.(hd) == y.(hd)) && eq_op_branch x.(tl) y.(tl)
  end.

Let eq_op : T -> T -> bool :=
  rec  (fun args1 =>
  case (fun args2 =>
          match leq_fin (IndF.constr args2) (IndF.constr args1) with
          | inl e =>
            eq_op_branch (IndF.args args1)
              (cast (fun c => hlist (fun i => argF T (@ΣT c i))) e (IndF.args args2))
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
apply/(@iffP (hmap (fun _ x => argF_map tag x) xargs = yargs)); first last.
- by move=> /Roll_inj /IndF.inj.
- by move=> <-.
elim: {yi} (nth_fin yi) (@ΣT yi) xargs yargs=> [|[] A IH] /= AT.
- by move=> _ []; constructor.
- move=> [[x xP] xs] [y ys] /=.
  apply/(iffP andP)=> [[/xP -> /IH -> //]|[/xP ? /IH ?]].
  by eauto.
- move=> [/= x xs] [/= y ys].
  apply/(iffP andP)=> [[/eqP -> /IH -> //]|[/eqP ? /IH]];
  by eauto.
Qed.

End EqType.

Definition pack :=
  fun (T : Type) =>
  fun Σ (ΣT : signatureT Type Σ) (sT : indType ΣT) & phant_id (Ind.sort sT) T =>
  let F := (fun (F : fin (PolyType.size Σ) -> preorder) &
                phant_id (forall c, po_untag (po_sort (F c))) (forall c : fin (PolyType.size Σ), arityT Type (nth_fin c)) => F) _ id in
  fun (sΣT : @class_lift (PolyType.size Σ) (fun c => arityT eqType (nth_fin c)) F (fun=> id)) & phant_id (cl_untag (cl_fun sΣT)) ΣT =>
  fun (cT : Ind.mixin_of sΣT T) & phant_id (Ind.class sT) cT =>
    ltac:(
      let ax := constr:(@eq_opP Σ (cl_funL sΣT) (Ind.cast (fun i j k => (cl_funP sΣT i j k)^-1) (Ind.Pack cT))) in
      match type of ax with
      | Equality.axiom ?e =>
        let e' := eval compute -[eq_op Equality.sort andb] in e in
        exact: @EqMixin T e' ax
      end).

Module Import Exports.
Notation "[ 'derive' 'eqMixin' 'for' T ]" :=
  (let m := @pack T _ _ _ id _ id _ id in
   ltac:(
     let x := eval hnf in m in
     exact x))
  (at level 0) : form_scope.
End Exports.

End DerEqType.

Export DerEqType.Exports.

Definition comparison_indMixin :=
  Eval simpl in [indMixin for comparison_rect].
Canonical comparison_indType :=
  Eval hnf in IndType _ comparison comparison_indMixin.
Definition comparison_eqMixin :=
  Eval simpl in [derive eqMixin for comparison].
Canonical comparison_eqType :=
  Eval hnf in EqType comparison comparison_eqMixin.
Definition comparison_choiceMixin :=
  Eval simpl in [derive choiceMixin for comparison].
Canonical comparison_choiceType :=
  Eval hnf in ChoiceType comparison comparison_choiceMixin.
Definition comparison_countMixin :=
  Eval simpl in [derive countMixin for comparison].
Canonical comparison_countType :=
  Eval hnf in CountType comparison comparison_countMixin.
Definition comparison_finMixin :=
  Eval simpl in [derive finMixin for comparison].
Canonical comparison_finType :=
  Eval hnf in FinType comparison comparison_finMixin.


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

Section TreeOfInd.

Variables (Σ : signature).
Let F := IndF.functor Σ.
Variables (T : initAlgType F).

Import GenTree.
Import PolyType.

Definition ind_arg :=
  hsum (fnth (fun As => hsum (fnth (type_of_arg void) As)) Σ).

Definition mk_ind_arg (i : fin (size Σ)) (j : fin (size (nth_fin i))) :
  type_of_arg void (nth_fin j) -> ind_arg :=
  fun x => hin (hin x).

Definition proj_ind_arg
  (i : fin (size Σ)) (j : fin (size (nth_fin i))) (x : ind_arg) :
  option (type_of_arg void (nth_fin j)) :=
  hcase (fun i' =>
    if leq_fin i' i is inl e then
      match e^-1 in _ = i'
      return hsum (fnth (type_of_arg void) (nth_fin i')) -> option _ with
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
  | Rec      => fun c x => x
  end (@mk_ind_arg i j).

Definition tree_of_coq_ind (x : T) : tree ind_arg :=
  rec (fun x =>
         let i := IndF.constr x in
         Node (nat_of_fin i)
           (list_of_seq (seq_of_hlist (@wrap i)
              (hmap (fun _ x => type_of_arg_map snd x) (IndF.args x))))) x.

Fixpoint coq_ind_of_tree (x : tree ind_arg) : option T :=
  match x with
  | Leaf _ => None
  | Node c xs =>
    if fin_of_nat (size Σ) c is Some i then
      let xs := seq_of_list [seq (t, coq_ind_of_tree t) | t <- xs] in
      if hlist_of_seq (fun j ts =>
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
set xs' := hlist_of_seq _ _.
suffices -> : xs' = Some (hmap (fun _ x => type_of_arg_map tag x) xs) by [].
rewrite {}/xs' seq_of_list_map list_of_seqK hlist_of_seq_map /= /wrap.
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

Notation "[ 'derive' 'choiceMixin' 'for' T ]" :=
  (PcanChoiceMixin (@pack_tree_of_indK T _ _ id))
  (at level 0, format "[ 'derive'  'choiceMixin'  'for'  T ]") : form_scope.

Notation "[ 'derive' 'countMixin' 'for' T ]" :=
  (PcanCountMixin (@pack_tree_of_indK T _ _ id))
  (at level 0, format "[ 'derive' 'countMixin'  'for'  T ]") : form_scope.

Module DerFinType.

Import PolyType.

Section FinType.

Fixpoint allP T (P : T -> bool) (xs : seq T) :
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
    _ (fun As => all (negb \o is_rec) As -> seq.seq (hlist (fnth (type_of_arg T) As)))
    (fun _ => [:: tt]%SEQ)
    (fun S As rec P => allpairs Cell (Finite.enum S) (rec P))
    (fun   As rec P => ltac:(done)).

Definition enum_ind :=
  flatten [seq [seq Roll (IndF.Cons args)
               | args <- enum_branch (hnth (sig_inst_class Σ) i) (allP not_rec i)]
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
  elim/arity_ind: {i} _ / (hnth _ i) xs (allP _ _)=> //=.
    by move=> [] _ P /(_ tt); case.
  move=> S As cAs IH [x xs] As_not_rec P PP.
  elim: (Finite.enum S) (enumP x)=> //= y ys IHys.
  have [-> {y} [e]|ne] := altP (y =P x).
    rewrite count_cat count_map (IH xs); last first.
      by move=> zs; apply/(iffP (PP (x ::: zs)))=> [[->]|->].
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
Notation "[ 'derive' 'finMixin' 'for' T ]" :=
  (let m := @pack T _ _ id _ _ id _ id _ id erefl in
   ltac:(
     let x := eval hnf in m in
     exact x))
  (at level 0, format "[ 'derive'  'finMixin'  'for'  T ]") : form_scope.
End Exports.

End DerFinType.
Export DerFinType.Exports.

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
  Eval simpl in [derive eqMixin for comparison].
Canonical comparison_eqType :=
  Eval hnf in EqType comparison comparison_eqMixin.
Definition comparison_choiceMixin :=
  Eval simpl in [derive choiceMixin for comparison].
Canonical comparison_choiceType :=
  Eval hnf in ChoiceType comparison comparison_choiceMixin.
Definition comparison_countMixin :=
  Eval simpl in [derive countMixin for comparison].
Canonical comparison_countType :=
  Eval hnf in CountType comparison comparison_countMixin.
Definition comparison_finMixin :=
  Eval simpl in [derive finMixin for comparison].
Canonical comparison_finType :=
  Eval hnf in FinType comparison comparison_finMixin.

Definition positive_indMixin :=
  Eval simpl in [indMixin for positive_rect].
Canonical positive_indType :=
  Eval hnf in IndType _ positive positive_indMixin.
Definition positive_eqMixin :=
  Eval simpl in [derive eqMixin for positive].
Canonical positive_eqType :=
  Eval hnf in EqType positive positive_eqMixin.
Definition positive_choiceMixin :=
  Eval simpl in [derive choiceMixin for positive].
Canonical positive_choiceType :=
  Eval hnf in ChoiceType positive positive_choiceMixin.
Definition positive_countMixin :=
  Eval simpl in [derive countMixin for positive].
Canonical positive_countType :=
  Eval hnf in CountType positive positive_countMixin.

Definition bin_nat_indMixin :=
  Eval simpl in [indMixin for N_rect].
Canonical bin_nat_indType :=
  Eval hnf in IndType _ N bin_nat_indMixin.
Definition bin_nat_choiceMixin :=
  Eval simpl in [derive choiceMixin for N].
Canonical bin_nat_choiceType :=
  Eval hnf in ChoiceType N bin_nat_choiceMixin.
Definition bin_nat_countMixin :=
  Eval simpl in [derive countMixin for N].
Canonical bin_nat_countType :=
  Eval hnf in CountType N bin_nat_countMixin.

Definition Z_indMixin :=
  Eval simpl in [indMixin for Z_rect].
Canonical Z_indType :=
  Eval hnf in IndType _ Z Z_indMixin.
Definition Z_eqMixin :=
  Eval simpl in [derive eqMixin for Z].
Canonical Z_eqType :=
  Eval hnf in EqType Z Z_eqMixin.
Definition Z_choiceMixin :=
  Eval simpl in [derive choiceMixin for Z].
Canonical Z_choiceType :=
  Eval hnf in ChoiceType Z Z_choiceMixin.
Definition Z_countMixin :=
  Eval simpl in [derive countMixin for Z].
Canonical Z_countType :=
  Eval hnf in CountType Z Z_countMixin.

Definition ascii_indMixin :=
  Eval simpl in [indMixin for ascii_rect].
Canonical ascii_indType :=
  Eval hnf in IndType _ ascii ascii_indMixin.
Definition ascii_eqMixin :=
  Eval simpl in [derive eqMixin for ascii].
Canonical ascii_eqType :=
  Eval hnf in EqType ascii ascii_eqMixin.
Definition ascii_choiceMixin :=
  Eval simpl in [derive choiceMixin for ascii].
Canonical ascii_choiceType :=
  Eval hnf in ChoiceType ascii ascii_choiceMixin.
Definition ascii_countMixin :=
  Eval simpl in [derive countMixin for ascii].
Canonical ascii_countType :=
  Eval hnf in CountType ascii ascii_countMixin.
Definition ascii_finMixin :=
  Eval simpl in [derive finMixin for ascii].
Canonical ascii_finType :=
  Eval hnf in FinType ascii ascii_finMixin.

Definition string_indMixin :=
  Eval simpl in [indMixin for string_rect].
Canonical string_indType :=
  Eval hnf in IndType _ string string_indMixin.
Definition string_eqMixin :=
  Eval simpl in [derive eqMixin for string].
Canonical string_eqType :=
  Eval hnf in EqType string string_eqMixin.
Definition string_choiceMixin :=
  Eval simpl in [derive choiceMixin for string].
Canonical string_choiceType :=
  Eval hnf in ChoiceType string string_choiceMixin.
Definition string_countMixin :=
  Eval simpl in [derive countMixin for string].
Canonical string_countType :=
  Eval hnf in CountType string string_countMixin.

End Instances.
