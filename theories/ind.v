From mathcomp Require Import
  ssreflect ssrfun ssrbool ssrnat eqtype seq choice fintype.

From deriving Require Import base.

From Coq Require Import ZArith NArith String Ascii.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Open Scope deriving_scope.

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

Hint Unfold fs_fun : deriving.
Hint Unfold fsE1 : deriving.
Hint Unfold fsE2 : deriving.
Hint Unfold fun_split1 : deriving.

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

Definition lift_class_proj n cK
           (class : forall sT, cK (sort sT))
           (sTs : lift_class n) (i : fin n)
  : cK (sTs i) :=
  cast cK (svalP (lift_class_class sTs i)) (class _).

End LiftClass.

Hint Unfold eq_class : deriving.
Hint Unfold untag_sort : deriving.
Hint Unfold ts_nil_tag : deriving.
Hint Unfold ts_cons_tag : deriving.
Hint Unfold lift_class_sort : deriving.
Hint Unfold lift_class_class : deriving.
Hint Unfold nil_lift_class : deriving.
Hint Unfold cons_lift_class : deriving.
Hint Unfold lift_class_proj : deriving.

Arguments lift_class_proj {K sort n cK} class sTs i.

Notation "T -F> S" :=
  (forall i, T i -> S i)
  (at level 30, only parsing, no associativity)
  : deriving_scope.

Notation "T *F S"  :=
  (fun i => T i * S i)%type
  (at level 20, only parsing, no associativity)
  : deriving_scope.

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

Definition arity        := seq arg.
Definition signature    := seq arity.
Definition declaration  := fin n -> signature.

Identity Coercion seq_of_arity : arity >-> seq.
Identity Coercion seq_of_sig   : signature >-> seq.

Definition empty_decl : declaration :=
  fun _ => [::].

Definition add_arity (D : declaration) i As : declaration :=
  fun j => if leq_fin i j is inl _ then As :: D i
           else D j.

Definition add_arity_ind (P : fin n -> signature -> Type) D i As j :
  P i (As :: D i) -> P j (D j) -> P j (add_arity D i As j) :=
  fun H1 H2 =>
    match leq_fin i j
    as X
    return P j (if X is inl _ then As :: D i else D j) with
    | inl e => cast (fun k => P k (As :: D i)) e H1
    | inr _ => H2
    end.

Variables (K : Type) (sort : K -> Type).

Definition arg_class A :=
  if A is NonRec T then eq_class sort T else unit.

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

Record tagged_decl k := TaggedDecl {
  untag_decl :> fin k -> signature;
}.

Record decl_inst k := DeclInst {
  decl_inst_sort  :> tagged_decl k;
  _               :  forall i, sig_class (decl_inst_sort i)
}.
Arguments DeclInst : clear implicits.

Definition decl_inst_class k (d : decl_inst k) :
  forall i, sig_class (@decl_inst_sort k d i) :=
  let: DeclInst _ d := d in d.

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

Definition nil_decl_tag k (D : fin k -> signature) := TaggedDecl D.
Canonical cons_decl_tag k (D : fin k -> signature) := nil_decl_tag D.

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

Hint Unfold type_of_arg : deriving.
Hint Unfold type_of_arg_map : deriving.
Hint Unfold is_rec : deriving.
Hint Unfold arity : deriving.
Hint Unfold signature : deriving.
Hint Unfold declaration : deriving.
Hint Unfold empty_decl : deriving.
Hint Unfold add_arity : deriving.
Hint Unfold add_arity_ind : deriving.
Hint Unfold arg_class : deriving.
Hint Unfold arg_inst_sort : deriving.
Hint Unfold arg_inst_class : deriving.
Hint Unfold arity_class : deriving.
Hint Unfold arity_inst_sort : deriving.
Hint Unfold arity_inst_class : deriving.
Hint Unfold sig_class : deriving.
Hint Unfold sig_inst_sort : deriving.
Hint Unfold sig_inst_class : deriving.
Hint Unfold untag_decl : deriving.
Hint Unfold decl_inst_sort : deriving.
Hint Unfold decl_inst_class : deriving.
Hint Unfold NonRec_arg_inst : deriving.
Hint Unfold Rec_arg_inst : deriving.
Hint Unfold nth_fin_arg_inst : deriving.
Hint Unfold nil_arity_inst : deriving.
Hint Unfold cons_arity_inst : deriving.
Hint Unfold nil_sig_inst : deriving.
Hint Unfold cons_sig_inst : deriving.
Hint Unfold nil_decl_tag : deriving.
Hint Unfold cons_decl_tag : deriving.
Hint Unfold nil_decl_inst : deriving.
Hint Unfold cons_decl_inst : deriving.
Hint Unfold arity_rec : deriving.

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

Definition pack_decl_inst
  n (D : declaration n) (Di : decl_inst n Equality.sort n)
  of phant_id D (untag_decl (decl_inst_sort Di)) := Di.

Unset Universe Polymorphism.

Arguments add_arity_ind {n} P D i As j H1 H2.
Arguments empty_decl {n}.
Arguments arity_rec {n K} _ _ _ _ _.

Module Ind.

Section Basic.

Variable n : nat.
Implicit Types (A : arg n) (As : arity n) (Σ : signature n).
Implicit Types (D : declaration n).
Implicit Types (T S : fin n -> Type).

Import PolyType.

Definition Cidx D i := fin (size (D i)).
Arguments Cidx : clear implicits.

Definition args D T i (j : Cidx D i) : Type :=
  hlist' (type_of_arg T) (nth_fin j).

Definition args_map D T S (f : T -F> S) i j (xs : @args D T i j) :
  args S j :=
  hmap' (type_of_arg_map f) xs.

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

Fixpoint rec_branch' T S i As : Type :=
  match As with
  | NonRec X :: As => X          -> rec_branch' T S i As
  | Rec    j :: As => T j -> S j -> rec_branch' T S i As
  | [::]           => S i
  end.

Definition rec_branch D T S i (j : Cidx D i) : Type :=
  rec_branch' T S i (nth_fin j).


Definition recursor D T :=
  forall S, hfun2 (@rec_branch D T S) (hlist1 (fun i => T i -> S i)).

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

Definition rec_of_des_branch D T S i (j : Cidx D i) (b : des_branch T S j) :
  rec_branch T S j :=
  rec_branch'_of_hfun' (hcurry (fun xs => b (args_map (fun _ => fst) xs))).

Definition destructor_of_recursor D T (r : recursor D T) : destructor D T :=
  fun S => hcurry2 (fun bs : hlist2 (@des_branch D T S) =>
    r S (hmap2 (@rec_of_des_branch D T S) bs)).

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

Section ClassDef.

Variables (n : nat).

Record def_class_of sorts := DefClass {
  decl      : declaration n;
  Cons      : constructors decl sorts;
  rec       : recursor decl sorts;
  case      : destructor decl sorts;
  recE      : recursor_eq Cons rec;
  caseE     : destructor_eq Cons case;
  indP      : induction Cons;
}.

Record def := Def {
  sorts     : fin n -> Type;
  def_class : def_class_of sorts;
}.

Import PolyType.

Record mixin_of T := Mixin {
  mixin_def : def;
  mixin_idx : {i : fin n | T = sorts mixin_def i}
}.

Record type := Pack {sort : Type; _ : mixin_of sort}.
Local Coercion sort : type >-> Sortclass.
Local Notation class_of := mixin_of.

Variables (T : Type) (cT : type).
Definition class := let: Pack _ c as cT' := cT return class_of cT' in c.
Definition clone c of phant_id class c := @Pack T c.
Let xT := let: Pack T _ := cT in T.
Notation xclass := (class : class_of xT).

End ClassDef.

Notation class_of := mixin_of.

Module Exports.
Identity Coercion hdfun_of_induction : induction >-> hdfun.
Coercion sorts : def >-> Funclass.
Coercion def_class : def >-> def_class_of.
Notation indDef := def.
Notation IndDef := Def.
Coercion sort : type >-> Sortclass.
Coercion class : type >-> class_of.
Coercion mixin_def : class_of >-> def.
Notation indType := type.
End Exports.

End Ind.
Export Ind.Exports.

Section IndTheory.

Variables (n : nat).

Import PolyType.

Definition type_idx (T : indType n) : fin n :=
  sval (Ind.mixin_idx T).

Definition type_idxP (T : indType n) : T = T (type_idx T) :> Type :=
  svalP (Ind.mixin_idx T).

End IndTheory.

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

Hint Extern 1 (find_idx ?n.+1 ?Ts ?T _ _) =>
  eapply (@find_idx_here n Ts) : typeclass_instances.

Hint Extern 2 (find_idx ?n.+1 ?Ts ?T _ _) =>
  eapply (@find_idx_there n Ts) : typeclass_instances.

Definition pack_indType
  n T (Ts : indDef n) i e
  of find_idx n Ts T i e :=
  Ind.Pack (@Ind.Mixin n T Ts (PolyType.exist _ i e)).

Notation IndType T Ts := (@pack_indType _ T Ts _ _ _).

Hint Unfold Ind.Cidx : deriving.
Hint Unfold Ind.args : deriving.
Hint Unfold Ind.args_map : deriving.
Hint Unfold Ind.constructors : deriving.
Hint Unfold Ind.empty_cons : deriving.
Hint Unfold Ind.add_cons : deriving.
Hint Unfold Ind.rec_branch' : deriving.
Hint Unfold Ind.rec_branch : deriving.
Hint Unfold Ind.recursor : deriving.
Hint Unfold Ind.rec_branch'_of_hfun' : deriving.
Hint Unfold Ind.hfun'_of_rec_branch' : deriving.
Hint Unfold Ind.recursor_eq : deriving.
Hint Unfold Ind.des_branch : deriving.
Hint Unfold Ind.destructor : deriving.
Hint Unfold Ind.destructor_eq : deriving.
Hint Unfold Ind.rec_of_des_branch : deriving.
Hint Unfold Ind.destructor_of_recursor : deriving.
Hint Unfold Ind.ind_branch' : deriving.
Hint Unfold Ind.ind_branch : deriving.
Hint Unfold Ind.induction : deriving.
Hint Unfold Ind.decl : deriving.
Hint Unfold Ind.Cons : deriving.
Hint Unfold Ind.rec : deriving.
Hint Unfold Ind.case : deriving.
Hint Unfold Ind.sorts : deriving.
Hint Unfold Ind.def_class : deriving.
Hint Unfold Ind.class : deriving.
Hint Unfold Ind.mixin_def : deriving.
Hint Unfold Ind.mixin_idx : deriving.
Hint Unfold Ind.sort : deriving.
Hint Unfold type_idx : deriving.
Hint Unfold type_idxP : deriving.
Hint Unfold find_idx_here : deriving.
Hint Unfold find_idx_there : deriving.
Hint Unfold pack_indType : deriving.

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

Variables (n : nat) (T : indDef n).

Notation D := (Ind.decl T).
Notation F := (@fobj n D).

Arguments Cons {n D T i} _ _.

Definition Roll i (x : F T i) : T i :=
  @Ind.Cons _ _ T i (constr x) (args x).

Definition rec_branches_of_fun S (body : F (T *F S) -F> S) :
  hlist2 (@Ind.rec_branch _ D T S) :=
  hlist_of_fun (fun i =>
  hlist_of_fun (fun j : Ind.Cidx D i =>
    Ind.rec_branch'_of_hfun'
      (hcurry
         (fun l => body i (Cons j l))))).

Definition rec S (body : F (T *F S) -F> S) :=
  @Ind.rec _ _ T S (rec_branches_of_fun body).

Definition lift_type R i : fin n -> Type :=
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
    (@Ind.case _ _ T _ (des_branches_of_fun body) i x).

Lemma recE S f i (a : F T i) :
  @rec S f i (Roll a) =
  f i (fmap (fun j (x : T j) => (x, rec f j x)) a).
Proof.
case: a=> [j args]; have := Ind.recE T S.
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
case: a => [j args]; have := Ind.caseE T (lift_type R i).
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
rewrite /Roll; case: (T) => S [/= D Cs _ _ _ _ indP] P.
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

Hint Unfold IndF.constr : deriving.
Hint Unfold IndF.args : deriving.
Hint Unfold IndF.fmap : deriving.
Hint Unfold IndF.Roll : deriving.
Hint Unfold IndF.rec_branches_of_fun : deriving.
Hint Unfold IndF.rec : deriving.
Hint Unfold IndF.lift_type : deriving.
Hint Unfold IndF.lift_typeE : deriving.
Hint Unfold IndF.lift_type_of : deriving.
Hint Unfold IndF.des_branches_of_fun : deriving.
Hint Unfold IndF.case : deriving.
Hint Unfold IndF.unroll : deriving.

Module IndClass.

Section ClassDef.

Variables (n : nat) (K : Type) (KS : K -> Type).

Record class_of T := Class {
  base  : @Ind.def_class_of n T;
  mixin : forall i, @sig_class n K KS (Ind.decl base i);
}.

Record def := Def {sorts : fin n -> Type; _ : class_of sorts}.
Local Coercion sorts : def >-> Funclass.

Variables (T : fin n -> Type) (cT : def).
Definition class := let: Def _ c as cT' := cT return class_of cT' in c.
Definition clone c of phant_id class c := @Def T c.
Let xT := let: Def T _ := cT in T.
Notation xclass := (class : class_of xT).

Definition indDef := Ind.Def (base class).

End ClassDef.

Module Exports.
Coercion sorts : def >-> Funclass.
Coercion class : def >-> class_of.
Coercion base  : class_of >-> Ind.def_class_of.
Coercion indDef : def >-> Ind.def.
Canonical indDef.
Notation indClassDef := def.
Notation IndClassDef := Def.
End Exports.
End IndClass.

Export IndClass.Exports.

Hint Unfold IndClass.base : deriving.
Hint Unfold IndClass.mixin : deriving.
Hint Unfold IndClass.sorts : deriving.
Hint Unfold IndClass.class : deriving.
Hint Unfold IndClass.indDef : deriving.

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
  infer_arity n T P (forall x, branchT x) (NonRec n S :: As) i C.
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

Hint Unfold infer_arity_end : deriving.
Hint Unfold infer_arity_rec : deriving.
Hint Unfold infer_arity_nonrec : deriving.
Hint Unfold infer_decl_end : deriving.
Hint Unfold infer_decl_cons : deriving.
Hint Unfold read_rect_type : deriving.
Hint Unfold read_rect_done : deriving.
Hint Unfold do_infer_ind : deriving.

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

Hint Extern 0 (infer_arity _ _ _ _ _ _ _) => infer_arity : typeclass_instances.

Ltac infer_decl :=
  cbv beta;
  match goal with
  | |- infer_decl ?n ?Ts ?Ps (?branchT -> ?rectT) _ _ =>
    eapply (@infer_decl_cons n Ts Ps branchT _ _ _ _ rectT)
  | |- infer_decl ?n ?Ts ?Ps _ _ _ =>
    eapply (@infer_decl_end n Ts Ps)
  end.

Hint Extern 0 (infer_decl _ _ _ _ _ _) => infer_decl : typeclass_instances.

Ltac bless_rect :=
  cbv beta;
  match goal with
  | |- bless_rect ?n ?Ts ?D ?Cs ?rectT ?rect _ =>
     exact (@Build_bless_rect n Ts D Cs rectT rect
                             (fun P => rect (fun i _ => P i)))
  end.

Hint Extern 0 (bless_rect _ _ _ _ _ _ _) => bless_rect : typeclass_instances.

Module IndEqType.

Record type n := Pack {
  sort      : fin n -> Type;
  eq_class  : forall i, Equality.class_of (sort i);
  ind_class : Ind.def_class_of sort;
}.

Definition eqType n (T : type n) (i : fin n) :=
  Equality.Pack (eq_class T i).
Definition indDef n (T : type n) :=
  Ind.Def (ind_class T).

Module Import Exports.
Notation indEqType := type.
Notation IndEqType := Pack.
Coercion sort : type >-> Funclass.
Canonical eqType.
Coercion indDef : type >-> Ind.def.
Canonical indDef.
End Exports.

End IndEqType.

Export IndEqType.Exports.

Hint Unfold IndEqType.sort : deriving.
Hint Unfold IndEqType.eq_class : deriving.
Hint Unfold IndEqType.ind_class : deriving.
Hint Unfold IndEqType.eqType : deriving.
Hint Unfold IndEqType.indDef : deriving.

Module IndChoiceType.

Record type n := Pack {
  sort         : fin n -> Type;
  choice_class : forall i, Choice.class_of (sort i);
  ind_class    : Ind.def_class_of sort;
}.

Definition eqType n (T : type n) (i : fin n) := Equality.Pack (choice_class T i).
Definition choiceType n (T : type n) (i : fin n) := Choice.Pack (choice_class T i).
Definition indDef n (T : type n) := Ind.Def (ind_class T).

Module Import Exports.
Notation indChoiceType := type.
Notation IndChoiceType := Pack.
Coercion sort : type >-> Funclass.
Canonical eqType.
Canonical choiceType.
Coercion indDef : type >-> Ind.def.
Canonical indDef.
End Exports.

End IndChoiceType.

Export IndChoiceType.Exports.

Hint Unfold IndChoiceType.sort : deriving.
Hint Unfold IndChoiceType.choice_class : deriving.
Hint Unfold IndChoiceType.ind_class : deriving.
Hint Unfold IndChoiceType.eqType : deriving.
Hint Unfold IndChoiceType.choiceType : deriving.
Hint Unfold IndChoiceType.indDef : deriving.

Module IndCountType.

Record type n := Pack {
  sort        : fin n -> Type;
  count_class : forall i, Countable.class_of (sort i);
  ind_class   : Ind.def_class_of sort;
}.

Definition eqType n (T : type n) (i : fin n) := Equality.Pack (count_class T i).
Definition choiceType n (T : type n) (i : fin n) := Choice.Pack (count_class T i).
Definition countType n (T : type n) (i : fin n) := Countable.Pack (count_class T i).
Definition indDef n (T : type n) := Ind.Def (ind_class T).

Module Import Exports.
Notation indCountType := type.
Notation IndCountType := Pack.
Coercion sort : type >-> Funclass.
Canonical eqType.
Canonical choiceType.
Canonical countType.
Coercion indDef : type >-> Ind.def.
Canonical indDef.
End Exports.

End IndCountType.

Export IndCountType.Exports.

Hint Unfold IndCountType.sort : deriving.
Hint Unfold IndCountType.count_class : deriving.
Hint Unfold IndCountType.ind_class : deriving.
Hint Unfold IndCountType.eqType : deriving.
Hint Unfold IndCountType.choiceType : deriving.
Hint Unfold IndCountType.countType : deriving.
Hint Unfold IndCountType.indDef : deriving.
