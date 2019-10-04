From mathcomp Require Import
  ssreflect ssrfun ssrbool ssrnat eqtype seq choice fintype.

From void Require Import void.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition cast T (P : T -> Type) x y (e : x = y) : P x -> P y :=
  match e with erefl => id end.

Arguments cast {_} _ {_ _} _.

Local Notation "e1 * e2" := (etrans e1 e2).
Local Notation "e ^-1" := (esym e).

(* The ssreflect definition is opaque, which interferes with some reductions. *)
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
Proof. by elim/indP=> args; rewrite RollK. Qed.

Lemma unroll_inj : injective unroll.
Proof. exact: can_inj unrollK. Qed.

End IndTheory.

Fixpoint fin n :=
  if n is n.+1 then option (fin n) else Empty_set.

Fixpoint all_fin n : (fin n -> Prop) -> Prop :=
  match n with
  | 0    => fun P => True
  | n.+1 => fun P => P None /\ @all_fin n (fun i => P (Some i))
  end.

Lemma all_finP n (P : fin n -> Prop) : all_fin P <-> (forall i, P i).
Proof.
split; elim: n P=> [|n IH] P //=.
- case=> ? H [i|] //; exact: (IH (fun i => P (Some i))).
- by move=> H; split; [exact: (H None)|apply: IH; eauto].
Qed.

Fixpoint nth_fin T (xs : seq T) : fin (size xs) -> T :=
  match xs with
  | [::]    => fun n => match n with end
  | x :: xs => fun n => if n is Some n then nth_fin n else x
  end.

Fixpoint leq_fin n : forall i j : fin n, (i = j) + bool :=
  match n with
  | 0    => fun i => match i with end
  | n.+1 =>
    fun i =>
      match i return forall j, (i = j) + bool with
      | None    => fun j => if j is None then inl erefl else inr true
      | Some i' => fun j => if j is Some j' then
                              match leq_fin i' j' with
                              | inl e => inl (f_equal Some e)
                              | inr b => inr b
                              end
                            else inr false
      end
  end.

Lemma leq_finii n i : @leq_fin n i i = inl erefl.
Proof.
elim: n i=> [|n IH] // [i|] //=; by rewrite IH.
Qed.

Fixpoint nat_of_fin n : fin n -> nat :=
  match n with
  | 0    => fun i => match i with end
  | n.+1 => fun i => if i is Some i then (nat_of_fin i).+1 else 0
  end.

Lemma leq_nat_of_fin n (i j : fin n) :
  (nat_of_fin i <= nat_of_fin j) = if leq_fin i j is inr b then b else true.
Proof.
elim: n i j=> [[]|n IH] /= [i|] [j|] //.
by rewrite ltnS IH; case: (leq_fin i j).
Qed.

Lemma nat_of_fin_inj n : injective (@nat_of_fin n).
Proof. by elim: n=> [[]|n IH] /= [i|] [j|] // [/IH ->]. Qed.

Fixpoint fin_of_nat n m : option (fin n) :=
  match n with
  | 0 => None
  | n.+1 => if m is m.+1 then if fin_of_nat n m is Some i then Some (Some i) else None
            else Some None
  end.

Lemma nat_of_finK n : pcancel (@nat_of_fin n) (@fin_of_nat n).
Proof.
by elim: n=> [[]|n IH /= [i|]] //=; rewrite IH.
Qed.

Lemma leq_fin_swap n (i j : fin n) :
  leq_fin i j =
  match leq_fin j i with
  | inl e => inl (esym e)
  | inr b => inr (~~ b)
  end.
Proof.
move: (leq_nat_of_fin i j) (leq_nat_of_fin j i).
case: ltngtP=> [||/nat_of_fin_inj ->]; last by rewrite leq_finii.
- case: (leq_fin i j)=> // _ ji <-.
  case: (leq_fin j i) ji => [e|b _ <- //].
  by rewrite {1}e ltnn.
- case: (leq_fin j i)=> // [] [] //=.
  case: (leq_fin i j)=> [e|b _ <- //].
  by rewrite {1}e ltnn.
Qed.

Fixpoint enum_fin n : seq (fin n) :=
  match n with
  | 0 => [::]
  | n.+1 => None :: [seq Some i | i <- enum_fin n]
  end.

Fixpoint size_map T S (f : T -> S) (s : seq T) : size [seq f i | i <- s] = size s :=
  match s with
  | [::] => erefl
  | i :: s => congr1 succn (size_map f s)
  end.

Fixpoint size_enum_fin n : size (enum_fin n) = n :=
  match n with
  | 0 => erefl
  | n.+1 => congr1 succn (size_map Some (enum_fin n) * size_enum_fin n)%EQ
  end.

Definition map_fin (n : nat) T (f : fin n -> T) : seq T :=
  [seq f i | i <- enum_fin n].

Definition cast_fin n m (e : n = m) : forall (i : fin n.+1),
  cast fin (congr1 succn e) i =
  if i is Some j then Some (cast fin e j) else None :=
  match e with
  | erefl => fun i => if i is None then erefl else erefl
  end.

Fixpoint fin_eqMixin n : Equality.mixin_of (fin n) :=
  match n with
  | 0 => void_eqMixin
  | n.+1 => option_eqMixin (EqType _ (fin_eqMixin n))
  end.
Canonical fin_eqType n := EqType (fin n) (fin_eqMixin n).

Fixpoint fin_choiceMixin n : Choice.mixin_of (fin n) :=
  match n with
  | 0 => void_choiceMixin
  | n.+1 => option_choiceMixin (ChoiceType _ (fin_choiceMixin n))
  end.
Canonical fin_choiceType n :=
  Eval hnf in ChoiceType (fin n) (fin_choiceMixin n).

Fixpoint fin_countMixin n : Countable.mixin_of (fin n) :=
  match n with
  | 0 => void_countMixin
  | n.+1 => option_countMixin (CountType _ (fin_countMixin n))
  end.
Canonical fin_countType n :=
  Eval hnf in CountType (fin n) (fin_countMixin n).

Section Ilist.

Variables (T : Type).

Definition ilist n := iter n (prod T) unit.

Fixpoint nth_ilist n : ilist n -> fin n -> T :=
  match n with
  | 0    => fun l i => match i with end
  | n.+1 => fun l i => if i is Some j then nth_ilist l.2 j else l.1
  end.

Fixpoint ilist_of_fun n : forall (f : fin n -> T), ilist n :=
  match n with
  | 0    => fun _ => tt
  | n.+1 => fun f => (f None, ilist_of_fun (fun i => f (Some i)))
  end.

Fixpoint nth_ilist_of_fun n : forall (f : fin n -> T) (i : fin n), nth_ilist (ilist_of_fun f) i = f i :=
  match n with
  | 0    => fun f i => match i with end
  | n.+1 => fun f i => if i is Some j then nth_ilist_of_fun (fun j => f (Some j)) j else erefl
  end.

Fixpoint ilist_of_seq s : ilist (size s) :=
  match s with
  | [::] => tt
  | x :: s => (x, ilist_of_seq s)
  end.

Fixpoint seq_of_ilist n : ilist n -> seq T :=
  match n with
  | 0    => fun l => [::]
  | n.+1 => fun l => l.1 :: seq_of_ilist l.2
  end.

End Ilist.

Fixpoint imap T S (f : T -> S) n : ilist T n -> ilist S n :=
  match n with
  | 0    => fun l => tt
  | n.+1 => fun l => (f l.1, imap f l.2)
  end.

Lemma imap_eq (T S : Type) (f g : T -> S) :
  f =1 g ->
  forall n, @imap _ _ f n =1 @imap _ _ g n.
Proof.
by move=> efg; elim=> [[]|n IH] // [x l] /=; rewrite efg IH.
Qed.

Lemma imap1 (T: Type) n (l : ilist T n) : imap id l = l.
Proof.
by elim: n l=> /= [[]|n IH] // [x l] /=; rewrite IH.
Qed.

Lemma imap_comp (T S R : Type)
                (f : T -> S) (g : S -> R) n (l : ilist T n) :
  imap g (imap f l) = imap (g \o f) l.
Proof.
by elim: n l=> [[]|n IH] //= [x l] /=; rewrite IH.
Qed.

Section Hsum.

Variables (I : Type) (T_ : I -> Type).

Implicit Types (i : I) (ix : seq I).

Definition hsum ix : Type :=
  foldr (fun i S => T_ i + S)%type void ix.

Fixpoint hin ix : forall n : fin (size ix), T_ (nth_fin n) -> hsum ix :=
  if ix is i :: ix then
    fun n : fin (size ix).+1 =>
      if n is Some n' then fun x : T_ (nth_fin n') => inr (hin x)
      else fun x => inl x
  else fun n => match n with end.

Fixpoint hcase S ix : (forall n : fin (size ix), T_ (nth_fin n) -> S) -> hsum ix -> S :=
  if ix is i :: ix then
    fun f x =>
      match x with
      | inl x => f None x
      | inr x => hcase (fun n x => f (Some n) x) x
      end
  else fun _ x => match x with end.

Lemma hcaseE S ix
  (f : forall n : fin (size ix), T_ (nth_fin n) -> S)
  (n : fin (size ix))
  (x : T_ (nth_fin n)) : hcase f (hin x) = f n x.
Proof.
by elim: ix f n x=> [_ []|i ix IH] /= f [n|] // x; rewrite IH.
Qed.

End Hsum.

Section Hlist.

Variables (I : Type) (T_ : I -> Type).

Implicit Types (i : I) (ix : seq I).

Definition hlist ix : Type :=
  foldr (fun i S => T_ i * S)%type unit ix.

Definition hfun ix S : Type :=
  foldr (fun i R => T_ i -> R) S ix.

Fixpoint happ ix S : hfun ix S -> hlist ix -> S :=
  match ix with
  | [::]    => fun f _    => f
  | i :: ix => fun f args => happ (f args.1) args.2
  end.

Fixpoint hcurry ix S : (hlist ix -> S) -> hfun ix S :=
  match ix with
  | [::]    => fun f   => f tt
  | i :: ix => fun f x => hcurry (fun args=> f (x, args))
  end.

Lemma hcurryK ix S (f : hlist ix -> S) l : happ (hcurry f) l = f l.
Proof.
by elim: ix f l=> /= [? []|i ix IH f [x l]] //; rewrite IH.
Qed.

Fixpoint hcat (ix1 ix2 : seq I) :
  hlist ix1 -> hlist ix2 -> hlist (ix1 ++ ix2) :=
  match ix1 with
  | [::] => fun _ l2 => l2
  | i :: ix1 => fun l1 l2 => (l1.1, hcat l1.2 l2)
  end.

Fixpoint nth_hlist (ix : seq I) :
    hlist ix -> forall n : fin (size ix), T_ (nth_fin n) :=
  match ix with
  | [::]    => fun l n => match n with end
  | i :: ix => fun l n => match n with
                          | Some n => nth_hlist l.2 n
                          | None   => l.1
                          end
  end.

(*
Fixpoint hlist_of_fun (f : forall i, T_ i) ix : hlist ix :=
  if ix is i :: ix then (f i, hlist_of_fun f ix) else tt.

Lemma nth_hlist_of_fun f ix n :
  nth_hlist (hlist_of_fun f ix) n = f (nth_fin n).
Proof. elim: ix n=> /= [|i ix IH] // [n|]; by rewrite ?IH. Qed.
*)

Fixpoint seq_of_hlist S ix (f : forall i, T_ i -> S) : hlist ix -> seq S :=
  match ix with
  | [::] => fun _ => [::]
  | i :: ix => fun l => f i l.1 :: seq_of_hlist f l.2
  end.

Fixpoint hlist_of_seq S ix (f : forall i, S -> option (T_ i)) : seq S -> option (hlist ix) :=
  match ix with
  | [::] => fun xs => Some tt
  | i :: ix => fun xs => if xs is x :: xs then
                           match f i x, hlist_of_seq ix f xs with
                           | Some y, Some l => Some (y, l)
                           | _ , _ => None
                           end
                         else None
  end.

Lemma seq_of_hlistK S ix f g :
  (forall i, pcancel (f i) (g i)) ->
  pcancel (@seq_of_hlist S ix f) (@hlist_of_seq S ix g).
Proof.
move=> fK; elim: ix=> [[]|i ix IH /= [x l]] //=.
by rewrite fK IH.
Qed.

Fixpoint seq_of_hlist_in S ix :
  (forall n : fin (size ix), T_ (nth_fin n) -> S) ->
  hlist ix -> seq S :=
  if ix is i :: ix then
    fun f xs => f None xs.1 :: seq_of_hlist_in (fun n => f (Some n)) xs.2
  else fun _ _ => [::].

Fixpoint hlist_of_seq_in S ix (f : forall n : fin (size ix), S -> option (T_ (nth_fin n))) (xs : seq S) {struct xs} : option (hlist ix) :=
  match xs with
  | [::] =>
    match ix return option (hlist ix) with
    | [::] => Some tt
    | _ => None
    end
  | x :: xs =>
    match ix return (forall n : fin (size ix), S -> option (T_ (nth_fin n))) -> option (hlist ix) with
    | [::] => fun _ => None
    | i :: ix => fun f =>
                   match f None x, hlist_of_seq_in (fun n => f (Some n)) xs with
                   | Some y, Some ys => Some (y, ys)
                   | _, _ => None
                   end
    end f
  end.

Lemma seq_of_hlist_inK S ix
  (f : forall n : fin (size ix), T_ (nth_fin n) -> S)
  (g : forall n : fin (size ix), S -> option (T_ (nth_fin n))) :
  (forall n, pcancel (f n) (g n)) ->
  pcancel (seq_of_hlist_in f) (hlist_of_seq_in g).
Proof.
elim: ix f g=> [??? []|i ix IH] //= f g fK [x xs] /=.
by rewrite fK IH // => n ?; rewrite fK.
Qed.

Lemma hlist_of_seq_in_map
  S R ix (f : forall n : fin (size ix), R -> option (T_ (nth_fin n))) (g : S -> R) (xs : seq S) :
  hlist_of_seq_in f [seq g x | x <- xs] = hlist_of_seq_in (fun n x => f n (g x)) xs.
Proof.
elim: ix f xs=> [|i ix IH] /= f [|x xs] //=.
by case: (f None (g x))=> [y|] //=; rewrite IH.
Qed.

Fixpoint hlist_of_fun ix : forall (f : forall n : fin (size ix), T_ (nth_fin n)), hlist ix :=
  match ix with
  | [::]    => fun _ => tt
  | i :: ix => fun f => (f None, hlist_of_fun (fun n => f (Some n)))
  end.

Lemma nth_hlist_of_fun ix f n : nth_hlist (@hlist_of_fun ix f) n = f n.
Proof.
by elim: ix f n=> [|i ix IH] //= f [n|] //; rewrite IH.
Qed.

Fixpoint all_hlist ix : (hlist ix -> Prop) -> Prop :=
  match ix with
  | i :: ix => fun P => forall x, all_hlist (fun l => P (x, l))
  | [::]    => fun P => P tt
  end.

Lemma all_hlistP ix P : @all_hlist ix P <-> (forall l, P l).
Proof.
split; elim: ix P=> [|i ix IH] //=; first by move=> P ? [].
- by move=> P H [x l]; move/(_ x)/IH in H.
- by move=> P H x; apply: IH=> l.
Qed.

Fixpoint hfold S (f : forall i, T_ i -> S -> S) a ix : hlist ix -> S :=
  match ix with
  | [::] => fun _ => a
  | i :: ix => fun l => f i l.1 (hfold f a l.2)
  end.

End Hlist.

Coercion happ : hfun >-> Funclass.

Fixpoint hmap I (T_ S_ : I -> Type) (f : forall i, T_ i -> S_ i) ix :
  hlist T_ ix -> hlist S_ ix :=
  match ix with
  | [::]    => fun _ => tt
  | i :: ix => fun l => (f i l.1, hmap f l.2)
  end.

Lemma hmap_eq I (T_ S_ : I -> Type) (f g : forall i, T_ i -> S_ i) :
  (forall i, f i =1 g i) ->
  forall ix, @hmap _ _ _ f ix =1 @hmap _ _ _ g ix.
Proof.
by move=> efg; elim=> [[]|i ix IH] // [x l] /=; rewrite efg IH.
Qed.

Lemma hmap1 I (T_ : I -> Type) ix (l : hlist T_ ix) : hmap (fun i => id) l = l.
Proof.
by elim: ix l=> /= [[]|i ix IH] // [x l] /=; rewrite IH.
Qed.

Lemma hmap_comp I (T_ S_ R_ : I -> Type)
                (f : forall i, T_ i -> S_ i)
                (g : forall i, S_ i -> R_ i) ix (l : hlist T_ ix) :
  hmap g (hmap f l) = hmap (fun i => g i \o f i) l.
Proof.
by elim: ix l=> [[]|i ix IH] //= [x l] /=; rewrite IH.
Qed.

Definition hmap_in I (T_ S_ : I -> Type) ix :
  (forall n : fin (size ix), T_ (nth_fin n) -> S_ (nth_fin n)) ->
  hlist T_ ix -> hlist S_ ix :=
  fun f l => hlist_of_fun (fun n => f n (nth_hlist l n)).

Fixpoint hpmap_in I (T_ S_ : I -> Type) ix :
  (forall n : fin (size ix), T_ (nth_fin n) -> option (S_ (nth_fin n))) ->
  hlist T_ ix -> option (hlist S_ ix) :=
  match ix with
  | [::] =>
    fun f l => Some tt
  | i :: ix =>
    fun f l => if hpmap_in (fun n => f (Some n)) l.2 is Some l' then
                 if f None l.1 is Some x then
                   Some (x, l')
                 else None
               else None
  end.

Lemma hmap_pinK I (T_ S_ : I -> Type) ix
  (f : forall n : fin (size ix), T_ (nth_fin n) -> S_ (nth_fin n))
  (g : forall n : fin (size ix), S_ (nth_fin n) -> option (T_ (nth_fin n))) :
  (forall n, pcancel (f n) (g n)) -> pcancel (hmap_in f) (hpmap_in g).
Proof.
rewrite /hmap_in; elim: ix f g=> [|i ix IH] //= f g fK => [[]|[x xs]] //=.
rewrite fK (IH (fun n => f (Some n)) (fun n => g (Some n))) //.
move=> n; exact: (fK (Some n)).
Qed.

Fixpoint hzip I (T_ S_ : I -> Type) ix :
  hlist T_ ix -> hlist S_ ix -> hlist (fun i => T_ i * S_ i)%type ix :=
  match ix with
  | [::] => fun _ _ => tt
  | i :: ix => fun lx ly => ((lx.1, ly.1), hzip lx.2 ly.2)
  end.

Fixpoint hlist_map I J (T_ : J -> Type) (f : I -> J) (ix : seq I) :
  hlist T_ [seq f i | i <- ix] = hlist (T_ \o f) ix :=
  match ix with
  | [::]    => erefl
  | i :: ix => f_equal (prod (T_ (f i))) (hlist_map T_ f ix)
  end.

Fixpoint hfun_map I J (T_ : J -> Type) (f : I -> J) S (ix : seq I) :
  hfun T_ [seq f i | i <- ix] S = hfun (T_ \o f) ix S :=
  match ix with
  | [::]    => erefl
  | i :: ix => f_equal (fun R => T_ (f i) -> R) (hfun_map T_ f S ix)
  end.

Fixpoint hlist_eq I (T_ S_ : I -> Type) (e : forall i, T_ i = S_ i) ix :
  hlist T_ ix = hlist S_ ix :=
  match ix with
  | [::]    => erefl
  | i :: ix => f_equal2 prod (e i) (hlist_eq e ix)
  end.

Fixpoint hfun_eq I (T_ S_ : I -> Type) (e : forall i, T_ i = S_ i) ix R :
  hfun T_ ix R = hfun S_ ix R :=
  match ix with
  | [::]    => erefl
  | i :: ix => f_equal2 (fun X Y => X -> Y) (e i) (hfun_eq e ix R)
  end.

Variant kind := Other of Type | Rec.

Definition is_other k := if k is Other R then Some R else None.
Definition is_rec k := ~~ (is_other k).

Definition arity := seq kind.
Definition signature := seq arity.

Identity Coercion seq_of_arity : arity >-> seq.
Identity Coercion seq_of_sig : signature >-> seq.

Section ClassLifting.

Variables (K : Type) (sort : K -> Type).

Definition kind_class k :=
  if k is Other T then {sT : K | sort sT = T} else unit.

Record kind_inst := KindInst {
  kind_inst_sort  :> kind;
  kind_inst_class :  kind_class kind_inst_sort
}.

Record arity_inst := ArityInst {
  arity_inst_sort  :> arity;
  arity_inst_class :  hlist kind_class arity_inst_sort;
}.

Record sig_inst := SigInst {
  sig_inst_sort  :> signature;
  sig_inst_class :  hlist (hlist kind_class) sig_inst_sort;
}.

Implicit Types (k : kind) (a : arity) (s : signature).
Implicit Types (ki : kind_inst) (ai : arity_inst) (si : sig_inst).

Canonical Other_kind_inst T :=
  @KindInst (Other (sort T)) (exist _ T erefl).

Canonical Rec_kind_inst :=
  @KindInst Rec tt.

Canonical nth_fin_kind_inst (ai : arity_inst) (i : fin (size ai)) :=
  @KindInst (nth_fin i) (nth_hlist (arity_inst_class ai) i).

Canonical nil_arity_inst :=
  @ArityInst nil tt.

Canonical cons_arity_inst ki ai :=
  @ArityInst (kind_inst_sort ki :: arity_inst_sort ai)
             (kind_inst_class ki, arity_inst_class ai).

Canonical nth_fin_arity_inst (si : sig_inst) (i : fin (size si)) :=
  @ArityInst (nth_fin i) (nth_hlist (sig_inst_class si) i).

Canonical nil_sig_inst :=
  @SigInst nil tt.

Canonical cons_sig_inst ai si :=
  @SigInst (arity_inst_sort ai :: sig_inst_sort si)
           (arity_inst_class ai, sig_inst_class si).

Definition arity_rec (T : arity -> Type)
  (Tnil   : T [::])
  (TOther : forall (R : K) (a : arity), T a -> T (Other (sort R) :: a))
  (TRec   : forall (a : arity), T a -> T (Rec :: a)) :=
  fix arity_rec (a : arity) : hlist kind_class a -> T a :=
    match a with
    | [::]             => fun ac => Tnil
    | Other Rsort :: a => fun ac =>
      cast (fun Rsort => T (Other Rsort :: a)) (svalP ac.1)
           (TOther (sval ac.1) a (arity_rec a ac.2))
    | Rec :: a         => fun ac => TRec a (arity_rec a ac.2)
    end.

Lemma arity_ind (T : forall a, hlist kind_class a -> Type)
  (Tnil : T [::] tt)
  (TOther : forall (R : K) (a : arity) (ac : hlist kind_class a),
      T a ac -> T (Other (sort R) :: a) (exist _ R erefl, ac))
  (TRec : forall (a : arity) (ac : hlist kind_class a),
      T a ac -> T (Rec :: a) (tt, ac))
  (a : arity) (ac : hlist kind_class a) : T a ac.
Proof.
elim: a ac=> [|[Rsort|] a IH] => /= [[]|[[R e] ac]|[[] ac]] //.
  by case: Rsort / e; apply: TOther.
by apply: TRec.
Qed.

End ClassLifting.

Definition type_of_kind S (k : kind) : Type :=
  if k is Other R then R else S.

Definition type_of_kind_map S R (f : S -> R) k :
  type_of_kind S k -> type_of_kind R k :=
  if k is Rec then f else id.

Module CoqInd.

Section Basic.

Variable (T : Type).

Implicit Types (k : kind) (a : arity) (s : signature).

Definition constructors s :=
  hlist (fun a => hfun (type_of_kind T) a T) s.

Fixpoint branch S a : Type :=
  match a with
  | Other R :: ks => R      -> branch S ks
  | Rec     :: ks => T -> S -> branch S ks
  | [::]          => S
  end.

Definition recursor s := forall S, hfun (branch S) s (T -> S).

Fixpoint branch_of_hfun S a :
  hfun (type_of_kind (T * S)) a S -> branch S a :=
  match a with
  | Other R :: a => fun f x   => branch_of_hfun (f x)
  | Rec     :: a => fun f x y => branch_of_hfun (f (x, y))
  | [::]         => fun f     => f
  end.

Fixpoint hfun_of_branch S a :
  branch S a -> hfun (type_of_kind (T * S)) a S :=
  match a with
  | Other R :: a => fun f x => hfun_of_branch (f x)
  | Rec     :: a => fun f p => hfun_of_branch (f p.1 p.2)
  | [::]         => fun f   => f
  end.

Lemma branch_of_hfunK S a f args :
  hfun_of_branch (@branch_of_hfun S a f) args = f args.
Proof.
by elim: a f args=> [|[R|] a IH] f //= [[x y] args] //.
Qed.

Definition recursor_eq s (cs : constructors s) (r : recursor s) :=
  forall S,
  all_hlist (fun bs : hlist (branch S) s =>
  all_fin   (fun i : fin (size s) =>
  all_hlist (fun args : hlist (type_of_kind T) (nth_fin i) =>
    r S bs (nth_hlist cs i args) =
    hfun_of_branch (nth_hlist bs i)
                   (hmap (type_of_kind_map (fun x => (x, r S bs x))) args)))).

Definition destructor s :=
  forall S, hfun (fun a => hfun (type_of_kind T) a S) s (T -> S).

Definition destructor_of_recursor s (rec : recursor s) : destructor s :=
  fun S =>
  hcurry (fun bs : hlist (fun a => hfun (type_of_kind T) a S) s =>
            happ (rec S) (hmap (fun a (b : hfun (type_of_kind T) a S) =>
                                  branch_of_hfun (hcurry (fun args => happ b (hmap (type_of_kind_map fst) args)))) bs)).

Definition destructor_eq s (cs : constructors s) (d : destructor s) :=
  forall S,
  all_hlist (fun bs : hlist (fun ks => hfun (type_of_kind T) ks S) s =>
  all_fin   (fun i : fin (size s) =>
  all_hlist (fun args : hlist (type_of_kind T) (nth_fin i) =>
    d S bs (nth_hlist cs i args) = nth_hlist bs i args))).

Fixpoint ind_branch (P : T -> Type) a :
  hfun (type_of_kind T) a T -> Type :=
  match a with
  | Other R :: a => fun c => forall x : R,        ind_branch P (c x)
  | Rec     :: a => fun c => forall x : T, P x -> ind_branch P (c x)
  | [::]         => fun c => P c
  end.

Fixpoint ind_at (P : T -> Type) s : constructors s -> Type :=
  match s with
  | ks :: s => fun cs => ind_branch P cs.1 -> ind_at P cs.2
  | [::]    => fun cs => forall x, P x
  end.

End Basic.

Section ClassDef.

Variables (s : signature).

Record mixin_of T := Mixin {
  Cons      : constructors T s;
  rec       : recursor T s;
  case      : destructor T s;
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

Class infer_arity T (P : T -> Type)
  (branchT : Type) (a : arity) (C : hfun (type_of_kind T) a T) : Type.

Instance infer_arity_end (T : Type) (P : T -> Type) (x : T) :
  @infer_arity T P (P x) [::] x.

Instance infer_arity_rec
  (T : Type) (P : T -> Type)
  (branchT : T -> Type) (a : arity) (C : T -> hfun (type_of_kind T) a T)
  (H : forall x, @infer_arity T P (branchT x) a (C x)) :
  @infer_arity T P (forall x, P x -> branchT x) (Rec :: a) C.

Instance infer_arity_other
  (T : Type) (P : T -> Type)
  (R : Type) (branchT : R -> Type) (a : arity) (C : R -> hfun (type_of_kind T) a T)
  (H : forall x, @infer_arity T P (branchT x) a (C x)) :
  @infer_arity T P (forall x, branchT x) (Other R :: a) C.

Class infer_sig T (P : T -> Type) (elimT : Type) s (Cs : CoqInd.constructors T s).

Instance infer_sig_end (T : Type) (P : T -> Type) : @infer_sig T P (forall x : T, P x) [::] tt.

Instance infer_sig_branch
  T (P : T -> Type)
  (branchT : Type) (a : arity) C (_ : @infer_arity T P branchT a C)
  (elimT : Type) (sig : signature) Cs (_ : @infer_sig T P elimT sig Cs) :
  @infer_sig T P (branchT -> elimT) (a :: sig) (C, Cs).

Ltac unwind_recursor P T t :=
  match goal with
  | |- ?F -> ?G =>
    let X := fresh "X" in intros X; unwind_recursor P T (t X)
  | |- _ => case; intros; apply t
  end.

Ltac coq_ind_mixin t :=
  match type of t with
  | forall (P : ?T -> Type), @?elimT P =>
    let Rec  := eval compute in t in
    let sCs  := constr:((fun s Cs (_ : forall P, @infer_sig T P (elimT P) s Cs) => (s, Cs)) _ _ _) in
    let sCs  := eval simpl in sCs in
    let case := constr:(ltac:(intros P; simpl; unwind_recursor P nat (Rec P)) : forall P, elimT P) in
    let case := eval compute in (@CoqInd.destructor_of_recursor T sCs.1 (fun S => case (fun _ => S))) in
    refine (
        @CoqInd.Mixin
          sCs.1 T sCs.2
          (fun S => Rec (fun _ => S)) case _ _ _
      );
    try by [abstract done|exact t]
  end.

Notation "[ 'coqIndMixin' 'for' rect ]" :=
  (ltac:(coq_ind_mixin rect))
  (at level 0) : form_scope.

Module CoqIndFunctor.

Section TypeDef.

Import CoqInd.

Variables (s : signature).

Record type T := CoqInd {
  constr : fin (size s);
  args : hlist (type_of_kind T) (nth_fin constr)
}.

Arguments CoqInd {_} _ _.

Local Notation F := type.

Definition fmap T S (f : T -> S) (x : F T) : F S :=
  CoqInd (constr x) (hmap (type_of_kind_map f) (args x)).

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

Lemma inj T (i : fin (size s)) (a b : hlist (type_of_kind T) (nth_fin i)) :
  CoqInd i a = CoqInd i b -> a = b.
Proof.
pose get x :=
  if leq_fin (constr x) i is inl e then
    cast (fun j : fin (size s) => hlist (type_of_kind T) (nth_fin j)) e (args x)
  else a.
by move=> /(congr1 get); rewrite /get /= leq_finii /=.
Qed.

Variable T : coqIndType s.

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
rewrite /Roll.
case: (T) P => S [/= Cons _ _ _ _ indP] P.
have {indP} indP:
    (forall i, CoqInd.ind_branch P (nth_hlist Cons i)) ->
    (forall x, P x).
  move/(_ P): indP.
  elim: (s) Cons=> [|a s' IH] //= [c cs] /= indP hyps.
  move: (hyps None)=> /indP/IH; apply=> i.
  exact: (hyps (Some i)).
move=> hyps; apply: indP=> j.
have {hyps} hyps:
  forall args : hlist (type_of_kind {x : S & P x}) (nth_fin j),
    P (nth_hlist Cons j (hmap (type_of_kind_map tag) args)).
  by move=> args; move: (hyps (CoqInd j args)).
elim: (nth_fin j) (nth_hlist Cons j) hyps=> [|[i|] ks IH] //=.
- by move=> ? /(_ tt).
- move=> c hyps x; apply: IH=> args.
  exact: (hyps (x, args)).
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

Local Notation kind_class := (kind_class Equality.sort).
Local Notation kind_inst := (kind_inst Equality.sort).
Local Notation arity_inst := (arity_inst Equality.sort).
Local Notation sig_inst := (sig_inst Equality.sort).

Section EqType.

Variable (s : sig_inst).
Let F := CoqIndFunctor.coqInd_functor s.
Variable (T : indType F).

Let eq_op_branch a (ac : hlist kind_class a) :
  hlist (type_of_kind (T * (T -> bool))) a ->
  hlist (type_of_kind T)                 a ->
  bool :=
  @arity_rec _ _ (fun a => hlist _ a -> hlist _ a -> bool)
    (fun _ _ => true)
    (fun R a rec x y => (x.1 == y.1) && rec x.2 y.2)
    (fun   a rec x y => x.1.2 y.1 && rec x.2 y.2) a ac.

Let eq_op : T -> T -> bool :=
  rec (fun args1 =>
         case
           (fun args2 =>
              match leq_fin (CoqIndFunctor.constr args2) (CoqIndFunctor.constr args1) with
              | inl e =>
                eq_op_branch
                  (nth_hlist (sig_inst_class s) (CoqIndFunctor.constr args1))
                  (CoqIndFunctor.args args1)
                  (cast (hlist (type_of_kind T) \o @nth_fin _ _) e (CoqIndFunctor.args args2))
              | inr _ => false
              end)).

Lemma eq_opP : Equality.axiom eq_op.
Proof.
elim/indP=> [[i_x xargs]] y.
rewrite /eq_op recE /= -[rec _]/(eq_op) /=.
rewrite -[y]unrollK caseE; move: {y} (unroll y)=> [i_y yargs] /=.
case le: (leq_fin i_y i_x)=> [e|b]; last first.
  constructor=> /Roll_inj /= [] e _.
  by move: le; rewrite e leq_finii.
case: i_x / e xargs {le} => /= xargs.
apply/(@iffP (hmap (type_of_kind_map tag) xargs = yargs)); first last.
- by move=> /Roll_inj /CoqIndFunctor.inj.
- by move=> <-.
elim/arity_ind: {i_y} (nth_fin i_y) / (nth_hlist _ _) xargs yargs=> //=.
- by move=> _ []; constructor.
- move=> R a ac IH [x xargs] [y yargs] /=.
  apply/(iffP andP)=> [[/eqP ? /IH ?]|[/eqP ? /IH]];
  intuition (eauto; congruence).
- move=> a ac IH [[x xP] xargs] [y yargs] /=.
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

Definition eqMixin :=
  fun (T : Type) =>
  fun s (sT : coqIndType s) & phant_id (CoqInd.sort sT) T =>
  fun (ss : sig_inst) & phant_id s (sig_inst_sort ss) =>
  fun (cT : CoqInd.mixin_of ss T) & phant_id (CoqInd.class sT) cT =>
    ltac:(
      let ax := constr:(@eq_opP ss (CoqInd.Pack cT)) in
      match type of ax with
      | Equality.axiom ?e =>
        let e' := eval compute -[eq_op Equality.sort andb] in e in
        exact: @EqMixin T e' ax
      end).

Module Import Exports.
Notation "[ 'indEqMixin' 'for' T ]" :=
  (let m := @eqMixin T _ _ id _ id _ id in
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

Variables (s : signature).
Let F := CoqIndFunctor.coqInd_functor s.
Variables (T : indType F).

Import GenTree.

Definition coq_ind_arg :=
  hsum (hsum (type_of_kind void)) s.

Definition mk_coq_ind_arg (i : fin (size s)) (j : fin (size (nth_fin i))) :
  type_of_kind void (nth_fin j) -> coq_ind_arg :=
  fun x => hin (hin x).

Definition proj_coq_ind_arg
  (i : fin (size s)) (j : fin (size (nth_fin i))) (x : coq_ind_arg) :
  option (type_of_kind void (nth_fin j)) :=
  hcase (fun i' =>
    if leq_fin i' i is inl e then
      match e^-1 in _ = i'
      return (hsum (fun k => type_of_kind void k) (nth_fin i') -> option _) with
      | erefl =>
        hcase (fun j' =>
          if leq_fin j' j is inl e then
            match e^-1 in _ = j'
            return (type_of_kind void (nth_fin j') -> option _)
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

Let wrap (i : fin (size s)) (j : fin (size (nth_fin i))) :
  type_of_kind (tree coq_ind_arg) (nth_fin j) -> tree coq_ind_arg :=
  match nth_fin j as k
  return (type_of_kind void k -> coq_ind_arg) ->
         type_of_kind (tree coq_ind_arg) k -> tree coq_ind_arg
  with
  | Other R => fun c x => Leaf (c x)
  | Rec     => fun c x => x
  end (@mk_coq_ind_arg i j).

Definition tree_of_coq_ind (x : T) : tree coq_ind_arg :=
  rec (fun x =>
         let i := CoqIndFunctor.constr x in
         Node (nat_of_fin i)
           (seq_of_hlist_in (@wrap i)
              (hmap (type_of_kind_map snd) (CoqIndFunctor.args x)))) x.

Fixpoint coq_ind_of_tree (x : tree coq_ind_arg) : option T :=
  match x with
  | Leaf _ => None
  | Node c args =>
    if fin_of_nat (size s) c is Some i then
      let args := [seq (t, coq_ind_of_tree t) | t <- args] in
      if hlist_of_seq_in (fun j ts =>
                            match nth_fin j as k
                                  return (coq_ind_arg -> option (type_of_kind void k)) ->
                                         option (type_of_kind T k) with
                            | Other R => fun f => if ts.1 is Leaf x then f x else None
                            | Rec => fun _ => ts.2
                            end (@proj_coq_ind_arg i j)) args is Some args then
        Some (Roll (CoqIndFunctor.CoqInd args))
      else None
    else None
  end.

Lemma tree_of_coq_indK : pcancel tree_of_coq_ind coq_ind_of_tree.
Proof.
elim/indP=> [[i args]].
rewrite /tree_of_coq_ind recE /= -[rec _]/(tree_of_coq_ind).
rewrite nat_of_finK !hmap_comp /=.
set args' := hlist_of_seq_in _ _.
suffices -> : args' = Some (hmap (type_of_kind_map tag) args) by [].
rewrite {}/args' hlist_of_seq_in_map /= /wrap.
move: (@mk_coq_ind_arg i) (@proj_coq_ind_arg i) (@mk_coq_ind_argK i).
elim: {i} (nth_fin i) args=> [|[R|] a IH] //= args C p CK.
  by rewrite CK IH //= => j x; rewrite CK.
case: args=> [[x xP] args] /=; rewrite xP IH //.
by move=> j ?; rewrite CK.
Qed.

End TreeOfCoqInd.

Definition pack_tree_of_coq_indK :=
  fun (T : Type) =>
  fun s (sT_ind : coqIndType s) & phant_id (CoqInd.sort sT_ind) T =>
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

Variable (sig : sig_inst Finite.sort).
Let F := CoqIndFunctor.coqInd_functor sig.
Variable (T : indEqType F).

Hypothesis not_rec : all (all is_other) sig.

Definition enum_branch :=
  @arity_rec
    _ _ (fun a => all is_other a -> seq (hlist (type_of_kind T) a))
    (fun _ => [:: tt])
    (fun (R : finType) a rec P => allpairs pair (Finite.enum R) (rec P))
    (fun               a rec P => ltac:(done)).

Definition enum_ind :=
  flatten [seq [seq Roll (CoqIndFunctor.CoqInd args)
               | args <- enum_branch (nth_hlist (sig_inst_class sig) i) (allP not_rec i)]
          | i <- enum_fin (size sig)].

Lemma enum_indP : Finite.axiom enum_ind.
Proof.
move=> x; rewrite -[x]unrollK; case: {x} (unroll x)=> i args.
rewrite /enum_ind count_flatten -!map_comp /comp /=.
have <- : sumn [seq i == j : nat | j <- enum_fin (size sig)] = 1.
  elim: (size sig) i {args}=> [|n IH] //= [i|] /=.
    by rewrite -map_comp /comp /= -(IH i) add0n.
  rewrite -map_comp /comp /=; congr addn; apply/eqP/natnseq0P.
  by elim: (enum_fin n)=> {IH} // m ms /= <-.
congr sumn; apply/eq_map=> j /=; rewrite count_map.
have [<- {j}|ne] /= := altP (i =P j).
  set P := preim _ _.
  have PP : forall args', reflect (args = args') (P args').
    move=> args'; rewrite /P /=; apply/(iffP idP); last by move=> ->.
    by move=> /eqP/Roll_inj/CoqIndFunctor.inj ->.
  move: P PP.
  elim/arity_ind: {i} _ / (nth_hlist _ i) args (allP _ _)=> //=.
    by move=> [] _ P /(_ tt); case.
  move=> R ar ac IH [x args] arP P PP.
  elim: (Finite.enum R) (enumP x)=> //= y xs IHxs.
  have [-> {y} [e]|ne] := altP (y =P x).
    rewrite count_cat count_map (IH args); last first.
      move=> args'; apply/(iffP (PP (x, args'))); congruence.
    congr S.
    elim: xs e {IHxs} => //= y xs; case: (altP eqP) => //= ne H /H.
    rewrite count_cat => ->; rewrite addn0.
    elim: (enum_branch _ _)=> //= args' e ->; rewrite addn0.
    apply/eqP; rewrite eqb0; apply/negP=> /PP [] /esym/eqP.
    by rewrite (negbTE ne).
  rewrite count_cat; move=> /IHxs ->; rewrite addn1; congr S.
  elim: (enum_branch _ _) {IHxs}=> //= args' e ->; rewrite addn0.
  apply/eqP; rewrite eqb0; apply/negP=> /PP [] /esym/eqP.
  by rewrite (negbTE ne).
set P := preim _ _.
rewrite (@eq_count _ _ pred0) ?count_pred0 //.
move=> args' /=; apply/negbTE; apply: contra ne.
by move=> /eqP/Roll_inj/(congr1 (@CoqIndFunctor.constr _ _)) /= ->.
Qed.

End FinType.

Definition pack :=
  fun (T : Type) =>
  fun (b : Countable.class_of T) bT & phant_id (Countable.class bT) b =>
  fun s (sT : coqIndType s) & phant_id (CoqInd.sort sT) T =>
  fun (ss : sig_inst Finite.sort) & phant_id s (sig_inst_sort ss) =>
  fun (cT : CoqInd.mixin_of ss T) & phant_id (CoqInd.class sT) cT =>
  fun (not_rec : all (all is_other) ss) =>
    ltac:(
      let ax := constr:(@enum_indP ss (IndEqType.Pack b (Ind.class (CoqInd.Pack cT))) not_rec) in
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

End Instances.
