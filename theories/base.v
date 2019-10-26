From mathcomp Require Import
  ssreflect ssrfun ssrbool ssrnat eqtype seq choice fintype.

From void Require Import void.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Universe Polymorphism.

(* The SSReflect definition is opaque, which interferes with certain reductions
   below. *)
Notation svalP := proj2_sig.

Definition cast T (P : T -> Type) x y (e : x = y) : P x -> P y :=
  match e with erefl => id end.

Arguments cast {_} _ {_ _} _.

Delimit Scope deriving_scope with deriving.

Local Open Scope deriving_scope.

Notation "e1 * e2" := (etrans e1 e2) : deriving_scope.
Notation "e ^-1" := (esym e) : deriving_scope.

Inductive seq T := nil | cons of T & seq T.
Arguments nil {_}.

Infix "::" := cons : deriving_scope.

Notation "[ :: ]" := nil : deriving_scope.

Notation "[ :: x1 ]" := (cons x1 nil) : deriving_scope.

Fixpoint list_of_seq T (xs : seq T) : seq.seq T :=
  if xs is x :: xs then (x :: list_of_seq xs)%SEQ else [::]%SEQ.

Fixpoint seq_of_list T (xs : seq.seq T) : seq T :=
  if xs is (x :: xs)%SEQ then x :: seq_of_list xs else [::].

Lemma list_of_seqK T : cancel (@list_of_seq T) (@seq_of_list T).
Proof. by elim=> //= ?? ->. Qed.

Lemma seq_of_listK T : cancel (@seq_of_list T) (@list_of_seq T).
Proof. by elim=> //= ?? ->. Qed.

Fixpoint size T (xs : seq T) :=
  if xs is x :: xs then (size xs).+1 else 0.

Definition map T S (f : T -> S) :=
  fix map xs := if xs is x :: xs then f x :: map xs else [::].

Definition foldr T S (f : T -> S -> S) (x : S) :=
  fix foldr xs := if xs is x' :: xs then f x' (foldr xs) else x.

Fixpoint cat T (xs ys : seq T) :=
  if xs is x :: xs then x :: cat xs ys else ys.

Infix "++" := cat : deriving_scope.

Lemma seq_of_list_map T S (f : T -> S) (xs : seq.seq T) :
  seq_of_list (seq.map f xs) = map f (seq_of_list xs).
Proof. by elim: xs=> //= x xs ->. Qed.

Lemma list_of_seq_map T S (f : T -> S) (xs : seq T) :
  list_of_seq (map f xs) = seq.map f (list_of_seq xs).
Proof. by elim: xs=> //= x xs ->. Qed.

Fixpoint all T (P : pred T) (xs : seq T) :=
  if xs is x :: xs then P x && all P xs else true.

Fixpoint fin n :=
  if n is n.+1 then option (fin n) else void.

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
                              | inl e => inl (congr1 Some e)
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
  | n.+1 => None :: map Some (enum_fin n)
  end.

Fixpoint size_map T S (f : T -> S) (s : seq T) : size (map f s) = size s :=
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
  map f (enum_fin n).

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
  hlist_of_seq_in f (map g xs) = hlist_of_seq_in (fun n x => f n (g x)) xs.
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
unfold hmap_in; elim: ix f g=> [|i ix IH] //= f g fK => [[]|[x xs]] //=.
rewrite fK (IH (fun n => f (Some n)) (fun n => g (Some n))) //.
move=> n; exact: (fK (Some n)).
Qed.

Lemma nth_hlist_hmap I (T_ S_ : I -> Type) (f : forall i, T_ i -> S_ i) ix :
  forall (l : hlist T_ ix) i, nth_hlist (hmap f l) i = f _ (nth_hlist l i).
Proof.
by elim: ix=> [[] []|i ix IH] /= [x xs] [j|] //=.
Qed.

Fixpoint hzip I (T_ S_ : I -> Type) ix :
  hlist T_ ix -> hlist S_ ix -> hlist (fun i => T_ i * S_ i)%type ix :=
  match ix with
  | [::] => fun _ _ => tt
  | i :: ix => fun lx ly => ((lx.1, ly.1), hzip lx.2 ly.2)
  end.

Fixpoint hlist_map I J (T_ : J -> Type) (f : I -> J) (ix : seq I) :
  hlist T_ (map f ix) = hlist (T_ \o f) ix :=
  match ix with
  | [::]    => erefl
  | i :: ix => congr1 (prod (T_ (f i))) (hlist_map T_ f ix)
  end.

Fixpoint hfun_map I J (T_ : J -> Type) (f : I -> J) S (ix : seq I) :
  hfun T_ (map f ix) S = hfun (T_ \o f) ix S :=
  match ix with
  | [::]    => erefl
  | i :: ix => congr1 (fun R => T_ (f i) -> R) (hfun_map T_ f S ix)
  end.

Fixpoint hlist_eq I (T_ S_ : I -> Type) (e : forall i, T_ i = S_ i) ix :
  hlist T_ ix = hlist S_ ix :=
  match ix with
  | [::]    => erefl
  | i :: ix => congr2 prod (e i) (hlist_eq e ix)
  end.

Fixpoint hfun_eq I (T_ S_ : I -> Type) (e : forall i, T_ i = S_ i) ix R :
  hfun T_ ix R = hfun S_ ix R :=
  match ix with
  | [::]    => erefl
  | i :: ix => congr2 (fun X Y => X -> Y) (e i) (hfun_eq e ix R)
  end.
