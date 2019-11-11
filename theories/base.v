From mathcomp Require Import
  ssreflect ssrfun ssrbool ssrnat eqtype seq choice fintype.

From void Require Import void.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Universe Polymorphism.

Declare Scope deriving_scope.
Delimit Scope deriving_scope with deriving.
Open Scope deriving_scope.

Definition cast T (P : T -> Type) x y (e : x = y) : P x -> P y :=
  match e with erefl => id end.

Arguments cast {_} _ {_ _} _.

Notation "e1 * e2" := (etrans e1 e2) : deriving_scope.
Notation "e ^-1" := (esym e) : deriving_scope.

(** An alternative to the standard prod type, to avoid name clashes and universe
    issues. *)

Record cell T S := Cell { hd : T; tl : S }.

Arguments Cell {_ _}.
Arguments hd {_ _}.
Arguments tl {_ _}.

Notation "x ::: y" := (Cell x y) (at level 60) : deriving_scope.

Module PolyType.

Record sig T (P : T -> Prop) := exist { sval : T; svalP : P sval }.

Arguments exist {T} P sval svalP.

Notation "{ x | P }" := (sig (fun x => P)) : type_scope.
Notation "{ x : T | P }" := (sig (fun x : T => P)) : type_scope.

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

Fixpoint all T (P : T -> bool) (xs : seq T) :=
  if xs is x :: xs then P x && all P xs else true.

End PolyType.

Import PolyType.

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
  | n.+1 => congr1 succn (size_map Some (enum_fin n) * size_enum_fin n)
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

Section Tuple.

Unset Elimination Schemes.
Record tuple T n := Tuple { tval : seq T; tvalP : size tval = n }.
Arguments Tuple {T n} _ _.
Set Elimination Schemes.

Definition nil_tuple T : tuple T 0 := Tuple [::] erefl.
Definition cons_tuple T n x xs : tuple T n.+1 :=
  Tuple (x :: tval xs) (congr1 succn (tvalP xs)).
Arguments nil_tuple {T}.
Arguments cons_tuple {T n} _ _.

Lemma tval_inj T n : injective (@tval T n).
Proof.
case=> [xs xsP] [ys ysP] /= e.
by case: ys / e ysP => ysP; rewrite (eq_irrelevance xsP ysP).
Qed.

Definition head T n (xs : tuple T n.+1) : T :=
  match tval xs as xs return size xs = n.+1 -> T with
  | [::]   => fun _ => ltac:(done)
  | x :: _ => fun _ => x
  end (tvalP xs).

Definition tail T n (xs : tuple T n.+1) : tuple T n :=
  match tval xs as xs return size xs = n.+1 -> tuple T n with
  | [::]    => fun _ => ltac:(done)
  | _ :: xs => fun e => Tuple xs (congr1 predn e)
  end (tvalP xs).

Fixpoint tnth T n : tuple T n -> fin n -> T :=
  match n with
  | 0    => fun xs i => match i with end
  | n.+1 => fun xs i => if i is Some j then tnth (tail xs) j else head xs
  end.

Definition tuple_of_seq T (xs : seq T) : tuple T (size xs) := Tuple xs erefl.

Definition map_tuple T S n (f : T -> S) (xs : tuple T n) : tuple S n :=
  Tuple (map f (tval xs)) (size_map f _ * tvalP xs).

End Tuple.

Section Ilist.

Variables (T : Type).

Definition ilist n := iter n (cell T) unit.

Fixpoint inth n : ilist n -> fin n -> T :=
  match n return ilist n -> fin n -> T with
  | 0    => fun l (i : void) => match i with end
  | n.+1 => fun l i => if i is Some j then inth l.(tl) j else l.(hd)
  end.

Fixpoint ilist_of_fun n : forall (f : fin n -> T), ilist n :=
  match n with
  | 0    => fun _ => tt
  | n.+1 => fun f => f None ::: ilist_of_fun (fun i => f (Some i))
  end.

Fixpoint inth_of_fun n : forall (f : fin n -> T) (i : fin n), inth (ilist_of_fun f) i = f i :=
  match n with
  | 0    => fun f i => match i with end
  | n.+1 => fun f i => if i is Some j then inth_of_fun (fun j => f (Some j)) j else erefl
  end.

Fixpoint ilist_of_seq s : ilist (size s) :=
  match s with
  | [::] => tt
  | x :: s => x ::: ilist_of_seq s
  end.

Fixpoint seq_of_ilist n : ilist n -> seq T :=
  match n with
  | 0    => fun l => [::]
  | n.+1 => fun l => l.(hd) :: seq_of_ilist l.(tl)
  end.

Fixpoint size_seq_of_ilist n : forall (xs : ilist n), size (seq_of_ilist xs) = n :=
  match n with
  | 0    => fun xs => erefl
  | n.+1 => fun xs => congr1 succn (size_seq_of_ilist xs.(tl))
  end.

End Ilist.

Fixpoint imap T S (f : T -> S) n : ilist T n -> ilist S n :=
  match n with
  | 0    => fun l => tt
  | n.+1 => fun l => f l.(hd) ::: imap f l.(tl)
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

Fixpoint izip T S n : ilist T n -> ilist S n -> ilist (T * S) n :=
  match n with
  | 0    => fun xs ys => tt
  | n.+1 => fun xs ys => (xs.(hd), ys.(hd)) ::: izip xs.(tl) ys.(tl)
  end.

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

Implicit Types (T S : Type).

Fixpoint hlist n : ilist Type n -> Type :=
  match n with
  | 0    => fun Ts => unit
  | n.+1 => fun Ts => cell Ts.(hd) (hlist Ts.(tl))
  end.

Fixpoint hfun n : ilist Type n -> Type -> Type :=
  match n with
  | 0    => fun Ts S => S
  | n.+1 => fun Ts S => Ts.(hd) -> hfun Ts.(tl) S
  end.

Fixpoint happ n : forall (Ts : ilist Type n) S, hfun Ts S -> hlist Ts -> S :=
  match n with
  | 0    => fun Ts S f xs => f
  | n.+1 => fun Ts S f xs => happ (f xs.(hd)) xs.(tl)
  end.

Fixpoint hcurry n : forall (Ts : ilist Type n) S, (hlist Ts -> S) -> hfun Ts S :=
  match n with
  | 0    => fun Ts S f => f tt
  | n.+1 => fun Ts S f => fun x => hcurry (fun xs => f (x ::: xs))
  end.

Lemma hcurryK n (Ts : ilist Type n) S (f : hlist Ts -> S) xs : happ (hcurry f) xs = f xs.
Proof.
by elim: n Ts S f xs=> [??? [] //|n IH] /= [??] /= ??[??]; rewrite IH.
Qed.

Fixpoint hnth n : forall (Ts : ilist Type n), hlist Ts -> forall i, inth Ts i :=
  match n with
  | 0    => fun Ts xs i => match i with end
  | n.+1 => fun Ts xs i => match i with
                           | Some j => hnth xs.(tl) j
                           | None   => xs.(hd)
                           end
  end.

(*
Fixpoint hlist_of_fun (f : forall i, T_ i) ix : hlist ix :=
  if ix is i :: ix then (f i, hlist_of_fun f ix) else tt.

Lemma hnth_of_fun f ix n :
  hnth (hlist_of_fun f ix) n = f (nth_fin n).
Proof. elim: ix n=> /= [|i ix IH] // [n|]; by rewrite ?IH. Qed.
*)

Fixpoint seq_of_hlist n S :
  forall (Ts : ilist Type n),
    (forall i, inth Ts i -> S) -> hlist Ts -> seq S :=
  match n with
  | 0    => fun Ts f xs => [::]
  | n.+1 => fun Ts f xs => f None xs.(hd) :: seq_of_hlist (fun i => f (Some i)) xs.(tl)
  end.

Fixpoint hlist_of_seq n S :
  forall (Ts : ilist Type n),
    (forall i, S -> option (inth Ts i)) -> seq S -> option (hlist Ts) :=
  match n with
  | 0    => fun Ts f xs => Some tt
  | n.+1 => fun Ts f xs =>
    match xs with
    | [::] => None
    | x :: xs =>
      match f None x, hlist_of_seq (fun i => f (Some i)) xs with
      | Some y, Some ys => Some (y ::: ys)
      | _, _ => None
      end
    end
  end.

Lemma seq_of_hlistK n S (Ts : ilist Type n)
  (f : forall i, inth Ts i -> S)
  (g : forall i, S -> option (inth Ts i)) :
  (forall i, pcancel (f i) (g i)) ->
  pcancel (seq_of_hlist f) (hlist_of_seq g).
Proof.
elim: n Ts f g=> [???? []|n IH] //= [??] /= f g fK [??] /=.
by rewrite fK IH // => i ?; rewrite fK.
Qed.

Lemma hlist_of_seq_in_map
  n S R (Ts : ilist Type n)
  (f : forall i, R -> option (inth Ts i)) (g : S -> R) (xs : seq S) :
  hlist_of_seq f (map g xs) = hlist_of_seq (fun i x => f i (g x)) xs.
Proof.
elim: n Ts f xs=> [??|n IH] //= [??] f [] //= x xs.
by case: (f None (g x))=> //= ?; rewrite IH.
Qed.

Fixpoint hlist_of_fun n : forall (Ts : ilist Type n) (f : forall i, inth Ts i), hlist Ts :=
  match n with
  | 0    => fun Ts f => tt
  | n.+1 => fun Ts f => f None ::: hlist_of_fun (fun i => f (Some i))
  end.

Lemma hnth_of_fun n Ts f i : hnth (@hlist_of_fun n Ts f) i = f i.
Proof.
by elim: n Ts f i=> [?? []|n IH] [T Ts] f /= [i|] //=; rewrite IH.
Qed.

Fixpoint all_hlist n : forall Ts, (@hlist n Ts -> Prop) -> Prop :=
  match n with
  | 0    => fun Ts P => P tt
  | n.+1 => fun Ts P => forall x, all_hlist (fun xs => P (x ::: xs))
  end.

Lemma all_hlistP n Ts P : @all_hlist n Ts P <-> (forall xs, P xs).
Proof.
elim: n Ts P=> /= [??|n IH [T Ts] P /=].
  split; last exact; by move=> ? [].
split.
- by move=> H [x xs]; move/(_ x)/IH in H.
- by move=> H x; apply/IH=> ?.
Qed.

Fixpoint hmap n :
  forall (Ts Ss : ilist Type n) (f : forall i, inth Ts i -> inth Ss i), hlist Ts -> hlist Ss :=
  match n with
  | 0    => fun _ _ _ _  => tt
  | n.+1 => fun _ _ f xs => f None xs.(hd) ::: hmap (fun j => f (Some j)) xs.(tl)
  end.

Lemma hmap_eq n (Ts Ss : ilist Type n) (f g : forall i, inth Ts i -> inth Ss i) :
  (forall i, f i =1 g i) ->
  @hmap _ _ _ f =1 @hmap _ _ _ g.
Proof.
elim: n Ts Ss f g=> [//|n IH] /= [T Ts] [S Ss] /= f g efg [x xs].
by rewrite efg (IH _ _ _ _ (fun j => efg (Some j))).
Qed.

Lemma hmap1 n (Ts : ilist Type n) (xs : hlist Ts) : hmap (fun i => id) xs = xs.
Proof.
by elim: n Ts xs=> [_ [] //|n IH] /= [T Ts] [x xs] /=; rewrite IH.
Qed.

Lemma hmap_comp
  n (Ts Ss Rs : ilist Type n)
  (f : forall i, inth Ts i -> inth Ss i)
  (g : forall i, inth Ss i -> inth Rs i)
  (xs : hlist Ts) :
  hmap g (hmap f xs) = hmap (fun i => g i \o f i) xs.
Proof.
by elim: n Ts Ss Rs f g xs=> //= n IH [??] [??] [??] /= ?? [??] /=; rewrite IH.
Qed.

Fixpoint hpmap n :
  forall (Ts Ss : ilist Type n),
    (forall i, inth Ts i -> option (inth Ss i)) ->
    hlist Ts -> option (hlist Ss) :=
  match n with
  | 0 => fun _ _ _ _ => Some tt
  | n.+1 => fun _ _ f xs =>
    if hpmap (fun i => f (Some i)) xs.(tl) is Some xs' then
      if f None xs.(hd) is Some x then
        Some (x ::: xs')
      else None
    else None
  end.

Lemma hmap_pK n (Ts Ss : ilist Type n)
  (f : forall i, inth Ts i -> inth Ss i)
  (g : forall i, inth Ss i -> option (inth Ts i)) :
  (forall i, pcancel (f i) (g i)) -> pcancel (hmap f) (hpmap g).
Proof.
elim: n Ts Ss f g=> [????? [] //|n IH] /= [T Ts] [S Ss] /= f g fgK [x xs] /=.
rewrite fgK /= IH // => i; exact: (fgK (Some i)).
Qed.

Lemma hnth_hmap n (Ts Ss : ilist Type n)
  (f : forall i, inth Ts i -> inth Ss i) :
  forall (xs : hlist Ts) i, hnth (hmap f xs) i = f _ (hnth xs i).
Proof.
elim: n Ts Ss f=> [//|/= n IH] [T Ts] [S Ss] /= f [x xs] [i|//].
by rewrite IH.
Qed.

Fixpoint hzip n :
  forall (Ts Ss : ilist Type n),
    hlist Ts -> hlist Ss -> hlist (imap (fun TS => TS.1 * TS.2)%type (izip Ts Ss)) :=
  match n with
  | 0    => fun Ts Ss xs ys => tt
  | n.+1 => fun Ts Ss xs ys => (xs.(hd), ys.(hd)) ::: hzip xs.(tl) ys.(tl)
  end.

(*
Fixpoint hlist_map I J (T_ : J -> Type) (f : I -> J) (ix : seq I) :
  hlist T_ (map f ix) = hlist (T_ \o f) ix :=
  match ix with
  | [::]    => erefl
  | i :: ix => congr1 (cell (T_ (f i))) (hlist_map T_ f ix)
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
  | i :: ix => congr2 cell (e i) (hlist_eq e ix)
  end.

Fixpoint hfun_eq I (T_ S_ : I -> Type) (e : forall i, T_ i = S_ i) ix R :
  hfun T_ ix R = hfun S_ ix R :=
  match ix with
  | [::]    => erefl
  | i :: ix => congr2 (fun X Y => X -> Y) (e i) (hfun_eq e ix R)
  end.
*)

End Hlist.

Coercion happ : hfun >-> Funclass.
