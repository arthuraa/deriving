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

(* We redefine some constants of the standard library here to avoid problems
   with universe inconsistency and opacity. *)

Definition congr1 T S (f : T -> S) x y (e : x = y) : f x = f y :=
  match e with erefl => erefl end.

Definition congr1V T S (f : T -> S) x y (e : x = y) : (congr1 f e)^-1 = congr1 f e^-1 :=
  match e with erefl => erefl end.

Definition etransV T (x y z : T) (p : x = y) (q : y = z) : (p * q)^-1 = q^-1 * p^-1 :=
  match p in _ = y return forall q : y = z, (p * q)^-1 = q^-1 * p^-1 with
  | erefl => fun q => match q with erefl => erefl end
  end q.

Definition etrans1p T (x y : T) (p : x = y) : erefl * p = p :=
  match p with erefl => erefl end.

Definition etransVp T (x y : T) (p : x = y) : p^-1 * p = erefl :=
  match p with erefl => erefl end.

Definition etranspV T (x y : T) (p : x = y) : p * p^-1 = erefl :=
  match p with erefl => erefl end.

Definition congr2 T1 T2 S (f : T1 -> T2 -> S) x1 y1 x2 y2 (e1 : x1 = y1) (e2 : x2 = y2) : f x1 x2 = f y1 y2 :=
  congr1 (f x1) e2 * congr1 (fun a => f a y2) e1.

Definition castCE T S (x y : T) (p : x = y) a : cast (fun=> S) p a = a :=
  match p with erefl => erefl end.

Definition castFE T (P Q : T -> Type) x y (p : x = y) :
  forall f a,
  cast (fun x => P x -> Q x) p f a = cast Q p (f (cast P p^-1 a)) :=
  match p with erefl => fun f a => erefl end.

Definition cast_idE T (P : T -> Type) x y (p : x = y) : cast id (congr1 P p) = cast P p :=
  match p with erefl => erefl end.

Definition castD T (P : T -> Type) x y z (p : x = y) (q : y = z) :
  forall a, cast P (p * q) a = cast P q (cast P p a) :=
  match q with erefl => fun a => erefl end.

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

Definition fnth T S (f : T -> S) (xs : seq T) (i : fin (size xs)) : S :=
  f (nth_fin i).
Arguments fnth {T S} f xs i.

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

Fixpoint hsum n : (fin n -> Type) -> Type :=
  match n with
  | 0    => fun T_ => void
  | n.+1 => fun T_ => (T_ None + hsum (fun i => T_ (Some i)))%type
  end.

Fixpoint hin n : forall (T_ : fin n -> Type) i, T_ i -> hsum T_ :=
  match n with
  | 0    => fun T_ i => match i with end
  | n.+1 => fun T_ i =>
    match i with
    | Some j => fun x => inr (@hin _ (fun i => T_ (Some i)) j x)
    | None   => fun x => inl x
    end
  end.

Fixpoint hcase S n : forall (T_ : fin n -> Type), (forall i, T_ i -> S) -> hsum T_ -> S :=
  match n with
  | 0    => fun T_ f x => match x with end
  | n.+1 => fun T_ f x =>
    match x with
    | inl x => f None x
    | inr x => hcase (fun i x => f (Some i) x) x
    end
  end.

Lemma hcaseE S n (T_ : fin n -> Type) (f : forall i, T_ i -> S)
  (i : fin n) (x : T_ i) : hcase f (hin x) = f i x.
Proof.
by elim: n T_ f i x=> [_ _ []|n IH] T_ f /= [i|//] x /=; rewrite IH.
Qed.

End Hsum.

Section Hlist.

Fixpoint hlist n : (fin n -> Type) -> Type :=
  match n with
  | 0    => fun T_ => unit
  | n.+1 => fun T_ => cell (T_ None) (hlist (fun i => T_ (Some i)))
  end.

Fixpoint hfun n : (fin n -> Type) -> Type -> Type :=
  match n with
  | 0    => fun T_ S => S
  | n.+1 => fun T_ S => T_ None -> hfun (fun i => T_ (Some i)) S
  end.

Fixpoint happ n : forall (T_ : fin n -> Type) S, hfun T_ S -> hlist T_ -> S :=
  match n with
  | 0    => fun T_ S f xs => f
  | n.+1 => fun T_ S f xs => happ (f xs.(hd)) xs.(tl)
  end.

Fixpoint hcurry n : forall (T_ : fin n -> Type) S, (hlist T_ -> S) -> hfun T_ S :=
  match n with
  | 0    => fun T_ S f => f tt
  | n.+1 => fun T_ S f => fun x => hcurry (fun xs => f (x ::: xs))
  end.

Lemma hcurryK n (T_ : fin n -> Type) S (f : hlist T_ -> S) xs : happ (hcurry f) xs = f xs.
Proof.
by elim: n T_ S f xs=> [??? [] //|n IH] /= ? /= ??[??]; rewrite IH.
Qed.

Fixpoint hnth n : forall (T_ : fin n -> Type), hlist T_ -> forall i, T_ i :=
  match n with
  | 0    => fun T_ xs i => match i with end
  | n.+1 => fun T_ xs i => match i with
                           | Some j => hnth xs.(tl) j
                           | None   => xs.(hd)
                           end
  end.

Fixpoint seq_of_hlist n S :
  forall (T_ : fin n -> Type),
    (forall i, T_ i -> S) -> hlist T_ -> seq S :=
  match n with
  | 0    => fun T_ f xs => [::]
  | n.+1 => fun T_ f xs => f None xs.(hd) :: seq_of_hlist (fun i => f (Some i)) xs.(tl)
  end.

Fixpoint hlist_of_seq n S :
  forall (T_ : fin n -> Type),
    (forall i, S -> option (T_ i)) -> seq S -> option (hlist T_) :=
  match n with
  | 0    => fun T_ f xs => Some tt
  | n.+1 => fun T_ f xs =>
    match xs with
    | [::] => None
    | x :: xs =>
      match f None x, hlist_of_seq (fun i => f (Some i)) xs with
      | Some y, Some ys => Some (y ::: ys)
      | _, _ => None
      end
    end
  end.

Lemma seq_of_hlistK n S (T_ : fin n -> Type)
  (f : forall i, T_ i -> S)
  (g : forall i, S -> option (T_ i)) :
  (forall i, pcancel (f i) (g i)) ->
  pcancel (seq_of_hlist f) (hlist_of_seq g).
Proof.
elim: n T_ f g=> [???? []|n IH] //= ? /= f g fK [??] /=.
by rewrite fK IH // => i ?; rewrite fK.
Qed.

Lemma hlist_of_seq_map
  n S R (T_ : fin n -> Type)
  (f : forall i, R -> option (T_ i)) (g : S -> R) (xs : seq S) :
  hlist_of_seq f (map g xs) = hlist_of_seq (fun i x => f i (g x)) xs.
Proof.
elim: n T_ f xs=> [??|n IH] //= ? f [] //= x xs.
by case: (f None (g x))=> //= ?; rewrite IH.
Qed.

Fixpoint hlist_of_fun n : forall (T_ : fin n -> Type) (f : forall i, T_ i), hlist T_ :=
  match n with
  | 0    => fun T_ f => tt
  | n.+1 => fun T_ f => f None ::: hlist_of_fun (fun i => f (Some i))
  end.

Lemma hnth_of_fun n T_ f i : hnth (@hlist_of_fun n T_ f) i = f i.
Proof.
by elim: n T_ f i=> [?? []|n IH] T_ f /= [i|] //=; rewrite IH.
Qed.

Fixpoint all_hlist n : forall T_, (@hlist n T_ -> Prop) -> Prop :=
  match n with
  | 0    => fun T_ P => P tt
  | n.+1 => fun T_ P => forall x, all_hlist (fun xs => P (x ::: xs))
  end.

Lemma all_hlistP n T_ P : @all_hlist n T_ P <-> (forall xs, P xs).
Proof.
elim: n T_ P=> /= [??|n IH T_ P /=].
  split; last exact; by move=> ? [].
split.
- by move=> H [x xs]; move/(_ x)/IH in H.
- by move=> H x; apply/IH=> ?.
Qed.

Fixpoint hmap n :
  forall (T_ S_ : fin n -> Type) (f : forall i, T_ i -> S_ i), hlist T_ -> hlist S_ :=
  match n with
  | 0    => fun _ _ _ _  => tt
  | n.+1 => fun _ _ f xs => f None xs.(hd) ::: hmap (fun j => f (Some j)) xs.(tl)
  end.

Lemma hmap_eq n (T_ S_ : fin n -> Type) (f g : forall i, T_ i -> S_ i) :
  (forall i, f i =1 g i) ->
  @hmap _ _ _ f =1 @hmap _ _ _ g.
Proof.
elim: n T_ S_ f g=> [//|n IH] /= T_ S_ /= f g efg [x xs].
by rewrite efg (IH _ _ _ _ (fun j => efg (Some j))).
Qed.

Lemma hmap1 n (T_ : fin n -> Type) (xs : hlist T_) : hmap (fun i => id) xs = xs.
Proof.
by elim: n T_ xs=> [_ [] //|n IH] /= T_ [x xs] /=; rewrite IH.
Qed.

Lemma hmap_comp
  n (T_ S_ R_ : fin n -> Type)
  (f : forall i, T_ i -> S_ i)
  (g : forall i, S_ i -> R_ i)
  (xs : hlist T_) :
  hmap g (hmap f xs) = hmap (fun i => g i \o f i) xs.
Proof.
by elim: n T_ S_ R_ f g xs=> //= n IH ??? /= ?? [??] /=; rewrite IH.
Qed.

Fixpoint hpmap n :
  forall (T_ S_ : fin n -> Type),
    (forall i, T_ i -> option (S_ i)) ->
    hlist T_ -> option (hlist S_) :=
  match n with
  | 0 => fun _ _ _ _ => Some tt
  | n.+1 => fun _ _ f xs =>
    if hpmap (fun i => f (Some i)) xs.(tl) is Some xs' then
      if f None xs.(hd) is Some x then
        Some (x ::: xs')
      else None
    else None
  end.

Lemma hmap_pK n (T_ S_ : fin n -> Type)
  (f : forall i, T_ i -> S_ i)
  (g : forall i, S_ i -> option (T_ i)) :
  (forall i, pcancel (f i) (g i)) -> pcancel (hmap f) (hpmap g).
Proof.
elim: n T_ S_ f g=> [????? [] //|n IH] /= ?? /= f g fgK [x xs] /=.
rewrite fgK /= IH // => i; exact: (fgK (Some i)).
Qed.

Lemma hnth_hmap n (T_ S_ : fin n -> Type)
  (f : forall i, T_ i -> S_ i) :
  forall (xs : hlist T_) i, hnth (hmap f xs) i = f _ (hnth xs i).
Proof.
elim: n T_ S_ f=> [//|/= n IH] T_ S_ /= f [x xs] [i|//].
by rewrite IH.
Qed.

Fixpoint hzip n :
  forall (T_ S_ : fin n -> Type),
    hlist T_ -> hlist S_ -> hlist (fun i => T_ i * S_ i)%type :=
  match n with
  | 0    => fun T_ S_ xs ys => tt
  | n.+1 => fun T_ S_ xs ys => (xs.(hd), ys.(hd)) ::: hzip xs.(tl) ys.(tl)
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
*)

Fixpoint hlist_eq n :
  forall (T_ S_ : fin n -> Type) (e : forall i, T_ i = S_ i),
  hlist T_ = hlist S_ :=
  match n with
  | 0    => fun T_ S_ e => erefl
  | n.+1 => fun T_ S_ e => congr2 cell (e None) (hlist_eq (fun i => e (Some i)))
  end.

Lemma hlist_eq_hmap n T_ S_ e xs :
  cast id (@hlist_eq n T_ S_ e) xs = hmap (fun i => cast id (e i)) xs.
Proof.
elim: n T_ S_ e xs=> [??? []|n IH] //= T_ S_ e [x xs] /=.
rewrite /congr2.
case: _ / (e None) x=> /= x; rewrite -IH.
by case: _ / (hlist_eq _) xs.
Qed.

Lemma hlist_eqV n (T_ S_ : fin n -> Type) e :
  (@hlist_eq n T_ S_ e)^-1 = hlist_eq (fun i => (e i)^-1).
Proof.
elim: n T_ S_ e=> //= n IH T_ S_ e.
by rewrite /congr2; case: _ / (e None)=> /=; rewrite -IH congr1V.
Qed.

Fixpoint hfun_eq n :
  forall (T_ S_ : fin n -> Type) (e : forall i, T_ i = S_ i) R,
  hfun T_ R = hfun S_ R :=
  match n with
  | 0    => fun T_ S_ e R => erefl
  | n.+1 => fun T_ S_ e R => congr2 (fun X Y => X -> Y) (e None) (hfun_eq (fun i => e (Some i)) R)
  end.

Lemma hfun_eqV n  T_ S_ e R :
  (@hfun_eq n T_ S_ e R)^-1 = hfun_eq (fun i => (e i)^-1) R.
Proof.
elim: n T_ S_ e=> //= n IH T_ S_ e; rewrite /congr2 /=.
by case: _ / (e None)=> /=; rewrite -IH congr1V.
Qed.

Lemma happ_eq n T_ S_ e R f xs :
  happ (cast id (@hfun_eq n T_ S_ e R) f) xs = happ f (cast id (hlist_eq e)^-1 xs).
Proof.
elim: n T_ S_ e f xs=> [|n IH] //= T_ S_ e f [x xs] /=.
rewrite /congr2; case: _ / (e None) x=> x /=.
transitivity (happ (cast id (hfun_eq (fun i => e (Some i)) R) (f x)) xs).
  by congr (happ _ xs); case: _ / (hfun_eq _ R) f=> f.
rewrite {}IH; congr (happ (f _) _); by case: _ / (hlist_eq _) xs.
Qed.

End Hlist.

Arguments fnth T S f xs i /.
Coercion happ : hfun >-> Funclass.

Unset Universe Polymorphism.

Section ProdCell.

Variables T S : Type.

Definition prod_of_cell (x : cell T S) := (x.(hd), x.(tl)).
Definition cell_of_prod (x : T * S) := Cell x.1 x.2.

Lemma prod_of_cellK : cancel prod_of_cell cell_of_prod.
Proof. by case. Qed.

Lemma cell_of_prodK : cancel cell_of_prod prod_of_cell.
Proof. by case. Qed.

End ProdCell.

Definition cell_eqMixin (T S : eqType) := CanEqMixin (@prod_of_cellK T S).
Canonical cell_eqType T S := EqType _ (@cell_eqMixin T S).
Definition cell_choiceMixin (T S : choiceType) :=
  CanChoiceMixin (@prod_of_cellK T S).
Canonical cell_choiceType T S :=
  Eval hnf in ChoiceType _ (@cell_choiceMixin T S).
Definition cell_countMixin (T S : countType) :=
  CanCountMixin (@prod_of_cellK T S).
Canonical cell_countType T S :=
  Eval hnf in CountType _ (@cell_countMixin T S).
Definition cell_finMixin (T S : finType) :=
  CanFinMixin (@prod_of_cellK T S).
Canonical cell_finType T S :=
  Eval hnf in FinType _ (@cell_finMixin T S).

Section HeterogeneousInstances.

Variables (K : Type) (sort : K -> Type).
Local Coercion sort : K >-> Sortclass.

Variables (sum_K : K -> K -> K).
Variables (sum_KP : forall sT sS, sort (sum_K sT sS) = (sort sT + sort sS)%type).

Variables (void_K : K).
Variables (void_KP : sort void_K = void).

Fixpoint hsum_lift_loop n :
  forall (T_ : fin n -> K), {sT | sort sT = hsum T_} :=
  match n with
  | 0    => fun T_ => exist _ void_K void_KP
  | n.+1 => fun T_ =>
    let sT := hsum_lift_loop (fun j => T_ (Some j)) in
    exist _ (sum_K (T_ None) (sval sT))
            (sum_KP (T_ None) (sval sT) * congr1 (sum (T_ None)) (svalP sT))
  end.

Variables (cell_K : K -> K -> K).
Variables (cell_KP : forall sT sS, sort (cell_K sT sS) = cell (sort sT) (sort sS)).

Variables (unit_K : K).
Variables (unit_KP : sort unit_K = unit).

Fixpoint hlist_lift_loop n :
  forall (T_ : fin n -> K), {sT | sort sT = hlist T_} :=
  match n with
  | 0    => fun T_ => exist _ unit_K unit_KP
  | n.+1 => fun T_ =>
    let sT := hlist_lift_loop (fun j => T_ (Some j)) in
    exist _ (cell_K (T_ None) (sval sT))
            (cell_KP (T_ None) (sval sT) * congr1 (cell (T_ None)) (svalP sT))
  end.

Variables (arr_K : K -> K -> K).
Variables (arr_KP : forall sT sS, sort (arr_K sT sS) = (sort sT -> sort sS)).

Fixpoint hfun_lift_loop n :
  forall (T_ : fin n -> K) (sS : K) , {sT | sort sT = hfun T_ sS} :=
  match n return forall (T_ : fin n -> K) (sS : K) , {sT | sort sT = hfun T_ sS} with
  | 0    => fun T_ sS => exist _ sS erefl
  | n.+1 => fun T_ sS =>
    let sT := hfun_lift_loop (fun j => T_ (Some j)) sS in
    exist _ (arr_K (T_ None) (sval sT))
            (arr_KP (T_ None) (sval sT) * congr1 (fun S => T_ None -> S) (svalP sT))
  end.

End HeterogeneousInstances.

Definition hsum_lift K sort n T_ sum_K sum_KP void_K void_KP :=
  @hsum_lift_loop K sort sum_K sum_KP void_K void_KP n T_.
Arguments hsum_lift {K} sort {n} _ _ _ _ _.

Definition hlist_lift K sort n T_ cell_K cell_KP unit_K unit_KP :=
  @hlist_lift_loop K sort cell_K cell_KP unit_K unit_KP n T_.
Arguments hlist_lift {K} sort {n} _ _ _ _ _.

Definition hfun_lift K sort n T_ arr_K arr_KP S :=
  @hlist_lift_loop K sort arr_K arr_KP n T_ S.
Arguments hfun_lift {K} sort {n} _ _ _ S.

Definition hsum_eqMixin n (T_ : fin n -> eqType) :=
  let lift := hsum_lift Equality.sort T_ sum_eqType (fun _ _ => erefl) void_eqType erefl in
  cast Equality.mixin_of (svalP lift) (Equality.class (sval lift)).
Canonical hsum_eqType n T_ :=
  EqType (hsum _) (@hsum_eqMixin n T_).

Definition hsum_choiceMixin n (T_ : fin n -> choiceType) :=
  let lift := hsum_lift Choice.sort T_ sum_choiceType (fun _ _ => erefl) void_choiceType erefl in
  cast Choice.mixin_of (svalP lift) (Choice.mixin (Choice.class (sval lift))).
Canonical hsum_choiceType n T_ :=
  Eval hnf in ChoiceType (hsum _) (@hsum_choiceMixin n T_).

Definition hsum_countMixin n (T_ : fin n -> countType) :=
  let lift := hsum_lift Countable.sort T_ sum_countType (fun _ _ => erefl) void_countType erefl in
  cast Countable.mixin_of (svalP lift) (Countable.mixin (Countable.class (sval lift))).
Canonical hsum_countType n T_ :=
  Eval hnf in CountType (hsum _) (@hsum_countMixin n T_).

Definition hlist_eqMixin n (T_ : fin n -> eqType) :=
  let lift := hlist_lift Equality.sort T_ cell_eqType (fun _ _ => erefl) unit_eqType erefl in
  cast Equality.mixin_of (svalP lift) (Equality.class (sval lift)).
Canonical hlist_eqType n T_ :=
  EqType (hlist _) (@hlist_eqMixin n T_).

Definition hlist_choiceMixin n (T_ : fin n -> choiceType) :=
  let lift := hlist_lift Choice.sort T_ cell_choiceType (fun _ _ => erefl) unit_choiceType erefl in
  cast Choice.mixin_of (svalP lift) (Choice.mixin (Choice.class (sval lift))).
Canonical hlist_choiceType n T_ :=
  Eval hnf in ChoiceType (hlist _) (@hlist_choiceMixin n T_).

Definition hlist_countMixin n (T_ : fin n -> countType) :=
  let lift := hlist_lift Countable.sort T_ cell_countType (fun _ _ => erefl) unit_countType erefl in
  cast Countable.mixin_of (svalP lift) (Countable.mixin (Countable.class (sval lift))).
Canonical hlist_countType n T_ :=
  Eval hnf in CountType (hlist _) (@hlist_countMixin n T_).
