From Coq Require Import Setoid.
From HB Require Import structures.
From mathcomp Require Import
  ssreflect ssrfun ssrbool ssrnat eqtype seq choice fintype order.
Set SsrOldRewriteGoalsOrder.  (* change Set to Unset when porting the file, then remove the line when requiring MathComp >= 2.6 *)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Primitive Projections.

(* Backwards compatibility for hint locality attributes *)
Set Warnings "-unsupported-attributes".

Declare Scope deriving_scope.
Delimit Scope deriving_scope with deriving.
Open Scope deriving_scope.
Create HintDb deriving.

Notation "f \o g" := (fun x => f (g x)) (only parsing) : deriving_scope.

Section EqEqType.

Variable (T : eqType) (x y : T).

Definition eq_eqb (p q : x = y :> T) := true.

Lemma eq_eqbP : Equality.axiom eq_eqb.
Proof. move=> p q; apply: ReflectT; apply: eq_irrelevance. Qed.

HB.instance Definition _ := hasDecEq.Build (x = y) eq_eqbP.

End EqEqType.

Definition cast T (P : T -> Type) x y (e : x = y) : P x -> P y :=
  match e with erefl => id end.

Arguments cast {_} _ {_ _} _.
#[global]
Hint Unfold cast : deriving.

Notation "e1 * e2" := (etrans e1 e2) : deriving_scope.
Notation "e ^-1" := (esym e) : deriving_scope.

(* We redefine some constants of the standard library here to avoid problems
   with universe inconsistency and opacity. *)

Definition castK T (P : T -> Type) x y (e : x = y) :
  cancel (cast P e) (cast P e^-1) :=
  match e with erefl => fun _ => erefl end.

Definition castKV T (P : T -> Type) x y (e : x = y) :
  cancel (cast P e^-1) (cast P e) :=
  match e with erefl => fun _ => erefl end.

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

#[global]
Hint Unfold Logic.eq_sym : deriving.
#[global]
Hint Unfold Logic.eq_trans : deriving.
#[global]
Hint Unfold etrans : deriving.
#[global]
Hint Unfold esym : deriving.
#[global]
Hint Unfold congr1 : deriving.
#[global]
Hint Unfold f_equal : deriving.
#[global]
Hint Unfold fst : deriving.
#[global]
Hint Unfold snd : deriving.

(** An alternative to the standard prod type, to avoid name clashes and universe
    issues. *)
Set Universe Polymorphism.
Record cell T S := Cell { hd : T; tl : S }.

Arguments Cell {_ _}.
Arguments hd {_ _}.
Arguments tl {_ _}.

#[global]
Hint Unfold hd : deriving.
#[global]
Hint Unfold tl : deriving.

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

Definition sumn := foldr addn 0.

Fixpoint cat T (xs ys : seq T) :=
  if xs is x :: xs then x :: cat xs ys else ys.

Infix "++" := cat : deriving_scope.

Definition flatten T (xxs : seq (seq T)) : seq T :=
  foldr (@cat T) [::] xxs.

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

#[global]
Hint Unfold PolyType.sval : deriving.
#[global]
Hint Unfold PolyType.svalP : deriving.
#[global]
Hint Unfold PolyType.list_of_seq : deriving.
#[global]
Hint Unfold PolyType.seq_of_list : deriving.
#[global]
Hint Unfold PolyType.size : deriving.
#[global]
Hint Unfold PolyType.map : deriving.
#[global]
Hint Unfold PolyType.foldr : deriving.
#[global]
Hint Unfold PolyType.sumn : deriving.
#[global]
Hint Unfold PolyType.cat : deriving.
#[global]
Hint Unfold PolyType.flatten : deriving.
#[global]
Hint Unfold PolyType.all : deriving.

Fixpoint fin n :=
  if n is n.+1 then option (fin n) else void.
#[global]
Hint Unfold fin : deriving.

Fixpoint all_fin n : (fin n -> Prop) -> Prop :=
  match n with
  | 0    => fun P => True
  | n.+1 => fun P => P None /\ @all_fin n (fun i => P (Some i))
  end.
#[global]
Hint Unfold all_fin : deriving.

Lemma all_finP n (P : fin n -> Prop) : all_fin P <-> (forall i, P i).
Proof.
split; elim: n P=> [|n IH] P //=.
- case=> ? H [i|] //; exact: (IH (fun i => P (Some i))).
- by move=> H; split; [exact: (H None)|apply: IH; eauto].
Qed.

Fixpoint all_finb n : (fin n -> bool) -> bool :=
  match n with
  | 0    => fun f => true
  | n.+1 => fun f => f None && @all_finb n (fun i => f (Some i))
  end.
#[global]
Hint Unfold all_finb : deriving.

Fixpoint nth_fin T (xs : seq T) : fin (size xs) -> T :=
  match xs with
  | [::]    => fun n => match n with end
  | x :: xs => fun n => if n is Some n then nth_fin n else x
  end.
#[global]
Hint Unfold nth_fin : deriving.

Definition fnth T S (f : T -> S) (xs : seq T) (i : fin (size xs)) : S :=
  f (nth_fin i).
Arguments fnth {T S} f xs i.
#[global]
Hint Unfold fnth : deriving.

Definition fcons n T (x : T) (f : fin n -> T) : fin n.+1 -> T :=
  fun i => if i is Some i then f i else x.
#[global]
Hint Unfold fcons : deriving.

Definition fnil T : fin 0 -> T :=
  fun i => match i with end.
#[global]
Hint Unfold fnil : deriving.

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
#[global]
Hint Unfold leq_fin : deriving.

Fixpoint leq_finii n : forall i : fin n, @leq_fin n i i = inl erefl :=
  match n return forall i : fin n, leq_fin i i = inl erefl with
  | 0    => fun i => match i with end
  | n.+1 =>
    fun i => match i return @leq_fin n.+1 i i = inl erefl with
             | None => erefl
             | Some i =>
               congr1 (fun r =>
                         match r with
                         | inl e => inl (congr1 Some e)
                         | inr b => inr b
                         end)
                      (@leq_finii n i)
             end
  end.
#[global]
Hint Unfold leq_finii : deriving.

Fixpoint nat_of_fin n : fin n -> nat :=
  match n with
  | 0    => fun i => match i with end
  | n.+1 => fun i => if i is Some i then (nat_of_fin i).+1 else 0
  end.
#[global]
Hint Unfold nat_of_fin : deriving.

Fixpoint finW n : forall (m : fin n), fin (nat_of_fin m) -> fin n :=
  match n with
  | 0 => fun m => match m with end
  | n.+1 => fun m =>
    match m with
    | None => fun i => match i with end
    | Some m => fun i =>
      match i with
      | None => None
      | Some i => Some (@finW n m i)
      end
    end
  end.
#[global]
Hint Unfold finW : deriving.

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
#[global]
Hint Unfold fin_of_nat : deriving.

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
- case: (leq_fin j i)=> // [] [] //=.
  case: (leq_fin i j)=> [e|b _ <- //].
  by rewrite {1}e ltnn.
- case: (leq_fin i j)=> // _ ji <-.
  case: (leq_fin j i) ji => [e|b _ <- //].
  by rewrite {1}e ltnn.
Qed.

Fixpoint enum_fin n : seq (fin n) :=
  match n with
  | 0 => [::]
  | n.+1 => None :: map Some (enum_fin n)
  end.
#[global]
Hint Unfold enum_fin : deriving.

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

Fixpoint sum_of_fin n m : fin (n + m) -> fin n + fin m :=
  match n with
  | 0    => inr
  | n.+1 => fun i =>
    match i with
    | None => inl None
    | Some i => match @sum_of_fin n m i with
                | inl j => inl (Some j)
                | inr j => inr j
                end
    end
  end.
#[global]
Hint Unfold sum_of_fin : deriving.
Arguments sum_of_fin : clear implicits.

Fixpoint fin_of_sumL n m : fin n -> fin (n + m) :=
  match n return fin n -> fin (n + m) with
  | 0    => fun i => match i with end
  | n.+1 => fun i =>
              match i with
              | None => None
              | Some i => Some (@fin_of_sumL n m i)
              end
  end.
#[global]
Hint Unfold fin_of_sumL : deriving.
Arguments fin_of_sumL : clear implicits.

Fixpoint fin_of_sumR n m : fin m -> fin (n + m) :=
  match n with
  | 0 => id
  | n.+1 => fun i => Some (@fin_of_sumR n m i)
  end.
#[global]
Hint Unfold fin_of_sumR : deriving.
Arguments fin_of_sumR : clear implicits.

Definition fin_of_sum n m (i : fin n + fin m) : fin (n + m) :=
  match i with
  | inl i => fin_of_sumL n m i
  | inr i => fin_of_sumR n m i
  end.
#[global]
Hint Unfold fin_of_sum : deriving.
Arguments fin_of_sum : clear implicits.

Lemma sum_of_finK n m : cancel (sum_of_fin n m) (fin_of_sum n m).
Proof.
elim: n=> [|n IH] //= [i|] //=.
by case: (sum_of_fin n m i) (IH i)=> //= ? ->.
Qed.

Lemma fin_of_sumK n m : cancel (fin_of_sum n m) (sum_of_fin n m).
Proof.
case=> i /=; elim: n i => [|n IH] //=.
- by case=> [i|] //=; rewrite IH.
- by move=> i; rewrite IH.
Qed.

Fixpoint sumn_fin n : (fin n -> nat) -> nat :=
  match n with
  | 0    => fun _  => 0
  | n.+1 => fun ns => ns None + sumn_fin (fun i => ns (Some i))
  end.

Fixpoint tag_of_fin n : forall (m : fin n -> nat),
  fin (sumn_fin m) -> {i : fin n & fin (m i)} :=
  match n return forall (m : fin n -> nat), fin (sumn_fin m) -> {i : fin n & fin (m i)} with
  | 0 => fun _ (i : fin 0) => match i with end
  | n.+1 => fun m (i : fin (sumn_fin m)) =>
              match sum_of_fin (m None) (sumn_fin (fun j => m (Some j))) i with
              | inl j =>
                @Tagged _ None (fun i => fin (m i)) j
              | inr j =>
                let p := tag_of_fin j in
                @Tagged _ (Some (tag p)) (fun i => fin (m i)) (tagged p)
              end
  end.
#[global]
Hint Unfold tag_of_fin : deriving.
Arguments tag_of_fin {n} _ _.

Fixpoint fin_of_tag' n :
  forall (m : fin n -> nat) (i : fin n), fin (m i) -> fin (sumn_fin m) :=
  match n with
  | 0 => fun m i => match i with end
  | n.+1 => fun m i j =>
    let ij := match i return fin (m i) -> _ with
              | None => fun j => inl j
              | Some i => fun j => inr (fin_of_tag' j)
              end j in
    fin_of_sum _ _ ij
  end.
#[global]
Hint Unfold fin_of_tag' : deriving.
Arguments fin_of_tag' {n} _ _ _.

Definition fin_of_tag n m (p : {i : fin n & fin (m i)}) :=
  @fin_of_tag' n m (tag p) (tagged p).
#[global]
Hint Unfold fin_of_tag : deriving.

Lemma tag_of_finK n m : cancel (@tag_of_fin n m) (@fin_of_tag n m).
Proof.
rewrite /fin_of_tag; elim: n m => [m []|n IH m x] /=.
rewrite -[RHS](sum_of_finK x) /=.
by case: (sum_of_fin _ _ x) => {}x //=; rewrite IH.
Qed.

Lemma fin_of_tagK n m : cancel (@fin_of_tag n m) (@tag_of_fin n m).
Proof.
rewrite /fin_of_tag; case=> i j /=.
elim: n m i j => [m []|n IH m i j /=].
by rewrite fin_of_sumK; case: i j => [i|] j; rewrite ?IH.
Qed.

Definition map_fin (n : nat) T (f : fin n -> T) : seq T :=
  map f (enum_fin n).

Definition cast_fin n m (e : n = m) : forall (i : fin n.+1),
  cast fin (congr1 succn e) i =
  if i is Some j then Some (cast fin e j) else None :=
  match e with
  | erefl => fun i => if i is None then erefl else erefl
  end.

Unset Universe Polymorphism.

Fixpoint fin_eqClass n : Equality (fin n) :=
  match n return Equality (fin n) with
  | 0 =>
    Equality.on void
  | n.+1 =>
    Equality.on (option (HB.pack_for Equality.type (fin n) (fin_eqClass n)))
  end.

Fixpoint fin_choiceClass n : Choice (fin n) :=
  match n with
  | 0 =>
    Choice.on void
  | n.+1 =>
    Choice.on (option (HB.pack_for Choice.type (fin n) (fin_choiceClass n)))
  end.

Fixpoint fin_countClass n : Countable (fin n) :=
  match n with
  | 0 =>
    Countable.on void
  | n.+1 =>
    Countable.on (option (HB.pack_for Countable.type (fin n)
                            (fin_countClass n)))
  end.

Section FinInstances.

Variable n : nat.

HB.instance Definition _ := fin_eqClass n.
HB.instance Definition _ := fin_choiceClass n.
HB.instance Definition _ := fin_countClass n.

End FinInstances.

Set Universe Polymorphism.

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

#[global]
Hint Unfold ilist : deriving.
#[global]
Hint Unfold inth : deriving.
#[global]
Hint Unfold ilist_of_fun : deriving.
#[global]
Hint Unfold inth_of_fun : deriving.
#[global]
Hint Unfold ilist_of_seq : deriving.
#[global]
Hint Unfold seq_of_ilist : deriving.

Fixpoint imap T S (f : T -> S) n : ilist T n -> ilist S n :=
  match n with
  | 0    => fun l => tt
  | n.+1 => fun l => f l.(hd) ::: imap f l.(tl)
  end.
#[global]
Hint Unfold imap : deriving.

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

Fixpoint hsum I (T_ : I -> Type) (xs : seq I) : Type :=
  match xs with
  | [::]    => void
  | x :: xs => (T_ x + hsum T_ xs)%type
  end.

Fixpoint hin I (T_ : I -> Type) (xs : seq I) :
  forall (i : fin (size xs)), T_ (nth_fin i) -> hsum T_ xs :=
  match xs with
  | [::]    => fun (i : void) _ => match i with end
  | x :: xs => fun i =>
    match i with
    | None   => fun y => inl y
    | Some j => fun y => inr (@hin I T_ xs j y)
    end
  end.
Arguments hin {I T_ xs} i _.

Fixpoint hcase S I (T_ : I -> Type) (xs : seq I) :
  (forall (i : fin (size xs)), T_ (nth_fin i) -> S) -> hsum T_ xs -> S :=
  match xs with
  | [::]    => fun _ (x : void) => match x with end
  | x :: xs => fun f x =>
    match x with
    | inl y => f None y
    | inr y => @hcase S I T_ xs (fun j => f (Some j)) y
    end
  end.
Arguments hcase {S I T_ xs} f _.

Lemma hcaseE S I (T_ : I -> Type) (xs : seq I)
  (f : forall i : fin (size xs), T_ (nth_fin i) -> S)
  (i : fin (size xs)) (x : T_ (nth_fin i)) :
  hcase f (hin i x) = f i x.
Proof.
by elim: xs f i x => [?[]|x xs IH] f [j|] //= y; rewrite IH.
Qed.

Definition hproj I (T_ : I -> Type) (xs : seq I) (i : fin (size xs)) :
  hsum T_ xs -> option (T_ (nth_fin i)) :=
  hcase (fun (j : fin (size xs)) (y : T_ (nth_fin j)) =>
           if leq_fin j i is inl e then
             Some (cast (fun k => T_ (nth_fin k)) e y)
           else None).
Arguments hproj {I T_ xs} i _.

Lemma hinK I (T_ : I -> Type) (xs : seq I) (i : fin (size xs)) :
  pcancel (@hin I T_ xs i) (@hproj I T_ xs i).
Proof. by move=> x; rewrite /hproj hcaseE leq_finii. Qed.

End Hsum.

#[global]
Hint Unfold hsum : deriving.
#[global]
Hint Unfold hin : deriving.
#[global]
Hint Unfold hcase : deriving.
#[global]
Hint Unfold hproj : deriving.

Section Hlist.

Fixpoint hlist I (T_ : I -> Type) (xs : seq I) : Type :=
  match xs with
  | [::]    => unit
  | x :: xs => cell (T_ x) (hlist T_ xs)
  end.

Fixpoint hfun I (T_ : I -> Type) (xs : seq I) (S : Type) : Type :=
  match xs with
  | [::]    => S
  | x :: xs => T_ x -> hfun T_ xs S
  end.

Fixpoint happ I (T_ : I -> Type) (xs : seq I) :
  forall S, hfun T_ xs S -> hlist T_ xs -> S :=
  match xs with
  | [::]    => fun _ f _ => f
  | x :: xs => fun _ f l => happ (f l.(hd)) l.(tl)
  end.
Coercion happ : hfun >-> Funclass.

Fixpoint hcurry I (T_ : I -> Type) (xs : seq I) :
  forall S, (hlist T_ xs -> S) -> hfun T_ xs S :=
  match xs with
  | [::]    => fun _ f => f tt
  | x :: xs => fun _ f y => hcurry (fun l => f (y ::: l))
  end.

Lemma hcurryK I (T_ : I -> Type) (xs : seq I) S
  (f : hlist T_ xs -> S) (l : hlist T_ xs) :
  happ (hcurry f) l = f l.
Proof.
elim: xs f l => [|x xs IH] f l /=; first by case: l.
by case: l => y l; rewrite IH.
Qed.

Fixpoint hnth I (T_ : I -> Type) (xs : seq I) :
  hlist T_ xs -> forall (i : fin (size xs)), T_ (nth_fin i) :=
  match xs with
  | [::]    => fun _ i => match i with end
  | x :: xs => fun l i =>
    match i with
    | None   => l.(hd)
    | Some j => hnth l.(tl) j
    end
  end.
Coercion hnth : hlist >-> Funclass.

Fixpoint seq_of_hlist S I (T_ : I -> Type) (xs : seq I) :
  (forall (i : fin (size xs)), T_ (nth_fin i) -> S) ->
  hlist T_ xs -> seq S :=
  match xs with
  | [::]    => fun _ _ => [::]
  | x :: xs => fun f l =>
    f None l.(hd) :: seq_of_hlist (fun j => f (Some j)) l.(tl)
  end.

Fixpoint hlist_of_seq S I (T_ : I -> Type) (xs : seq I) :
  (forall (i : fin (size xs)), S -> option (T_ (nth_fin i))) ->
  seq S -> option (hlist T_ xs) :=
  match xs with
  | [::]    => fun _ _ => Some tt
  | x :: xs => fun f ys =>
    match ys with
    | [::]    => None
    | y :: ys =>
      match f None y, hlist_of_seq (fun j => f (Some j)) ys with
      | Some z, Some l => Some (z ::: l)
      | _, _ => None
      end
    end
  end.

Lemma seq_of_hlistK S I (T_ : I -> Type) (xs : seq I)
  (f : forall i : fin (size xs), T_ (nth_fin i) -> S)
  (g : forall i : fin (size xs), S -> option (T_ (nth_fin i))) :
  (forall i, pcancel (f i) (g i)) ->
  pcancel (@seq_of_hlist S I T_ xs f) (@hlist_of_seq S I T_ xs g).
Proof.
elim: xs f g => [??? []|x xs IH] //= f g fK [y l] /=.
by rewrite (fK None) /= IH // => i ?; rewrite (fK (Some i)).
Qed.

Lemma hlist_of_seq_map
  S R I (T_ : I -> Type) (xs : seq I)
  (f : forall i : fin (size xs), R -> option (T_ (nth_fin i)))
  (g : S -> R) (ys : seq S) :
  hlist_of_seq f (map g ys) = hlist_of_seq (fun i z => f i (g z)) ys.
Proof.
elim: xs f ys => [|x xs IH] f ys //=.
case: ys => [|y ys] //=.
by case: (f None (g y)) => //= ?; rewrite IH.
Qed.

Fixpoint hlist_of_fun I (T_ : I -> Type) (xs : seq I) :
  (forall i : fin (size xs), T_ (nth_fin i)) -> hlist T_ xs :=
  match xs with
  | [::]    => fun _ => tt
  | x :: xs => fun f =>
    f None ::: hlist_of_fun (fun j => f (Some j))
  end.

Lemma hnth_of_fun I (T_ : I -> Type) (xs : seq I)
  (f : forall i : fin (size xs), T_ (nth_fin i)) (i : fin (size xs)) :
  hnth (hlist_of_fun f) i = f i.
Proof.
by elim: xs f i => [?[]|x xs IH] /= f [j|] //=; rewrite IH.
Qed.

Fixpoint all_hlist I (T_ : I -> Type) (xs : seq I) :
  (hlist T_ xs -> Prop) -> Prop :=
  match xs with
  | [::]    => fun P => P tt
  | x :: xs => fun P =>
    forall (y : T_ x), all_hlist (fun l => P (y ::: l))
  end.

Lemma all_hlistP I (T_ : I -> Type) (xs : seq I) P :
  @all_hlist I T_ xs P <-> (forall l, P l).
Proof.
elim: xs P => [|x xs IH] P /=.
  by split => [h [] //|h]; apply: h.
split.
- by move=> H [y l]; move/(_ y): H; rewrite IH; apply.
- by move=> H y; apply/IH=> ?.
Qed.

Fixpoint hfold S I (T_ : I -> Type)
  (f : forall i, T_ i -> S -> S) (a : S) (xs : seq I) :
  hlist T_ xs -> S :=
  match xs with
  | [::]    => fun _ => a
  | x :: xs => fun l => f x l.(hd) (hfold f a l.(tl))
  end.

End Hlist.

#[global]
Hint Unfold hlist : deriving.
#[global]
Hint Unfold hfun : deriving.
#[global]
Hint Unfold happ : deriving.
#[global]
Hint Unfold hcurry : deriving.
#[global]
Hint Unfold hnth : deriving.
#[global]
Hint Unfold seq_of_hlist : deriving.
#[global]
Hint Unfold hlist_of_seq : deriving.
#[global]
Hint Unfold hlist_of_fun : deriving.
#[global]
Hint Unfold all_hlist : deriving.
#[global]
Hint Unfold hfold : deriving.

Section Hmap.

Fixpoint hmap I (T_ S_ : I -> Type) (f : forall i, T_ i -> S_ i)
  (xs : seq I) : hlist T_ xs -> hlist S_ xs :=
  match xs with
  | [::]    => fun _ => tt
  | x :: xs => fun l => f x l.(hd) ::: hmap f l.(tl)
  end.

Lemma hmap_eq I (T_ S_ : I -> Type) (f g : forall i, T_ i -> S_ i) :
  (forall i, f i =1 g i) ->
  forall (xs : seq I), @hmap I T_ S_ f xs =1 @hmap I T_ S_ g xs.
Proof.
move=> efg; elim=> [[] //|x xs IH] /= [y l] /=.
by rewrite efg IH.
Qed.

Lemma hmap1 I (T_ : I -> Type) (xs : seq I) (l : hlist T_ xs) :
  hmap (fun i => id) l = l.
Proof.
by elim: xs l => [[] //|x xs IH] /= [??] /=; rewrite IH.
Qed.

Lemma hmap_comp I (T_ S_ R_ : I -> Type)
  (f : forall i, T_ i -> S_ i) (g : forall i, S_ i -> R_ i)
  (xs : seq I) (l : hlist T_ xs) :
  hmap g (hmap f l) = hmap (fun i => g i \o f i) l.
Proof.
by elim: xs l => [[] //|x xs IH] //= [??] /=; rewrite IH.
Qed.

Fixpoint hpmap I (T_ S_ : I -> Type)
  (f : forall i, T_ i -> option (S_ i)) (xs : seq I) :
  hlist T_ xs -> option (hlist S_ xs) :=
  match xs with
  | [::]    => fun _ => Some tt
  | x :: xs => fun l =>
    if hpmap f l.(tl) is Some l' then
      if f x l.(hd) is Some y then Some (y ::: l')
      else None
    else None
  end.

Lemma hmap_pK I (T_ S_ : I -> Type)
  (f : forall i, T_ i -> S_ i)
  (g : forall i, S_ i -> option (T_ i)) :
  (forall i, pcancel (f i) (g i)) ->
  forall xs, pcancel (@hmap I T_ S_ f xs) (@hpmap I S_ T_ g xs).
Proof.
move=> fgK; elim=> [[] //|x xs IH] /= [??] /=.
by rewrite fgK /= IH.
Qed.

Lemma hnth_hmap I (T_ S_ : I -> Type) (f : forall i, T_ i -> S_ i)
  (xs : seq I) (l : hlist T_ xs) (i : fin (size xs)) :
  hnth (hmap f l) i = f (nth_fin i) (hnth l i).
Proof.
by elim: xs l i => [_ []|x xs IH] //= [??] [j|] //=; rewrite IH.
Qed.

Fixpoint hzip I (T_ S_ : I -> Type) (xs : seq I) :
  hlist T_ xs -> hlist S_ xs ->
  hlist (fun i => T_ i * S_ i)%type xs :=
  match xs with
  | [::]    => fun _ _ => tt
  | x :: xs => fun l1 l2 =>
    (l1.(hd), l2.(hd)) ::: hzip l1.(tl) l2.(tl)
  end.

End Hmap.

#[global]
Hint Unfold hmap : deriving.
#[global]
Hint Unfold hpmap : deriving.
#[global]
Hint Unfold hzip : deriving.

Section Hlist2.

Fixpoint hlist2 I (T_ : nat -> I -> Type) (xss : seq (seq I)) : Type :=
  match xss with
  | [::]      => unit
  | xs :: xss =>
    cell (hlist (T_ 0) xs) (@hlist2 I (fun k => T_ k.+1) xss)
  end.

Fixpoint hfun2 I (T_ : nat -> I -> Type) (xss : seq (seq I)) (S : Type) : Type :=
  match xss with
  | [::]      => S
  | xs :: xss =>
    hfun (T_ 0) xs (@hfun2 I (fun k => T_ k.+1) xss S)
  end.

Fixpoint happ2 I (T_ : nat -> I -> Type) (xss : seq (seq I)) :
  forall S, hfun2 T_ xss S -> hlist2 T_ xss -> S :=
  match xss with
  | [::]      => fun _ f _ => f
  | xs :: xss => fun _ f l =>
    @happ2 I (fun k => T_ k.+1) xss _ (happ f l.(hd)) l.(tl)
  end.
Coercion happ2 : hfun2 >-> Funclass.

Fixpoint hcurry2 I (T_ : nat -> I -> Type) (xss : seq (seq I)) :
  forall S, (hlist2 T_ xss -> S) -> hfun2 T_ xss S :=
  match xss with
  | [::]      => fun _ f => f tt
  | xs :: xss => fun _ f =>
    hcurry (fun (l1 : hlist (T_ 0) xs) =>
              @hcurry2 I (fun k => T_ k.+1) xss _
                (fun l2 => f (l1 ::: l2)))
  end.

Fixpoint hmap2 I (T_ S_ : nat -> I -> Type)
  (f : forall k i, T_ k i -> S_ k i) (xss : seq (seq I)) :
  hlist2 T_ xss -> hlist2 S_ xss :=
  match xss with
  | [::]      => fun _ => tt
  | xs :: xss => fun l =>
    hmap (f 0) l.(hd) :::
    @hmap2 I (fun k => T_ k.+1) (fun k => S_ k.+1)
           (fun k => f k.+1) xss l.(tl)
  end.

Fixpoint all_hlist2 I (T_ : nat -> I -> Type) (xss : seq (seq I)) :
  (hlist2 T_ xss -> Prop) -> Prop :=
  match xss with
  | [::]      => fun P => P tt
  | xs :: xss => fun P =>
    all_hlist (fun (l1 : hlist (T_ 0) xs) =>
                 @all_hlist2 I (fun k => T_ k.+1) xss
                             (fun l2 => P (l1 ::: l2)))
  end.

Lemma all_hlist2P I (T_ : nat -> I -> Type) (xss : seq (seq I)) P :
  @all_hlist2 I T_ xss P <-> (forall l, P l).
Proof.
elim: xss T_ P => [|xs xss IH] T_ P /=.
  by split => [h [] //|h]; apply: h.
rewrite all_hlistP; split.
- by move=> H [l1 l2]; move/(_ l1): H; rewrite IH; apply.
- by move=> H l1; apply/IH=> l2.
Qed.

End Hlist2.

#[global]
Hint Unfold hlist2 : deriving.
#[global]
Hint Unfold hfun2 : deriving.
#[global]
Hint Unfold happ2 : deriving.
#[global]
Hint Unfold hcurry2 : deriving.
#[global]
Hint Unfold hmap2 : deriving.
#[global]
Hint Unfold all_hlist2 : deriving.

Section Bridge.

Fixpoint seqOf_fn n I : (fin n -> seq I) -> seq (seq I) :=
  match n with
  | 0    => fun _ => [::]
  | n.+1 => fun D => D None :: seqOf_fn (fun i => D (Some i))
  end.

Definition fin_at n A (S : fin n -> A) (default : A) (k : nat) : A :=
  match fin_of_nat n k with
  | Some i => S i
  | None   => default
  end.

End Bridge.

#[global]
Hint Unfold seqOf_fn : deriving.
#[global]
Hint Unfold fin_at : deriving.

Fixpoint hlist_eq I (T_ S_ : I -> Type) (e : forall i, T_ i = S_ i)
  (xs : seq I) : hlist T_ xs = hlist S_ xs :=
  match xs with
  | [::]    => erefl
  | x :: xs => congr2 cell (e x) (hlist_eq e xs)
  end.
#[global]
Hint Unfold hlist_eq : deriving.

Lemma hlist_eq_hmap I (T_ S_ : I -> Type) (e : forall i, T_ i = S_ i)
  (xs : seq I) (l : hlist T_ xs) :
  cast id (@hlist_eq I T_ S_ e xs) l = hmap (fun i => cast id (e i)) l.
Proof.
elim: xs l => [[] //|x xs IH] /= [y l] /=.
rewrite /congr2.
case: _ / (e x) y => /= y; rewrite -IH.
by case: _ / (hlist_eq e xs) l.
Qed.

Lemma hlist_eqV I (T_ S_ : I -> Type) (e : forall i, T_ i = S_ i) (xs : seq I) :
  (@hlist_eq I T_ S_ e xs)^-1 = hlist_eq (fun i => (e i)^-1) xs.
Proof.
elim: xs => //= x xs IH.
by rewrite /congr2; case: _ / (e x)=> /=; rewrite -IH congr1V.
Qed.

Fixpoint hfun_eq I (T_ S_ : I -> Type) (e : forall i, T_ i = S_ i)
  (xs : seq I) (R : Type) : hfun T_ xs R = hfun S_ xs R :=
  match xs with
  | [::]    => erefl
  | x :: xs => congr2 (fun X Y => X -> Y) (e x) (hfun_eq e xs R)
  end.
#[global]
Hint Unfold hfun_eq : deriving.

Lemma hfun_eqV I (T_ S_ : I -> Type) (e : forall i, T_ i = S_ i)
  (xs : seq I) R :
  (@hfun_eq I T_ S_ e xs R)^-1 = hfun_eq (fun i => (e i)^-1) xs R.
Proof.
elim: xs => //= x xs IH.
by rewrite /congr2; case: _ / (e x)=> /=; rewrite -IH congr1V.
Qed.

Lemma happ_eq I (T_ S_ : I -> Type) (e : forall i, T_ i = S_ i)
  (xs : seq I) R f l :
  happ (cast id (@hfun_eq I T_ S_ e xs R) f) l =
  happ f (cast id (hlist_eq e xs)^-1 l).
Proof.
elim: xs f l => [|x xs IH] //= f [y l] /=.
rewrite /congr2; case: _ / (e x) y => y /=.
transitivity (happ (cast id (hfun_eq e xs R) (f y)) l).
  by congr (happ _ l); case: _ / (hfun_eq e xs R) f => f.
rewrite {}IH; congr (happ (f _) _); by case: _ / (hlist_eq e xs) l.
Qed.

Arguments fnth T S f xs i /.
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

Unset Universe Polymorphism.

Section CellEqType.
Variables T S : eqType.
HB.instance Definition _ :=
  Equality.copy (cell T S) (can_type (@prod_of_cellK T S)).
End CellEqType.

Section CellChoiceType.
Variables T S : choiceType.
HB.instance Definition _ :=
  Choice.copy (cell T S) (can_type (@prod_of_cellK T S)).
End CellChoiceType.

Section CellCountType.
Variables T S : countType.
HB.instance Definition _ :=
  Countable.copy (cell T S) (can_type (@prod_of_cellK T S)).
End CellCountType.

Section CellFinType.
Variables T S : finType.
HB.instance Definition _ :=
  Finite.copy (cell T S) (can_type (@prod_of_cellK T S)).
End CellFinType.

Section HeterogeneousInstances.

Variables (K : Type) (sort : K -> Type).
Local Coercion sort : K >-> Sortclass.

Variables (sum_K : K -> K -> K).
Variables (sum_KP : forall sT sS, sort (sum_K sT sS) = (sort sT + sort sS)%type).

Variables (void_K : K).
Variables (void_KP : sort void_K = void).

Fixpoint hsum_lift_loop I (T_ : I -> K) (xs : seq I) {struct xs} :
  {sT : K | sort sT = hsum (fun i => sort (T_ i)) xs} :=
  match xs with
  | [::]    => exist _ void_K void_KP
  | x :: xs =>
    let sT := hsum_lift_loop T_ xs in
    exist _ (sum_K (T_ x) (sval sT))
            (sum_KP (T_ x) (sval sT) * congr1 (sum (sort (T_ x))) (svalP sT))
  end.

Variables (cell_K : K -> K -> K).
Variables (cell_KP : forall sT sS, sort (cell_K sT sS) = cell (sort sT) (sort sS)).

Variables (unit_K : K).
Variables (unit_KP : sort unit_K = unit).

Fixpoint hlist_lift_loop I (T_ : I -> K) (xs : seq I) {struct xs} :
  {sT : K | sort sT = hlist (fun i => sort (T_ i)) xs} :=
  match xs with
  | [::]    => exist _ unit_K unit_KP
  | x :: xs =>
    let sT := hlist_lift_loop T_ xs in
    exist _ (cell_K (T_ x) (sval sT))
            (cell_KP (T_ x) (sval sT) * congr1 (cell (sort (T_ x))) (svalP sT))
  end.

Variables (arr_K : K -> K -> K).
Variables (arr_KP : forall sT sS, sort (arr_K sT sS) = (sort sT -> sort sS)).

Fixpoint hfun_lift_loop I (T_ : I -> K) (xs : seq I) (sS : K) {struct xs} :
  {sT : K | sort sT = hfun (fun i => sort (T_ i)) xs sS} :=
  match xs with
  | [::]    => exist _ sS erefl
  | x :: xs =>
    let sT := hfun_lift_loop T_ xs sS in
    exist _ (arr_K (T_ x) (sval sT))
            (arr_KP (T_ x) (sval sT) * congr1 (fun S => sort (T_ x) -> S) (svalP sT))
  end.

End HeterogeneousInstances.

Definition hsum_lift K sort I xs T_ sum_K sum_KP void_K void_KP :=
  @hsum_lift_loop K sort sum_K sum_KP void_K void_KP I T_ xs.
Arguments hsum_lift {K} sort {I} xs _ _ _ _ _.

Definition hlist_lift K sort I xs T_ cell_K cell_KP unit_K unit_KP :=
  @hlist_lift_loop K sort cell_K cell_KP unit_K unit_KP I T_ xs.
Arguments hlist_lift {K} sort {I} xs _ _ _ _ _.

Definition hfun_lift K sort I xs T_ arr_K arr_KP S :=
  @hfun_lift_loop K sort arr_K arr_KP I T_ xs S.
Arguments hfun_lift {K} sort {I} xs _ _ _ S.

Section HSumEqType.

Variables (I : Type) (xs : seq I) (T_ : I -> eqType).

Definition hsum_eqType :=
  let sum_eqType := fun A B : eqType => Equality.clone (A + B)%type _ in
  let void_eqType := Equality.clone void _ in
  let lift := hsum_lift Equality.sort xs T_ sum_eqType (fun _ _ => erefl) void_eqType erefl in
  cast (fun A => Equality A) (svalP lift) (Equality.class (sval lift)).

HB.instance Definition _ := hsum_eqType.

End HSumEqType.

Section HSumChoiceType.

Variables (I : Type) (xs : seq I) (T_ : I -> choiceType).

Definition hsum_choiceType :=
  let sum_choiceType := fun A B : choiceType => Choice.clone (A + B)%type _ in
  let void_choiceType := Choice.clone void _ in
  let lift := hsum_lift Choice.sort xs T_ sum_choiceType (fun _ _ => erefl) void_choiceType erefl in
  cast (fun A => Choice A) (svalP lift) (Choice.class (sval lift)).

HB.instance Definition _ := hsum_choiceType.

End HSumChoiceType.

Section HSumCountType.

Variables (I : Type) (xs : seq I) (T_ : I -> countType).

Definition hsum_countType :=
  let sum_countType := fun A B : countType => Countable.clone (A + B)%type _ in
  let void_countType := Countable.clone void _ in
  let lift := hsum_lift Countable.sort xs T_ sum_countType (fun _ _ => erefl) void_countType erefl in
  cast (fun A => Countable A) (svalP lift) (Countable.class (sval lift)).

HB.instance Definition _ := hsum_countType.

End HSumCountType.

Section HListEqType.

Variables (I : Type) (xs : seq I) (T_ : I -> eqType).

Definition hlist_eqType :=
  let cell_eqType := fun A B : eqType => Equality.clone (cell A B)%type _ in
  let unit_eqType := Equality.clone unit _ in
  let lift := hlist_lift Equality.sort xs T_ cell_eqType (fun _ _ => erefl) unit_eqType erefl in
  cast (fun A => Equality A) (svalP lift) (Equality.class (sval lift)).

HB.instance Definition _ := hlist_eqType.

End HListEqType.

Section HListChoiceType.

Variables (I : Type) (xs : seq I) (T_ : I -> choiceType).

Definition hlist_choiceType :=
  let cell_choiceType := fun A B : choiceType => Choice.clone (cell A B)%type _ in
  let unit_choiceType := Choice.clone unit _ in
  let lift := hlist_lift Choice.sort xs T_ cell_choiceType (fun _ _ => erefl) unit_choiceType erefl in
  cast (fun A => Choice A) (svalP lift) (Choice.class (sval lift)).

HB.instance Definition _ := hlist_choiceType.

End HListChoiceType.

Section HListCountType.

Variables (I : Type) (xs : seq I) (T_ : I -> countType).

Definition hlist_countType :=
  let cell_countType := fun A B : countType => Countable.clone (cell A B)%type _ in
  let unit_countType := Countable.clone unit _ in
  let lift := hlist_lift Countable.sort xs T_ cell_countType (fun _ _ => erefl) unit_countType erefl in
  cast (fun A => Countable A) (svalP lift) (Countable.class (sval lift)).

HB.instance Definition _ := hlist_countType.

End HListCountType.

Set Universe Polymorphism.

Fixpoint hlist1' m : (fin m.+1 -> Type) -> Type :=
  match m with
  | 0    => fun X => X None
  | m.+1 => fun X => X None * hlist1' (fun i => X (Some i))
  end%type.
#[global]
Hint Unfold hlist1' : deriving.

Fixpoint hnth1' m : forall T, @hlist1' m T -> forall i : fin m.+1, T i :=
  match m with
  | 0 =>
    fun T l i => if i isn't Some i then l else match i with end
  | m.+1 =>
    fun T l i => if i isn't Some i then l.1 else @hnth1' m _ l.2 i
  end.
#[global]
Hint Unfold hnth1' : deriving.

Definition hlist1 m :=
  match m return (fin m -> Type) -> Type with
  | 0    => fun _ => unit
  | n.+1 => fun X => hlist1' X
  end.
#[global]
Hint Unfold hlist1 : deriving.

Definition hnth1 m :=
  match m return forall (T : fin m -> Type) (l : hlist1 T) i, T i with
  | 0    => fun _ _ i => match i with end
  | n.+1 => fun X l i => hnth1' l i
  end.
Coercion hnth1 : hlist1 >-> Funclass.
#[global]
Hint Unfold hnth1 : deriving.
