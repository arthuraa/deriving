From mathcomp Require Import
  ssreflect ssrfun ssrbool ssrnat eqtype seq choice fintype order.

From deriving Require Import base ind tactics infer.

From Coq Require Import ZArith NArith String Ascii.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Open Scope deriving_scope.

Section TreeOfInd.

Variables (T : indDef).
Notation n := (Ind.Def.n T).
Let D := Ind.Def.decl T.

Import GenTree.
Import PolyType.
Import IndF.

Definition ind_arg :=
  hsum (fun i => hsum' (hsum' (type_of_arg (fun=> void))) (D i)).

Definition mk_ind_arg i (j : Ind.Cidx D i) (k : fin (size (nth_fin j))) :
  type_of_arg (fun=> void) (nth_fin k) -> ind_arg :=
  fun x => hin (hin (hin x)).

Definition proj_ind_arg
  i (j : Ind.Cidx D i) (k : fin (size (nth_fin j))) (x : ind_arg) :
  option (type_of_arg (fun=> void) (nth_fin k)) :=
  if hproj i x is Some x then
    if hproj j x is Some x then hproj k x
    else None
  else None.

Lemma mk_ind_argK i j k : pcancel (@mk_ind_arg i j k) (@proj_ind_arg i j k).
Proof. by move=> x; rewrite /proj_ind_arg !hinK. Qed.

Let wrap i (j : Ind.Cidx D i) (k : fin (size (nth_fin j))) :
  type_of_arg (fun=> tree ind_arg) (nth_fin k) -> tree ind_arg :=
  match nth_fin k as A
  return (type_of_arg (fun=> void) A -> ind_arg) ->
         type_of_arg (fun=> tree ind_arg) A -> tree ind_arg
  with
  | NonRec R  => fun c x => Leaf (c x)
  | Rec    i' => fun c x => x
  end (@mk_ind_arg i j k).

Definition tree_of_coq_ind : forall i, T i -> tree ind_arg :=
  rec (fun i x =>
         let j := constr x in
         Node (nat_of_fin j)
           (list_of_seq (seq_of_hlist (@wrap i j)
              (hmap' (type_of_arg_map (fun=> snd)) (args x))))).

Fixpoint coq_ind_of_tree i (x : tree ind_arg) : option (T i) :=
  match x with
  | Leaf _ => None
  | Node c xs =>
    if fin_of_nat (size (D i)) c isn't Some j then None else
    let xs := seq_of_list [seq (t, coq_ind_of_tree^~ t) | t <- xs] in
    if hlist_of_seq (fun k ts =>
                       match nth_fin k as A
                       return (ind_arg -> option (type_of_arg (fun=> void) A)) ->
                               option (type_of_arg T A) with
                       | NonRec R => fun f => if ts.1 is Leaf x then f x else None
                       | Rec i'   => fun _ => ts.2 i'
                       end (@proj_ind_arg i j k)) xs
    is Some args then Some (Roll (Cons args))
    else None
  end.

Lemma tree_of_coq_indK i : pcancel (@tree_of_coq_ind i) (@coq_ind_of_tree i).
Proof.
elim/indP: i / => i [j xs].
rewrite /tree_of_coq_ind recE /= -/tree_of_coq_ind.
rewrite nat_of_finK /hmap' !hmap_comp /=.
set xs' := hlist_of_seq _ _.
suffices -> : xs' = Some (hmap' (type_of_arg_map (fun=> tag)) xs) by [].
rewrite {}/xs' seq_of_list_map list_of_seqK hlist_of_seq_map /= /wrap.
move: (@mk_ind_arg i j) (@proj_ind_arg i j) (@mk_ind_argK i j).
elim: {j} (nth_fin j) xs=> //= - [S|i'] As IH /= xs C p CK.
  by rewrite CK IH //= => j x; rewrite CK.
case: xs=> [[x xP] xs] /=; rewrite xP IH //.
by move=> j ?; rewrite CK.
Qed.

End TreeOfInd.

Definition pack_tree_of_indK :=
  fun (T : Type) =>
  fun (sT_ind : indType) & phant_id (Ind.sort sT_ind) T =>
  @tree_of_coq_indK sT_ind (Ind.idx sT_ind).

Notation "[ 'derive' 'choiceMixin' 'for' T ]" :=
  (PcanChoiceMixin (@pack_tree_of_indK T _ id))
  (at level 0, format "[ 'derive'  'choiceMixin'  'for'  T ]") : form_scope.

Notation "[ 'derive' 'countMixin' 'for' T ]" :=
  (PcanCountMixin (@pack_tree_of_indK T _ id))
  (at level 0, format "[ 'derive' 'countMixin'  'for'  T ]") : form_scope.
