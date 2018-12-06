From mathcomp Require Import all_ssreflect.
Require Import vds_sort Program.
Require Import Coq.Sorting.Permutation.

Set Implicit Arguments.
  
Program Definition part_leq s piv : { s' | size s' <= size s /\ all (leq^~ piv) s' } :=
  filter (leq^~ piv) s.

Next Obligation.
Proof.
  split. by rewrite size_filter count_size.
  exact: filter_all.
Qed.

Program Definition part_gt s piv : { s' | size s' <= size s /\ all [eta ltn piv] s'} :=
  filter [eta ltn piv] s.

Next Obligation.
Proof.
  split. by rewrite size_filter count_size.
  exact: filter_all.
Qed.

Program Definition split s piv : { (l, r) : seq nat * seq nat |
                                   size l <= size s /\ size r <= size s /\
                                   all (leq^~ piv) l /\ all [eta ltn piv] r /\
                                   Permutation s (l ++ r) } :=
  (part_leq s piv, part_gt s piv).

Next Obligation.
Proof.
  repeat split. by rewrite size_filter count_size. by rewrite size_filter count_size.
  exact: filter_all. exact: filter_all.
  elim: s => [| h s IHs] //=. case: ifP => Hpiv.
  rewrite ltnNge Hpiv //=. exact: perm_skip.
  rewrite ltnNge Hpiv //=. exact: Permutation_cons_app.
Qed.

Program Fixpoint qs s { measure (size s) } : { s' | sorted s' /\ Permutation s s' } :=
  match s with
  | [::] => s
  | piv :: rest =>
    let (pair, _) := split rest piv in
    match pair with
    | (l, r) => (qs l) ++ piv :: (qs r)
    end
  end.

Next Obligation.
Proof.
  apply/leP => //=.
Qed.

Next Obligation.
Proof.
  apply/leP => //=.
Qed.

Next Obligation.
  split. apply: sorted_cat_cons;rewrite /proj1_sig.
  destruct qs_obligation_2; destruct qs;
  move: a => [a1 a2]; rewrite -(all_perm (leq^~ piv) a2);
  replace l with l0 => //=; by move/(f_equal fst) in Heq_pair. 
  destruct qs_obligation_2; destruct qs; apply a.
  destruct qs_obligation_3; destruct qs; apply: sorted_cons;
  move: a => [a1 a2]; try exact; apply: (weaken_all_geq piv.+1);
  try rewrite -(all_perm [eta leq piv.+1] a2); replace r with l1 => //=; by move/(f_equal snd) in Heq_pair.
  apply: Permutation_cons_app.
  rewrite /proj1_sig. destruct qs. destruct qs.
  have Hp: Permutation (l ++ r) (x ++ x0).
  move: a a0 => [a1 a2] [a01 a02]. by apply: Permutation_app.
  apply: Permutation_trans. apply: p.
  replace l0 with l. replace l1 with r => //=.
  by move/(f_equal snd) in Heq_pair. by move/(f_equal fst) in Heq_pair.
Qed.

Definition quicksort s := let (s', _) := qs s in s'.

Lemma quicksort_sort : sort_spec quicksort.
Proof.
  rewrite /quicksort /sort_spec. move => s.
  split; destruct qs; apply a.
Qed.

(* 
Require Extraction.
Require Coq.extraction.ExtrOcamlNatInt. (* not a great idea but should be good for what we have *)

Extraction Language OCaml.
Extract Inductive list => "list" [ "[]" "(::)" ].
Extract Inductive prod => "(*)"  [ "(,)" ].

Extract Constant fst => "fst".
Extract Constant snd => "snd".

Extraction "quicksort.ml" part_leq part_gt split qs quicksort.
*)