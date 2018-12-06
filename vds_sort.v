From mathcomp Require Import all_ssreflect.
Require Import Coq.Sorting.Permutation.

Set Implicit Arguments.

Section sorted.

  Fixpoint sorted (xs : seq nat) :=
    match xs with
    | [::] => true
    | x :: t => match t with
                | [::] => true
                | y :: tl => (x <= y) && sorted t
                end
    end.

  Lemma sorted_cat_cons x (s t : seq nat) : all (leq^~ x) s ->
    sorted s -> sorted (x :: t) -> sorted (s ++ x :: t).
  Proof.
    elim: s => [|h s] //=. case: s => //=.
    move => L /andP [Hleq _] _ Ht.
      by rewrite Hleq andTb.
      move => k s IH. move/and3P => [Hhx Hkx Hall].
      move/andP => [Hhk Hs] Ht. rewrite Hhk andTb.
      apply: IH. by rewrite Hkx Hall.
      exact. exact.
  Qed.

  Lemma sorted_cat_cons_e x (s t : seq nat) : all (leq^~ x) s &&
    sorted s && sorted (x :: t) = sorted (s ++ x :: t).
  Proof.
    elim: s => [|h s] //=. case: s => //=.
    case: (h <= x) => //=.
    move => k s IH. rewrite -IH.
    case Hhk: (h <= k) => //=. case Hkx: (k <= x) => //=.
    have Hhx: (h <= x).
    { apply: leq_trans. apply: Hhk. apply: Hkx. }
      by rewrite Hhx andTb. by rewrite andbF. by rewrite andbF.
  Qed.

  Lemma sorted_cons x s : sorted s -> all (geq^~ x) s -> sorted (x :: s).
  Proof.
    case: s => [| h s] //=. case: s => [| k s] //=.
    by move => /andP [-> ->] /and3P [-> _ _].
  Qed.

  Lemma sorted_cons_e x s : sorted s && all (geq^~ x) s = sorted (x :: s).
  Proof.
    case: s => [| h s] //=. case: s => [| k s] //=.
    rewrite andbCA !andbA.
  Admitted.

  Lemma sorted_rest x s : sorted (x :: s) -> sorted s.
  Proof.
    case: s => [| h s] //=. by move => /andP [_ ->].
  Qed.

  Lemma cat_sorted_l s t : sorted (s ++ t) -> sorted s.
  Proof.
    elim: t => [| y t IH] //=. by rewrite cats0.
    rewrite -sorted_cat_cons_e. by move/andP => [/andP [_ ->] _].
  Qed.

  Lemma cat_sorted_r s t : sorted (s ++ t) -> sorted t.
  Proof.
    elim: s => [| x s IH] // H. rewrite cat_cons in H.
    apply: IH. by move/sorted_rest: H.
  Qed.
  
End sorted.


Section spec.

  Definition sort_spec sort_fun := forall s, sorted (sort_fun s) /\ Permutation s (sort_fun s).

End spec.

Section insert.

  (* insert into sorted list *)
  Fixpoint seq_insert x s :=
    match s with
    | [::] => [:: x]
    | h :: t => if x == h
                then h :: t
                else if x < h
                     then [:: x, h & t]
                     else h :: (seq_insert x t)
    end.

  Lemma sorted_insert x s : sorted s -> sorted (seq_insert x s).
  Proof.
    elim: s => [| h s] //=. case: s => [| h' s] //=.
    move => _ _. case: ifP => Heq //=. case: ifP => Hlt //=.
    by rewrite leq_eqVlt Hlt orbT. by rewrite leqNgt Hlt.
    move => IH H. move/andP: H => [Hhh' Hs]. move: IH.
    case: ifP => Heq' //=. case: ifP => Heq //=.
    move => _. by rewrite Hhh' Hs.
    case: ifP => Hlt //=. by rewrite Hhh' Hs leq_eqVlt Hlt orbT.
    by rewrite Hhh' Hs.
    move => IH. case: ifP => Heq //=. by rewrite Hhh' Hs.
    case: ifP => Hlt //=. by rewrite leq_eqVlt Hlt orbT //= Hhh' Hs. 
    case: ifP => Hlt' //=. by rewrite leqNgt Hlt //= leq_eqVlt Hlt' orbT Hs.
    rewrite Hlt' //= in IH. rewrite IH. by rewrite Hhh'. exact.
  Qed.

  Lemma sorted_insert_cat_cons x s p t : sorted (s ++ p :: t) -> x <= p -> sorted (seq_insert x s ++ (p :: t)).
  Proof.
    elim: s => [| h s] //=. by move => -> ->.
    case: s => //=. move => _ /andP [Hhp H] Hleq. case: ifP => Hxh //=.
    by rewrite Hhp H. case: ifP => Hlt //=. by rewrite leq_eqVlt Hlt orbT Hhp H.
    by rewrite leqNgt Hlt Hleq H.
    move => h' s IH /andP [Hhh' H] Hxp. case: ifP => Hxh //=.
    by rewrite Hhh' H. case: ifP => Hlt //=. by rewrite leq_eqVlt Hlt orbT Hhh' H.
    case: ifP => Hxh' //=. by rewrite Hhh' H. case: ifP => Hlt' //=.
    by rewrite leqNgt Hlt leq_eqVlt Hlt' orbT H.
    rewrite Hhh' //=. rewrite Hxh' Hlt' //= in IH. apply: IH. exact. exact.
  Qed.

  Lemma insert_cat_cons_l x s p t : sorted (s ++ p :: t) -> x < p -> seq_insert x (s ++ p :: t) = seq_insert x s ++ (p :: t).
  Proof.
    elim: s => [| h s] //. move => _ Hlt //=. rewrite ifN. by rewrite Hlt.
    by rewrite neq_ltn Hlt.
    move => IH H Hlt. rewrite /=. case: ifP => Heq //=. case: ifP => Hlt_xh //=.
    rewrite IH //. rewrite cat_cons in H. apply: sorted_rest. exact: H.
  Qed.

  Lemma insert_same s p t : sorted (s ++ p :: t) -> seq_insert p (s ++ p :: t) = s ++ p :: t.
  Proof.
    elim: s => [| h s] //. move => _ //=. by rewrite eq_refl.
    move => IH H. rewrite /=. case: ifP => Heq //=. case: ifP => Hlt //=.
    rewrite -sorted_cat_cons_e in H. move/andP: H => [/andP [Hall_leq Hhs] Hpt]. 
    by rewrite //= leqNgt Hlt in Hall_leq.
    rewrite IH //=. apply: sorted_rest. rewrite -cat_cons. exact: H.
  Qed.

  Lemma insert_cat_cons_r x s p t : sorted (s ++ p :: t) -> x > p -> seq_insert x (s ++ p :: t) = s ++ (p :: (seq_insert x t)).
  Proof.
    elim: s => [| h s] //. move => _ Hlt //=. rewrite ifN.
    by rewrite ltnNge leq_eqVlt Hlt orbT. by rewrite neq_ltn Hlt orbT.
    move => IH H Hlt /=.
    have x_lt_h: x > h. rewrite -sorted_cat_cons_e in H.
    move/andP: H => [/andP [Hall_leq _] _]. rewrite /= in Hall_leq.
    move/andP: Hall_leq => [Hleq _]. apply: leq_ltn_trans. exact: Hleq. exact.
    case: ifP => Heq //=. by rewrite (eqP Heq) ltnn in x_lt_h.
    rewrite ltnNge leq_eqVlt x_lt_h orbT //= IH //=.
    apply: sorted_rest. rewrite -cat_cons. exact: H.
  Qed.
  
End insert.


Section util.
  
  Lemma weaken_all_geq x y s : all [eta leq x] s -> x >= y -> all [eta leq y] s.
  Proof.
    elim: s => [| h s IHs] //=. move => /andP [Hxh Hxs] Hyx. apply/andP. split.
    apply: leq_trans. exact: Hyx. exact. exact: IHs.
  Qed.
  

  Lemma all_perm T pred (s t : seq T) : Permutation s t -> all pred s = all pred t.
  Proof.
    move => H. elim: H => //=.
      by move => x s' t' _ ->.
      move => x y l. by rewrite andbCA.
      move => l l' l''. move => _ H _ H'. apply: eq_trans. exact H. exact.
  Qed.

End util.