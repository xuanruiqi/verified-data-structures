From mathcomp Require Import all_ssreflect.
Require Import Compare_dec Program.
Require Import vds_sort.

Set Implicit Arguments.


Section defn.

  Inductive tree : nat -> Type :=
  | Leaf : tree 0
  | Node2 : forall h, tree h -> nat -> tree h -> tree h.+1
  | Node3 : forall h, tree h -> nat -> tree h -> nat -> tree h -> tree h.+1.


  Fixpoint flatten {n} (tr : tree n) :=
    match tr with
    | Leaf => [::]
    | Node2 _ l v r => flatten l ++ v :: (flatten r)
    | Node3 _ l v1 m v2 r => flatten l ++ v1 :: (flatten m ++ (v2 :: flatten r))
    end.

  Fixpoint height {n} (tr : tree n) :=
    match tr with
    | Leaf => 0
    | Node2 _ l _ r => 1 + maxn (height l) (height r)
    | Node3 _ l _ m _ r => 1 + maxn (height l) (maxn (height m) (height r))
    end.

  Lemma height_correct {n} (tr : tree n) : height tr = n.
  Proof.
    elim: tr => [| h l IHl _ r IHr | h l IHl _ m IHm _ r IHr] //=.
    by rewrite IHl IHr //= maxnn add1n.
    by rewrite IHl IHm IHr //= !maxnn add1n.
  Qed.

  Fixpoint tree_size {n} (tr : tree n) :=
    match tr with
    | Leaf => 1
    | Node2 _ l _ r => 1 + tree_size l + tree_size r
    | Node3 _ l _ m _ r => 1 + tree_size l + tree_size m + tree_size r
    end.

End defn.

Section search_tree.

  Definition is_search_tree {h} (tr : tree h) := sorted (flatten tr).

  Fixpoint search {h} (x : nat) (tr : tree h) :=
    match tr with
    | Leaf => false
    | Node2 _ l v r => if x < v
                       then search x l
                       else if x == v
                            then true
                            else search x r
    | Node3 _ l v m v' r => if x < v
                            then search x l
                            else if x == v
                                 then true
                                 else if x < v'
                                      then search x m
                                      else if x == v'
                                           then true
                                           else search x r
    end.
    
End search_tree.

Section insert.

  Inductive put_tree : nat -> Type :=
  (* wraps a well-formed tree *)
  | T : forall h, tree h -> put_tree h
  (* an intermediate node that is disregarded in height calculation *)
  | Put : forall h, tree h -> nat -> tree h -> put_tree h.

  Definition flattenp {h} (pt : put_tree h) :=
    match pt with
    | T _ tr => flatten tr
    | Put _ l a r => flatten l ++ a :: flatten r
    end.
  
  Program Definition fix_2_l {h} (l : put_tree h) v (r : tree h) : { t' : tree h.+1 | flatten t' = flattenp l ++ v :: flatten r } :=
    match l with
    | Put _ t1 a t2 => Node3 t1 a t2 v r
    | T _ tr => Node2 tr v r
    end.

  Next Obligation.
  Proof.
    rewrite /eq_rect. destruct fix_2_l_obligation_2 => //=. rewrite -Heq_l //=.
    by rewrite -!cat_cons -catA.
  Qed.

  Next Obligation.
  Proof.
    rewrite /eq_rect. destruct fix_2_l_obligation_5 => //=. by rewrite -Heq_l.
  Qed.
  
  Program Definition fix_2_r {h} (l : tree h) v (r : put_tree h) : { t' : tree h.+1 | flatten t' = flatten l ++ v :: flattenp r }:=
    match r with
    | Put _ t2 b t3 => Node3 l v t2 b t3
    | T _ tr => Node2 l v tr
    end.

  Next Obligation.
  Proof.
    rewrite /eq_rect. destruct fix_2_r_obligation_1. by rewrite -Heq_r.
  Qed.

  Next Obligation.
  Proof.
    rewrite /eq_rect. destruct fix_2_r_obligation_4. by rewrite -Heq_r.
  Qed.
    
  Program Definition bubble_3_l {h} (l : put_tree h) b (m : tree h) c (r : tree h)
    : { pt : put_tree h.+1 | flattenp pt = flattenp l ++ b :: (flatten m ++ c :: flatten r) } :=
    match l with
    | Put _ t1 a t2 => Put (Node2 t1 a t2) b (Node2 m c r)
    | T _ tr => T (Node3 tr b m c r)
    end.

  Next Obligation.
  Proof.
    rewrite /eq_rect. destruct bubble_3_l_obligation_2 => //=. by rewrite -Heq_l.
  Qed.

  Next Obligation.
  Proof.
    rewrite /eq_rect. destruct bubble_3_l_obligation_6 => //=. by rewrite -Heq_l.
  Qed.
  
  Program Definition bubble_3_m {h} (l : tree h) a (m : put_tree h) c (r : tree h)
      : { pt : put_tree h.+1 | flattenp pt = flatten l ++ a :: (flattenp m ++ c :: flatten r) } :=
    match m with
    | Put _ t2 b t3 => Put (Node2 l a t2) b (Node2 t3 c r)
    | T _ tr => T (Node3 l a tr c r)
    end.

  Next Obligation.
    rewrite /eq_rect. destruct bubble_3_m_obligation_1 => //=. rewrite -Heq_m //=.
    by rewrite -!catA -!cat_cons.
  Qed.

  Next Obligation.
    rewrite /eq_rect. destruct bubble_3_m_obligation_5 => //=. by rewrite -Heq_m.
  Qed.
    
  Program Definition bubble_3_r {h} (l : tree h) a (m : tree h) b (r : put_tree h)
    : { pt : put_tree h.+1 | flattenp pt = flatten l ++ a :: (flatten m ++ b :: flattenp r) } :=
    match r with
    | Put _ t3 c t4 => Put (Node2 l a m) b (Node2 t3 c t4)
    | T _ tr => T (Node3 l a m b tr)
    end.

  Next Obligation.
    rewrite /eq_rect. destruct bubble_3_r_obligation_1 => //=. rewrite -Heq_r //=.
    by rewrite -!catA -!cat_cons.
  Qed.

  Next Obligation.
    rewrite /eq_rect. destruct bubble_3_r_obligation_3 => //=. by rewrite -Heq_r.
  Qed.
    
  Program Fixpoint put {h} v (t : tree h) { measure (tree_size t) } : { pt : put_tree h | is_search_tree t -> flattenp pt = seq_insert v (flatten t) } :=
    match t with
    | Leaf => Put Leaf v Leaf
    | Node2 _ l a r => if v == a
                       then T t
                       else if v < a
                            then let (l', _) := put v l in
                                 let (t', _) := fix_2_l l' a r in T t'
                            else let (r', _) := put v r in
                                 let (t', _) := fix_2_r l a r' in T t'
    | Node3 _ l a m b r => if (v == a) || (v == b)
                           then T t
                           else if v < a
                                then let (l', _) := put v l in
                                     let (t', _) := bubble_3_l l' a m b r in t'
                                else if (* a < *) v < b
                                     then let (m', _) := put v m in
                                          let (t', _) := bubble_3_m l a m' b r in
                                          t'
                                     else let (r', _) := put v r in
                                          let (t', _) := bubble_3_r l a m b r' in
                                          t'
    end.

  Next Obligation.
  Proof.
    apply/ltP. rewrite -Heq_t //=. rewrite addnAC add1n.
    by rewrite -[X in X < _]add0n ltn_add2r. 
  Qed.

  Next Obligation.
  Proof.
    apply/ltP. rewrite -Heq_t //=. rewrite add1n.
    by rewrite -[X in X < _]add0n ltn_add2r.
  Qed.
    
  Next Obligation.
  Proof.
    rewrite /eq_rect. destruct put_func_obligation_5. case: ifP => Heq //=.
    rewrite -Heq_t //=. rewrite -(eqP Heq) insert_same //=.
    rewrite /is_search_tree //= in H. by rewrite (eqP Heq).
    case: ifP => Hlt //=. destruct put. destruct fix_2_l => //=. rewrite e0.
    rewrite insert_cat_cons_l. rewrite -e //=.
    rewrite /is_search_tree //= in H. rewrite /is_search_tree.
    apply: cat_sorted_l. exact: H. by rewrite /is_search_tree in H. exact.
    destruct put. destruct fix_2_r => //=. rewrite e0. rewrite insert_cat_cons_r.
    rewrite e //=. rewrite /is_search_tree //= -cat_rcons in H.
    rewrite /is_search_tree. apply: cat_sorted_r. exact: H.
    by rewrite /is_search_tree in H. by rewrite ltnNge leq_eqVlt Hlt Heq.
  Qed.

  Next Obligation.
    apply/ltP. rewrite -Heq_t //=. rewrite add1n -[X in X + _ + _]addn1.
    rewrite -!addnA add1n. by rewrite -[X in X < _]addn0 ltn_add2l.
  Qed.

  Next Obligation.
  Proof.
    apply/ltP. rewrite -Heq_t //=. rewrite addnAC. rewrite -[X in X < _]add0n.
    by rewrite ltn_add2r add1n.
  Qed.

  Next Obligation.
  Proof.
    apply/ltP. rewrite -Heq_t //=. rewrite -[X in X < _]add0n.
    by rewrite ltn_add2r add1n.
  Qed.
    
  Next Obligation.
  Proof.
    rewrite /eq_rect. destruct put_func_obligation_11.
    case: ifP. move => /orP [Heq_a | Heq_b] //=.
    rewrite -Heq_t //= -(eqP Heq_a) insert_same //=.
    by rewrite /is_search_tree /= -(eqP Heq_a) in H.
    rewrite -Heq_t //= -(eqP Heq_b). rewrite -![in RHS]cat_cons.
    rewrite [in RHS]catA insert_same. by rewrite -!catA -cat_cons.
    by rewrite /is_search_tree /= -(eqP Heq_b) -!cat_cons catA in H.
    move/negbT/norP => [Hneq_a Hneq_b]. case: ifP => Hlt_a. destruct put.
    destruct bubble_3_l => //=. rewrite e0 insert_cat_cons_l. rewrite -e //=.
    rewrite /is_search_tree /= in H. rewrite /is_search_tree. apply: cat_sorted_l.
    exact: H. by rewrite /is_search_tree in H. exact.
    case: ifP => Hlt_b. destruct put. destruct bubble_3_m => //=.
    rewrite -cat_cons catA insert_cat_cons_l. rewrite insert_cat_cons_r.
    rewrite e0. rewrite e. by rewrite -catA -cat_cons. 
    rewrite /is_search_tree. apply: cat_sorted_r. apply: cat_sorted_l.
    rewrite /is_search_tree /= -cat_cons catA -[X in X ++ _ :: _]cat_rcons in H.
    exact: H. apply: cat_sorted_l. rewrite /is_search_tree /= -cat_cons catA in H.
    exact: H. by rewrite ltnNge leq_eqVlt Hlt_a orbF Hneq_a.
    by rewrite /is_search_tree /= -cat_cons catA in H. exact. destruct put.
    destruct bubble_3_r => //=. rewrite e0. rewrite insert_cat_cons_r.
    rewrite insert_cat_cons_r. rewrite -e //=.
    rewrite /is_search_tree. rewrite /is_search_tree /= in H.
    by move/cat_sorted_r/sorted_rest/cat_sorted_r/sorted_rest: H.
    rewrite /is_search_tree /= in H. by move/cat_sorted_r/sorted_rest: H.
    by rewrite ltnNge leq_eqVlt Hlt_b orbF Hneq_b.
    by rewrite /is_search_tree /= in H.
    by rewrite ltnNge leq_eqVlt Hlt_a orbF Hneq_a.
  Qed.
      
  Definition put_height {h} (pt : put_tree h) :=
    match pt with
    | Put _ _ _ _ => h.+1
    | T _ _ => h
    end.

  Definition fix_tree {h} (pt : put_tree h) : tree (put_height pt) :=
    match pt with
    | Put _ l a r => Node2 l a r
    | T _ t => t
    end.

  (* encode height using a dependent pair *) 
  Program Definition insert {h} v (t : tree h) :
    { res : { h' : nat & tree h' } |
      is_search_tree t -> (flatten (projT2 res) = seq_insert v (flatten t) /\
      is_search_tree (projT2 res)) } :=
    let (pt, _) := put v t in
    let h' := put_height pt in existT tree h' (fix_tree pt).

  Next Obligation.
    split.
    + rewrite /fix_tree. destruct pt => //=.
    + rewrite /fix_tree /is_search_tree. simpl in H. by rewrite H.
      simpl in H. by rewrite H. rewrite /fix_tree.
      destruct pt => //=. simpl in H. rewrite /is_search_tree H.
      apply: sorted_insert. by rewrite /is_search_tree in H0.
      exact. simpl in H. rewrite /is_search_tree //= H. apply: sorted_insert.
      by rewrite /is_search_tree in H0. exact.
  Qed.
  
End insert.