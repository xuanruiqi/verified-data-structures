From mathcomp Require Import all_ssreflect.
Require Import vds_sort.
Require Import Coq.Sorting.Permutation.

Section Define.

  Inductive color : Type := Red | Black.

  Inductive tree : Type :=
  | E : tree
  | T : color -> tree -> nat -> tree -> tree.

  Definition empty := E.

  Fixpoint flatten t :=
    match t with
    | E => [::]
    | T _ l v r => flatten l ++ (v :: flatten r)
    end.
  
End Define.

Section Query.

  Fixpoint member (n : nat)  (t : tree) : bool :=
    match t with
    | E => false
    | T _ l v r => if n < v
                   then member n l
                   else if n == v then true
                        else member n r
    end.

  Lemma member_in t n : member n t -> n \in (flatten t).
  Proof.
    elim: t => [|c l IHl v r IHr] //=.
    case: ifP => Hlt.
    move => H. rewrite mem_cat IHl. by rewrite orTb. exact.
    case: ifP => Heq. move => H {H}.
    by rewrite mem_cat in_cons Heq //= orbT.
    move => H. rewrite mem_cat in_cons IHr. by rewrite orbA orbT. exact.
  Qed.
  
  Fixpoint height t : nat :=
    match t with
    | E => 0
    | T _ l _ r => 1 + max (height l) (height r)
    end.

  Fixpoint tree_size t : nat :=
    match t with
    | E => 0
    | T _ l _ r => 1 + tree_size l + tree_size r
    end.

  Lemma tree_sizeK t : tree_size t = size (flatten t).
  Proof.
    elim: t => [| c l IHl v r IHr] //=.
    rewrite size_cat //= IHl IHr. rewrite -[in RHS]addn1.
    by rewrite addnA -[in LHS]addnA [in LHS]addnC.
  Qed.

End Query.

(* tactic written by Jacques Garrigue *)
Ltac decompose_rewrite :=
  let H := fresh "H" in
  move/andP=>[] || (move=>H; try rewrite H; try rewrite (eqP H)).

Section Insert.

  Definition balanceL c l v r :=
    match c, l with
    | Black, T Red (T Red a x b) y c
    | Black, T Red a x (T Red b y c)
      => T Red (T Black a x b) y (T Black c v r)
    | _, _ => T c l v r
    end.

  Definition balanceR c l v r :=
    match c, r with
    | Black, T Red (T Red b y c) z d
    | Black, T Red b y (T Red c z d)
      => T Red (T Black l v b) y (T Black c z d)
    | _, _ => T c l v r
    end.

  Fixpoint ins x t :=
    match t with
    | E => T Red E x E
    | T c l v r as s =>
      if x < v
      then balanceL c (ins x l) v r
      else if x > v
           then balanceR c l v (ins x r)
           else s
    end.

  Definition insert x t :=
    match ins x t with
    | E => E (* impossible *)
    | T _ l v r => T Black l v r
    end.

  Fixpoint is_redblack (t : tree) ctxt bh :=
    match t with
    | E => bh == 0
    | T c l _ r =>
      match c, ctxt with
      | Red, Red => false (* red child can't have red parent *)
      | Red, Black => is_redblack l Red bh && is_redblack r Red bh
      | Black, _ => (bh > 0) && is_redblack l Black (bh.-1) && is_redblack r Black (bh.-1)
      end
    end.

  Definition nearly_redblack (t : tree) bh :=
    match t with
    | T Red l _ r => is_redblack l Black bh && is_redblack r Black bh
    | _ => is_redblack t Black bh
    end.

  Lemma is_redblack_red_black t n : is_redblack t Red n -> is_redblack t Black n.
  Proof.
    elim: t => [| c l IHl v r IHr] //=. case: c => //=.
  Qed.

  Lemma is_redblack_nearly_redblack c t n : is_redblack t c n -> 
                                            nearly_redblack t n.
  Proof.
    case: c; elim: t => [| tc l IHl v r IHr] //=; case: tc => //=.
    move/andP => [Hl Hr]. by rewrite !is_redblack_red_black.
  Qed.

  Lemma balanceL_black_is_redblack l r v n :
    nearly_redblack l n -> is_redblack r Black n ->
    is_redblack (balanceL Black l v r) Black n.+1.
  Proof.
    case: l => [| [] [| [] lll llval llr] lval [| [] lrl lrval lrr]] //=;
    repeat decompose_rewrite => //=;
    try (by rewrite !is_redblack_red_black).
    move/eqP in H1. by rewrite -!H1 !is_redblack_red_black.
  Qed.

  Lemma balanceR_black_is_redblack l r v n :
    is_redblack l Black n -> nearly_redblack r n ->
    is_redblack (balanceR Black l v r) Black n.+1.
  Proof.
    case: r => [| [] [| [] rll rlval rlr] rval [| [] rrl rrval rrr]] //=;
    repeat decompose_rewrite => //=;
    try (by rewrite !is_redblack_red_black).
    move/eqP in H2. by rewrite -!H2 !is_redblack_red_black.
  Qed.
     
  Lemma ins_is_redblack (t : tree) x n :
    (is_redblack t Black n -> nearly_redblack (ins x t) n) /\
    (is_redblack t Red n -> is_redblack (ins x t) Black n).
  Proof.
    elim: t n => [| c l IHl v r IHr] n //.
    rewrite //=. split => -> //.
    have ins_black: (is_redblack (T Black l v r) Black n -> is_redblack (ins x (T Black l v r)) Black n).
    { rewrite {3}[Black]lock /= -lock => /andP [/andP [/prednK <- Hl] Hr].
      case: ifP => _. 
      rewrite balanceL_black_is_redblack //; by apply IHl.
      case: ifP => _. rewrite balanceR_black_is_redblack //; by apply IHr.
      rewrite //=. rewrite succnK in Hl. rewrite succnK in Hr. by rewrite Hl Hr. }
    split; case: c => //.
    specialize IHl with n. specialize IHr with n.
    move: IHl => [IHl_b IHl_r]. move: IHr => [IHr_b IHr_r].
    move=> /= /andP [Hl Hr] //=.
    case: ifP => _ //=. rewrite IHl_r. by rewrite is_redblack_red_black. exact.
    case: ifP => _ //=. rewrite IHr_r. by rewrite is_redblack_red_black. exact.
    rewrite !is_redblack_red_black; exact.
    move/ins_black => H. by apply: (is_redblack_nearly_redblack Black).
  Qed.
    
  Lemma insert_is_redblack (t : tree) x n :
    is_redblack t Red n -> exists n', is_redblack (insert x t) Red n'.
  Proof.
    exists (if (ins x t) is T Red _ _ _ then n.+1 else n).
    move/(proj2 (ins_is_redblack t x n)): H.
    rewrite /insert => //=. destruct ins => //=.
    case: c => //= /andP [Hd1 Hd2].
    by rewrite !is_redblack_red_black.
  Qed.

End Insert.

Section BST.

  Definition is_bst t := sorted (flatten t).
  
  Lemma empty_is_bst : is_bst empty.
  Proof. exact. Qed.

  Fixpoint tree_all (pred : nat -> bool) t :=
    match t with
    | E => true
    | T _ l v r => pred v && tree_all pred l && tree_all pred r
    end.

  Lemma tree_allK pred t : tree_all pred t = all pred (flatten t).
  Proof.
    elim: t => [| c l IHl v r IHr] //=.
    by rewrite all_cat //= IHl IHr andbCA andbA.
  Qed.
  
  Fixpoint is_bst_rec (t : tree) :=
    match t with
    | E => true
    | T _ l v r => is_bst_rec l && is_bst_rec r && tree_all (leq^~ v) l &&
                   tree_all [eta leq v] r
    end.
                   
  Lemma is_bst_is_bst_rec : is_bst =1 is_bst_rec.
  Proof.
    rewrite /eqfun. move => t. elim: t => [| c l IHl v r IHr] //=.
    rewrite -IHl -IHr /is_bst /= -sorted_cat_cons_e.
    rewrite -sorted_cons_e. rewrite !tree_allK. rewrite -!andbA.
    case: (all (leq^~ v) (flatten l)) => //=. by rewrite !andbF.
  Qed.

  Lemma balanceLK c l v r : flatten (balanceL c l v r) = flatten l ++ v :: flatten r.
  Proof.
    rewrite /balanceL; case c => //=; 
    case: l => [| [] [| [] lll llval llr] lval [| [] lrl lrval lrr]] //=;
    try rewrite -!cat_cons; try rewrite !catA; try exact. 
    by rewrite -!catA cat_cons.
  Qed.

  Lemma balanceRK c l v r : flatten (balanceR c l v r) = flatten l ++ v :: flatten r.
  Proof.
    rewrite /balanceR; case c => //=; 
    case: r => [| [] [| [] rll rlval rlr] rval [| [] rrl rrval rrr]] //=;
    try rewrite -!cat_cons; try rewrite !catA; try exact. 
    by rewrite -!catA cat_cons.
  Qed.
      
  Lemma insK x (t : tree) : is_bst t -> flatten (ins x t) = seq_insert x (flatten t).
  Proof.
    elim: t => [| c l IHl v r IHr] //=. move => H.
    case Hlt: (x < v). rewrite balanceLK insert_cat_cons_l. rewrite IHl //=.
    rewrite is_bst_is_bst_rec. rewrite is_bst_is_bst_rec /= -!andbA in H.
    by move/and4P: H => [-> _ _ _]. by rewrite /is_bst in H.
    by rewrite Hlt.
    rewrite ltnNge leq_eqVlt Hlt orbF. case Heq: (x == v) => //=.
    by rewrite (eqP Heq) insert_same.
    rewrite balanceRK insert_cat_cons_r. rewrite IHr //=.
    rewrite is_bst_is_bst_rec. rewrite is_bst_is_bst_rec /= -!andbA in H.
    by move/and4P: H => [_ -> _ _]. by rewrite /is_bst in H.
    by rewrite ltnNge leq_eqVlt Hlt Heq.   
  Qed.

  Lemma insertK x (t : tree) : is_bst t -> flatten (insert x t) = seq_insert x (flatten t).
  Proof.
    move => H. rewrite /insert -insK. by case: ins. exact.
  Qed.

  Lemma insert_is_bst x t : is_bst t -> is_bst (insert x t).
  Proof.
    move => H. rewrite /is_bst. rewrite insertK. apply: sorted_insert.
    by rewrite /is_bst in H. exact.
  Qed.  
  
  Lemma tree_all_geq_trans t x y : tree_all (geq^~ x) t -> y <= x -> tree_all (geq^~ y) t.
  Proof.
    elim: t => [| c l IHl v r IHr] //=. rewrite -andbA.
    move/and3P => [Hxv Hl Hr] Hyx. rewrite IHl; try (rewrite IHr); try exact.
    rewrite !andbT. apply: leq_trans. apply: Hyx. apply: Hxv.
  Qed.

  Lemma tree_all_leq_trans t x y : tree_all (leq^~ x) t -> x <= y -> tree_all (leq^~ y) t.
  Proof.
    elim: t => [| c l IHl v r IHr] //=. rewrite -andbA.
    move/and3P => [Hvx Hl Hr] Hxy. rewrite IHl; try (rewrite IHr); try exact.
    rewrite !andbT. apply: leq_trans. apply: Hvx. apply: Hxy.
  Qed.
    
  Lemma balanceL_is_bst c l r x : is_bst_rec l -> is_bst_rec r -> tree_all (leq^~ x) l -> tree_all (geq^~ x) r -> is_bst_rec (balanceL c l x r).
  Proof.
    rewrite /balanceL. case: c => //=; case: l => [| [] [| [] lll llval llr] lval [| [] lrl lrval lrr]] //=; repeat decompose_rewrite; try exact.
    by rewrite (@tree_all_geq_trans r x lrval).
    by rewrite (@tree_all_geq_trans r x lval).
    by rewrite (@tree_all_geq_trans r x lval).
    by rewrite (@tree_all_geq_trans r x lval).
    rewrite (@tree_all_leq_trans lll llval lrval).
    rewrite (@tree_all_leq_trans llr lval lrval) //=.
    rewrite (@tree_all_geq_trans r x lrval) //= !andbT.
    all: (try apply: leq_trans; try apply: H7; try apply: H10; try exact). 
  Qed.

  Lemma balanceR_is_bst c l r x : is_bst_rec l -> is_bst_rec r -> tree_all (leq^~ x) l -> tree_all (geq^~ x) r -> is_bst_rec (balanceR c l x r).
  Proof.
    rewrite /balanceR. case: c => //=; case: r => [| [] [| [] rll rlval rlr] rval [| [] rrl rrval rrr]] //=; repeat decompose_rewrite; try exact.
    by rewrite (@tree_all_leq_trans l x rval).
    by rewrite (@tree_all_leq_trans l x rlval).
    rewrite (@tree_all_leq_trans l x rlval).
    rewrite (@tree_all_geq_trans rrl rval rlval).
    rewrite (@tree_all_geq_trans rrr rval rlval) //=. rewrite !andbT.
    apply: leq_trans. apply: H8. apply: H11. all: try exact.
    rewrite (@tree_all_leq_trans l x rlval).
    rewrite (@tree_all_geq_trans rrl rval rlval).
    rewrite (@tree_all_geq_trans rrr rval rlval) //= !andbT.
    apply: leq_trans. apply: H8. apply: H11. all: try exact.
    by rewrite (@tree_all_leq_trans l x rval).
  Qed.

  Lemma tree_all_balanceL pred c l r v : tree_all pred l && tree_all pred r &&
    pred v = tree_all pred (balanceL c l v r).
  Proof.
    rewrite /balanceL. case: c => //=; case: l => [| [] [| [] lll llval llr] lval [| [] lrl lrval lrr]] //=;
    repeat decompose_rewrite; try (rewrite !andbT); try (rewrite andbC);
    try (rewrite -!andbA); try exact;
    case: (pred v) => //=; try (by rewrite !andbF). by rewrite andbCA.
    case: (pred lval) => //=; case: (pred lrval) => //=; case: (pred llval) => //=.
    by rewrite !andbF.
  Qed.

  Lemma tree_all_balanceR pred c l r v : tree_all pred l && tree_all pred r &&
    pred v = tree_all pred (balanceR c l v r).
  Proof.
    rewrite /balanceR. case: c => //=; case: r => [| [] [| [] rll rlval rlr] rval [| [] rrl rrval rrr]] //=; repeat decompose_rewrite;
    try (rewrite !andbT); try (rewrite andbC);
    try (rewrite -!andbA); try exact; case: (pred v) => //=; 
    try (case: (pred rval) => //=; case: (pred rlval) => //=); 
    try (by rewrite !andbF).
    by rewrite andbCA.
  Qed.
    
  Lemma tree_all_ins pred t x : tree_all pred t && pred x = tree_all pred (ins x t).
  Proof.
    elim: t => [| c l IHl v r IHr] //=. by rewrite !andbT.
    case: ifP => H; try (case: ifP => H'); try (rewrite -tree_all_balanceL -IHl);
    try (rewrite -tree_all_balanceR -IHr);
    case pv: (pred v) => //=; case px: (pred x) => //=; try (by rewrite !andbT); try (by rewrite !andbF).
    by rewrite pv andbT.
    have He: (v == x). apply: negbNE. by rewrite neq_ltn H H'.
    by rewrite -(eqP He) pv in px.
    by rewrite pv. by rewrite pv. 
  Qed.
    
  Lemma ins_is_bst (t : tree) x : is_bst_rec t -> is_bst_rec (ins x t).
  Proof.
    elim: t => [| c l IHl v r IHr] //=.
    rewrite -!andbA. move/and4P => [Hl Hr Hleq Hgeq].
    case: ifP => Hlt.
    apply: balanceL_is_bst; try exact. by apply: IHl.
    by rewrite -tree_all_ins Hleq //= leq_eqVlt Hlt orbT.
    case: ifP => Hlt'. apply: balanceR_is_bst; try exact. by apply: IHr.
    rewrite -tree_all_ins. rewrite ltnNge in Hlt. move/negbFE in Hlt.
    by rewrite /geq //= Hlt Hgeq.
    by rewrite //= Hl Hr Hleq Hgeq.
  Qed.

  Lemma insert_is_bst_rec (t : tree) x : is_bst_rec t -> is_bst_rec (insert x t).
  Proof.
    move/(ins_is_bst t x). rewrite /insert => //=.
    destruct ins => //=.
  Qed.
  
End BST.

Section Membership.

  Lemma all_gt_not_in x s : all [eta ltn x] s -> x \notin s.
  Proof.
    elim: s => [| h s IHs] //=. move/andP => [Hltn Hs].
    rewrite in_cons negb_or. rewrite IHs. by rewrite neq_ltn Hltn. 
    exact.
  Qed.
  
  Lemma all_geq_gt_trans x y s : all [eta leq y] s -> x < y -> all [eta ltn x] s.
  Proof.
    elim: s => [| h s IHs] //=. move => /andP [Hyh Hy] Hxy.
    rewrite IHs. rewrite andbT. apply: leq_trans. apply: Hxy. apply: Hyh. exact.
    exact.
  Qed.

  Lemma all_lt_not_in x s : all (ltn^~ x) s -> x \notin s.
  Proof.
    elim: s => [| h s IHs] //=. move/andP => [Hltn Hs].
    rewrite in_cons negb_or. rewrite IHs. by rewrite neq_ltn Hltn orbT. 
    exact.
  Qed.

  Lemma all_leq_lt_trans x y s : all (leq^~ x) s -> x < y -> all (ltn^~ y) s.
  Proof.
    elim: s => [| h s IHs] //=. move => /andP [Hyh Hy] Hxy.
    rewrite IHs. rewrite andbT. apply: leq_ltn_trans. apply: Hyh. apply: Hxy.
    exact. exact.
  Qed.
  
  Lemma memberK x t : (is_bst_rec t) -> member x t = (x \in (flatten t)).
  Proof.
    elim: t => [| c l IHl v r IHr] //=.
    rewrite -!andbA. move/and4P => [Hl Hr Hleq Hgeq].
    case: ifP => x_lt_v. rewrite mem_cat IHl.
    have not_r: member x r = false. 
    { apply/negbTE. rewrite tree_allK in Hgeq. rewrite IHr.
      apply: all_gt_not_in. apply: all_geq_gt_trans. apply: Hgeq. exact.
      exact. }
    rewrite in_cons. rewrite -IHr. rewrite not_r orbF.
    have neq_xv: (x == v) = false. apply/negbTE. by rewrite neq_ltn x_lt_v.
    by rewrite neq_xv orbF. exact. exact.
    case: ifP => Heq_xv. by rewrite mem_cat in_cons Heq_xv orbC.  
    rewrite mem_cat IHr.
    have not_l: member x l = false.
    { apply/negbTE. rewrite tree_allK in Hleq. rewrite IHl.
      apply: all_lt_not_in. apply: all_leq_lt_trans. apply: Hleq.
      rewrite ltn_neqAle. by rewrite eq_sym negbT //= leqNgt x_lt_v. exact. }
    rewrite in_cons. rewrite -IHl. by rewrite not_l //= Heq_xv.
    exact. exact.
  Qed.

End Membership.

Section TreeSort.
  
  Fixpoint build_tree s :=
    match s with
    | [::] => E
    | h :: t => insert h (build_tree t)
    end.

  Definition tree_sort s := flatten (build_tree s).

  Lemma bst_sorted (t : tree) : is_bst_rec t = sorted (flatten t).
  Proof. by rewrite -is_bst_is_bst_rec /is_bst. Qed.

  Lemma tree_sort_sorted s : sorted (tree_sort s).
  Proof.
    rewrite /tree_sort. rewrite -bst_sorted.
    elim: s => [| h s IHs] //=. by apply: insert_is_bst_rec.
  Qed.

End TreeSort.