(** * Binary Numbers Helper Lemmas

    In this file, we prove several helper lemmas for
    Rocq binary number type 'N', that we will need in our 
    other proofs. *)

From Coq Require Import ZArith.
Require Import Lia.

From Core Require Import Core.

Open Scope positive_scope.

Lemma Pos_size_succ : forall n,
	Pos.size (Pos.succ n) <= Pos.succ (Pos.size n).
Proof.
	induction n; simpl.
	+ apply -> Pos.succ_le_mono.
		apply IHn.
	+ apply Pos.lt_le_incl.
		apply Pos.lt_succ_diag_r.
	+ apply Pos.le_refl.
Qed.

Lemma Pos_size_succ_cases : forall n,
	Pos.size (Pos.succ n) = Pos.succ (Pos.size n) \/ 
	Pos.size (Pos.succ n) = (Pos.size n).
Proof.
	intros.
	induction n; simpl.
	+ destruct IHn as [IHn|IHn].
		- left. rewrite IHn. reflexivity.
		- right. rewrite IHn. reflexivity.
	+ destruct IHn as [IHn|IHn].
		- right. reflexivity.
		- right. reflexivity.
	+ left. reflexivity.
Qed.   

Lemma Pos_size_lt_val : forall n,
	2 < n -> 
	Pos.size n < n.
Proof.
	intros n H.  
	induction n using Pos.peano_ind; simpl; try lia. (* n = 1 *)
	induction n using Pos.peano_ind; simpl; try lia. (* n = 2*)
	induction n using Pos.peano_ind; simpl; try lia. (* n = 3*)
	destruct (Pos_size_succ_cases (Pos.succ (Pos.succ (n)))) as [H1|H2].
	- rewrite H1.
		apply -> Pos.succ_lt_mono.
		apply IHn.
		lia.
	- rewrite H2.
		apply Pos.lt_lt_succ.
		apply IHn.
		lia.
Qed.

Lemma Pos_lt_succ_l : forall n m,
	Pos.lt (Pos.succ n) m -> Pos.lt n m.
Proof.
	intros n m H.
	induction n using Pos.peano_ind; lia.
Qed.

Lemma Pos_size_lt_if_sum_lt_l : forall x y n,
	Pos.size (x + y) < n -> Pos.size x < n.
Proof.
	intros x y n H.
	generalize dependent x.
	induction y using Pos.peano_ind.
	- intros.
		rewrite Pos.add_1_r in H.
		destruct (Pos_size_succ_cases x).
		+ rewrite H0 in H.
			apply Pos_lt_succ_l in H.
			apply H.
		+ rewrite H0 in H.
			apply H.
	- intros. 
		apply IHy.
		rewrite Pos.add_succ_r in H.
		destruct (Pos_size_succ_cases (x + y)).
		+ rewrite H0 in H.
			apply Pos_lt_succ_l in H.
			apply H.
		+ rewrite H0 in H.
			apply H.
Qed.  

Lemma Pos_size_lt_if_prod_lt_l : forall x y n,
	Pos.size (x * y) < n -> Pos.size x < n.
Proof.
	intros.
	generalize dependent x.
	destruct y using Pos.peano_ind.
	- intros.
		rewrite Pos.mul_1_r in H.
		apply H.
	- intros.
		rewrite Pos.mul_succ_r in H.
		apply Pos_size_lt_if_sum_lt_l in H.
		apply H. 
Qed.



		
Open Scope N_scope.

Lemma N_pos_succ : forall n,
	N.pos (Pos.succ n) = N.succ (N.pos n).
Proof. auto. Qed.

Lemma N_size_succ : forall n,
	N.size (N.succ n) <= N.succ (N.size n).
Proof.
	destruct n as [|n]; simpl.
	- apply N.le_refl.
	- apply Pos_size_succ.
Qed.    

Theorem N_size_lt_val : forall n,
	2 < n -> 
	N.size n < n.
Proof.
	intros n H.
	destruct n as [|n]; simpl.
	- inversion H.
	- apply Pos_size_lt_val. apply H.
Qed.

Lemma N_succ_mod_small : forall n m, 
	(N.succ n) < m -> 
  (N.succ n) mod m = N.succ (n mod m).
Proof.
  intros.
  rewrite N.mod_small; auto.
  apply N.lt_succ_l in H.
  rewrite N.mod_small; auto.
Qed.

Lemma N_succ_mod_lt : forall n m,
  n < m ->
  (N.succ n) mod m = N.succ n \/ (N.succ n) mod m = 0.
Proof.
  intros.
  destruct (N.compare_spec (N.succ n) m) as [Hlt | Heq | Hgt].
  - subst. right. apply N.Div0.mod_same.
  - left. apply N.mod_small. apply Heq.
  - lia.
Qed.


Lemma N_succ_mod : forall n m,
  (N.succ n) mod m = N.succ (n mod m) \/ 
  (N.succ n) mod m = 0.
Proof.
  intros.
  destruct (N.compare_spec n m) as [ Heq | Hlt | Hgt].
  - subst. 
    rewrite N.Div0.mod_same. 
    rewrite <- N.add_1_l.
    rewrite <- N.Div0.add_mod_idemp_r. 
    rewrite N.Div0.mod_same.
    destruct (m =? 0) eqn:E.
    + simpl. apply N.eqb_eq in E. subst. rewrite N.mod_0_r. left. reflexivity.
    + simpl. apply N.eqb_neq in E. destruct (m =? 1) eqn:E1.
      * apply N.eqb_eq in E1. subst. rewrite N.mod_1_r. right. reflexivity.
      * apply N.eqb_neq in E1. rewrite N.mod_small. left. reflexivity.
        -- lia.
  - pose proof (N_succ_mod_lt n m Hlt). destruct H.
    + rewrite H. rewrite N.mod_small by assumption. left. reflexivity.
    + right. apply H.
  - destruct (N.eq_dec m 0) as [Hm0 | Hmnot0].
    + subst. rewrite N.mod_0_r. rewrite N.mod_0_r. left. reflexivity.
    + set (r := n mod m).
      assert (Hlt : r < m).
      { apply N.mod_lt; assumption. }
      destruct (N.lt_ge_cases (r + 1) m).
      * apply N.mod_small in H.
        rewrite N.add_1_r in H. 
        rewrite <- H. 
        subst r.
        repeat rewrite <- N.add_1_r.
        rewrite N.add_mod_idemp_l by assumption.
        left. 
        reflexivity.
      * assert (Hlt1 : r + 1 = m) by lia.
        subst r.
        rewrite N.add_1_r in *.
        rewrite Hlt1.
        rewrite <- N.add_1_r.
        rewrite <- N.add_mod_idemp_l.
        rewrite N.add_1_r.
        rewrite Hlt1.
        rewrite N.Div0.mod_same.
        right.
        reflexivity.
        apply Hmnot0.
Qed.

Theorem N_sub_inv_mod : forall n m,
  n < m ->
  (n + (m - n)) mod m = 0.
Proof.
  intros.
  rewrite N.add_sub_assoc.
  rewrite N.add_comm.
  rewrite <- N.add_sub_assoc.
  rewrite N.sub_diag.
  rewrite N.add_0_r.
  rewrite N.Div0.mod_same.
  reflexivity.
  * lia.
  * destruct (N.eqb n v_WORDSIZE_64_) eqn:E.
    + apply N.eqb_eq in E.
      subst n.
      lia.
    + apply N.eqb_neq in E.
      apply N.lt_eq_cases.
      left.
      apply H.
Qed.

Theorem N_sub_inv : forall n m,
  n < m ->
  (n + (m - n)) = m.
Proof.
  intros.
  rewrite N.add_sub_assoc.
  rewrite N.add_comm.
  rewrite <- N.add_sub_assoc.
  rewrite N.sub_diag.
  rewrite N.add_0_r.
  reflexivity.
  * lia.
  * destruct (N.eqb n v_WORDSIZE_64_) eqn:E.
    + apply N.eqb_eq in E.
      subst n.
      lia.
    + apply N.eqb_neq in E.
      apply N.lt_eq_cases.
      left.
      apply H.
Qed.

Lemma N_pos_destruct : forall a b,
  Npos (a + b) = Npos a + Npos b.
Proof. intros. destruct a, b; simpl; auto. Qed.

Lemma N_size_lt_if_size_succ : forall n m,
  N.size (N.succ n) < m ->
  N.size n < m.
Proof.
  intros n m H.
	destruct n as [|n]; simpl.
  - lia. 
  - simpl in *.
		destruct (Pos_size_succ_cases n).
    + rewrite H0 in H.
			rewrite N_pos_succ in H.
	  	apply N.lt_succ_l in H.
			apply H.
		+ rewrite H0 in H.
			apply H.
Qed.  

Lemma N_size_lt_if_sum_lt_l : forall x y n,
	N.size (x + y) < n -> N.size x < n.
Proof.
	intros x y n H.
	destruct x as [|x], y as [|y], n as [|n]; simpl in *; auto.
	- lia.
	- lia.
	- apply Pos_size_lt_if_sum_lt_l with (y := y).
		apply H.
Qed.

Lemma N_size_lt_if_sum_lt_r : forall x y n,
	N.size (x + y) < n -> N.size y < n.
Proof.
	intros.
	rewrite N.add_comm in H.
	apply N_size_lt_if_sum_lt_l in H.
	apply H.
Qed.

Lemma lt_xI : forall n m,
  (Npos (xI n)) < m ->
  Npos (n) < m.
Proof.
  intros.
  rewrite Pos.xI_succ_xO in H.
  rewrite N_pos_succ in H. 
  apply N.lt_succ_l in H.
  rewrite <- Pos.add_diag in H.
  lia.
Qed.


Lemma lt_xO : forall n m,
  (Npos (xO n)) < m ->
  Npos (n) < m.
Proof.
  intros. 
  rewrite <- Pos.add_diag in H.
  lia.
Qed.

Lemma lt_xI_succ : forall n m,
  (Npos (xI n)) < m ->
  Npos (Pos.succ n) < m.
Proof.
  intros.
  rewrite Pos.xI_succ_xO in H.
  rewrite N_pos_succ in H.
  rewrite <- Pos.add_diag in H.
  simpl in *.
  lia.
Qed. 

Lemma lt_succ_xO : forall n m,
  N.succ (Npos (xO n)) < m ->
  N.succ (Npos (n)) < m.
Proof. 
  intros.
  rewrite <- Pos.add_diag in H.
  simpl in *.
  lia.
Qed.

Lemma succ_lt_pred : forall n m,
  N.succ n < m <-> n < N.pred m.
Proof. intros. split; lia. Qed.


Lemma lt_size : forall n m : N,
  n < m -> N.size n < m.
Proof.
  intros n m H.
  destruct n as [ | n ]; auto.
  destruct m as [ | m ]; auto.
  generalize dependent m.
  induction n; auto; simpl.
  - intros.
    simpl in *.
    rewrite N_pos_succ.
    apply succ_lt_pred.
    destruct (N.pred (Npos m)) eqn:E.
    + lia.
    + apply IHn.
      rewrite <- E; clear E.
      apply succ_lt_pred.
      apply lt_xI_succ.
      apply H.
  - intros.
    simpl in *.
    rewrite N_pos_succ.
    apply succ_lt_pred.
    destruct (N.pred (Npos m)) eqn:E.
    + lia.
    + apply IHn.
      rewrite <- E; clear E.
      apply succ_lt_pred.
      lia.
Qed.

Require Import Coq.NArith.BinNat.

Lemma lt_size_size : forall n m : N,
  n < m -> N.size n <= N.size m.
Proof.
  intros.
  destruct n eqn:Hn, m eqn:Hm.
  - inversion H.
  - simpl. apply N.lt_le_incl. apply N.lt_0_1.
  - rewrite !N.size_log2; lia.
  - rewrite !N.size_log2; try lia. 
    apply -> N.succ_le_mono.
    apply N.log2_le_mono.
    apply N.lt_le_incl.
    apply H.
Qed.
  


  

Lemma lt_succ_xI : forall n m,
  N.succ (Npos (xI n)) < m ->
  N.succ (Npos (n)) < m.
Proof.
  intros. 
  rewrite Pos.xI_succ_xO in H.
  apply N.lt_succ_l in H.
  rewrite N_pos_succ in H.
  apply N.lt_succ_l in H.
  rewrite <- Pos.add_diag in H.
  lia.
Qed.


Lemma N_size_0 : forall n m : N,
  N.size n = 0 -> n = 0.
Proof.
  intros.
  destruct n as [ | n ]; auto.
  inversion H.
Qed.

Lemma pos_size_0 : forall n,
  Npos (Pos.size n) = 0 -> (Npos n) = 0.
Proof.
  intros.
  inversion H.
Qed.

Lemma pred_mod : forall n m,
  n <> 0 -> m <> 0 ->
  (N.pred n) mod m = (n + (m - 1)) mod m.
Proof.
  intros.
  rewrite N.sub_1_r.
  rewrite N.add_pred_r.
  rewrite <- N.add_pred_l.
  rewrite <- N.Div0.add_mod_idemp_r.
  rewrite N.Div0.mod_same.
  rewrite N.add_0_r.
  reflexivity.
  auto.
  auto.
Qed.


Lemma mod_inv_sub : forall a b m,
  b <= a -> b <= m ->
  (a + (m - b)) mod m = (a - b) mod m.
Proof.
  intros.
  rewrite N.add_sub_assoc; auto.
  rewrite N.add_comm.
  rewrite <- N.add_sub_assoc; auto.
  rewrite <- N.Div0.add_mod_idemp_l.
  rewrite N.Div0.mod_same.
  rewrite N.add_0_l.
  reflexivity.
Qed.


Lemma mod_add_inv : forall n m,
  n <= m ->
  (n + (m - n)) mod m = 0.
Proof.
  intros.
  rewrite N.add_sub_assoc.
  rewrite N.add_comm.
  rewrite <- N.add_sub_assoc.
  rewrite N.sub_diag.
  rewrite N.add_0_r.
  rewrite N.Div0.mod_same.
  reflexivity.
  * apply N.le_refl.
  * apply H. 
Qed.

Lemma size_xI : forall n,
  N.size (Npos (xI n)) = N.succ (N.size (Npos n)).
Proof. reflexivity. Qed.

Lemma size_xO : forall n,
  N.size (Npos (xO n)) = N.succ (N.size (Npos n)).
Proof. reflexivity. Qed.

Lemma n_add_lt : forall n a b,
  n < a ->
  n < b ->
  n < a + b.
Proof.
  intros.
  rewrite <- N.add_0_l at 1.
  apply N.add_lt_mono; auto.
  lia.
Qed.   

Lemma N_size_lt_double_val : forall n,
  N.size (Npos n) < Npos (xO n).
Proof.
  intros.
  induction n; simpl in *.
  - rewrite <- Pos.add_diag.
    rewrite <- N.add_0_l at 1.
    rewrite N_pos_destruct.
    apply N.add_lt_mono.
    + lia.
    + rewrite Pos.xI_succ_xO.
      rewrite N_pos_succ.
      rewrite N_pos_succ.
      rewrite <- N.succ_lt_mono.
      apply IHn.
  - rewrite N_pos_succ.
    rewrite <- Pos.add_diag.
    rewrite N_pos_destruct.
    rewrite <- N.add_1_r.
    apply N.add_lt_mono.
    + apply IHn.
    + lia.   
  - rewrite <- Pos.add_diag. lia.
Qed.


Lemma N2Pos_lt : forall n m,
  Npos n < Npos m ->
  (n < m)%positive.
Proof.
  intros.
  inversion H.
  rewrite Pos.compare_lt_iff in H1.
  apply H1.
Qed.

Lemma Pos_lt_xO : forall n m,
  (xO n < xO m)%positive ->
  (n < m)%positive.
Proof.
  intros.
  rewrite <- Pos.add_diag in H.
  rewrite <- Pos.add_diag in H.
  lia.
Qed.

Lemma Pos_lt_xO_l : forall n m,
  (xO n < m)%positive ->
  (n < m)%positive.
Proof.
  intros.
  rewrite <- Pos.add_diag in H.
  lia.
Qed.

Lemma N_lt_xO_l : forall n m,
  Npos (xO n) < m ->
  (Npos n) < m.
Proof.
  intros. 
  rewrite <- Pos.add_diag in H.
  lia.
Qed.
  
Lemma Pos_lt_xI : forall n m,
  (xI n < xI m)%positive
  -> (n < m)%positive.
Proof.
  intros.
  rewrite Pos.xI_succ_xO in H.
  rewrite Pos.xI_succ_xO in H.
  rewrite <- Pos.succ_lt_mono in H.
  lia.
Qed.

Lemma Pos2N_lt : forall n m,
  (n < m)%positive ->
  Npos n < Npos m.
Proof. intros. lia. Qed. 

Lemma Pos_size_lt_double_val : forall n,
  (Pos.size n < xO n)%positive.
Proof.
  intros.
  induction n.
  - simpl.
    rewrite Pos.xI_succ_xO.
    rewrite <- Pos.add_diag.
    rewrite <- Pos.add_1_l at 1.
    apply Pos.add_lt_mono.
    + lia.
    + apply Pos.lt_lt_succ. apply IHn.
  - simpl.
    rewrite <- Pos.add_diag.
    rewrite <- Pos.add_1_l at 1.
    apply Pos.add_lt_mono.
    + lia.
    + apply IHn.
  - simpl. 
    rewrite <- Pos.add_diag.
    lia.
Qed.

Lemma pos_2_eq_1_plus_1 : (2%positive = 1 + 1)%positive.
Proof. reflexivity. Qed.

Lemma pos_lt_split : forall n m,
  (n + n < m + m)%positive ->
  (n < m)%positive.
Proof.
  intros.
  rewrite Pos.add_diag in H.
  rewrite Pos.add_diag in H.
  apply Pos_lt_xO.
  apply H.
Qed.



Lemma N_pos_size_fold : forall n,
  Npos (Pos.size n) = N.size (Npos n).
Proof. reflexivity. Qed.

Lemma pos_size_lt : forall n m,
  (Npos n) < m ->
  Npos (Pos.size n) < m.
Proof.
  intros.
  rewrite N_pos_size_fold.
  apply lt_size.
  apply H.
Qed.

Lemma N_xO_lt : forall n m,
  Npos (xO n) < m ->
  (Npos n) < m.
Proof.
  intros.
  rewrite <- Pos.add_diag in H.
  lia.
Qed.

Lemma N_xI_lt : forall n m,
  Npos (xI n) < m ->
  (Npos n) < m.
Proof.
  intros.
  rewrite Pos.xI_succ_xO in H.
  rewrite <- Pos.add_diag in H.
  lia.
Qed.

Lemma N2Nat_lt_Pos2Nat : forall a b,
  (N.to_nat a < Pos.to_nat b)%nat ->
  a < Npos b.
Proof. intros. lia. Qed.


Lemma lt_antisym : forall n m,
  n < m -> m < n -> False.
Proof. intros. lia. Qed.


	
Lemma nat_to_N : forall (n : nat),
  exists (m : N), n = N.to_nat m.
Proof.
  intros.
  destruct n.
  - exists 0. reflexivity.
  - exists (N.of_nat (S n)).
    rewrite Nnat.Nat2N.id.
    reflexivity.
Qed.

Lemma N2Nat_lt : forall n m,
  (N.to_nat n < N.to_nat m)%nat <->
  n < m.
Proof. intros. split; lia. Qed. 

Lemma N_lt_sum : forall x y n,
  x + y < n -> x < n /\ y < n.
Proof.
  intros.
  split.
  - lia.
  - lia.
Qed.





Open Scope nat_scope.


Lemma Nat_succ_mod : forall n m,
  (Nat.succ n) mod m = Nat.succ (n mod m) \/ 
  (Nat.succ n) mod m = 0.
Proof.
  intros.
  (* convert all Nat's to N *)
  pose proof (N_succ_mod (N.of_nat n) (N.of_nat m)).
  rewrite <- Nnat.Nat2N.inj_succ in H.
  rewrite <- Nnat.Nat2N.inj_mod in H.
  rewrite <- Nnat.Nat2N.inj_mod in H.
  rewrite <- Nnat.Nat2N.inj_succ in H.
  destruct H as [H1|H2].
  - apply Nnat.Nat2N.inj in H1. left. apply H1.
  - assert (0%N = N.of_nat 0) by lia. rewrite H in H2. apply Nnat.Nat2N.inj in H2. right. apply H2. 
Qed.



Close Scope nat_scope.
