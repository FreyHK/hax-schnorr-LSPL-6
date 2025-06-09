(** * Fold Range Helper Lemmas

    In this file we define a corrected version of fold_range,
    and prove several lemmas that we will need to prove the
    correctness of our implementation of scalar multiplication.
   *)


From Coq Require Import ZArith.
Require Import List.
Import List.ListNotations.
Open Scope Z_scope.
Open Scope bool_scope.
Require Import Ascii.
Require Import String.
Require Import Coq.Floats.Floats.
From RecordUpdate Require Import RecordSet.
Import RecordSetNotations.
From Core Require Import Core.

From Schnorr Require Import HaxintSpec.
From Schnorr Require Import Binary_Nums.

Definition fold_range {A : Type} (l : t_usize) (u : t_usize) (_ : A -> t_usize -> bool) (x : A) (f : A -> t_usize -> A) : A := 
  List.fold_left f 
    (List.rev (build_range 
      (unary_from_int (U64_f_v (usize_0 l))) 
      (unary_from_int (U64_f_v (usize_0 (Sub_f_sub u l)))) 
      nil
    )) x.

Lemma fold_left_invariant `{A : Type} (Inv : A -> Prop) :
  forall (l : list t_usize) (f : A -> t_usize -> A),
  (forall (x : A) (idx : t_usize), Inv x -> Inv (f x idx)) ->
  forall x : A, Inv x -> Inv (List.fold_left f l x).
Proof.
  intros.
  generalize dependent x.
  induction l as [| h t IH].
  - simpl. auto.
  - intros. simpl. specialize (IH (f x h)). auto.
Qed.

Theorem fold_range_invariant `{A : Type} (Inv : A -> Prop) :
  forall (l : t_usize) (u : t_usize) (b : A -> t_usize -> bool) (f : A -> t_usize -> A),
  (forall (x : A) (idx : t_usize), Inv x -> Inv (f x idx)) ->
  forall x : A, Inv x -> Inv (fold_range l u b x f).
Proof.
  intros.
  unfold fold_range.
  apply fold_left_invariant; auto.
Qed.

Lemma build_range_step : forall a b l,
  build_range a (S b) l = build_range (S a) b ((nat_to_usize a) :: l).
Proof. auto. Qed.

Lemma build_range_succ : forall a b l,
  build_range a (S b) l = (nat_to_usize (a + b)%nat) :: (build_range a b l).
Proof.
  intros a b.
  generalize dependent a.
  induction b; intros.
  - simpl. rewrite Nat.add_0_r. reflexivity.
  - simpl. rewrite Nat.add_succ_r. rewrite <- build_range_step. rewrite IHb. reflexivity. 
Qed.

Theorem fold_left_build_range_succ : forall {A : Type} (f : A -> t_usize -> A) (x : A) (a b : nat),
  fold_left f (List.rev (build_range a (S b) LIST_NIL)) x = 
  f (fold_left f (List.rev (build_range a b LIST_NIL)) x) (nat_to_usize (a + b)).
Proof.
  intros A f x a b.
  rewrite build_range_succ.
  simpl.
  rewrite fold_left_app.
  simpl.
  reflexivity.
Qed.


Lemma fold_left_ext {A B} (f g : B -> A -> B) (l : list A) (init : B) :
  (forall acc x, In x l -> f acc x = g acc x) ->
  fold_left f l init = fold_left g l init.
Proof.
  revert init.
  induction l as [|a l IH]; intros init Hfg.
  - reflexivity.
  - simpl.
    rewrite Hfg by now left.
    apply IH.
    intros acc x Hx.
    apply Hfg.
    now right.
Qed.

Lemma in_build_range : forall (x : t_usize) (a b : nat) (l : list t_usize),
  In x (build_range a b l) -> ((usize_to_nat x) < a + b)%nat \/ In x l.
Proof.
  intros x a b.
  destruct b as [|b].
  - intros. simpl in H. right. apply H.
  - generalize dependent x.
    generalize dependent a.
    simpl. 
    induction (b); intros.
    + simpl in H. destruct H.
      * left. subst x. 
        unfold usize_to_nat, unary_to_int. 
        simpl. 
        rewrite Nnat.Nat2N.id. 
        auto with zarith.
      * right. apply H.
    + simpl in *. apply IHn in H. destruct H.
      * left. auto with zarith.
      * destruct (Nat.eqb a (usize_to_nat x)) eqn:E. 
        -- apply Nat.eqb_eq in E. 
          subst a. 
          auto with zarith.
        -- right. 
          apply Nat.eqb_neq in E. 
          simpl in *. 
          destruct H; 
          auto with zarith. 
          destruct E.
          subst x.
          unfold unary_to_int, usize_to_nat. 
          simpl.
          rewrite Nnat.Nat2N.id. 
          reflexivity.
Qed.


Theorem if_then_else_eq : forall (A : Type) (b1 b2 : bool) (x1 x2 y1 y2 : A),
  b1 = b2 -> x1 = x2 -> y1 = y2 ->
  (if b1 then x1 else y1) = (if b2 then x2 else y2).
Proof. intros. subst. reflexivity. Qed.
