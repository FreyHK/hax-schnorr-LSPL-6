(** 
	In this file we prove the equivalence between the hax integer type
	and Rocq standard Binary Numbers type 'N'.  
*)


From Coq Require Import ZArith.
Require Import List.
Import List.ListNotations.
Open Scope bool_scope.
Require Import Ascii.
Require Import String.
Require Import Coq.Floats.Floats.
From RecordUpdate Require Import RecordSet.
Import RecordSetNotations.
From Core Require Import Core.

Require Import Lia.

Open Scope N_scope.
(** ** Definition of usize operations

    We define operations for usize, where the specific type class is used
	to avoid problems with type class resolution. *)


Definition usize_add x y : t_usize := Add_f_add (t_Add := t_Add_192585125) x y.
Definition usize_sub x y : t_usize := Sub_f_sub (t_Sub := t_Sub_1064369889) x y.
Definition usize_rem x y : t_usize := Rem_f_rem (t_Rem := t_Rem_796467486) x y.
Definition usize_mul x y : t_usize := Mul_f_mul (t_Mul := t_Mul_490480124) x y.
Definition usize_ltb x y : bool := PartialOrd_f_lt (t_PartialOrd := t_PartialOrd_917114071) x y.
Definition usize_leb x y : bool := PartialOrd_f_le (t_PartialOrd := t_PartialOrd_917114071) x y.

Definition usize_to_haxint (x : t_usize) : t_HaxInt := (U64_f_v (usize_0 x)).
Definition haxint_to_usize (x : t_HaxInt) : t_usize := (Build_t_usize x).
Definition usize_to_nat (x : t_usize) : nat := N.to_nat (U64_f_v (usize_0 x)).
Definition nat_to_usize (x : nat) : t_usize := Build_t_usize (N.of_nat x).

(** ** Wordsize Helper Lemmas 

    We prove simple lemmas about the wordsize to simplify 
	other proofs *)

Definition pos_wordsize := (2^64)%positive.

Theorem wordsize_to_pos : 
	v_WORDSIZE_64_ = Npos (pos_wordsize)%positive.
Proof. reflexivity. Qed.

Theorem wordsize_to_pos_pred : 
	(v_WORDSIZE_64_ - 1)%N = Npos (pos_wordsize - 1)%positive.
Proof. reflexivity. Qed.

Lemma one_lt_wordsize : 1 < v_WORDSIZE_64_.
Proof. unfold v_WORDSIZE_64_. lia. Qed. 

Lemma one_le_wordsize : 1 <= v_WORDSIZE_64_.
Proof. unfold v_WORDSIZE_64_. lia. Qed. 

Lemma word_size_neq_one : v_WORDSIZE_64_ <> 0.
Proof. unfold v_WORDSIZE_64_. lia. Qed.

Lemma wordsize_sub_1_neq_0 : 
	(v_WORDSIZE_64_ - 1)%N <> 0.
Proof.
	unfold v_WORDSIZE_64_.
	lia.
Qed.

(** ** Haxint and N equivalence Proofs

    Here we prove the equivalence between the haxinteger
	operations and the binary number Rocq type 'N'. *)

(** The [haxint_rem_spec] proof as been admitted. *)
Theorem haxint_rem_spec : forall (a b : t_HaxInt), 
	haxint_rem a b = N.modulo a b.
Proof.
	intros.
	unfold haxint_rem.
	unfold haxint_divmod.
	simpl.
	destruct (match_pos a) eqn:E.
	- unfold match_pos in *. subst a. unfold v_HaxInt_ZERO. rewrite N.Div0.mod_0_l. reflexivity.
	- destruct (match_pos b) eqn:E0.
		+ unfold positive_to_int. unfold match_pos in *.
			subst. rewrite N.mod_0_r. reflexivity.
		+ unfold haxint_divmod__divmod_binary.
Admitted.
	
Theorem positive_add_spec : forall (a b : positive), 
  positive_add a b = Pos.add a b.
Proof. induction a; auto. Qed.

Theorem haxint_add_spec : forall (a b : t_HaxInt), 
  haxint_add a b = N.add a b.
Proof. destruct a, b; auto. Qed.

Theorem haxint_mul_spec : forall (a b : t_HaxInt), 
	haxint_mul a b = N.mul a b.
Proof. destruct a, b; auto. Qed.

(** The [haxint_sub_spec] proof has been admitted. The Theorem 
	is currently invalid because of an error in the Hax extraction 
	of Rust Core.When the error is fixed, then this Theorem will 
	be valid.  *)
Theorem haxint_sub_spec : forall (a b : t_HaxInt), 
	haxint_sub a b = N.sub a b. 
Proof. Admitted.

