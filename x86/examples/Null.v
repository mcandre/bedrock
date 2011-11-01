Require Import x86.
Require Import WordView.
Require Import BinNat.

Definition NULL : SepArg.addr := wzero _ .

Definition noneNull (base : word W64) (len : nat) : Prop :=
  forall n , (n < len)%nat -> base ^+ ## n <> NULL.
(*  
  base <> NULL /\ (wordToNat base + len < pow2 64)%nat.
*)

Lemma noneNull_not_null_start : forall l b, 
  (l > 0)%nat -> noneNull b l -> b = NULL -> False.
Proof.
  unfold noneNull. intros. specialize (H0 0). apply H0. omega. word_simpl. auto.
Qed. 

Lemma noneNull_move_noneNull : forall b l o p,
  noneNull b l -> (p < l - ext o)%nat -> noneNull (b ^+ o) p.
Proof.
(*
  unfold noneNull. intros.
  specialize (H (n + wordToNat o)).
  assert ((n + wordToNat o < l)%nat) by omega.
  rewrite <- Word.wplus_assoc.
  cutrewrite (o ^+ ## n = ## (n + wordToNat o)). auto.
  clear.

  rewrite wplus_alt. unfold wplusN, wordBinN.
  rewrite Plus.plus_comm. simpl inj.
  destruct (wordToNat_natToWord 64 n). destruct H. rewrite H. generalize dependent (wordToNat o). intros.
  repeat rewrite <- WordViewNat.natToWord_plus. rewrite <- WordViewNat.natToWord_minus. 2: auto.
  rewrite natToWord_n_pow2. word_simpl. auto.
Qed. *)
Admitted.

Lemma le_ext : forall sz (a b : word sz), 
  (a <= b)%word -> (ext a <= ext b)%nat.
Proof.
  unfold wlt. intros. 
  unfold Nlt in *. rewrite Nnat.nat_of_Ncompare in H.
  unfold ext. simpl.
  repeat rewrite wordToN_nat in H.
  repeat rewrite Nnat.nat_of_N_of_nat in H.
  apply <- Compare_dec.nat_compare_ge in H. (*omega.
Qed.*) Admitted.
Lemma lt_ext : forall sz (a b : word sz), 
  (a < b)%word -> (ext a < ext b)%nat.
Proof.
(*
  unfold wlt. intros. 
  unfold Nlt in *. rewrite Nnat.nat_of_Ncompare in H.
  unfold ext. simpl.
  repeat rewrite wordToN_nat in H.
  repeat rewrite Nnat.nat_of_N_of_nat in H.
  apply <- Compare_dec.nat_compare_lt in H. omega.
Qed. *) Admitted.

Require Import Omega.

Lemma noneNull_not_null : forall l l' b,
  noneNull l b -> (l <= l')%word -> (l' < l ^+ ## b)%word -> l' <> NULL.
Proof.
(*
  intros. unfold not. unfold noneNull in H.
  intros; subst. unfold NULL in *.
  cut (l = wzero 64). intros; subst. word_simpl_in H1.
  eapply H. instantiate (1 := 0). 
  destruct b. 2: omega. exfalso. unfold wlt in H1.
  simpl in H1. zify; omega.
  word_simpl. reflexivity.
  unfold wlt in H0. simpl in H0.
  rewrite wordToN_nat in H0. clear H.
  remember (wordToNat l). destruct n. simpl in H0.
  unfold wzero. generalize dependent 64. intros.
  rewrite Heqn. rewrite natToWord_wordToNat. reflexivity.
  exfalso. apply H0. cutrewrite (S n = 1 + n). 2: omega.
  rewrite Nnat.N_of_plus. simpl Nnat.N_of_nat. generalize (Nnat.N_of_nat n).
  intros.
  clear. zify; omega.
Qed.
*) Admitted.