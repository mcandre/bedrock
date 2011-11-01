Require Import NArith.
Require Import WordViewNat.
Require Import Word.

Set Implicit Arguments.
Set Strict Implicit.

Lemma NToWord_plus : forall sz b c,
  NToWord _ b ^+ NToWord _ c = NToWord sz (b + c).
Proof.
  intros. repeat rewrite NToWord_nat. rewrite natToWord_plus.
  rewrite nat_of_Nplus. auto.
Qed.

Theorem NToWord_minus : forall sz (b c : N),
  (c <= b)%N ->
  NToWord sz b ^- NToWord _ c = NToWord _ (b - c).
Proof.
  intros; repeat rewrite NToWord_nat; rewrite natToWord_minus. rewrite nat_of_Nminus; auto.
  unfold Nle in H.
  rewrite nat_of_Ncompare in H. apply <- Compare_dec.nat_compare_le in H. auto.
Qed.

Theorem NToWord_minus_neg : forall sz (b c : N),
  (b < c)%N ->
  NToWord sz b ^- NToWord _ c = ^~ (NToWord _ (c - b)).
Proof.
  intros. repeat rewrite NToWord_nat; rewrite natToWord_minus_neg. rewrite nat_of_Nminus; auto.
  unfold Nlt in H. rewrite nat_of_Ncompare in H. apply <- Compare_dec.nat_compare_lt in H. auto.
Qed.

Lemma N_le_lt_eq : forall a b : N, (a <= b)%N <-> (a < b)%N \/ a = b.
Proof.
  Require Import Omega.
  intros; split; intros; zify; omega.
Qed.

Lemma sbound_ext_N : forall sz (n : N),
  ((Npow2 (sz - 1)) ?= n = Gt)%N ->
  forall sz', sext (NToWord sz n) sz' = NToWord (sz + sz') n.
Proof.
  
Admitted.

Lemma inj_ext_N : forall (sz : nat) (v : word sz), NToWord sz (wordToN v) = v.
Proof.
  intros. rewrite NToWord_nat. rewrite wordToN_nat. rewrite nat_of_N_of_nat.
  apply natToWord_wordToNat. 
Qed.

Lemma ext_inj_N : forall (sz : nat) (v : N),
 (Npow2 sz ?= v)%N = Gt -> wordToN (NToWord sz v) = v.
Proof.
  intros. rewrite NToWord_nat. rewrite wordToN_nat. 
  rewrite ext_inj_nat. apply N_of_nat_of_N. 
  rewrite N_of_nat_of_N. auto.
Qed.

Lemma sext_neg_N : forall (sz sz' : nat) (n : N),
  (Npow2 sz ?= n)%N = Gt ->
  sext (^~ (NToWord sz n)) sz' = ^~ (NToWord (sz + sz') n).
Proof.
  unfold wneg. intros. repeat rewrite ext_inj_N; auto. 
  unfold sext.
Admitted.
