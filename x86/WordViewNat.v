Require Import Word.

Set Implicit Arguments.
Set Strict Implicit.

Lemma natToWord_plus : forall sz b c,
  natToWord _ b ^+ natToWord _ c = natToWord sz (b + c).
Proof.
  intros.
  rewrite wplus_alt. unfold wplusN. unfold wordBinN.
  destruct (wordToNat_natToWord sz b).
  destruct (wordToNat_natToWord sz c). destruct H. destruct H0.
  rewrite H. rewrite H0.
  cutrewrite (b - x * pow2 sz + (c - x0 * pow2 sz) = b + c - (x + x0) * pow2 sz).
  Focus 2. rewrite Mult.mult_plus_distr_r. omega.
  rewrite drop_sub. f_equal. rewrite Mult.mult_plus_distr_r. omega.
Qed.

Theorem natToWord_minus : forall sz (b c : nat),
  (b >= c)%nat ->
  natToWord sz b ^- natToWord _ c = natToWord _ (b - c).
Proof.
  intros. unfold wminus. rewrite wplus_alt. rewrite wneg_alt.
  unfold wplusN, wordBinN, wnegN.
  repeat match goal with
           | [ |- context [ wordToNat (@natToWord ?SZ ?X) ] ] => 
             let H := fresh in 
               generalize (wordToNat_bound (@natToWord SZ X));
                 destruct (wordToNat_natToWord SZ X) as [ ? [ H ? ] ]; rewrite H in *; clear H
         end; intros.
  cutrewrite (b - x * pow2 sz + (pow2 sz - (c - x1 * pow2 sz) - x0 * pow2 sz) = 
              b + (pow2 sz - (c - x1 * pow2 sz) - x0 * pow2 sz) - x * pow2 sz).
  Focus 2. generalize (pow2 sz - (c - x1 * pow2 sz) - x0 * pow2 sz). intros. generalize H1; clear. intros. omega.
  rewrite drop_sub.
  Focus 2. generalize ((pow2 sz - (c - x1 * pow2 sz) - x0 * pow2 sz)); generalize H1; clear; intros; omega.
  cutrewrite (b + (pow2 sz - (c - x1 * pow2 sz) - x0 * pow2 sz) = 
              b + (pow2 sz - (c - x1 * pow2 sz)) - x0 * pow2 sz). 
  Focus 2. generalize dependent (pow2 sz - (c - x1 * pow2 sz)). clear. intros. omega.
  rewrite drop_sub.
  Focus 2. generalize dependent (c - x1 * pow2 sz). intros. omega.
  cutrewrite (b + (pow2 sz - (c - x1 * pow2 sz)) = b - c + pow2 sz + x1 * pow2 sz).
  Focus 2. generalize dependent (pow2 sz). intros; generalize dependent (x1 * n). intros.
  remember (c - n0) as Cno. destruct Cno. omega. omega.
  
  do 2 rewrite <- natToWord_plus. rewrite natToWord_pow2.
  assert (natToWord sz (x1 * pow2 sz) = natToWord _ 0). clear.
  induction x1. auto. simpl. rewrite <- natToWord_plus. rewrite natToWord_pow2. rewrite IHx1. rewrite wplus_unit. auto.
  rewrite H6. rewrite <- wplus_assoc. rewrite wplus_unit. rewrite wplus_comm. rewrite wplus_unit. reflexivity.
Qed.

Theorem natToWord_minus_neg : forall sz (b c : nat),
  (c > b)%nat ->
  natToWord sz b ^- natToWord _ c = ^~ (natToWord _ (c - b)).
Proof.
  intros. unfold wminus. repeat rewrite wplus_alt. repeat rewrite wneg_alt.
  unfold wplusN, wordBinN, wnegN.
  repeat match goal with
           | [ |- context [ wordToNat (@natToWord ?SZ ?X) ] ] => 
             match X with
               | context [ natToWord _ _ ] => fail 1
               | _ => 
                 let H := fresh in 
                   generalize (wordToNat_bound (@natToWord SZ X));
                     destruct (wordToNat_natToWord SZ X) as [ ? [ H ? ] ]; rewrite H in *; clear H
             end
         end; intros.
  Lemma push1 : forall a b c,
    (a >= b)%nat ->
    a - b + c = a + c - b.
  intros; omega.
  Qed.
  repeat rewrite push1.
  Focus 2. generalize H1; clear; intros; omega.
  rewrite Plus.plus_comm.
  rewrite drop_sub.
  Focus 2. generalize H1. clear; intros. omega.
  Lemma pull1 : forall a b c, 
    (b <= a)%nat ->
    a - b + c = a + c - b.
    intros; omega.
  Qed.
  rewrite pull1; [ | assumption ].
  rewrite drop_sub.
  Focus 2. generalize H3; clear; intros. omega.

  Lemma pull2 : forall a b c,
    (b >= c)%nat ->
    a - (b - c) = a + c - b.
    intros. omega.
  Qed.
  repeat rewrite pull2; eauto. 
  2: generalize H; clear; intros; omega.
  cutrewrite (pow2 sz + x0 * pow2 sz - c + b = pow2 sz + x0 * pow2 sz + b - c).
  Focus 2. generalize H6. clear. intros; omega.
  destruct (Compare_dec.le_lt_dec x0 x2).
  assert (exists y, x0 + y = x2). exists (x2 - x0). generalize l; clear; intros; omega. destruct H8.
  rewrite <- H8. cutrewrite (pow2 sz + (x0 + x3) * pow2 sz + b - c = pow2 sz + x0 * pow2 sz + b - c + x3 * pow2 sz).
  Focus 2. rewrite <- H8 in *. clear H8. generalize H0.
  assert (c < pow2 sz + b + x0 * pow2 sz)%nat. generalize H6; clear; intros; omega. generalize H8. clear.
  repeat rewrite Mult.mult_plus_distr_r. repeat rewrite Plus.plus_assoc. intros.
  omega. generalize (pow2 sz + x0 * pow2 sz + b - c). clear. intros.
  rewrite <- natToWord_plus. induction x3. simpl. rewrite wplus_comm. rewrite wplus_unit. auto.
  simpl. rewrite <- natToWord_plus. rewrite natToWord_pow2. rewrite wplus_unit. auto.

  assert (exists y, x2 + y = x0). exists (x0 - x2). generalize l; clear; intros; omega. destruct H8. subst.
  assert (c < pow2 sz + b + x2 * pow2 sz)%nat. generalize H0; clear; intros; omega. generalize H8. clear.
  intros. 
  cutrewrite (pow2 sz + (x2 + x3) * pow2 sz + b - c = pow2 sz + x2 * pow2 sz + b - c + x3 * pow2 sz).
  Focus 2.
  repeat rewrite Mult.mult_plus_distr_r. repeat rewrite Plus.plus_assoc. generalize H8; clear.   
  generalize (x2 * pow2 sz). generalize (x3*pow2 sz). intros. omega.

  rewrite <- natToWord_plus. clear. induction x3.
  simpl. rewrite wplus_comm. rewrite wplus_unit. reflexivity.
  simpl. rewrite <- natToWord_plus. rewrite natToWord_pow2. rewrite wplus_unit. auto.
Qed.

Lemma nat_le_lt_eq : forall a b : nat, (a <= b)%nat <-> (a < b)%nat \/ a = b.
Proof.
  intros; split; intros; omega.
Qed.

Require Import NArith.

  Lemma natToWord_sext_sbound : forall sz (n : nat), 
    ((Npow2 (sz - 1)) ?= (N_of_nat n) = Gt)%N ->
    forall sz', sext (natToWord sz n) sz' = natToWord (sz + sz') n.
  Proof.

    unfold sext. simpl in *. 
  Lemma wordToNat_bounded : forall sz n,
    (n < pow2 sz)%nat -> 
    forall sz', combine (natToWord sz n) (wzero sz') = natToWord (sz + sz') n.
  Proof.
    Transparent natToWord.
    induction sz. simpl. destruct n. auto. intro. exfalso; omega.
    simpl. intros. f_equal. erewrite <- IHsz. auto. clear IHsz.
    cut (Div2.div2 n + Div2.div2 n < pow2 sz + pow2 sz)%nat.
    intros. omega.
    Lemma div2_times2_le : forall n,
      (2 * Div2.div2 n <= n)%nat.
    Proof.
      clear; intros.
      induction n using Div2.ind_0_1_SS; auto.
      simpl. omega.
    Qed.
    generalize (div2_times2_le n). simpl. omega.
  Qed.

  Admitted.



Lemma sbound_wmsb_nat : forall sz n : nat,
  ((Npow2 (sz - 1)) ?= (N_of_nat n) = Gt)%N -> wmsb (natToWord sz n) false = false.
Proof.
  destruct sz. auto.
  simpl. intros; generalize (mod2 n). rewrite <- Minus.minus_n_O in H.
  generalize dependent n. induction sz. 
  simpl in *.
Admitted.

Lemma sext_neg_nat : forall sz sz' (n : nat),
  ((Npow2 sz) ?= (N_of_nat n) = Gt)%N ->
  sext (^~ (natToWord sz n)) sz' = ^~(natToWord (sz + sz') n).
Proof.
  intros. unfold sext, wneg.
Admitted.

Lemma ext_inj_nat : forall sz v : nat,
  (Npow2 sz ?= N_of_nat v)%N = Gt -> wordToNat (natToWord sz v) = v.
Proof.
  intros. destruct (wordToNat_natToWord sz v) as [ ? [ ? ? ] ]. 
  cut (x = 0). intros. subst. simpl in *. rewrite H0. omega.
  clear H0. rewrite nat_of_Ncompare in H. rewrite nat_of_N_of_nat in H.
  apply Compare_dec.nat_compare_gt in H. rewrite Npow2_nat in H.
  destruct x. auto. simpl in H1. exfalso. generalize dependent (x * pow2 sz). intros. omega.
Qed.

(*

Theorem sext_lat : forall sz a b,
  (N_of_nat a < Npow2 (sz - 1))%N ->
  sext (natToWord sz a) b = natToWord _ a.
Proof.
  assert (forall sz a b, (a < pow2 (sz - 1))%nat -> 
    ((sz = 0 -> wmsb (natToWord sz a) b = b) /\
     (sz <> 0 -> wmsb (natToWord sz a) b = false))).
  Focus. 
  induction sz; auto. intuition.
  Transparent natToWord. simpl. intros. split. intros. inversion H0. intros.
  assert (Div2.div2 a < pow2 (sz - 1))%nat. admit.
  eapply IHsz with (b := mod2 a) in H1. destruct H1.
  destruct sz. simpl in H. destruct a. auto. elimtype False. omega.
  eapply H2. auto.
(*
  unfold sext. intros. specialize (H sz a false H0). destruct H.
  destruct sz. rewrite H; auto. admit.
  rewrite H1; auto. admit.
*)
Admitted.
Lemma sext_neg : forall sz a b,
  (N_of_nat a < Npow2 (sz - 1))%N ->
  sext (^~ (natToWord sz a)) b = ^~ (natToWord (sz + b) a).
Admitted.

*)
