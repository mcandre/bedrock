Require Import Word.
Require Import WordViewNat.
Require Import WordViewN.

Set Implicit Arguments.
Set Strict Implicit.

Class BitView (V : Type) : Type :=
{ inj : forall sz, V -> word sz
; ext : forall sz, word sz -> V
; Vbound : nat -> V -> Prop
; Vsbound : nat -> V -> Prop
; Vplus : V -> V -> V
; Vminus : V -> V -> V
; Vlt : V -> V -> Prop
; Vle : V -> V -> Prop
; Veq : V -> V -> Prop

; Vle_lt_eq : forall a b, Vle a b <-> (Vlt a b \/ Veq a b)

; winj_plus : forall sz b c,
  inj _ b ^+ inj _ c = inj sz (Vplus b c)

; winj_minus : forall sz (b c : V),
  Vle c b ->
  inj sz b ^- inj _ c = inj _ (Vminus b c)

; winj_minus_neg : forall sz (b c : V),
  Vlt b c ->
  inj sz b ^- inj _ c = ^~ (inj _ (Vminus c b))

; sbound_ext : forall sz n,
  Vsbound sz n ->
  forall sz', sext (inj sz n) sz' = inj (sz + sz') n

; sext_neg : forall sz sz' (n : V),
  Vbound sz n ->
  sext (^~ (inj sz n)) sz' = ^~(inj (sz + sz') n)

; inj_ext : forall sz (v : word sz),
  @inj sz (@ext sz v) = v
; ext_inj : forall sz v,
  Vbound sz v ->
  @ext sz (@inj sz v) = v
}.


Lemma natToWord_n_pow2 : forall sz x,
  natToWord sz (x * pow2 sz) = wzero _.
Proof.
  induction x. simpl. auto.
  simpl. rewrite <- IHx. 
  rewrite <- natToWord_plus. rewrite natToWord_pow2. 
  rewrite IHx. destruct (wring sz). rewrite Radd_comm. rewrite Radd_0_l. auto.
Qed.

Lemma wneg_involutive : forall sz (w : word sz),
  ^~ (^~ w) = w.
Proof.
  intros.
  repeat rewrite wneg_alt. unfold wnegN.
  destruct (wordToNat_natToWord sz (pow2 sz - wordToNat w)). destruct H.
  rewrite H.
  assert (pow2 sz - wordToNat w - x * pow2 sz <= pow2 sz)%nat.
  generalize dependent (pow2 sz). intros. generalize dependent (x * n). intros. omega.
  clear H.
  Lemma minus_minus_minus : forall c a b : nat,
    (c <= b)%nat -> a - (b - c) = a + c - b.
  Proof. intros. omega. Qed.
  generalize (wordToNat_bound w). intros.
  repeat rewrite minus_minus_minus by omega.
  cutrewrite (pow2 sz + x * pow2 sz + wordToNat w - pow2 sz = wordToNat w + x * pow2 sz).
  2: omega.
  rewrite <- natToWord_plus.
  rewrite natToWord_n_pow2. destruct (wring sz). rewrite Radd_comm. rewrite Radd_0_l.
  apply natToWord_wordToNat. 
Qed.

Lemma pow2_gt_0 : forall sz, (pow2 sz > 0)%nat.
Proof.
  induction sz; auto. simpl. omega.
Qed.

Theorem wneg_wmult_1 : forall sz (a : word sz),
  a ^* ^~ (wone _) = ^~ a.
Proof.
  destruct sz. intros. 
  Require Import Program. dependent destruction a. reflexivity.

  intros. repeat rewrite wneg_alt; rewrite wmult_alt.
  unfold wmultN, wnegN, wone, wordBinN.
  destruct (wordToNat_natToWord (S sz) 1).
  assert (x = 0). intuition. destruct x; auto. exfalso. simpl in H1. generalize (pow2_gt_0 sz). 
  intros. generalize dependent (x * (pow2 sz + (pow2 sz + 0))). clear H0. intros. omega. subst.
  destruct H. rewrite H. Opaque pow2 natToWord. simpl.
  destruct (wordToNat_natToWord (S sz) (pow2 (S sz) - 1)). destruct H1.
  rewrite H1.
  assert (x = 0). destruct x. auto. exfalso. generalize (pow2_gt_0 sz).
  Transparent pow2. simpl in H2. generalize H2. clear. intros.
  generalize dependent (pow2 sz). intros. generalize dependent (x * (n + (n + 0))). intros. omega.
  subst. generalize dependent (S sz). simpl. intros.
  rewrite Mult.mult_comm.  
  repeat rewrite Mult.mult_minus_distr_r. simpl.
  rewrite <- Minus.minus_n_O. rewrite <- plus_n_O.
  generalize (wordToNat_bound a). intros.
  case_eq (wordToNat a). intros. 
  repeat rewrite <- Minus.minus_n_O. rewrite Mult.mult_comm. simpl. rewrite natToWord_pow2. auto.
  intros. rewrite <- H4.
  cutrewrite (pow2 n * wordToNat a - wordToNat a = pow2 n - wordToNat a + (wordToNat a - 1) * pow2 n).
  rewrite H4. simpl. rewrite <- Minus.minus_n_O.
  rewrite <- natToWord_plus. rewrite natToWord_n_pow2.
  destruct (wring n). rewrite <- Radd_comm. rewrite Radd_0_l. auto.

  rewrite H4 in *. clear H4. generalize H3. clear. intros.
  simpl. rewrite <- Minus.minus_n_O. rewrite Mult.mult_comm. simpl.
  generalize dependent (n0 * pow2 n). intros. omega.
Qed.

Section BitViewFacts.
  Variable V : Type.
  Variable WV : BitView V.

  Ltac bit_simpl' :=
    repeat (rewrite winj_plus in * ||
      rewrite winj_minus in * by assumption ||
      rewrite winj_minus_neg in * by assumption).

  Theorem inj_plus_plus : forall sz (a : word sz) b c,
    a ^+ inj _ b ^+ inj _ c = a ^+ inj _ (Vplus b c).
  Proof.
    intros. rewrite <- wplus_assoc. bit_simpl'. reflexivity.
  Qed.
  
  Theorem inj_plus_minus_gt : forall sz (a : word sz) (b c : V),
    Vle c b ->
    a ^+ inj _ b ^- inj _ c = a ^+ inj _ (Vminus b c).
  Proof.
    intros. assert (inj sz b ^- inj _ c = inj _ (Vminus b c)). bit_simpl'; eauto.
    rewrite <- H0. repeat rewrite wminus_def. rewrite wplus_assoc. reflexivity.
  Qed.
  
  Theorem inj_minus_plus_lt : forall sz (a : word sz) (b c : V),
    Vle b c ->
    a ^- inj _ b ^+ inj _ c = a ^+ inj _ (Vminus c b).
  Proof.
    intros. rewrite <- inj_plus_minus_gt; auto. repeat rewrite wminus_def.
    repeat rewrite <- wplus_assoc. f_equal. rewrite wplus_comm. reflexivity.
  Qed.
  
  Theorem inj_minus_plus_gt : forall sz (a : word sz) (b c : V),
    Vlt c b ->
    a ^- inj _ b ^+ inj _ c = a ^- inj _ (Vminus b c).
  Proof.
    intros; repeat rewrite wminus_def. repeat rewrite <- wplus_assoc. f_equal.
    rewrite <- winj_minus_neg; auto. rewrite wminus_def. rewrite wplus_comm. auto.
  Qed.

  Theorem inj_minus_minus : forall sz (a : word sz) (b c : V), 
    a ^- inj _ b ^- inj _ c = a ^- inj _ (Vplus b c).
  Proof.
    intros. repeat rewrite wminus_def. rewrite <- wplus_assoc. f_equal.
    generalize (@wmult_plus_distr sz (inj _ b) (inj _ c) (^~ (wone _))); intros.
    repeat rewrite wneg_wmult_1 in H. rewrite <- H. rewrite winj_plus. auto.
  Qed.

  Theorem inj_plus_minus_lt : forall sz (a : word sz) (b c : V),
    Vlt b c ->
    a ^+ inj _ b ^- inj _ c = a ^- inj _ (Vminus c b).
  Proof.
    intros. rewrite <- inj_minus_plus_gt; auto. repeat rewrite wminus_def.
    repeat rewrite <- wplus_assoc. f_equal. rewrite wplus_comm. auto.
  Qed.

  Lemma inj_neg_plus_plus : forall sz a b c,
    ^~(inj sz a) ^+ b ^+ inj _ c = b ^+ inj _ c ^- inj _ a.
  Proof.
    intros. unfold wminus. rewrite wplus_comm. rewrite (wplus_comm b (inj _ c)). rewrite <- wplus_assoc.
    f_equal. apply wplus_comm.
  Qed.

  Theorem inj_plus_x_plus : forall sz (a : word sz) b c,
    inj _ b ^+ a ^+ inj _ c = a ^+ inj _ (Vplus c b).
  Proof.
    intros. rewrite <- wplus_assoc. rewrite wplus_comm. rewrite <- wplus_assoc. f_equal.
    rewrite winj_plus. f_equal. 
  Qed.

  Theorem inj_plus_x_minus_gt : forall sz (a : word sz) b c,
    Vle c b ->
    inj _ b ^+ a ^- inj _ c = a ^+ inj _ (Vminus b c).
  Proof.
    intros. rewrite wminus_def. rewrite (wplus_comm (inj _ b) a). rewrite <- wplus_assoc. f_equal.
    rewrite <- winj_minus; eauto.
  Qed.

  Theorem inj_plus_x_minus_lt : forall sz (a : word sz) b c,
    Vlt b c ->
    inj _ b ^+ a ^- inj _ c = a ^- inj _ (Vminus c b).
  Proof.
    intros. repeat rewrite wminus_def. rewrite (wplus_comm (inj _ b) a). rewrite <- wplus_assoc. f_equal.
    rewrite <- winj_minus; [ | destruct WV; eapply Vle_lt_eq0; auto ]. generalize (wring sz). intros. destruct H0.
    rewrite <- (wneg_wmult_1 (inj sz c ^- inj sz b)). rewrite Rsub_def. rewrite Rdistr_l.
    rewrite wneg_wmult_1. rewrite Radd_comm. f_equal. rewrite wneg_wmult_1. generalize (inj sz b).
    intros. rewrite wneg_involutive. auto.
  Qed.

End BitViewFacts.

Lemma wzero_plus_l : forall sz a, wzero sz ^+ a = a.
Proof.
  intros. destruct (wring sz). auto.
Qed.

Lemma wzero_plus_r : forall sz a, a ^+ wzero sz = a.
Proof.
  intros. destruct (wring sz). rewrite Radd_comm. auto.
Qed.

Transparent natToWord.

Lemma wneg_wzero_wzero : forall sz, 
  wneg (wzero sz) = wzero sz.
Proof.
  unfold wneg,wzero. 
  intros; rewrite wordToN_nat. edestruct wordToNat_natToWord.
  destruct H. rewrite H.
  destruct x. simpl in *. rewrite BinNat.Nminus_0_r.
  rewrite <- natToWord_pow2. rewrite NToWord_nat. 
  rewrite Npow2_nat. reflexivity.
  exfalso. generalize (pow2_gt_0 sz). simpl in *. intros.
  generalize dependent (pow2 sz). clear. intros. generalize dependent (x * n).
  intros. omega.
Qed.
  
Lemma wzero_minus_r : forall sz a, a ^- wzero sz = a.
Proof.
  intros. unfold wminus.
  cutrewrite (^~ (wzero sz) = wzero sz). apply wzero_plus_r.
  eapply wneg_wzero_wzero.
Qed.

Lemma sext_wzero : forall sz sz', sext (wzero sz') sz = wzero _.
Proof.
  unfold sext. assert (forall sz, wmsb (wzero sz) false = false).
  induction sz; auto.
  intros. rewrite H. clear. induction sz'; auto. simpl.
  change (natToWord sz' 0) with (wzero sz').
  rewrite IHsz'. unfold wzero. auto.
Qed.

Lemma wneg_plus : forall sz (a b : word sz),
    ^~ a ^+ b = b ^- a.
Proof.
  unfold wminus. intros. rewrite wplus_comm. auto.
Qed.

Require Import Omega.

Ltac inj_solver := simpl Vlt; simpl Vle; simpl Veq; (omega || zify; omega).

Ltac post_reduce := simpl plus; simpl minus; simpl Nplus; simpl Nminus.
Ltac post_reduce_in_star := simpl plus in *; simpl minus in *; simpl Nplus in *; simpl Nminus in *.
Ltac post_reduce_in H := simpl plus in H; simpl minus in H; simpl Nplus in H; simpl Nminus in H.

Hint Rewrite @winj_plus : bit_simpl.
Hint Rewrite @winj_minus @winj_minus_neg using inj_solver : bit_simpl.

Hint Rewrite inj_neg_plus_plus : bit_simpl.
Hint Rewrite inj_plus_plus inj_minus_minus : bit_simpl. 
Hint Rewrite inj_plus_minus_gt inj_plus_minus_lt using inj_solver : bit_simpl.
Hint Rewrite inj_minus_plus_lt inj_minus_plus_gt using inj_solver : bit_simpl.

Hint Rewrite wzero_plus_l wzero_plus_r wzero_minus_r sext_wzero : bit_simpl.
Hint Rewrite @sbound_ext using (reflexivity || inj_solver) : bit_simpl.
Hint Rewrite @sext_neg using (reflexivity || inj_solver) : bit_simpl.

Hint Rewrite inj_plus_x_plus inj_plus_x_minus_gt inj_plus_x_minus_lt using inj_solver : bit_canon.
Hint Rewrite wplus_assoc wneg_plus : bit_canon.
Hint Rewrite @inj_ext : bit_canon.
Hint Rewrite @ext_inj using eauto : bit_canon.

Lemma word_solve_plus : forall sz (a b c : word sz),
  a = c ^- b -> a ^+ b = c.
Proof. intros. subst. unfold wminus. rewrite <- wplus_assoc.
  rewrite (wplus_comm _ b). rewrite wminus_inv. rewrite wplus_comm. rewrite wplus_unit.
  reflexivity.
Qed.



(** N **)
Require Import NArith.

Global Instance BitView_N : BitView N :=
{ inj := NToWord
; ext := wordToN
; Vsbound := fun sz n => ((Npow2 (sz - 1)) ?= n = Gt)%N
; Vbound := fun sz n => ((Npow2 sz) ?= n = Gt)%N
; Vplus := Nplus
; Vminus := Nminus
; Vlt := Nlt
; Vle := Nle
; Veq := @eq N
; Vle_lt_eq := N_le_lt_eq 
; winj_plus := NToWord_plus
; winj_minus := NToWord_minus
; winj_minus_neg := NToWord_minus_neg
; sbound_ext := sbound_ext_N
; sext_neg := sext_neg_N
; inj_ext := inj_ext_N
; ext_inj := ext_inj_N
}.


(** nat **)
Global Instance BitView_nat : BitView nat :=
{ inj := natToWord
; ext := wordToNat
; Vsbound := fun sz n => ((Npow2 (sz - 1)) ?= (N_of_nat n) = Gt)%N
; Vbound := fun sz n : nat => ((Npow2 sz) ?= (N_of_nat n) = Gt)%N
; Vplus := plus
; Vminus := minus
; Vlt := lt
; Vle := le
; Veq := @eq nat
; Vle_lt_eq := nat_le_lt_eq 
; winj_plus := natToWord_plus
; winj_minus := natToWord_minus
; winj_minus_neg := natToWord_minus_neg
; sbound_ext := natToWord_sext_sbound
; sext_neg := sext_neg_nat
; inj_ext := natToWord_wordToNat
; ext_inj := ext_inj_nat
}.

(* nat hacks *)
Theorem Vbound_le : forall sz (n m : nat),
  Vbound sz n -> (m <= n)%nat -> Vbound sz m.
Proof.
  simpl. intros. 
  change ((Npow2 sz ?= N_of_nat n)%N = Gt) with (Ngt (Npow2 sz) (N_of_nat n)) in H.
  change ((Npow2 sz ?= N_of_nat m)%N = Gt) with (Ngt (Npow2 sz) (N_of_nat m)).
  zify. omega.
Qed.
Hint Resolve Vbound_le.

(** Begin Tactics **)
Require Import ExtTactics.

Ltac bit_simpl_in H :=
  let pre := hide_evars_in H;
             try (change (NToWord) with (@inj _ BitView_N) in H);
             try (change (natToWord) with (@inj _ BitView_nat) in H) in
  let post := (simpl plus in H; simpl minus in H;
               simpl Nplus in H; simpl Nminus in H) in
  pre;
  repeat progress (autorewrite with bit_simpl in H; 
                   autorewrite with bit_canon in H;
                   simpl Vplus in H; simpl Vminus in H); restore_evars.

Ltac bit_simpl :=
  let pre := hide_evars;
             try (change (NToWord) with (@inj _ BitView_N));
             try (change (natToWord) with (@inj _ BitView_nat)) in
  let post := (simpl plus; simpl minus;
               simpl Nplus; simpl Nminus) in
  pre;
  repeat progress (autorewrite with bit_simpl;
                   autorewrite with bit_canon;
                   simpl Vplus; simpl Vminus; post); restore_evars.

Ltac bit_simpl_in_star :=
  let pre := hide_evars;
             try (change (NToWord) with (@inj _ BitView_N) in * );
             try (change (natToWord) with (@inj _ BitView_nat) in * ) in
  let post := (simpl plus in *; simpl minus in *; 
               simpl Nplus in *; simpl Nminus in * ) in
  pre;
  repeat progress (autorewrite with bit_simpl in *;
                   autorewrite with bit_canon in *;
                   simpl Vplus in *; simpl Vminus in *; post); restore_evars.
(** End Tactics **)

Notation "## n" := (@inj _ _ _ n) (at level 0).
Notation "#! s n" := (@inj _ _ s n) (at level 0).

(*
Goal forall sz (a : word sz),
  a ^+ ##4 ^- ##8 ^+ ##16 ^- ##32 ^+ ##20 ^- ##64 = ##64 ^+ a ^- ##128.
intros. bit_simpl. reflexivity.
*)
