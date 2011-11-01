Require Import Word.
Require Import BitView.

Set Implicit Arguments.
Set Strict Implicit.

Module Type WordSizes.
  Parameter wsize : Type.
  Parameter wsize_size : wsize -> nat.
End WordSizes.

Module Words (WS : WordSizes).
  Import WS.

  Definition wsize_le (a b : wsize) : Prop :=
    (wsize_size a <= wsize_size b)%nat.

Definition word (sz : wsize) : Type := word (wsize_size sz).

Definition wzero (sz : wsize) : word sz := wzero (wsize_size sz).
Definition wone (sz : wsize) : word sz := wone (wsize_size sz).

Definition sext (sz : wsize) (w : word sz) (sz' : wsize) : word sz'.  
  refine (
    match Compare_dec.le_lt_dec (wsize_size sz) (wsize_size sz') with
      | left  pf => _
      | right _ => _
    end).
  pose (@sext (wsize_size sz) w (wsize_size sz' - wsize_size sz)).
  cutrewrite (wsize_size sz + (wsize_size sz' - wsize_size sz) = wsize_size sz') in w0.
  apply w0. abstract omega.
  eapply split1. instantiate (1 := (wsize_size sz) - (wsize_size sz')).
  cutrewrite ((wsize_size sz' + (wsize_size sz - wsize_size sz')) = wsize_size sz). eapply w.
  abstract omega.
Defined.

Definition zext (sz : wsize) (w : word sz) (sz' : wsize) : word sz'.
  refine (
    match Compare_dec.le_lt_dec (wsize_size sz) (wsize_size sz') with
      | left  pf => _
      | right _ => _
    end).
  pose (@zext (wsize_size sz) w (wsize_size sz' - wsize_size sz)).
  cutrewrite (wsize_size sz + (wsize_size sz' - wsize_size sz) = wsize_size sz') in w0.
  apply w0. abstract omega.
  eapply split1. instantiate (1 := (wsize_size sz) - (wsize_size sz')).
  cutrewrite ((wsize_size sz' + (wsize_size sz - wsize_size sz')) = wsize_size sz). eapply w.
  abstract omega.
Defined.

Definition wplus sz (a b : word sz) : word sz :=
  @wplus (wsize_size sz) a b.
Definition wminus sz (a b : word sz) : word sz :=
  @wminus (wsize_size sz) a b.
Definition wmult sz (a b : word sz) : word sz :=
  @wmult (wsize_size sz) a b.
Definition wneg sz (a : word sz) : word sz :=
  @wneg (wsize_size sz) a.

Definition weq sz (l r : word sz) : {l = r} + {l <> r} :=
  weq l r.

Definition weqb sz (l r : word sz) : bool :=
  if weq l r then true else false.

Theorem weqb_sound : forall sz (x y : word sz),
  weqb x y = true -> x = y.
Proof.
  unfold weqb. intros; destruct (weq x y); auto. discriminate.
Qed.

Definition wlt sz (l r : word sz) : Prop :=
  BinNat.Nlt (wordToN l) (wordToN r).
Definition wslt sz (l r : word sz) : Prop :=
  BinInt.Zlt (wordToZ l) (wordToZ r).

Delimit Scope word_scope with word.
Bind Scope word_scope with word.

Notation "^~" := wneg.
Notation "l ^+ r" := (@wplus _ l%word r%word) (at level 50, left associativity).
Notation "l ^* r" := (@wmult _ l%word r%word) (at level 40, left associativity).
Notation "l ^- r" := (@wminus _ l%word r%word) (at level 50, left associativity).

Notation "w1 > w2" := (@wlt _ w2%word w1%word) : word_scope.
Notation "w1 >= w2" := (~(@wlt _ w1%word w2%word)) : word_scope.
Notation "w1 < w2" := (@wlt _ w1%word w2%word) : word_scope.
Notation "w1 <= w2" := (~(@wlt _ w2%word w1%word)) : word_scope.

Notation "w1 '>s' w2" := (@wslt _ w2%word w1%word) (at level 70, arguments at next level) : word_scope.
Notation "w1 '>s=' w2" := (~(@wslt _ w1%word w2%word)) (at level 70, arguments at next level) : word_scope.
Notation "w1 '<s' w2" := (@wslt _ w1%word w2%word) (at level 70, arguments at next level) : word_scope.
Notation "w1 '<s=' w2" := (~(@wslt _ w2%word w1%word)) (at level 70, arguments at next level) : word_scope.

Definition  wlt_dec sz (a b : word sz) : {a < b} + {a >= b} :=
  wlt_dec a b.
Definition  wslt_dec sz (a b : word sz) : {a <s b} + {a >s= b} :=
  wslt_dec a b.

Lemma rewrite_weq : forall sz (a b : word sz)
  (pf : a = b),  
  weq a b = left pf.
Proof.
  intros; destruct (weq a b); try solve [ elimtype False; auto ].
  f_equal. 
  Require Import Eqdep_dec.
  eapply UIP_dec. eapply weq.
Qed.

Lemma wplus_comm : forall sz (x y : word sz),
  x ^+ y = y ^+ x.
Proof. intros; eapply wplus_comm. Qed.

Lemma wplus_assoc : forall sz (x y z : word sz),
  x ^+ (y ^+ z) = x ^+ y ^+ z.
Proof. intros; eapply wplus_assoc. Qed.

Lemma wminus_def : forall sz (x y : word sz), x ^- y = x ^+ ^~ y.
Proof. intros; eapply wminus_def. Qed.

Class WordView (V : Type) : Type :=
{ inj : forall sz, V -> word sz
; ext : forall sz, word sz -> V
; Vbound : wsize -> V -> Prop
; Vsbound : wsize -> V -> Prop
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
  forall sz', wsize_le sz sz' ->
  sext (inj sz n) sz' = inj sz' n

; sext_neg : forall sz sz' (n : V),
  Vbound sz n ->
  wsize_le sz sz' ->
  sext (^~ (inj sz n)) sz' = ^~(inj sz' n)

; inj_ext : forall sz (v : word sz),
  @inj sz (@ext sz v) = v
; ext_inj : forall sz v,
  Vbound sz v ->
  @ext sz (@inj sz v) = v
}.

Global Instance BitView_WordView (V : Type) (BV : BitView V) : WordView V :=
  { inj := fun sz => @BitView.inj V BV (wsize_size sz)
  ; ext := fun sz => @BitView.ext V BV (wsize_size sz)
  ; Vbound := fun sz => @BitView.Vbound V BV (wsize_size sz)
  ; Vsbound := fun sz => @BitView.Vsbound V BV (wsize_size sz)
  ; Vplus := @BitView.Vplus V BV
  ; Vminus := @BitView.Vminus V BV
  ; Vlt := @BitView.Vlt V BV
  ; Vle := @BitView.Vle V BV
  ; Veq := @BitView.Veq V BV
  ; Vle_lt_eq := @BitView.Vle_lt_eq V BV
  ; winj_plus := fun sz => @BitView.winj_plus V BV (wsize_size sz)
  ; winj_minus := fun sz => @BitView.winj_minus V BV (wsize_size sz)
  ; winj_minus_neg := fun sz => @BitView.winj_minus_neg V BV (wsize_size sz)
  ; inj_ext := fun sz => @BitView.inj_ext V BV (wsize_size sz)
  ; ext_inj := fun sz => @BitView.ext_inj V BV (wsize_size sz)
  }.
Focus.
intros. eapply BitView.sbound_ext in H. unfold sext.
unfold wsize_le in H0. rewrite H.
destruct (Compare_dec.le_lt_dec (wsize_size sz) (wsize_size sz')).
2: exfalso; omega.
clear H.
unfold eq_rec, eq_rect. clear H0.
match goal with
  | [ |- match ?X with | eq_refl => _ end  = _ ] => generalize dependent X
end. intro. simpl in e. generalize dependent (wsize_size sz). clear.
intros. generalize dependent (n0 + (wsize_size sz' - n0)). intros. 
subst. auto.

intros. eapply BitView.sext_neg in H. unfold sext. rewrite H.
unfold wsize_le in H0.
match goal with 
  | [ |- match ?X with | left _ => _ | right _ => _ end = _ ] => destruct X
end.
2: exfalso; omega.
unfold eq_rec, eq_rect. clear H0.
match goal with
  | [ |- match ?X with | eq_refl => _ end  = _ ] => generalize dependent X
end. intro. simpl in e. generalize dependent (wsize_size sz). clear.
intros. clear H. generalize dependent (n0 + (wsize_size sz' - n0)). intros. 
subst. auto.
Defined.

Coercion wsize_size : wsize >-> nat.

Lemma natToWord_n_pow2 : forall (sz : wsize) x,
  natToWord sz (x * pow2 sz) = wzero _.
Proof.
  unfold wzero. simpl; intros.
  eapply natToWord_n_pow2.
Qed.

Lemma wneg_involutive : forall sz (w : word sz),
  ^~ (^~ w) = w.
Proof.
  intros. apply BitView.wneg_involutive.
Qed.

Theorem wneg_wmult_1 : forall sz (a : word sz),
  a ^* ^~ (wone sz) = ^~ a.
Proof.
  intros. apply BitView.wneg_wmult_1.
Qed.

Section WordViewFacts.
  Variable V : Type.
  Variable WV : WordView V.

  Ltac to_raw :=
    unfold wplus, wminus, wmult.
  Ltac from_raw :=
    repeat match goal with
             | [ |- context [ @Word.wplus (wsize_size ?X) _ _ ] ] =>
             change (@Word.wplus (wsize_size X)) with (@wplus X) in *
             | [ H : context [ @Word.wplus (wsize_size ?X) _ _ ] |- _ ] =>
               change (@Word.wplus (wsize_size X)) with (@wplus X) in *
             | [ |- context [ @Word.wminus (wsize_size ?X) _ _ ] ] =>
             change (@Word.wminus (wsize_size X)) with (@wminus X) in *
             | [ H : context [ @Word.wminus (wsize_size ?X) _ _ ] |- _ ] =>
               change (@Word.wminus (wsize_size X)) with (@wminus X) in *
             | [ |- context [ @Word.wneg (wsize_size ?X) _ ] ] =>
             change (@Word.wneg (wsize_size X)) with (@wneg X) in *
             | [ H : context [ @Word.wneg (wsize_size ?X) _ ] |- _ ] =>
               change (@Word.wneg (wsize_size X)) with (@wneg X) in *
         end.


  Ltac word_simpl' :=
    from_raw;
    repeat (rewrite winj_plus in * ||
      rewrite winj_minus in * by assumption ||
      rewrite winj_minus_neg in * by assumption).

  Theorem inj_plus_plus : forall sz (a : word sz) b c,
    a ^+ inj _ b ^+ inj _ c = a ^+ inj _ (Vplus b c).
  Proof.
    intros; to_raw. rewrite <- Word.wplus_assoc. word_simpl'. reflexivity.
  Qed.
  
  Theorem inj_plus_minus_gt : forall sz (a : word sz) (b c : V),
    Vle c b ->
    a ^+ inj _ b ^- inj _ c = a ^+ inj _ (Vminus b c).
  Proof.
    intros. assert (inj sz b ^- inj _ c = inj _ (Vminus b c)). word_simpl'; eauto.
    rewrite <- H0. to_raw. repeat rewrite Word.wminus_def. rewrite Word.wplus_assoc. reflexivity.
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
  Admitted.

  Theorem inj_plus_minus_lt : forall sz (a : word sz) (b c : V),
    Vlt b c ->
    a ^+ inj _ b ^- inj _ c = a ^- inj _ (Vminus c b).
  Proof.
  Admitted.

  Lemma inj_neg_plus_plus : forall sz a b c,
    ^~(inj sz a) ^+ b ^+ inj _ c = b ^+ inj _ c ^- inj _ a.
  Proof.
  Admitted.

  Theorem inj_plus_x_plus : forall sz (a : word sz) b c,
    inj _ b ^+ a ^+ inj _ c = a ^+ inj _ (Vplus c b).
  Proof.
  Admitted.

  Theorem inj_plus_x_minus_gt : forall sz (a : word sz) b c,
    Vle c b ->
    inj _ b ^+ a ^- inj _ c = a ^+ inj _ (Vminus b c).
  Proof.
  Admitted.

  Theorem inj_plus_x_minus_lt : forall sz (a : word sz) b c,
    Vlt b c ->
    inj _ b ^+ a ^- inj _ c = a ^- inj _ (Vminus c b).
  Proof.
  Admitted.

End WordViewFacts.

Lemma wzero_plus_l : forall (sz : wsize) a, wzero sz ^+ a = a.
Proof.
  intros. destruct (wring sz). auto.
Admitted.

Lemma wzero_plus_r : forall (sz : wsize) a, a ^+ wzero sz = a.
Proof.
  intros. destruct (wring sz). unfold wplus. rewrite Radd_comm. auto.
Qed.

Transparent natToWord.

Lemma wneg_wzero_wzero : forall (sz : wsize), 
  wneg (wzero sz) = wzero sz.
Proof.
Admitted.
  
Lemma wzero_minus_r : forall (sz : wsize) a, a ^- wzero sz = a.
Proof.
  intros. unfold wminus, Word.wminus.
  Admitted.

Lemma sext_wzero : forall sz sz', sext (wzero sz') sz = wzero sz.
Proof.
Admitted.

Lemma wneg_plus : forall sz (a b : word sz),
    ^~ a ^+ b = b ^- a.
Proof.
  intros; apply BitView.wneg_plus.
Admitted.

Require Import Omega.

Ltac inj_solver := simpl Vlt; simpl Vle; simpl Veq; (omega || zify; omega).

Ltac post_reduce := simpl plus; simpl minus; simpl Nplus; simpl Nminus.
Ltac post_reduce_in_star := simpl plus in *; simpl minus in *; simpl Nplus in *; simpl Nminus in *.
Ltac post_reduce_in H := simpl plus in H; simpl minus in H; simpl Nplus in H; simpl Nminus in H.

Hint Rewrite @winj_plus : word_simpl.
Hint Rewrite @winj_minus @winj_minus_neg using inj_solver : word_simpl.

Hint Rewrite inj_neg_plus_plus : word_simpl.
Hint Rewrite inj_plus_plus inj_minus_minus : word_simpl. 
Hint Rewrite inj_plus_minus_gt inj_plus_minus_lt using inj_solver : word_simpl.
Hint Rewrite inj_minus_plus_lt inj_minus_plus_gt using inj_solver : word_simpl.

Hint Rewrite wzero_plus_l wzero_plus_r wzero_minus_r sext_wzero : word_simpl.
Hint Rewrite @sbound_ext using (reflexivity || inj_solver) : word_simpl.
Hint Rewrite @sext_neg using (reflexivity || inj_solver) : word_simpl.

Hint Rewrite inj_plus_x_plus inj_plus_x_minus_gt inj_plus_x_minus_lt using inj_solver : word_canon.
Hint Rewrite wplus_assoc wneg_plus : word_canon.
Hint Rewrite @inj_ext : word_canon.
Hint Rewrite @ext_inj using eauto : word_canon.

Lemma wminus_inv : forall sz (x : word sz), x ^+ ^~ x = wzero sz.
Proof. intros; eapply wminus_inv. Qed.

Lemma word_solve_plus : forall sz (a b c : word sz),
  a = c ^- b -> a ^+ b = c.
Proof. 
  intros. subst. rewrite wminus_def. rewrite <- wplus_assoc.
  rewrite (wplus_comm _ b). rewrite wminus_inv. rewrite wplus_comm. rewrite wzero_plus_l.
  reflexivity.
Qed.

(** N **)
Require Import NArith.

Definition NToWord (sz : wsize) (n : N) : word sz :=
  NToWord sz n.
Definition wordToN (sz : wsize) (w : word sz) : N :=
  wordToN w.
Global Instance WordView_N : WordView N :=
{ inj := NToWord
; ext := wordToN
; Vsbound := fun sz n => ((Npow2 (sz - 1)) ?= n = Gt)%N
; Vbound := fun sz n => ((Npow2 sz) ?= n = Gt)%N
; Vplus := Nplus
; Vminus := Nminus
; Vlt := Nlt
; Vle := Nle
; Veq := @eq N
(*; Vle_lt_eq := N_le_lt_eq  *)
(*; winj_plus := NToWord_plus *)
(*; winj_minus := NToWord_minus *)
(*; inj_minus_neg := NToWord_minus_neg *)
(*; sbound_ext := sbound_ext_N *)
(*; sext_neg := sext_neg_N *)
(*; inj_ext := inj_ext_N *)
(*; ext_inj := ext_inj_N *)
}.
admit. admit. admit. admit. admit. admit. admit. admit.
Defined.

(** nat **)
Definition natToWord (sz : wsize) (n : nat) : word sz := natToWord sz n.
Definition wordToNat (sz : wsize) (w : word sz) : nat := wordToNat w.
Global Instance WordView_nat : WordView nat :=
{ inj := natToWord
; ext := wordToNat
; Vsbound := fun sz n => ((Npow2 (sz - 1)) ?= (N_of_nat n) = Gt)%N
; Vbound := fun sz (n : nat) => ((Npow2 sz) ?= (N_of_nat n) = Gt)%N
; Vplus := plus
; Vminus := minus
; Vlt := lt
; Vle := le
; Veq := @eq nat
(*; Vle_lt_eq := nat_le_lt_eq 
; winj_plus := natToWord_plus
; winj_minus := natToWord_minus
; inj_minus_neg := natToWord_minus_neg
; sbound_ext := natToWord_sext_sbound
; sext_neg := sext_neg_nat
; inj_ext := natToWord_wordToNat
; ext_inj := ext_inj_nat
*)
}.
admit. admit. admit. admit. admit. admit. admit. admit.
Defined. 

(* nat hacks *)
Theorem Vbound_le : forall sz (n m : nat),
  Vbound sz n -> (m <= n)%nat -> Vbound sz m.
Proof.
  simpl. intros. 
  change ((Npow2 sz ?= N_of_nat n)%N = Gt) with (Ngt (Npow2 sz) (N_of_nat n)) in H.
  change ((Npow2 sz ?= N_of_nat m)%N = Gt) with (Ngt (Npow2 sz) (N_of_nat m)).
  zify. omega.
Qed.

Lemma wone_inj : forall sz, wone sz = inj sz 1.
Proof. unfold wone, inj, Word.wone. simpl. auto. Qed.
Hint Rewrite wone_inj : word_simpl.

Hint Resolve Vbound_le.

(** Begin Tactics **)
Require Import ExtTactics.

Ltac word_simpl_in H :=
  let pre := hide_evars_in H;
             try (change (NToWord) with (@inj _ WordView_N) in H);
             try (change (natToWord) with (@inj _ WordView_nat) in H) in
  let post := (simpl plus in H; simpl minus in H;
               simpl Nplus in H; simpl Nminus in H) in
  pre;
  repeat progress (autorewrite with word_simpl in H; 
                   autorewrite with word_canon in H;
                   simpl Vplus in H; simpl Vminus in H); restore_evars.

Ltac word_simpl :=
  let pre := hide_evars;
             try (change (NToWord) with (@inj _ WordView_N));
             try (change (natToWord) with (@inj _ WordView_nat)) in
  let post := (simpl plus; simpl minus;
               simpl Nplus; simpl Nminus) in
  pre;
  repeat progress (autorewrite with word_simpl;
                   autorewrite with word_canon;
                   simpl Vplus; simpl Vminus; post); restore_evars.

Ltac word_simpl_in_star :=
  let pre := hide_evars;
             try (change (NToWord) with (@inj _ WordView_N) in * );
             try (change (natToWord) with (@inj _ WordView_nat) in * ) in
  let post := (simpl plus in *; simpl minus in *; 
               simpl Nplus in *; simpl Nminus in * ) in
  pre;
  repeat progress (autorewrite with word_simpl in *;
                   autorewrite with word_canon in *;
                   simpl Vplus in *; simpl Vminus in *; post); restore_evars.
(** End Tactics **)

Notation "## n" := (@inj _ _ _ n) (at level 0).
Notation "#! s n" := (@inj _ _ s n) (at level 0).

(*
Goal forall sz (a : word sz),
  a ^+ ##4 ^- ##8 ^+ ##16 ^- ##32 ^+ ##20 ^- ##64 = ##64 ^+ a ^- ##128.
intros. word_simpl. reflexivity.
*)
End Words.