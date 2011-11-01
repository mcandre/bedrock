Require Import Bedrock.
Require Import Sep.
Require Import WordView.
Import Sep.

Set Implicit Arguments.
Set Strict Implicit.

Opaque Word.split1 Word.split2 Word.combine Word.natToWord Word.NToWord.

Notation "'#n' x" := (@inj _ WordView_nat _ x) (at level 0).

Ltac word_simpl' := 
  change (natToWord) with (@inj _ WordView_nat) in *;
    word_simpl_in_star.

(** Combining words with readWord' **)
Lemma readWord'16 : forall a b p (c d : SepArg.word W8),
  readWord' a p c ->
  readWord' b (p ^+ #n 1) d ->
  a (p ^+ #n 1) = None ->
  readWord' (join a b) p ((combine8 c d):SepArg.word W16).
Proof.
  unfold readWord', combine8. inversion 1. inversion 1. subst; simpl in *.
  repeat econstructor; simpl; unfold join. rewrite Word.split1_combine. rewrite H2. auto.
  unfold wone in H0. simpl in *. rewrite H0. rewrite Word.split2_combine. auto.
Qed.

Lemma readWord'32 : forall a b p (c d : SepArg.word W16),
  readWord' a p c ->
  readWord' b (p ^+ #n 2) d ->
  a (p ^+ #n 2) = None ->
  a (p ^+ #n 3) = None ->
  readWord' (join a b) p ((combine16 c d):SepArg.word W32).
Proof.
(*
  unfold readWord'; intros;
    repeat match goal with
             | [ H : Forall _ _ |- _ ] => inversion H; [ clear H; try subst ]
           end; simpl in *.
  word_simpl'.
  repeat rewrite <- wplus_assoc in *; unfold wone,wplus,wordBin in *; simpl in *.
  repeat econstructor; simpl; unfold join;
    repeat match goal with
             | [ H : _ |- _ ] => rewrite H
             | [ H : _ |- _ ] => rewrite split1_combine
             | [ H : _ |- _ ] => rewrite split2_combine
           end; try reflexivity.
Qed.
*)
Admitted. (** TOO LONG **)

Lemma readWord'64 : forall a b p (c d : SepArg.word W32),
  readWord' a p c ->
  readWord' b (p ^+ #n 4) d ->
  a (p ^+ #n 4) = None ->
  a (p ^+ #n 5) = None ->
  a (p ^+ #n 6) = None ->
  a (p ^+ #n 7) = None ->
  readWord' (join a b) p ((combine32 c d):SepArg.word W64).
Proof.
(*
  unfold readWord'; intros;
    repeat match goal with
             | [ H : Forall _ _ |- _ ] => inversion H; [ clear H; try subst ]
           end; simpl in *.
  word_simpl';
  repeat rewrite <- wplus_assoc in *; unfold wone,wplus,wordBin in *; simpl in *.
  repeat econstructor; simpl; unfold join;
    repeat match goal with
             | [ H : _ |- _ ] => rewrite H
             | [ H : _ |- _ ] => rewrite split1_combine
             | [ H : _ |- _ ] => rewrite split2_combine
           end; try reflexivity.
Qed.
*)
Admitted. (** TOO LONG **)

(** **)
Section Combine_himp.
  Lemma join_None : forall a b p,
    a p = None ->
    b p = None ->
    join a b p = None.
  Proof. unfold join. intros. rewrite H. auto. Qed.

  Hint Resolve split_join.
  Lemma O_neq_q : forall a (q : SepArg.addr),
    a = a ^+ q ->
    wzero _ <> q ->
    False.
  Proof.
    intros. apply H0. clear H0. unfold SepArg.addr in *. simpl in *. 
    assert (a ^- a = a ^+ q ^- a) by congruence.
    unfold wminus in *.
    rewrite Word.wminus_def in H0. rewrite Word.wminus_inv in H0. 
    unfold Word.wminus in *. rewrite Word.wplus_comm in H0. unfold wplus in *. 
    rewrite Word.wplus_assoc in H0. rewrite (Word.wplus_comm _ a) in H0. 
    rewrite Word.wminus_inv in H0. rewrite Word.wplus_unit in H0. auto.
  Qed.
  Lemma p_neq_q : forall a (p q : SepArg.addr),
    a ^+ p = a ^+ q ->
    p <> q ->
    False.
  Proof.
    intros. apply H0. unfold SepArg.addr, word in *. simpl. clear H0.
    assert (^~ a ^+ (a ^+ p) = ^~ a ^+ (a ^+ q)) by congruence.
    unfold wplus, wminus, wneg in *.
    repeat rewrite Word.wplus_assoc in H0. repeat rewrite (Word.wplus_comm _ a) in H0.
    repeat rewrite Word.wminus_inv in H0. repeat rewrite Word.wplus_unit in H0. auto.
  Qed.
  Ltac solve_notin :=
    let r_solver := idtac;
      match goal with
        | [ H : _ = _ |- _ ] => 
          (eapply (p_neq_q _ H) || eapply (O_neq_q H)); discriminate
      end
    in
      (repeat eapply join_None); try match goal with 
                                       | [ H : _ |- _ ] => 
                                         apply H; simpl; clear; intuition r_solver
                                     end.
  Ltac dive :=
    unfold himp, ptsTo; rewrite stars_def; simpl; unfold star; intros;
      word_simpl';
      repeat (match goal with 
                | [ H : exists x, _ |- _ ] => destruct H
                | [ |- _ ] => intuition idtac
              end);
      match goal with
        | [ H : readWord' ?M1 ?P ?L , H' : readWord' ?M2 (?P ^+ _) ?V2 |- _ ] =>
          cut (readWord' (join M1 M2) P ((combine8 L V2) : SepArg.word W16)); [ clear H H' | 
            abstract (eapply (@readWord'16 _ _ _ _ _ H H'); solve_notin) ]
        | [ H : readWord' ?M1 ?P ?L , H' : readWord' ?M2 (?P ^+ _ ) ?V2 |- _ ] =>
          cut (readWord' (join M1 M2) P ((combine16 L V2) : SepArg.word W32)); [ clear H H' | 
            abstract (eapply (@readWord'32 _ _ _ _ _ H H'); solve_notin) ]
        | [ H : readWord' ?M1 ?P ?L , H' : readWord' ?M2 (?P ^+ _) ?V2 |- _ ] =>
          cut (readWord' (join M1 M2) P ((combine32 L V2) : SepArg.word W64)); [ clear H H' | 
            abstract (eapply (@readWord'64 _ _ _ _ _ H H'); solve_notin) ]
      end;
      eexists; eexists; split; [ | split; [ split; [ eassumption | ] | eassumption ] ]; eauto;
        intros; unfold join;
          abstract (repeat match goal with
                             | [ H : SepArg.addr , H' : _ |- _ ] => specialize (H' H)
                             | [ |- match ?X with 
                                      | Some _ => _
                                      | None => _ 
                                    end = _ ] => destruct X
                             | [ H : _ |- _ ] => eapply H; intuition eauto
                           end).

  Open Local Scope Sep_scope.

  Ltac split_solver :=
    unfold wone in *; simpl in *;
      unfold split, disjoint; split; [ do 2 intro | intro ];
        repeat match goal with
                 | [ H : forall x, ?X x = _ |- _ ] => rewrite H
                 | [ H : _ = _ |- _ ] => rewrite H
                 | [ |- context [ weq ?A ?B ] ] => destruct (weq A B); try subst
                 | [ H : ?X ^+ _ = ?X |- _ ] => symmetry in H; eapply O_neq_q in H; try solve [ inversion H ]
                 | [ H : ?X ^+ _ = ?X ^+ _ |- _ ] => eapply p_neq_q in H; try solve [ inversion H ]
                 | [ |- match ?X with
                          | Some _ => _
                          | None => _
                        end = _ ] => case_eq X; intros
               end; (reflexivity || congruence || discriminate || auto).
  Ltac readWord'_solver :=
    repeat econstructor; simpl; intros;
      repeat match goal with
               | [ H : forall x, ?X x = _ |- _ ] => rewrite H
               | [ H : _ = _ |- _ ] => rewrite H
               | [ |- context [ weq ?A ?B ] ] => destruct (weq A B); try subst
               | [ H : ?X ^+ _ = ?X |- _ ] => symmetry in H; eapply O_neq_q in H; try solve [ inversion H ]
               | [ |- match ?X with
                        | Some _ => _
                        | None => _
                      end = _ ] => case_eq X; intros
             end; (reflexivity || congruence || discriminate || tauto || auto).

  Theorem combine_88_16 : forall (p : word W64) (x y : SepArg.word W8),
    ptsTo p x :: ptsTo (p ^+ wone W64) y :: nil --->
    ptsTo p ((combine8 x y) : SepArg.word W16) :: nil.
  Proof.
    intros; dive.
  Qed.

  Ltac fix_wones :=
    change (Word.wone 8) with (wone W8) in *;
    change (Word.wone 16) with (wone W16) in *;
    change (Word.wone 32) with (wone W32) in *;
    change (Word.wone 64) with (wone W64) in *;
    change (natToWord W8 1) with (wone W8) in *;
    change (natToWord W16 1) with (wone W16) in *;
    change (natToWord W32 1) with (wone W32) in *;
    change (natToWord W64 1) with (wone W64) in *.

  Theorem split_16_88 : forall (p : word W64) (x : SepArg.word W16),
    ptsTo p x :: nil --->
    @ptsTo p W8 (Word.split1 8 8 x) :: @ptsTo (p ^+ wone W64) W8 (Word.split2 8 8 x) :: nil.
  Proof.
    unfold himp, ptsTo; rewrite stars_def; simpl; unfold star; intros.
    word_simpl';
      repeat (match goal with
                | [ H : exists x, _ |- _ ] => destruct H
                | [ |- _ ] => intuition idtac
              end).
    exists (fun p' => if weq p p' then Some (Word.split1 8 8 x) else None).
    exists (fun p' => if weq (p ^+ wone _) p' then Some (Word.split2 8 8 x) else None).
    split. 2: split. 3: exists (fun p' => if weq (p ^+ wone _) p' then Some (Word.split2 8 8 x) else None).
    3: exists (fun _ => None).
    unfold split,readWord',disjoint,pure in * |-; intuition;
      repeat match goal with
               | [ H : Forall _ _ |- _ ] => inversion H; [ clear H; try subst ]
               | [ H : forall x, _ = _ |- _ ] => rewrite H in *
               | [ H : _ /\ _ |- _ ] => destruct H
               | _ => rewrite Word.split1_combine in * || rewrite Word.split2_combine in *
               | _ => progress (simpl in * )
           end; simpl in *.
    Focus.
    fix_wones. split_solver. rewrite <- H1. eapply H3; tauto.
    fix_wones. word_simpl_in_star.
    readWord'_solver. fix_wones. split; [ split_solver | readWord'_solver ].
  Qed.

  Require Import NArith. 
  Lemma eight_lt_pow2_64 : (8 < Word.pow2 64)%nat.
  Proof.
    assert (8 < Word.Npow2 64)%N. simpl. repeat constructor.
    generalize (N_of_nat_compare 8 (nat_of_N (Word.Npow2 64))). intros. unfold Nlt in *.
    rewrite N_of_nat_of_N in *. simpl N_of_nat in *. rewrite H in H0.
    apply Compare_dec.nat_compare_lt in H0. rewrite Word.Npow2_nat in *. auto.
  Qed.

  Lemma small_words : forall n , 
    (n < 8)%nat ->
    inj  _ (S n) <> wzero W64.
  Proof. 
    intros. intro. unfold wzero, inj in *. simpl in *.
    assert (wordToNat (natToWord W64 (S n)) = wordToNat (natToWord W64 0)). abstract( rewrite H0; auto).
    edestruct (Word.wordToNat_natToWord 64 (S n)). unfold natToWord, wordToNat in *.
    simpl x86WordSizes.wsize_size in H1. rewrite H1 in H2. destruct H2.
    cut (x = 0).  intros; subst. simpl mult in *. simpl in *. discriminate.
    generalize eight_lt_pow2_64. intros. generalize dependent (Word.pow2 64). intros.

    destruct x. auto. exfalso. clear H2 H1 H0.
    rewrite Mult.mult_succ_l in H3. 
    generalize dependent (x * n0)%nat. intros.  omega.
  Qed.

  Lemma small_words' : forall p n m, 
    p ^+ inj W64 n = p ^+ inj _ m ->
    n <> m ->
    (n < 8)%nat ->
    (m < 8)%nat ->
    False.
  Proof.
    intros. eapply p_neq_q; eauto. intro. apply H0. clear H H0.
    assert (wordToNat (natToWord W64 n) = wordToNat (natToWord W64 m)). unfold inj in H3.
    simpl in H3. rewrite H3; reflexivity.
    unfold wordToNat in H; unfold natToWord in H.
    edestruct Word.wordToNat_natToWord. destruct H0. rewrite H0 in H.
    edestruct Word.wordToNat_natToWord. destruct H5. rewrite H5 in H.

    generalize eight_lt_pow2_64; intro.
    
    assert (x = 0). destruct x. auto. exfalso. simpl x86WordSizes.wsize_size in *. generalize H7; generalize H4; generalize H1; clear; generalize (Word.pow2 64); intros.
    rewrite Mult.mult_succ_l in H4. generalize dependent (x * n0)%nat.  intros. omega.

    assert (x0 = 0). destruct x0. auto. exfalso. simpl x86WordSizes.wsize_size in *. generalize H7; generalize H6; generalize H2; clear; generalize (Word.pow2 64); intros.
    rewrite Mult.mult_succ_l in H6. generalize dependent (x0 * n)%nat.  intros. omega.
    subst. repeat rewrite Mult.mult_0_l in *. omega.
  Qed.
  Hint Extern 1 (False) => eapply p_neq_q; [ eassumption | congruence ].
  Hint Extern 1 (False) => eapply small_words'; [ eassumption | omega | omega | omega ].
  Hint Extern 1 (Some _ = Some _) => exfalso;
    eapply O_neq_q; [ eassumption | intro; discriminate ].
  Hint Extern 1 (natToWord _ _ <> wzero _) => eapply small_words; clear; omega.
  Hint Extern 1 (Some _ = Some _) => exfalso;
    eapply O_neq_q; [ eassumption | intro; eapply small_words; clear; omega ].



  Theorem split_32_1616 : forall (p : word W64) (x : SepArg.word W32),
    ptsTo p x :: nil --->
    @ptsTo p W16 (Word.split1 16 16 x) :: @ptsTo (p ^+ inj _ 2) W16 (Word.split2 16 16 x) :: nil.
  Proof.
(*
    unfold himp, ptsTo; rewrite stars_def; simpl; unfold star; intros.
      repeat (match goal with
                | [ H : exists x, _ |- _ ] => destruct H
                | [ |- _ ] => intuition idtac
              end).
    exists (fun p' => if weq p p' then Some (split1 8 8 (split1 16 16 x)) else 
                      if weq (p ^+ natToWord _ 1) p' then Some (split2 8 8 (split1 16 16 x))
                      else None).
    exists (fun p' => if weq (p ^+ natToWord _ 2) p' then Some (split1 8 8 (split2 16 16 x)) else
                      if weq (p ^+ natToWord _ 3) p' then Some (split2 8 8 (split2 16 16 x))
                      else None).
      unfold split,readWord',disjoint,pure in * |-; intuition;
      repeat match goal with
               | [ H : Forall _ _ |- _ ] => inversion H; [ clear H; try subst ]
               | [ H : forall x, _ = _ |- _ ] => rewrite H in *
               | [ H : _ /\ _ |- _ ] => destruct H
               | _ => rewrite split1_combine in * || rewrite split2_combine in *
               | _ => progress (simpl in * )
           end; simpl in *.
    abstract (split_solver; rewrite <- H1; eapply H3; tauto).
    abstract readWord'_solver.
    abstract readWord'_solver.
    exists (fun p' => if weq (p ^+ natToWord _ 2) p' then Some (split1 8 8 (split2 16 16 x)) else 
                      if weq (p ^+ natToWord _ 3) p' then Some (split2 8 8 (split2 16 16 x))
                      else None).
    exists (fun p' => None).
    repeat econstructor. intros. simpl. abstract readWord'_solver. simpl. abstract readWord'_solver.
    abstract (readWord'_solver; word_simpl'; exfalso; eapply n0; reflexivity).
    abstract (word_simpl'; readWord'_solver).
  Qed.
*)
  Admitted. (** TOO LONG **)

  Theorem  split_64_3232 : forall (p : word W64) (x : SepArg.word W64),
    ptsTo p x :: nil --->
    @ptsTo p W32 (Word.split1 32 32 x) :: @ptsTo (p ^+ inj _ 4) W32 (Word.split2 32 32 x) :: nil.
  Proof.
(*
    unfold himp, ptsTo; rewrite stars_def; simpl; unfold star; intros.
    repeat (match goal with
              | [ H : exists x, _ |- _ ] => destruct H
              | [ |- _ ] => intuition idtac
            end).
    exists (fun p' => if weq p p'                    then Some (split1 8 8 (split1 16 16 (split1 32 32 x))) else 
                      if weq (p ^+ natToWord _ 1) p' then Some (split2 8 8 (split1 16 16 (split1 32 32 x))) else
                      if weq (p ^+ natToWord _ 2) p' then Some (split1 8 8 (split2 16 16 (split1 32 32 x))) else
                      if weq (p ^+ natToWord _ 3) p' then Some (split2 8 8 (split2 16 16 (split1 32 32 x)))
                      else None).
    exists (fun p' => if weq (p ^+ natToWord _ 4) p' then Some (split1 8 8 (split1 16 16 (split2 32 32 x))) else
                      if weq (p ^+ natToWord _ 5) p' then Some (split2 8 8 (split1 16 16 (split2 32 32 x))) else
                      if weq (p ^+ natToWord _ 6) p' then Some (split1 8 8 (split2 16 16 (split2 32 32 x))) else
                      if weq (p ^+ natToWord _ 7) p' then Some (split2 8 8 (split2 16 16 (split2 32 32 x)))
                      else None).
    unfold split,readWord',disjoint,pure in * |-; intuition;
      repeat match goal with
               | [ H : Forall _ _ |- _ ] => inversion H; [ clear H; try subst ]
               | [ H : forall x, _ = _ |- _ ] => rewrite H in *
               | [ H : _ /\ _ |- _ ] => destruct H
               | _ => rewrite split1_combine in * || rewrite split2_combine in *
               | _ => progress (simpl in * )
           end; simpl in *.
    abstract (split_solver; rewrite <- H1; eapply H3; tauto).
    abstract (readWord'_solver; exfalso; eauto).
    abstract (readWord'_solver; exfalso; eauto).
    exists (fun p' => if weq (p ^+ natToWord _ 4) p' then Some (split1 8 8 (split1 16 16 (split2 32 32 x))) else
                      if weq (p ^+ natToWord _ 5) p' then Some (split2 8 8 (split1 16 16 (split2 32 32 x))) else
                      if weq (p ^+ natToWord _ 6) p' then Some (split1 8 8 (split2 16 16 (split2 32 32 x))) else
                      if weq (p ^+ natToWord _ 7) p' then Some (split2 8 8 (split2 16 16 (split2 32 32 x)))
                      else None).
    exists (fun _ => None).
    repeat econstructor. intros. simpl. abstract readWord'_solver. simpl. abstract readWord'_solver.
    abstract (word_simpl'; readWord'_solver; exfalso; eauto).
    abstract (word_simpl'; readWord'_solver; exfalso; eauto).
    abstract (word_simpl'; readWord'_solver; exfalso; eauto).
    word_simpl'; readWord'_solver.
  Qed.
**)
  Admitted. (** TOO LONG **)

  Theorem combine_1616_32 : forall (p : word W64) (x y : SepArg.word W16),
    ptsTo p x :: ptsTo (p ^+ inj _ 2) y :: nil --->
    ptsTo p ((combine16 x y) : SepArg.word W32) :: nil.
  Proof.
(**
    intros; dive.
  Qed.
**)
  Admitted. (** TOO LONG **)

  Theorem combine_3232_64 : forall (p : word W64) (x y : SepArg.word W32),
    ptsTo p x :: ptsTo (p ^+ inj _ 4) y :: nil --->
    ptsTo p ((combine32 x y) : SepArg.word W64) :: nil.
  Proof.
(**
    intros; dive.
  Qed.
**)
  Admitted. (** TOO LONG **)

End Combine_himp.
