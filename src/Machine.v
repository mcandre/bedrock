(** Certified machine language packages *)

Require Import PropX.

Set Implicit Arguments.


Section mapping.
  Variables A B : Type.

  Definition mapping := A -> option B.

  Definition mIncl (f1 f2 : mapping) :=
    forall i p, f1 i = Some p -> f2 i = Some p.

  Theorem mIncl_refl : forall f, mIncl f f.
    red; intuition.
  Qed.

  Definition mMerge (f1 f2 : mapping) : mapping := fun x =>
    match f1 x with
      | None => f2 x
      | v => v
    end.

  Definition mAgree (f1 f2 : mapping) :=
    forall x y1 y2, f1 x = Some y1 -> f2 x = Some y2 -> y1 = y2.

  Theorem mMergeIncl1 : forall f1 f2, mIncl f1 (mMerge f1 f2).
    unfold mIncl, mMerge; intuition; destruct (f1 i); auto; discriminate.
  Qed.

  Theorem mMergeIncl2 : forall f1 f2, mAgree f1 f2 -> mIncl f2 (mMerge f1 f2).
    unfold mIncl, mMerge, mAgree; intros ? ? Hag i p ?; specialize (Hag i).
    destruct (f1 i); auto.
    rewrite (Hag _ _ (refl_equal _) H); auto.
  Qed.

  Theorem mIncl_trans : forall f1 f2 f3, mIncl f1 f2
    -> mIncl f2 f3
    -> mIncl f1 f3.
    unfold mIncl; intuition.
  Qed.
End mapping.

Section Machine.
  Variables pc state block : Type.
  Variable step : block -> state -> pc -> state -> Prop.

  Record module := Mod {
    Blocks : mapping pc block;
    Specs : codeSpec pc state
  }.

  Section moduleOk.
    Variable m : module.

    Record moduleOk : Prop := {
      Inclusion : forall i b, Blocks m i = Some b -> exists p, Specs m i = Some p;
      Progress : forall i b p, Blocks m i = Some b -> Specs m i = Some p
        -> forall specs, mIncl (Specs m) specs
          -> forall s, interp specs (p s)
            -> exists i', exists s', step b s i' s';
      Preservation : forall i b p, Blocks m i = Some b -> Specs m i = Some p
        -> forall specs, mIncl (Specs m) specs
          -> forall s, interp specs (p s)
            -> forall i' s', step b s i' s'
              -> exists p', specs i' = Some p' /\ interp specs (p' s')
    }.

    Definition mstep (i : pc) (s : state) (i' : pc) (s' : state) :=
      exists b, Blocks m i = Some b /\ step b s i' s'.

    CoInductive safe (i : pc) (s : state) : Prop :=
    | Safe : forall b p, Blocks m i = Some b
      -> Specs m i = Some p
      -> interp (Specs m) (p s)
      -> (exists i', exists s', step b s i' s')
      -> (forall i' s', step b s i' s' -> safe i' s')
      -> safe i s.

    Hypothesis Hok : moduleOk.
    Hypothesis Hclosed : forall i p, Specs m i = Some p -> exists b, Blocks m i = Some b.

    Theorem safety : forall i p, Specs m i = Some p
      -> forall s, interp (Specs m) (p s)
        -> safe i s.
      cofix; intros.
      destruct (Hclosed _ H) as [b].
      destruct (Progress Hok _ H1 H (mIncl_refl _) _ H0) as [i' [s']].
      econstructor; try eassumption.
      eauto.
      intros.
      destruct (Preservation Hok _ H1 H (mIncl_refl _) H0 H3) as [p' [? ?]]; eauto.
    Qed.
  End moduleOk.

  Section link.
    Variables m1 m2 : module.

    Definition link := Mod (mMerge (Blocks m1) (Blocks m2))
      (mMerge (Specs m1) (Specs m2)).

    Hypothesis m1Ok : moduleOk m1.
    Hypothesis m2Ok : moduleOk m2.

    Hypothesis blocks_agree : mAgree (Blocks m1) (Blocks m2).
    Hypothesis specs_agree : mAgree (Specs m1) (Specs m2).

    Theorem linkOk : moduleOk link.
      split; simpl; intuition.


      unfold mMerge, mAgree in *.
      specialize (blocks_agree i).
      specialize (specs_agree i).
      generalize (Inclusion m1Ok i); intro Hinc1.
      generalize (Inclusion m2Ok i); intro Hinc2.
      destruct (Blocks m1 i).
      destruct (Hinc1 _ (refl_equal _)) as [p]; clear Hinc1.
      rewrite H0; eauto.
      destruct (Hinc2 _ H) as [p]; clear Hinc2.
      destruct (Specs m1 i); eauto.


      unfold mMerge, mAgree in *.
      specialize (blocks_agree i).
      generalize (specs_agree i); intro Hspecs.
      generalize (Inclusion m1Ok i); intro Hinc1.
      generalize (Inclusion m2Ok i); intro Hinc2.
      generalize (Progress m1Ok i); intro Hp1.
      generalize (Progress m2Ok i); intro Hp2.
      destruct (Blocks m1 i).

      eapply Hp1; eauto.
      destruct (Hinc1 _ (refl_equal _)); clear Hinc1.
      destruct (Specs m1 i); auto; discriminate.
      eapply mIncl_trans.
      eapply mMergeIncl1.
      eauto.

      destruct (Hinc2 _ H); clear Hinc2.
      eapply Hp2; eauto.
      eapply mIncl_trans.
      apply mMergeIncl2; eauto.
      eauto.
      destruct (Specs m1 i).
      specialize (Hspecs _ _ (refl_equal _) H3).
      subst.
      injection H0; intro; subst; auto.
      rewrite H0 in H3; injection H3; intro; subst; auto.


      unfold mMerge, mAgree in *.
      specialize (blocks_agree i).
      generalize (specs_agree i); intro Hspecs.
      generalize (Inclusion m1Ok i); intro Hinc1.
      generalize (Inclusion m2Ok i); intro Hinc2.
      generalize (Preservation m1Ok i); intro Hp1.
      generalize (Preservation m2Ok i); intro Hp2.
      destruct (Blocks m1 i).

      eapply Hp1; eauto.
      destruct (Hinc1 _ (refl_equal _)); clear Hinc1.
      destruct (Specs m1 i); auto; discriminate.
      eapply mIncl_trans.
      eapply mMergeIncl1.
      eauto.

      destruct (Hinc2 _ H); clear Hinc2.
      eapply Hp2; eauto.
      eapply mIncl_trans.
      apply mMergeIncl2; eauto.
      eauto.
      destruct (Specs m1 i).
      specialize (Hspecs _ _ (refl_equal _) H4).
      subst.
      injection H0; intro; subst; auto.
      rewrite H0 in H4; injection H4; intro; subst; auto.
    Qed.
  End link.
End Machine.
