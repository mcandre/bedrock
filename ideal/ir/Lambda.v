Require Import Mir.
Import Mir.SP.


Section Lambda.
  Variables (x : var) (pre : spec) (func : scode).

  Definition Lambda := let funcR := toStructured func in
    SStructured (Scode (ScLabT := option (ScLabT funcR)) None (fun _ is cin =>
      let iout := is (makeIin cin) in
        let funcOut := ScCompile funcR nullInstrs
          (CompIn pre (CinInject cin (Some (ScEntry funcR))) (fun v => CinInject cin (Some v))) in
          CompOut (Some (fun st => Ex st', Ex i, [< evalCmd (Assign x (Const i)) st' = Some st >]
            /\ IoutPostcondition iout st'
            /\ ExX, Cptr i (PropX.Var VO) /\ Al st, ^[pre st] --> VO @ st)%PropX)
          (Loc (CinInject cin None) (CinPrecondition cin) (fun lo =>
            (IoutCode iout lo ++ Assign x (Const (lo (Local (CinInject cin (Some (ScEntry funcR)))))) :: nil,
              Jmp (lo (Local (CinExit cin)))))
          :: CoutCode funcOut)
          ((fun lo => (CinPrecondition cin, notStuck iout lo))
            :: (fun lo => (IoutPostcondition iout, fun st => [< exists fr, exists frs, Frames st = fr :: frs >])%PropX)
            :: CoutConditions funcOut))).
            
  Variables imports exports : list (string * prop).
  Hypothesis Hfunc : scodeOk imports exports func.

  Hypothesis no_fallthru : forall T (is : instrs) (cin : compileIn _ T),
    CoutPostcondition (ScCompile (toStructured func) is cin) = None.

  Theorem LambdaOk : scodeOk imports exports Lambda.
    unfold Lambda.
    generalize (toStructuredOk _ _ _ Hfunc).
    generalize dependent no_fallthru.
    generalize (toStructured func).
    intros func' no_fallthru' Hfunc'; simpl in *.

    split; simpl; intros; eauto.

    repeat esplit.
    eauto.
    intros; apply Imply_I; apply Env; simpl; auto.

    repeat (constructor || apply AllS_app); simpl; eauto.

    eapply AllS_weaken ; [ apply (ScInject Hfunc') | ].
    simpl; intuition.
    destruct H0; eauto.

    intuition; repeat match goal with
                        | [ H : _ |- _ ] => apply in_app_or in H; intuition
                      end; subst; simpl in *; auto.
    
    destruct (AllS_In (ScInject Hfunc' _ _) H0).
    simpl in H1.
    rewrite <- H2 in H1.
    apply H in H1; congruence.

    destruct (AllS_In (ScInject Hfunc' _ _) H3).
    simpl in H3.
    rewrite H2 in H0.
    apply H in H0; congruence.

    destruct (AllS_In (ScInject Hfunc' _ _) H3).
    destruct (AllS_In (ScInject Hfunc' _ _) H0).
    simpl in *.
    eapply (ScNoDups Hfunc'); eauto.
    simpl.
    intros.
    apply H in H5; congruence.


    repeat match goal with
             | [ H : AllS _ (_ :: _) |- _ ] => inversion H; clear H; intros; subst
             | [ H : _ |- _ ] => (apply AllS_deapp in H || apply incl_app in H || apply incl_cons in H); intuition
           end; simpl in *.

    repeat (constructor || apply AllS_app); simpl; intros.

    unfold step, SPArg.exec, SPArg.resolve; simpl.
    specialize (H14 _ lo _ H15); propxFo.
    assert (interp specs (IoutPostcondition (is (CinPrecondition cin)) x0)).
    eapply H4; eauto.
    eapply imports_in; eauto.
    eapply exports_in; eauto.
    specialize (H13 _ lo _ H11); propxFo.

    repeat esplit.
    eapply execs_app'; eauto.
    unfold SPArg.exec; simpl.
    rewrite H13; eauto.
    
    red in H17; simpl in H17; intuition.
    apply execs_app in H18; destruct H18; intuition.
    simpl in H20.
    destruct H20.
    unfold SPArg.exec in H17; simpl in H17.
    assert (interp specs (IoutPostcondition (is (CinPrecondition cin)) x0)).
    eapply H4; eauto.
    eapply imports_in; eauto.
    eapply exports_in; eauto.
    specialize (H13 _ lo _ H20); propxFo.
    rewrite H13 in H21.
    injection H21; clear H21; intro; subst.
    unfold SPArg.resolve in H19; simpl in H19.
    injection H19; clear H19; intros; subst.
    repeat esplit; eauto.
    eapply local_spec; eauto.
    apply (Imply_sound (H23 _ _)); simpl.
    destruct (ScInclude Hfunc' _ _ H16) as [ ? [ ? [ ] ] ]; simpl in *.
    propxFo; repeat esplit.
    match goal with
      | [ _ : Frames ?st' = _ :: _ |- match Frames ?st with nil => _ | _ :: _ => _ end = _ ] => equate st st'
    end.
    rewrite H13; eauto.
    apply simplify_fwd; auto.

    autorewrite with PropXF.
    eapply local_spec; eauto.

    intro.
    autorewrite with PropX.
    eauto.

    match goal with
      | [ |- context[ScCompile _ ?cin ?is] ] => apply (ScVerified Hfunc' m cin is); simpl; intuition; subst; auto
    end.
    eapply AllS_weaken; [ eauto | ].
    simpl; intuition.
    specialize (H15 _ H17); intuition; subst; simpl in *.
    apply H10 in H17; congruence.
    apply H10 in H8; congruence.

    rewrite no_fallthru'; constructor.
  Qed.
End Lambda.

Notation "x <-- 'blambda' args [ p ] { b }" :=
  (fun imp exp => Lambda x p ((Preamble;;
    (fun imp exp => fold_right (fun i p' => SP.Seq (SP.StraightLine i) p')
      (b imp exp)
      (getArgs O args%MirImps)))%Mir imp exp))
  (no associativity, at level 90) : Mir_scope.

Hint Resolve LambdaOk : Structured.
