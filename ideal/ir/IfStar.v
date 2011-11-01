Require Import Bool Mir.
Import Mir.SP.

Set Implicit Arguments.


Inductive test : Type :=
| TCond : SPArg.cond -> test
| TNot : test -> test
| TAnd : test -> test -> test
| TOr : test -> test -> test.

Fixpoint evalTest (t : test) (st : state) : option bool :=
  match t with
    | TCond c => match evalExp (SPArg.CondOp1 c) st, evalExp (SPArg.CondOp2 c) st with
                   | Some v1, Some v2 => Some (evalRel (SPArg.CondRel c) v1 v2)
                   | _, _ => None
                 end
    | TNot t => match evalTest t st with
                  | Some b => Some (negb b)
                  | _ => None
                end
    | TAnd t1 t2 => match evalTest t1 st with
                      | Some true => evalTest t2 st
                      | Some false => Some false
                      | None => None
                    end
    | TOr t1 t2 => match evalTest t1 st with
                     | Some true => Some true
                     | Some false => evalTest t2 st
                     | None => None
                   end
  end.

Fixpoint labelsOf (t : test) : Type :=
  match t with
    | TCond _ => unit
    | TNot t1 => labelsOf t1
    | TAnd t1 t2 => labelsOf t1 + labelsOf t2
    | TOr t1 t2 => labelsOf t1 + labelsOf t2
  end%type.

Fixpoint entryOf (t : test) : labelsOf t :=
  match t with
    | TCond _ => tt
    | TNot t1 => entryOf t1
    | TAnd t1 t2 => inl _ (entryOf t1)
    | TOr t1 t2 => inl _ (entryOf t1)
  end.

Fixpoint localsOf (t : test) (pre : spec) T (tru fals : T) : (labelsOf t -> T) -> list (local pc state code T) :=
  match t return (labelsOf t -> T) -> _ with
    | TCond b => fun inj => Loc (inj tt) pre (fun lo => SPArg.conditionalJump b (lo (Local tru)) (lo (Local fals))) :: nil
    | TNot t => localsOf t pre fals tru
    | TAnd t1 t2 => fun inj => localsOf t1 pre (inj (inr _ (entryOf t2))) fals (fun x => inj (inl _ x))
      ++ localsOf t2 (st ~> pre st /\ [< evalTest t1 st = Some true >]) tru fals (fun x => inj (inr _ x))
    | TOr t1 t2 => fun inj => localsOf t1 pre tru (inj (inr _ (entryOf t2))) (fun x => inj (inl _ x))
      ++ localsOf t2 (st ~> pre st /\ [< evalTest t1 st = Some false >]) tru fals (fun x => inj (inr _ x))
  end.

Lemma Imply_refl : forall pc state specs (p : PropX pc state),
  interp specs (p --> p).
  intros; apply Imply_I; apply Env; simpl; auto.
Qed.

Local Hint Immediate Imply_refl.

Local Hint Resolve in_or_app.

Theorem localsOf_entry : forall t pre T (tru fals : T) inj,
  exists p, exists cd, In (Loc (inj (entryOf t)) p cd) (localsOf t pre tru fals inj)
    /\ (forall specs st, interp specs (pre st --> p st)).
  induction t; simpl; fold labelsOf; intuition;
    repeat match goal with
             | [ H : context[localsOf ?t _ _ _ _] |- context[localsOf ?t ?pre ?tru ?fals ?inj] ] =>
               destruct (H pre _ tru fals inj) as [? [ ? [ ] ] ]; clear H
           end; eauto 6.
Qed.

Theorem localsOf_Inject : forall t pre T (tru fals : T) inj,
  AllS (fun L => exists x, LLabel L = inj x) (localsOf t pre tru fals inj).
  induction t; simpl; fold labelsOf; intuition; repeat (constructor || apply AllS_app); simpl; eauto;
    (eapply AllS_weaken; [ eauto | cbv beta; firstorder ]).
Qed.

Local Hint Extern 1 (_ = _) =>
  match goal with
    | [ H : forall x y, _ -> x = y, H1 : _ = _ |- _ ] => cbv beta in H1; apply H in H1; congruence
  end.

Theorem localsOf_NoDups : forall t pre T (tru fals : T) inj l1 l2,
  In l1 (localsOf t pre tru fals inj)
  -> In l2 (localsOf t pre tru fals inj)
  -> LLabel l1 = LLabel l2
  -> (forall x y, inj x = inj y -> x = y)
  -> l1 = l2.
  induction t; simpl; fold labelsOf; intuition; subst;
    repeat match goal with
             | [ H : _ |- _ ] => apply in_app_or in H
           end; intuition; eauto;
    repeat match goal with
             | [ H : In _ (localsOf ?t ?pre ?tru ?fals ?inj) |- _ ] =>
               apply (AllS_In (localsOf_Inject t pre tru fals inj)) in H; destruct H
             | [ H : LLabel _ = LLabel _ |- _ ] => rewrite H in *; clear H
             | [ H1 : ?x = _, H2 : ?x = _ |- _ ] => rewrite H1 in H2; clear H1
           end; eauto.
Qed.

Theorem localsOf_Verified : forall m lo t pre tru fals inj trup trucd falsp falscd,
  (forall specs st, interp specs (pre st --> [< exists b, evalTest t st = Some b >])%PropX)
  -> In (Loc tru trup trucd) (Locals m)
  -> (forall specs st, interp specs (pre st /\ [< evalTest t st = Some true >] --> trup st)%PropX)
  -> In (Loc fals falsp falscd) (Locals m)
  -> (forall specs st, interp specs (pre st /\ [< evalTest t st = Some false >] --> falsp st)%PropX)
  -> incl (localsOf t pre tru fals inj) (Locals m)
  -> injective lo
  -> (forall L1, In L1 (Locals m) -> forall L2, In L2 (Locals m) -> LLabel L1 = LLabel L2 -> L1 = L2)
  -> Forall (fun L => blockOk step SPArg.pc_eq m lo (LSpec L) (LBlock L lo))
  (localsOf t pre tru fals inj).
  induction t; simpl; fold labelsOf; intuition; repeat (constructor || apply AllS_app); simpl; intros;
    repeat match goal with
             | [ H : _, H1 : interp _ _ |- _ ] => destruct (H _ _ H1); clear H
           end.

  Ltac t := repeat match goal with
                     | [ H : step _ _ _ _ |- _ ] => red in H; simpl in H; intuition; subst
                     | [ H : SPArg.resolve _ _ _ |- _ ] => red in H; simpl in H
                     | [ H : Some _ = Some _ |- _ ] => injection H; clear H; intros; subst
                     | [ _ : context[match ?E with Some _ => _ | None => _ end] |- _ ] =>
                       let Heq := fresh "Heq" in case_eq E; [ intros ? Heq | intro Heq ]; rewrite Heq in *; try discriminate
                   end.

  unfold SPArg.conditionalJump, step, SPArg.resolve; simpl.
  generalize (Imply_sound (H _ _) H8); clear H; propxFo.
  t; eauto.
  repeat esplit.
  rewrite Heq.
  rewrite Heq0.
  eauto.

  generalize (Imply_sound (H _ _) H8); clear H; propxFo.
  t.
  case_eq (evalRel (SPArg.CondRel c) w w0); intro Her; repeat esplit; try (eapply local_spec; eauto);
    match goal with
      | [ H : _ |- _ ] => apply (Imply_sound (H _ _)); propxFo; rewrite Heq; rewrite Heq0; congruence
    end.


  eapply IHt; eauto; intuition.
  eapply Imply_trans; eauto.
  propxFo.
  destruct (evalTest t st); eauto.

  eapply Imply_trans; [ | eauto ].
  apply Imply_I; apply And_I.
  eapply And_E1; apply Env; simpl; eauto.
  eapply Inj_E; [ eapply And_E2; apply Env; simpl; eauto | intro; apply Inj_I ].
  rewrite H7; reflexivity.

  eapply Imply_trans; [ | eauto ].
  apply Imply_I; apply And_I.
  eapply And_E1; apply Env; simpl; eauto.
  eapply Inj_E; [ eapply And_E2; apply Env; simpl; eauto | intro; apply Inj_I ].
  rewrite H7; reflexivity.

  
  eapply IHt2; eauto; intuition.

  apply Imply_I.
  apply Imply_E with (Inj (exists b : bool,
    match evalTest t1 st with
      | Some true => evalTest t2 st
      | Some false => Some false
      | None => None
    end = Some b)).
  apply Imply_I.
  eapply Inj_E; eauto; destruct 1.
  eapply Inj_E; [ eapply And_E2; apply Env; simpl; auto | intro ].
  apply Inj_I.
  rewrite H8 in H7.
  destruct (evalTest t2 st); discriminate || eauto.
  eapply Imply_E; eauto.
  eapply And_E1; apply Env; simpl; eauto.
  
  eapply Imply_trans; [ | eauto ].
  apply Imply_I; apply And_I.
  do 2 eapply And_E1; apply Env; simpl; eauto.
  eapply Inj_E; [ eapply And_E2; apply Env; simpl; eauto | intro ].
  eapply Inj_E; [ eapply And_E2; eapply And_E1; apply Env; simpl; eauto | intro ].
  apply Inj_I.
  rewrite H7.
  rewrite H8.
  reflexivity.

  eapply Imply_trans; [ | eauto ].
  apply Imply_I; apply And_I.
  do 2 eapply And_E1; apply Env; simpl; eauto.
  eapply Inj_E; [ eapply And_E2; apply Env; simpl; eauto | intro ].
  eapply Inj_E; [ eapply And_E2; eapply And_E1; apply Env; simpl; eauto | intro ].
  apply Inj_I.
  rewrite H7.
  rewrite H8.
  reflexivity.

  apply incl_app in H4; tauto.


  apply incl_app in H4; intuition.

  match type of H8 with
    | context[localsOf ?t ?pre ?tru ?fals ?inj] =>
      destruct (localsOf_entry t pre tru fals inj) as [ ? [ ? [ ] ] ]
  end.
  eapply IHt1; eauto; intuition.

  apply Imply_I.
  apply Imply_E with (Inj (exists b : bool,
    match evalTest t1 st with
      | Some true => evalTest t2 st
      | Some false => Some false
      | None => None
    end = Some b)).
  apply interp_weaken; propxFo.
  destruct (evalTest t1 st); discriminate || eauto.
  eapply Imply_E; eauto.

  eapply Imply_trans; [ | eauto ].
  apply Imply_I; apply And_I.
  eapply And_E1; apply Env; simpl; eauto.
  eapply Inj_E; [ eapply And_E2; apply Env; simpl; eauto | intro ].
  apply Imply_E with (Inj (exists b : bool,
    match evalTest t1 st with
      | Some true => evalTest t2 st
      | Some false => Some false
      | None => None
    end = Some b)).
  apply interp_weaken; propxFo.
  rewrite H10 in *.
  destruct (evalTest t2 st); discriminate || reflexivity.
  eapply Imply_E; eauto.
  eapply And_E1; apply Env; simpl; eauto.


  eapply IHt2; eauto; intuition.

  apply Imply_I.
  apply Imply_E with (Inj (exists b : bool,
    match evalTest t1 st with
      | Some true => Some true
      | Some false => evalTest t2 st
      | None => None
    end = Some b)).
  apply Imply_I.
  eapply Inj_E; eauto; destruct 1.
  eapply Inj_E; [ eapply And_E2; apply Env; simpl; auto | intro ].
  apply Inj_I.
  rewrite H8 in H7.
  destruct (evalTest t2 st); discriminate || eauto.
  eapply Imply_E; eauto.
  eapply And_E1; apply Env; simpl; eauto.
  
  eapply Imply_trans; [ | eauto ].
  apply Imply_I; apply And_I.
  do 2 eapply And_E1; apply Env; simpl; eauto.
  eapply Inj_E; [ eapply And_E2; apply Env; simpl; eauto | intro ].
  eapply Inj_E; [ eapply And_E2; eapply And_E1; apply Env; simpl; eauto | intro ].
  apply Inj_I.
  rewrite H7.
  rewrite H8.
  reflexivity.

  eapply Imply_trans; [ | eauto ].
  apply Imply_I; apply And_I.
  do 2 eapply And_E1; apply Env; simpl; eauto.
  eapply Inj_E; [ eapply And_E2; apply Env; simpl; eauto | intro ].
  eapply Inj_E; [ eapply And_E2; eapply And_E1; apply Env; simpl; eauto | intro ].
  apply Inj_I.
  rewrite H7.
  rewrite H8.
  reflexivity.

  apply incl_app in H4; tauto.


  apply incl_app in H4; intuition.

  match type of H8 with
    | context[localsOf ?t ?pre ?tru ?fals ?inj] =>
      destruct (localsOf_entry t pre tru fals inj) as [ ? [ ? [ ] ] ]
  end.
  eapply IHt1; eauto; intuition.

  apply Imply_I.
  apply Imply_E with (Inj (exists b : bool,
    match evalTest t1 st with
      | Some true => Some true
      | Some false => evalTest t2 st
      | None => None
    end = Some b)).
  apply interp_weaken; propxFo.
  destruct (evalTest t1 st); discriminate || eauto.
  eapply Imply_E; eauto.

  eapply Imply_trans; [ | eauto ].
  apply Imply_I; apply And_I.
  eapply And_E1; apply Env; simpl; eauto.
  eapply Inj_E; [ eapply And_E2; apply Env; simpl; eauto | intro ].
  apply Imply_E with (Inj (exists b : bool,
    match evalTest t1 st with
      | Some true => Some true
      | Some false => evalTest t2 st
      | None => None
    end = Some b)).
  apply interp_weaken; propxFo.
  rewrite H10 in *.
  destruct (evalTest t2 st); discriminate || reflexivity.
  eapply Imply_E; eauto.
  eapply And_E1; apply Env; simpl; eauto.
Qed.

Section IfStar.
  Variables (t : test) (c1 c2 : scode).

  Definition IfStar := let r1 := toStructured c1 in
    let r2 := toStructured c2 in
      SStructured (Scode (ScLabT := option (labelsOf t + (ScLabT r1 + ScLabT r2))) None (fun _ is cin =>
        let iout := is (makeIin cin) in
          let pre1 st := (IoutPostcondition iout st /\ [< evalTest t st = Some true >])%PropX in
            let pre2 st := (IoutPostcondition iout st /\ [< evalTest t st = Some false >])%PropX in
              let cout1 := ScCompile r1 nullInstrs
                (CompIn pre1 (CinExit cin) (fun v => CinInject cin (Some (inr _ (inl _ v))))) in
                let cout2 := ScCompile r2 nullInstrs
                  (CompIn pre2 (CinExit cin) (fun v => CinInject cin (Some (inr _ (inr _ v))))) in
                  CompOut (match CoutPostcondition cout1, CoutPostcondition cout2 with
                             | None, None => None
                             | Some post1, None => Some post1
                             | None, Some post2 => Some post2
                             | Some post1, Some post2 => Some (fun st => post1 st \/ post2 st)%PropX
                           end)
                  (Loc (CinInject cin None) (CinPrecondition cin) (fun lo => (IoutCode iout lo,
                    Jmp (lo (Local (CinInject cin (Some (inl _ (entryOf t))))))))
                    :: localsOf t (IoutPostcondition iout) (CinInject cin (Some (inr _ (inl _ (ScEntry r1)))))
                    (CinInject cin (Some (inr _ (inr _ (ScEntry r2)))))
                    (fun x => CinInject cin (Some (inl _ x)))
                    ++ CoutCode cout1 ++ CoutCode cout2)
                  ((fun lo => (CinPrecondition cin, notStuck iout lo))
                    :: (fun lo => (fun _ => [< True >], fun st => IoutPostcondition iout st --> [<exists b, evalTest t st = Some b>]))%PropX
                  :: CoutConditions cout1 ++ CoutConditions cout2))).

  Variables imports exports : list (string * prop).
  Hypotheses (Hc1 : scodeOk imports exports c1) (Hc2 : scodeOk imports exports c2).

  Theorem IfStarOk : scodeOk imports exports IfStar.
    unfold IfStar.
    generalize (toStructuredOk _ _ _ Hc1).
    generalize (toStructuredOk _ _ _ Hc2).
    generalize (toStructured c1).
    generalize (toStructured c2).
    intros c2' c1' Hc2' Hc1'; simpl in *.

    split; simpl; intros; eauto.

    destruct (localsOf_entry t (IoutPostcondition (is (makeIin cin)))
      (CinInject cin (Some (inr _ (inl _ (ScEntry c1')))))
      (CinInject cin (Some (inr _ (inr _ (ScEntry c2')))))
      (fun x => CinInject cin (Some (inl _ x)))) as [? [? [ ] ] ]; eauto 6.
    repeat (constructor || apply AllS_app); simpl.
    eauto.
    eapply AllS_weaken; [ apply (ScInject Hc2') | ].
    simpl; intuition.
    destruct H2; rewrite H2; eauto.
    eapply AllS_weaken; [ apply (ScInject Hc1') | ].
    simpl; intuition.
    destruct H2; rewrite H2; eauto.
    eapply AllS_weaken.
    apply localsOf_Inject.
    clear; firstorder.

    intuition; subst;
      repeat match goal with
               | [ H : _ |- _ ] => apply in_app_or in H; intuition; simpl in *
             end;
      solve [ eapply localsOf_NoDups; eauto
        | eapply (ScNoDups Hc1'); eauto; simpl; eauto
        | eapply (ScNoDups Hc2'); eauto; simpl; eauto
        | repeat (unfold SPArg.pc, SPArg.state, pc, block, code, SPArg.instr, SPArg.jmp in *;
          match goal with
            | [ H : In _ _ |- _ ] => (destruct (AllS_In (localsOf_Inject _ _ _ _ _) H)
              || destruct (AllS_In (ScInject Hc1' _ _) H)
                || destruct (AllS_In (ScInject Hc2' _ _) H)); clear H; simpl in *
            | [ H : LLabel _ = LLabel _ |- _ ] => rewrite H in *; clear H
            | [ H1 : ?x = _, H2 : ?x = _ |- _ ] => rewrite H1 in H2; clear H1
            | [ H1 : ?x = _, H2 : _ = ?x |- _ ] => rewrite H1 in H2; clear H1
          end); auto ].

    repeat match goal with
             | [ H : AllS _ (_ :: _) |- _ ] => inversion H; clear H; intros; subst
             | [ H : _ |- _ ] => (apply AllS_deapp in H || apply incl_app in H || apply incl_cons in H); intuition
           end; simpl in *.
    
    repeat ((constructor; simpl) || apply AllS_app).

    intuition.
    specialize (H14 _ lo _ H19).
    propxFo.
    repeat esplit; simpl.
    eauto.
    intuition.
    intuition.
    red in H20; simpl in H20; intuition; subst.
    red in H22; simpl in H22; injection H22; clear H22; intros; subst.
    destruct (localsOf_entry t (IoutPostcondition (is (makeIin cin)))
      (CinInject cin (Some (inr _ (inl _ (ScEntry c1')))))
      (CinInject cin (Some (inr _ (inr _ (ScEntry c2')))))
      (fun x => CinInject cin (Some (inl _ x)))) as [? [? [ ] ] ].

    repeat esplit.
    eapply local_spec; eauto.
    repeat match goal with
             | [ H : _ |- _ ] => (apply incl_app in H || apply incl_cons in H); intuition
           end; simpl in *.
    eauto.
    apply (Imply_sound (H22 _ _)).
    eapply H4; eauto.
    eapply imports_in; eauto.
    eapply exports_in; eauto.

    match goal with
      | [ |- context[ScCompile _ ?cin ?is] ] => apply (ScVerified Hc2' m cin is); simpl; intuition; subst; auto
    end.
    eapply AllS_weaken; [ eauto | ].
    simpl; intuition.
    specialize (H19 _ H20); intuition; subst; simpl in *.
    apply H10 in H20; congruence.
    apply in_app_or in H21; intuition.
    destruct (AllS_In (localsOf_Inject _ _ _ _ _) H19); simpl in *.
    unfold SPArg.pc, SPArg.state, pc, block, code, SPArg.instr, SPArg.jmp in *.
    rewrite H20 in H21.
    apply H10 in H21; congruence.
    apply in_app_or in H19; intuition.
    destruct (AllS_In (ScInject Hc1' _ _) H21); simpl in *.
    rewrite H20 in H19.
    apply H10 in H19; congruence.
    match type of H11 with
      | match match ?E with Some _ => _ | None => _ end with Some _ => _ | None => _ end => destruct E
    end;
    match goal with
      | [ |- match ?E with Some _ => _ | None => _ end ] => destruct E
    end; repeat match goal with
                  | [ H : ex _ |- _ ] => destruct H; intuition
                end; eauto.
    repeat esplit; eauto.
    intros.
    specialize (H19 specs st).
    apply Imply_I.
    eapply Imply_E; eauto.
    apply Or_I2; apply Env; simpl; auto.

    match goal with
      | [ |- context[ScCompile _ ?cin ?is] ] => apply (ScVerified Hc1' m cin is); simpl; intuition; subst; auto
    end.
    eapply AllS_weaken; [ eauto | ].
    simpl; intuition.
    specialize (H19 _ H20); intuition; subst; simpl in *.
    apply H10 in H20; congruence.
    apply in_app_or in H21; intuition.
    destruct (AllS_In (localsOf_Inject _ _ _ _ _) H19); simpl in *.
    unfold SPArg.pc, SPArg.state, pc, block, code, SPArg.instr, SPArg.jmp in *.
    rewrite H20 in H21.
    apply H10 in H21; congruence.
    apply in_app_or in H19; intuition.
    destruct (AllS_In (ScInject Hc2' _ _) H21); simpl in *.
    rewrite H20 in H19.
    apply H10 in H19; congruence.
    repeat match type of H11 with
             | match match ?E with Some _ => _ | None => _ end with Some _ => _ | None => _ end => destruct E
           end; repeat match goal with
                         | [ H : ex _ |- _ ] => destruct H; intuition
                       end; eauto.
    repeat esplit; eauto.
    intros.
    specialize (H19 specs st).
    apply Imply_I.
    eapply Imply_E; eauto.
    apply Or_I1; apply Env; simpl; auto.
    repeat match goal with
      | [ H : incl (CoutCode (ScCompile _ ?is ?cin)) _, H' : _, H'' : _ |- _ ] =>
        destruct (ScInclude H' is cin H'') as [ ? [ ? [ ] ] ]; clear H'; simpl in *
    end.
    eapply localsOf_Verified; eauto; intuition.
    apply (H13 _ lo _ (Inj_I _ _ I)).
  Qed.
End IfStar.

Notation "e1 == e2" := (TCond (SPArg.Build_cond' Eq e1 e2)) : test_scope.
Notation "e1 != e2" := (TCond (SPArg.Build_cond' Ne e1 e2)) : test_scope.
Notation "e1 < e2" := (TCond (SPArg.Build_cond' Lt e1 e2)) : test_scope.
Notation "e1 <= e2" := (TCond (SPArg.Build_cond' Le e1 e2)) : test_scope.
Notation "e1 > e2" := (TCond (SPArg.Build_cond' Gt e1 e2)) : test_scope.
Notation "e1 >= e2" := (TCond (SPArg.Build_cond' Ge e1 e2)) : test_scope.

Notation "!" := TNot : test_scope.
Infix "&&" := TAnd : test_scope.
Infix "||" := TOr : test_scope.

Delimit Scope test_scope with test.

Notation "If* c { b1 } 'else' { b2 }" := (fun imp exp => IfStar c%test (b1 imp exp) (b2 imp exp))
  (no associativity, at level 95, c at level 0) : Mir_scope.


Hint Resolve IfStarOk : Structured.


Theorem pull_Some : forall (b : bool) T (v1 v2 : T),
  (if b then Some v1 else Some v2) = Some (if b then v1 else v2).
  destruct b; reflexivity.
Qed.

Hint Extern 1 (_ = _) => reflexivity : sep0.
Hint Extern 1 (_ = Some _) => rewrite pull_Some : sep0.

Global Opaque Compare_dec.leb.

Theorem simplify_and_true : forall (b : bool) v,
  (if b then v else Some false) = Some true
  -> b = true /\ v = Some true.
  destruct b; intuition congruence.
Qed.

Theorem simplify_and_false : forall (b : bool) v,
  (if b then v else Some false) = Some false
  -> b = false \/ v = Some false.
  destruct b; intuition congruence.
Qed.

Theorem simplify_or_true : forall (b : bool) v,
  (if b then Some true else v) = Some true
  -> b = true \/ v = Some true.
  destruct b; intuition congruence.
Qed.

Theorem simplify_or_false : forall (b : bool) v,
  (if b then Some true else v) = Some false
  -> b = false /\ v = Some false.
  destruct b; intuition congruence.
Qed.

Theorem simplify_and_true' : forall (b : bool) v,
  (if b then v else false) = true
  -> b = true /\ v = true.
  destruct b; intuition congruence.
Qed.

Theorem simplify_and_false' : forall (b : bool) v,
  (if b then v else false) = false
  -> b = false \/ v = false.
  destruct b; intuition congruence.
Qed.

Theorem simplify_or_true' : forall (b : bool) v,
  (if b then true else v) = true
  -> b = true \/ v = true.
  destruct b; intuition congruence.
Qed.

Theorem simplify_or_false' : forall (b : bool) v,
  (if b then true else v) = false
  -> b = false /\ v = false.
  destruct b; intuition congruence.
Qed.

Theorem negb_true : forall b, negb b = true -> b = false.
  destruct b; auto.
Qed.

Theorem negb_false : forall b, negb b = false -> b = true.
  destruct b; auto.
Qed.

Ltac ifStarSimp := repeat match goal with
                            | [ H : _ |- _ ] => (rewrite pull_Some in H || apply negb_true in H || apply negb_false in H
                              || apply simplify_and_true in H || apply simplify_or_true in H
                                || apply simplify_and_false in H || apply simplify_or_false in H
                                  || apply simplify_and_true' in H || apply simplify_or_true' in H
                                    || apply simplify_and_false' in H || apply simplify_or_false' in H); intuition
                            | [ H : Some _ = Some _ |- _ ] => injection H; clear H; intros; subst
                          end.

Ltac ifStar := pre; ifStarSimp; sep.
