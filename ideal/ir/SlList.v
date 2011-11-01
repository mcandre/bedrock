Require Import Typed Impure.


Notation "^data p" := p (at level 38, only parsing) : Sep_scope.
Notation "^next p" := (p + 1) (at level 38, only parsing) : Sep_scope.

Notation "^data p" := p (only parsing) : Mir_scope.
Notation "^next p" := (p + #1)%Mir (only parsing) : Mir_scope.

Module Type PRIVATE.
  Parameter rep : forall model, (word -> model -> sprop) -> list (word * model) -> word -> sprop.

  Axiom rep_empty_fwd : forall model P ls p, p = 0
    -> rep model P ls p ===> emp.

  Axiom rep_empty_bwd : forall model P ls p, p = 0
    -> [< ls = nil >] ===> rep model P ls p.

  Axiom rep_nonempty_fwd : forall model P ls p, p <> 0
    -> rep model P ls p ===> Ex v, Ex m, Ex ls', Ex p', [< ls = (v, m) :: ls' >] * ^data p ==> v * !{P v m} * ^next p ==> p' * !{rep model P ls' p'}.

  Axiom rep_nonempty_bwd : forall model m P ls p, p <> 0
    -> (Ex v, Ex ls', Ex p', [< ls = (v, m) :: ls' >] * ^data p ==> v * !{P v m} * ^next p ==> p' * !{rep model P ls' p'}) ===> rep model P ls p.
End PRIVATE.

Module Private : PRIVATE.
  Open Scope Sep_scope.

  Fixpoint rep model (P : word -> model -> sprop) (ls : list (word * model)) (p : word) : sprop :=
    match ls with
      | nil => [< p = 0 >]
      | (x, m) :: ls' => Ex p', [< p <> 0 >] * p ==> x * !{P x m} * (p+1) ==> p' * !{rep model P ls' p'}
    end.

  Lemma rep_empty_fwd : forall model P ls p, p = 0
    -> rep model P ls p ===> emp.
    destruct ls; sepLemma.
  Qed.

  Lemma rep_empty_bwd : forall model P ls p, p = 0
    -> [< ls = nil >] ===> rep model P ls p.
    sepLemma.
  Qed.

  Lemma rep_nonempty_fwd : forall model P ls p, p <> 0
    -> rep model P ls p ===> Ex v, Ex m, Ex ls', Ex p', [< ls = (v, m) :: ls' >] * p ==> v * !{P v m} * (p+1) ==> p' * !{rep model P ls' p'}.
    destruct ls; sepLemma.
  Qed.

  Lemma rep_nonempty_bwd : forall model m P ls p, p <> 0
    -> (Ex v, Ex ls', Ex p', [< ls = (v, m) :: ls' >] * p ==> v * !{P v m} * (p+1) ==> p' * !{rep model P ls' p'}) ===> rep model P ls p.
    sepLemma.
  Qed.
End Private.

Import Private.
Export Private.

Implicit Arguments rep [model].

Hint Extern 1 (rep _ _ _ ===> _) => makeDarnSure rep_empty_fwd : Forward.
Hint Extern 1 (_ ===> rep _ _ _) => makeDarnSure rep_empty_bwd : Backward.

Hint Extern 1 (rep _ _ _ ===> _) => makeDarnSure rep_nonempty_fwd : SafeAddress Forward.
Hint Extern 1 (_ ===> rep (model := ?T) _ _ _) =>
  witness T ltac:(fun v =>
    makeDarnSure (rep_nonempty_bwd T v)) : Backward.

Local Open Scope PropX_scope.

Definition slList (t : type1 word) : type1 word :=
  {| Model1 := list (word * models (Model1 t)) :: nil;
    Typing1 := fun hd ms => {| Pure := Al m, [< In m (fst ms) >] --> Pure (Typing1 t (fst m) (snd m));
      Impure := !{rep (fun w ms' => Impure (Typing1 t w ms')) (fst ms) hd} |}
    |}.

Definition slListNonempty (t : type1 word) : type1 word :=
  {| Model1 := list (word * models (Model1 t)) :: nil;
    Typing1 := fun hd ms => {| Pure := [< hd <> 0 >] /\ Al m, [< In m (fst ms) >] --> Pure (Typing1 t (fst m) (snd m));
      Impure := !{rep (fun w ms' => Impure (Typing1 t w ms')) (fst ms) hd} |}
    |}.

Definition slListNode (next : word) : type1 word :=
  {| Model1 := nil;
    Typing1 := fun hd _ => {| Pure := [< hd <> 0 >];
      Impure := (Ex w, ^data hd ==> w * ^next hd ==> next)%Sep |}
    |}.

Theorem decompose_And : forall pc state specs (p1 p2 q1 q2 : PropX pc state),
  interp specs (p1 --> q1)
  -> interp specs (p2 --> q2)
  -> interp specs (p1 /\ p2 --> q1 /\ q2)%PropX.
  intros; apply Imply_I.
  apply And_I.
  eapply Imply_E; eauto.
  eapply And_E1; apply Env; simpl; eauto.
  eapply Imply_E; eauto.
  eapply And_E2; apply Env; simpl; eauto.
Qed.

Theorem decompose_Exists : forall pc state specs A (p q : A -> PropX pc state),
  (forall x, exists y, interp specs (p x --> q y))
  -> interp specs (PropX.Exists p --> PropX.Exists q).
  intros; apply Imply_I.
  eapply Exists_E; eauto; intro x.
  destruct (H x); clear H.
  apply Exists_I with x0.
  eapply Imply_E; eauto.
  apply Env; simpl; auto.
Qed.

Theorem decompose_Forall : forall pc state specs A (p q : A -> PropX pc state),
  (forall x, exists y, interp specs (p y --> q x))
  -> interp specs (PropX.Forall p --> PropX.Forall q).
  intros; apply Imply_I.
  apply Forall_I; intro x.
  destruct (H x); clear H.
  eapply Imply_E; eauto.
  eapply Forall_E; eauto.
Qed.

Theorem decompose_Imply : forall pc state specs (p q r : PropX pc state),
  interp specs (q --> p \/ r)%PropX
  -> interp specs ((p --> r) --> (q --> r))%PropX.
  intros; do 2 apply Imply_I.
  eapply Or_E.
  eapply Imply_E.
  eapply interp_weaken; eauto.
  apply Env; simpl; auto.
  eapply Imply_E.
  apply Env; simpl; eauto.
  apply Env; simpl; auto.
  apply Env; simpl; auto.
Qed.

Ltac decompose_Imply := match goal with
                          | [ |- interp _ (?p --> _)%PropX ] =>
                            match p with
                              | context[sep] => idtac
                            end;
                            apply decompose_And || apply decompose_Imply
                              || (apply decompose_Exists; intro; eexists)
                                || (apply decompose_Forall; intro; eexists)
                        end.

Theorem forall_cong : forall T (f g : T -> Prop),
  f = g
  -> (forall x, f x) = (forall x, g x).
  intros; subst; reflexivity.
Qed.

Require Import FunctionalExtensionality.

Hint Extern 2 =>
  match goal with
    | [ H : forall x : ?dom, _ |- forall y : ?dom, _ ] =>
      match goal with
        | [ |- ?G ] =>
          let T := type of H in replace G with T; [ assumption
            | solve [ repeat (apply forall_cong || (progress f_equal) || let x := fresh "x" in extensionality x) ] ]
      end
  end : sep0.

Hint Extern 2 (interp _ _) =>
  eapply Imply_trans; [ | solve [ eauto ] ]; simpl;
    repeat decompose_Imply; (propxFo; sep1;
      repeat match goal with
               | [ H : (_, _) = (_, _) |- _ ] => injection H; clear H; intros; subst
             end; try solve [ right; sep ]) : sep0.

Theorem split_AllS : forall pc state T (v : T) ls (p : _ -> PropX pc state) specs,
  (forall x, interp specs ([<v = x \/ In x ls>] --> p x)%PropX)
  -> interp specs (p v) /\ (forall x, interp specs ([<In x ls>] --> p x)%PropX).
  propxFo.
  apply (Imply_sound (H _) (Inj_I _ _ (or_introl _ (refl_equal _)))).
  apply (Imply_sound (H _) (Inj_I _ _ (or_intror _ H0))).
Qed.

Ltac slList := pre; sepSimp; sepFwd;
    repeat match goal with
             | [ H : _ |- _ ] => generalize H; apply split_AllS in H
           end; simpl in *; intuition idtac; propxFo; sep.
