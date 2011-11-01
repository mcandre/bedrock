Require Import FunctionalExtensionality List TheoryList Omega.

Require Import PropXTac.

Set Implicit Arguments.


Module Type S.
  Parameter addr : Type.
  (** Locations in memory *)

  Parameter byte : Type.
  (** Contents of the smallest addressable memory segment *)

  Parameter size : Type.
  (** Supported memory read/write sizes in the ISA *)

  Parameter word : size -> Type.
  (** The type read/written by operations for a given size *)

  Parameter addresses : addr -> size -> list addr.
  (** Which addresses are used to represent a particular size word, starting at a given address? *)

  Parameter explode : addr -> forall sz, word sz -> list (addr * byte).
  (** How to represent a points-to fact, as a list of byte-size points-to facts *)

  Parameter implode : list byte -> forall sz, word sz.
  (** The inverse of [explode], to recreate a word from its constituent bytes, in the order given by [addresses] *)

  Axiom explode_addresses : forall a sz (w : word sz),
    map (@fst _ _) (explode a w) = addresses a sz.

  Axiom explode_functional : forall a sz (w : word sz) a' b b',
    In (a', b) (explode a w)
    -> In (a', b') (explode a w)
    -> b = b'.

  Axiom implode_explode : forall a sz (w : word sz),
    implode (map (@snd _ _) (explode a w)) sz = w.

  Parameter addr_eq : forall x y : addr, {x = y} + {x <> y}.

  Parameter state : Type.
  Parameter Mem : state -> addr -> byte.
End S.

Module Make (M : S).
  Definition smem := M.addr -> option M.byte.

  Definition disjoint (m1 m2 : smem) :=
    forall a v, m1 a = Some v -> m2 a = None.

  Definition hprop := smem -> Prop.

  Definition pure (P : Prop) : hprop := fun sm => P /\ forall a, sm a = None.

  Definition split (sm sm1 sm2 : smem) : Prop :=
    disjoint sm1 sm2
    /\ forall a, sm a = match sm1 a with
                          | None => sm2 a
                          | v => v
                        end.
  Definition join (m1 m2 : smem) : smem :=
    fun a => match m1 a with
               | None => m2 a
               | Some x => Some x
             end.

  Definition star (p1 p2 : hprop) : hprop := fun sm =>
    exists sm1, exists sm2, split sm sm1 sm2 /\ p1 sm1 /\ p2 sm2.

  Definition exis T (p : T -> hprop) : hprop := fun sm =>
    exists v, p v sm.

  Definition readWord' (sm : smem) (a : M.addr) sz (w : M.word sz) : Prop :=
    AllS (fun p => sm (fst p) = Some (snd p)) (M.explode a w).

  Fixpoint collect (sm : smem) (al : list M.addr) : option (list M.byte) :=
    match al with
      | nil => Some nil
      | a :: al' =>
        match sm a with
          | None => None
          | Some b =>
            match collect sm al' with
              | None => None
              | Some bs => Some (b :: bs)
            end
        end
    end.

  Definition readWord (sm : smem) (a : M.addr) (sz : M.size) : option (M.word sz) :=
    match collect sm (M.addresses a sz) with
      | None => None
      | Some bs => Some (M.implode bs sz)
    end.

  Lemma collect_addresses : forall a sz (w : M.word sz) sm,
    AllS (fun p => sm (fst p) = Some (snd p)) (M.explode a w)
    -> collect sm (M.addresses a sz) = Some (map (@snd _ _) (M.explode a w)).
    intros; generalize (M.explode_addresses a w).
    generalize (M.addresses a sz).
    induction H; simpl; intuition.

    rewrite <- H; auto.

    subst; simpl.
    rewrite H.
    rewrite IHForall; auto.
  Qed.    

  Lemma readWord_functionalize : forall sm a sz w,
    readWord' sm a w
    -> readWord sm a sz = Some w.
    unfold readWord', readWord; intros.

    erewrite collect_addresses.
    rewrite M.implode_explode; eauto.
    auto.
  Qed.

  Definition ptsTo (a : M.addr) sz (w : M.word sz) : hprop := fun sm =>
    readWord' sm a w
    /\ forall a', ~In a' (M.addresses a sz) -> sm a' = None.

  Inductive sprop : Type :=
  | Pure : Prop -> sprop
  | Impure : hprop -> sprop
  | Star : sprop -> sprop -> sprop
  | Exis : forall T, (T -> sprop) -> sprop.

  (* You'll probably want a notation like this, with an appropriate inner scope:
     Notation "[< p >]" := (Pure p%nat) : Sep_scope.
     This isn't hardcoded here because the scope depends on factors like which type you use for addresses. *)

  Infix "*" := Star : Sep_scope.

  Delimit Scope Sep_scope with Sep.
  Bind Scope Sep_scope with sprop.

  Notation "'Ex' x , P" := (Exis (fun x => P%Sep)) (x ident, at level 89) : Sep_scope.
  Notation "'Ex' x : A , P" := (Exis (fun x : A => P%Sep)) (x ident, at level 89) : Sep_scope.
  Notation "![ p ]" := (Impure p) : Sep_scope.

  Definition emp : sprop := Pure True.

  Definition stars' := fold_right star (pure True).

  Module Type STARS_DEF.
    Parameter stars : list hprop -> hprop.
    Axiom stars_def : stars = stars'.
  End STARS_DEF.

  Module StarsDef : STARS_DEF.
    Definition stars := stars'.

    Theorem stars_def : stars = stars'.
      reflexivity.
    Qed.
  End StarsDef.

  Import StarsDef.
  Export StarsDef.

  Fixpoint sep' (p : sprop) (k : Prop -> list hprop -> Prop) : Prop :=
    match p with
      | Pure P => k P nil
      | Impure p => k True (p :: nil)
      | Star p1 p2 => sep' p1 (fun P1 ps1 =>
        sep' p2 (fun P2 ps2 =>
          k (P1 /\ P2) (ps1 ++ ps2)))
      | Exis _ p1 => exists x, sep' (p1 x) k
    end.

  Definition sep (p : sprop) sm := sep' p (fun P ps => P /\ stars ps sm).

  (* You'll probably want a machine-dependent notation like this one:
     Notation "![ p ]" := (fun st => [< sep p%Sep (fun a => Some (Mem st a)) >]) : PropX_scope. *)

  Notation "!{ p }" := (Impure (sep p)) : Sep_scope.

  Definition Himp (p p' : sprop) := forall sm, sep p sm -> sep p' sm.

  Notation "p1 ===> p2" := (Himp p1%Sep p2%Sep) (no associativity, at level 90).

  Ltac splitmaster := unfold split, disjoint, star; intuition;
    repeat match goal with
             | [ a : M.addr, H : forall a : M.addr, _ |- _ ] => specialize (H a)
             | [ a : M.addr |- _ ] =>
               match goal with
                 | [ |- ?sm a = _ ] => destruct (sm a); try congruence
               end
             | [ H : context[match ?E with None => _ | Some _ => _ end] |- _ ] => destruct E; try congruence
             | [ |- context[match ?E with None => _ | Some _ => _ end] ] => destruct E; try congruence
             | [ H : _, H' : _ = _ |- _ ] => erewrite H in H'; congruence || reflexivity
             | [ H : _ |- _ ] => erewrite H; congruence || reflexivity
             | [ H : _ |- _ ] => specialize (H _ (refl_equal _)); congruence
           end.

  Theorem split_sym : forall sm sm1 sm2,
    split sm sm1 sm2
    -> split sm sm2 sm1.
    splitmaster.
  Qed.

  Hint Immediate split_sym.

  Theorem AllS_In : forall A (P : A -> Prop) x ls,
    AllS P ls
    -> In x ls
    -> P x.
    induction 1; simpl; intuition congruence.
  Qed.

  Implicit Arguments AllS_In [A P x ls].

  Theorem AllS_weaken : forall A (P P' : A -> Prop) ls,
    AllS P ls
    -> (forall x, In x ls -> P x -> P' x)
    -> AllS P' ls.
    induction 1; simpl; intuition.
  Qed.

  Implicit Arguments AllS_weaken [A P P' ls].

  Theorem read' : forall a sz (w : M.word sz) (ps2 ps1 : list hprop) sm,
    stars (ps1 ++ ptsTo a w :: ps2) sm
    -> readWord' sm a w.
    rewrite stars_def; induction ps1; simpl; intuition; subst.

    red in H; firstorder.
    apply (AllS_weaken H0); intros.
    rewrite H1.
    rewrite H5.
    reflexivity.
    
    red in H; firstorder.
    specialize (IHps1 _ H2).
    apply (AllS_weaken IHps1); intros.
    rewrite H1.
    specialize (H (fst x1)).
    splitmaster.
  Qed.

  Theorem read : forall a a' sz (w : M.word sz) (ps2 ps1 : list hprop) sm,
    stars (ps1 ++ ptsTo a w :: ps2) sm
    -> a' = a
    -> readWord sm a' sz = Some w.
    intros; subst; apply readWord_functionalize; eapply read'; eauto.
  Qed.

  Fixpoint noOverlap (al al' : list M.addr) : Prop :=
    match al with
      | nil => True
      | a :: al0 =>
        if In_dec M.addr_eq a al'
          then False
          else noOverlap al0 al'
    end.

  Theorem noOverlap_nil : forall al, noOverlap al nil.
    induction al; simpl; intuition.
  Qed.

  Theorem noOverlap_cons : forall a al' al,
    ~In a al
    -> noOverlap al al'
    -> noOverlap al (a :: al').
    induction al; simpl; intuition.
    destruct (M.addr_eq a a0); intuition.
    destruct (In_dec M.addr_eq a0 al'); intuition.
  Qed.

  Theorem In_map : forall A B (f : A -> B) x ls,
    In x (map f ls)
    -> exists y, x = f y /\ In y ls.
    induction ls; simpl; firstorder; eauto.
  Qed.

  Implicit Arguments In_map [A B f x ls].

  Theorem In_map' : forall A B (f : A -> B) x ls,
    In x ls
    -> In (f x) (map f ls).
    induction ls; simpl; intuition.
    subst; auto.
  Qed.

  Implicit Arguments In_map' [A B f x ls].

  Theorem ptrsNeq : forall ps1 ps2 ps3 a1 a2 a1' a2' sz1 (w1 : M.word sz1) sz2 (w2 : M.word sz2) sm,
    stars (ps1 ++ ptsTo a1' w1 :: ps2 ++ ptsTo a2' w2 :: ps3) sm
    -> a1' = a1
    -> a2' = a2
    -> noOverlap (M.addresses a1 sz1) (M.addresses a2 sz2).
    rewrite stars_def; induction ps1; simpl; intuition; subst; eauto.

    red in H; firstorder.
    rewrite <- stars_def in H2.
    apply read' in H2.
    unfold readWord' in *.
    generalize (M.explode_addresses a2 w2).
    generalize (M.explode_addresses a1 w1).
    generalize dependent (M.explode a1 w1).
    generalize (M.addresses a1 sz1) (M.addresses a2 sz2).
    generalize H2 H; clear.
    induction 1; simpl; intuition; subst.
    apply noOverlap_nil.
    apply noOverlap_cons; eauto.

    clear H1.
    intro.
    apply (In_map (f := @fst _ _)) in H1.
    firstorder.
    apply (AllS_In H3) in H4.
    rewrite H1 in H.
    apply H0 in H4; congruence.
    
    red in H; firstorder.
    eauto.
  Qed.

  Definition writeWord (sm : smem) (a : M.addr) sz (w : M.word sz) : smem :=
    fold_left (fun sm p a' => if M.addr_eq a' (fst p) then Some (snd p) else sm a') (M.explode a w) sm.

  Lemma writeWord_cause_Some : forall sm a sz (w : M.word sz) a' b,
    writeWord sm a w a' = Some b
    -> (~In a' (map (@fst _ _) (M.explode a w)) /\ sm a' = Some b) \/ In (a', b) (M.explode a w).
    unfold writeWord; intros; generalize dependent sm; induction (M.explode a w); simpl in *; intuition.
    specialize (IHl _ H); clear H.
    simpl in *; intuition.
    destruct (M.addr_eq a' a1); intuition congruence.
  Qed.

  Implicit Arguments writeWord_cause_Some [sm a sz w a' b].

  Lemma writeWord_cause_None : forall sm a sz (w : M.word sz) a',
    writeWord sm a w a' = None
    -> sm a' = None /\ ~In a' (map (@fst _ _) (M.explode a w)).
    unfold writeWord; intros; generalize dependent sm; induction (M.explode a w); simpl in *; intuition;
    specialize (IHl _ H); clear H; simpl in *; intuition; destruct (M.addr_eq a' a1); intuition congruence.
  Qed.

  Implicit Arguments writeWord_cause_None [sm a sz w a'].

  Lemma readWord'_writeWord' : forall a (b : M.byte) ls sm,
    (forall b', In (a, b') ls -> b' = b)
    -> sm a = Some b
    -> fold_left (fun sm p a' => if M.addr_eq a' (fst p) then Some (snd p) else sm a') ls sm a = Some b.
    induction ls; simpl; intuition.

    apply IHls; intuition.

    simpl.
    destruct (M.addr_eq a a1); intuition; subst.
    specialize (H _ (or_introl _ (refl_equal _))); intuition congruence.
  Qed.

  Lemma readWord'_writeWord : forall a sz (w : M.word sz) sm,
    readWord' (writeWord sm a w) a w.
    unfold readWord', writeWord; intros; generalize dependent sm.
    generalize (M.explode_functional a w); induction (M.explode a w); simpl in *; intuition.

    constructor; simpl; intuition.

    apply readWord'_writeWord'; intuition.
    specialize (H (fst a0) (snd a0) b'); destruct a0; simpl in *; intuition.
    destruct (M.addr_eq (fst a0) (fst a0)); tauto.

    apply IHl; intuition.
    specialize (H a' b b'); tauto.
  Qed.

  Theorem overwrite : forall a a' sz (w w' : M.word sz) ps2 ps1 sm,
    stars (ps1 ++ ptsTo a w :: ps2) sm
    -> a' = a
    -> stars (ps1 ++ ptsTo a w' :: ps2) (writeWord sm a' w').
    rewrite stars_def; induction ps1; simpl; intuition; subst.

    unfold star in *; firstorder.
    exists (writeWord (fun _ => None) a w').
    exists x0; intuition.
    
    red; intuition.
    red; intros.
    destruct (In_dec M.addr_eq a0 (map (@fst _ _) (M.explode a w))).

    destruct (In_map i); intuition; subst.
    eapply H.
    eapply (AllS_In H0); eauto.
    
    apply writeWord_cause_Some in H4; intuition; try discriminate.
    elimtype False; apply n.
    rewrite M.explode_addresses.
    apply (In_map' (f := @fst _ _)) in H5.
    rewrite M.explode_addresses in H5; auto.

    generalize (@writeWord_cause_None sm a _ w' a0).
    generalize (@writeWord_cause_None (fun _ => None) a _ w' a0).
    generalize (@writeWord_cause_Some sm a _ w' a0).
    generalize (@writeWord_cause_Some (fun _ => None) a _ w' a0).
    intros.
    destruct (writeWord sm a w' a0); destruct (writeWord (fun _ => None) a w' a0);
      repeat match goal with
               | [ H : _ |- _ ] => specialize (H _ (refl_equal _)) || specialize (H (refl_equal _))
             end; intuition; try discriminate.

    apply (In_map' (f := @fst _ _)) in H8; tauto.

    f_equal; eapply M.explode_functional; eauto.
    
    rewrite H1 in H10.
    rewrite H3 in H10; auto.
    repeat rewrite M.explode_addresses in *; auto.

    elimtype False; apply H9.
    apply (In_map' (f := @fst _ _)) in H6; auto.

    elimtype False; apply H9.
    apply (In_map' (f := @fst _ _)) in H7; auto.

    rewrite H1 in H6.
    rewrite H3 in H6; auto.
    repeat rewrite M.explode_addresses in *; auto.

    red; intuition.

    apply readWord'_writeWord.

    generalize (@writeWord_cause_Some (fun _ => None) a _ w' a').
    destruct (writeWord (fun _ => None) a w' a'); intuition.
    specialize (H5 _ (refl_equal _)); intuition.
    elimtype False; apply H4.
    apply (In_map' (f := @fst _ _)) in H6.
    rewrite M.explode_addresses in H6; auto.

    unfold star in *; firstorder.
    exists x; exists (writeWord x0 a w'); intuition.

    red; intuition.
    red; intros.
    generalize (@writeWord_cause_Some x0 a _ w' a1).
    destruct (writeWord x0 a w' a1); intuition.
    specialize (H4 _ (refl_equal _)); intuition.
    apply H in H3; congruence.

    rewrite <- stars_def in H2.
    apply read' in H2; auto.
    apply (In_map' (f := @fst _ _)) in H5; simpl in H5.
    rewrite M.explode_addresses in H5.
    rewrite <- (M.explode_addresses _ w) in H5.
    apply In_map in H5; firstorder; subst.
    apply (AllS_In H2) in H5.
    apply H in H3; congruence.

    generalize (@writeWord_cause_None sm a _ w' a1).
    generalize (@writeWord_cause_None x0 a _ w' a1).
    generalize (@writeWord_cause_Some sm a _ w' a1).
    generalize (@writeWord_cause_Some x0 a _ w' a1).
    intros.
    destruct (writeWord sm a w' a1); destruct (writeWord x0 a w' a1);
      repeat match goal with
               | [ H : _ |- _ ] => specialize (H _ (refl_equal _)) || specialize (H (refl_equal _))
             end; intuition; try discriminate.  

    rewrite H1 in H9.
    specialize (H a1).
    destruct (x a1); congruence.

    elimtype False; apply H3.
    apply (In_map' (f := @fst _ _)) in H7; auto.

    elimtype False; apply H4.
    apply (In_map' (f := @fst _ _)) in H7; auto.

    rewrite <- stars_def in H2.
    apply read' in H2; auto.  
    generalize (In_map' (f := @fst _ _) H7); intro Hm; simpl in Hm.
    rewrite M.explode_addresses in Hm.
    rewrite <- (M.explode_addresses _ w) in Hm.
    apply In_map in Hm; firstorder; subst.
    apply (AllS_In H2) in H8.
    specialize (H (fst x1)).
    destruct (x (fst x1)).
    specialize (H _ (refl_equal _)); congruence.
    f_equal; eapply M.explode_functional; eauto.

    rewrite H1 in H9.
    destruct (x a1); congruence.

    elimtype False; apply H8.
    apply (In_map' (f := @fst _ _)) in H5; auto.

    rewrite H1 in H7.
    destruct (x a1); congruence.

    elimtype False; apply H8.
    apply (In_map' (f := @fst _ _)) in H6; auto.

    rewrite H1 in H5.
    destruct (x a1); congruence.
  Qed.

  Definition himp (ps ps' : list hprop) := forall sm, stars ps sm -> stars ps' sm.

  Infix "--->" := himp (no associativity, at level 90).

  Theorem stars_final : forall ls ls' sm sm',
    stars ls sm
    -> (forall a, sm a = sm' a)
    -> ls ---> ls'
    -> stars ls' sm'.
    intros; replace sm' with sm; auto.
    extensionality x; auto.
  Qed.

  Theorem himp_refl : forall ps, ps ---> ps.
    red; auto.
  Qed.

  Hint Unfold pure.

  Lemma split_right : forall sm x x0,
    split sm x x0
      -> (forall a, x0 a = None)
      -> x = sm.
    unfold split, disjoint; intuition.
    extensionality a.
    specialize (H0 a); specialize (H1 a); specialize (H2 a).
    rewrite H0 in H2.
    destruct (x a); auto.
  Qed.

  Theorem sep'_weaken : forall p k, sep' p k
    -> forall k' : _ -> _ -> Prop, (forall P ps, k P ps -> k' P ps)
      -> sep' p k'.
    induction p; simpl; firstorder.

    eapply IHp1; eauto.
    simpl; eauto.
  Qed.

  Lemma frame_finish : forall ps,
    ps ---> sep (fold_right Star (Pure True) (map Impure ps)) :: nil.
    unfold himp; induction ps; simpl; intuition; rewrite stars_def in *; simpl in *.

    unfold sep; simpl.
    rewrite stars_def; simpl.
    exists sm; exists (fun _ => None); intuition.
    red; intuition.
    red; intuition.
    destruct (sm a); tauto.
    red; auto.

    red in H; firstorder.
    specialize (IHps _ H2).
    exists sm; exists (fun _ => None); intuition.
    splitmaster.
    red in IHps; firstorder.
    generalize (split_right (conj H3 H5) H7); intro; subst.
    unfold sep in *; simpl in *.
    eapply sep'_weaken.
    eauto.
    simpl; intuition.
    rewrite stars_def in *; simpl.
    exists x; exists x0; intuition.
    red; tauto.
  Qed.

  Theorem himp_cancel_front : forall p ps ps',
    ps ---> ps'
    -> p :: ps ---> p :: ps'.
    unfold himp; rewrite stars_def; simpl; intuition.

    unfold star in *; firstorder.
  Qed.

  Lemma himp_pullout' : forall p p' ps,
    p :: p' :: ps ---> p' :: p :: ps.
    unfold himp; rewrite stars_def; simpl; firstorder.

    exists x1; exists (fun a => match x a with
                                  | None => x2 a
                                  | v => v
                                end); intuition.
    unfold split, disjoint in *; intuition.

    splitmaster.
    splitmaster.

    exists x; exists x2; intuition.
    unfold split, disjoint in *; intuition.
    specialize (H _ _ H6).
    specialize (H4 a).
    rewrite H in H4.
    specialize (H2 a).
    destruct (x1 a); congruence.
  Qed.

  Theorem himp_trans : forall p1 p2 p3,
    p1 ---> p2
    -> p2 ---> p3
    -> p1 ---> p3.
    unfold himp; eauto.
  Qed.

  Lemma himp_pullout1 : forall ps2 p ps1,
    ps1 ++ p :: ps2 ---> p :: ps1 ++ ps2.
    induction ps1; simpl; intuition.

    apply himp_refl.

    apply himp_trans with (a :: p :: ps1 ++ ps2).

    apply himp_cancel_front; eauto.

    apply himp_pullout'; eauto.
  Qed.

  Lemma himp_pullout2 : forall ps2 p ps1,
    p :: ps1 ++ ps2 ---> ps1 ++ p :: ps2.
    induction ps1; simpl; intuition.

    apply himp_refl.

    apply himp_trans with (a :: p :: ps1 ++ ps2).

    apply himp_pullout'; eauto.

    apply himp_cancel_front; eauto.
  Qed.

  Theorem himp_cancel : forall p ps2 ps2' ps1 ps1',
    ps1 ++ ps2 ---> ps1' ++ ps2'
    -> ps1 ++ p :: ps2 ---> ps1' ++ p :: ps2'.
    intros.
    apply himp_trans with (p :: ps1 ++ ps2).

    apply himp_pullout1; eauto.

    apply himp_trans with (p :: ps1' ++ ps2').

    apply himp_cancel_front; eauto.

    apply himp_pullout2; eauto.
  Qed.

  Theorem himp_cancel_eq : forall ps1 ps2 ps1' ps2' p p',
    p' = p
    -> ps1 ++ ps2 ---> ps1' ++ ps2'
    -> ps1 ++ p :: ps2 ---> ps1' ++ p' :: ps2'.
    intros; subst; apply himp_cancel; auto.
  Qed.

  Theorem himp_cancel_ptsTo : forall ps1 ps2 ps1' ps2' sz p p' v v',
    p' = p 
    -> ps1 ++ ps2 ---> ps1' ++ ps2'
    -> v' = v 
    -> ps1 ++ @ptsTo p sz v :: ps2 ---> ps1' ++ @ptsTo p' sz v' :: ps2'.
  Proof.
    intros. subst. eapply himp_cancel_eq. reflexivity. assumption.
  Qed.

  Lemma himp_guard_elim_r : forall s : sprop,
    sep s :: nil ---> sep !{s} :: nil.
  Proof.
    unfold sep,himp. rewrite stars_def. simpl. unfold star. intros.
    repeat match goal with
             | [ H : exists x, _ |- _ ] => destruct H
             | [ H : _ /\ _ |- _ ] => destruct H
           end.
    do 2 eexists. split. Focus 2. split. 2: eassumption. split. tauto. do 2 eexists. split; [ | split ]. 3: eassumption.
    2: eassumption. eassumption. unfold split, pure in *. firstorder. rewrite H2. destruct (x a); eauto. rewrite H3. auto.
  Qed.

  Lemma himp_guard_elim_l : forall s : sprop,
    sep !{s} :: nil ---> sep s :: nil.
  Proof.
    unfold sep,himp. rewrite stars_def. simpl. unfold star. intros.
    repeat match goal with
             | [ H : exists x, _ |- _ ] => destruct H
             | [ H : _ /\ _ |- _ ] => destruct H
           end.
    do 2 eexists. split. Focus 2. split. eassumption. eassumption. 
    unfold split, disjoint, pure in *; intuition. rewrite H6. rewrite H7.
    destruct (x1 a); auto. rewrite H8. auto.
  Qed.

  Theorem stars_elim_Pure : forall P ps2 ps1 sm,
    stars (ps1 ++ sep (Pure P) :: ps2) sm
    -> P /\ stars (ps1 ++ ps2) sm.
    induction ps1; simpl; firstorder; rewrite stars_def in *; firstorder.

    rewrite stars_def in H3; simpl in H3.
    red in H3; intuition.

    replace sm with x0; auto.
    extensionality a.
    rewrite H1.
    rewrite H5.
    reflexivity.
  Qed.

  Lemma stars'_sep_fwd : forall ps2 sm,
    stars' ps2 sm
    -> sep (fold_right Star (Pure True) (map Impure ps2)) sm.
    induction ps2; simpl; firstorder.

    rewrite stars_def; firstorder.

    unfold sep in *; simpl in *.
    specialize (IHps2 _ H2).
    eapply sep'_weaken; eauto.
    simpl; intuition.
    rewrite stars_def in *; firstorder.
  Qed.

  Lemma split_shuffle : forall sm x x0 x1 x2,
    split sm x x0
    -> split x x1 x2
    -> split (fun a => match x1 a with
                         | None => sm a
                         | _ => None
                       end) x2 x0.
    splitmaster.
  Qed.

  Theorem desep_fwd : forall p ps2 ps1 sm, stars (ps1 ++ sep p :: ps2) sm
    -> sep (fold_right Star (Pure True) (map Impure ps1 ++ p :: map Impure ps2)) sm.
    rewrite stars_def; induction ps1; simpl; firstorder.

    unfold sep; simpl.
    eapply sep'_weaken.
    eauto.
    simpl; intuition.
    rewrite stars_def in *.
    clear H0.
    generalize dependent x0.
    generalize dependent x.
    generalize dependent sm.
    generalize dependent ps2.
    induction ps; simpl; firstorder.

    apply stars'_sep_fwd in H2.
    eapply sep'_weaken.
    eassumption.
    simpl; intuition.
    rewrite stars_def in *.
    replace sm with x0; eauto.
    extensionality a.
    rewrite H1; rewrite H3; reflexivity.

    specialize (IHps _ _ _ H6 _ (proj1 (split_shuffle (conj H H1) (conj H0 H5))) (proj2 (split_shuffle (conj H H1) (conj H0 H5))) H2).
    eapply sep'_weaken; [ eauto | ].
    simpl; intuition.

    exists x1.
    exists (fun a : M.addr =>
      match x1 a with
        | Some _ => None
        | None => sm a
      end).
    intuition.
    splitmaster.

    unfold sep in *; simpl.
    specialize (IHps1 _ H2).
    eapply sep'_weaken; [ eauto | ].
    simpl; intuition.
    rewrite stars_def in *; firstorder.
  Qed.

  Theorem unfold_sep : forall p p' ps2 ps1 sm,
    stars (ps1 ++ sep p :: ps2) sm
    -> p ===> p'
    -> stars (ps1 ++ sep p' :: ps2) sm.
    unfold Himp; rewrite stars_def; induction ps1; simpl; firstorder.
  Qed.

  Theorem unfold_sep_fwd : forall p p' ps2 ps1 sm,
    stars (ps1 ++ sep p :: ps2) sm
    -> p ===> p'
    -> sep (fold_right Star (Pure True)
      (map Impure ps1 ++ p' :: map Impure ps2)) sm.
    intros; apply desep_fwd; eapply unfold_sep; eauto.
  Qed.

  Lemma split_assoc : forall sm x x0 x1 x2,
    split sm x x0
      -> split x0 x1 x2
        -> split sm (fun a => match x a with
                                | None => x1 a
                                | v => v
                              end) x2.
    splitmaster.
  Qed.

  Lemma stars'_app_fwd : forall ps2 ps1 sm,
    stars' (ps1 ++ ps2) sm
    -> exists sm1, exists sm2, split sm sm1 sm2
      /\ stars' ps1 sm1
      /\ stars' ps2 sm2.
    induction ps1; simpl; firstorder.

    exists (fun _ => None); exists sm; intuition.
    splitmaster.

    specialize (IHps1 _ H2); firstorder.
    exists (fun a => match x a with
                       | None => x1 a
                       | v => v
                     end); exists x2.
    split.
    eapply split_assoc; eauto.
    red; eauto.
    red; intuition.
    intuition.
    exists x; exists x1; intuition eauto.
    red; intuition.
    unfold disjoint in *; intuition.
    specialize (H3 a0).
    specialize (H a0).
    specialize (H5 a0).
    destruct (x1 a0); auto.
    specialize (H1 a0).
    rewrite H7 in H1.
    specialize (H _ H7).
    congruence.
  Qed.

  Lemma stars'_app_bwd : forall ps2 sm2 ps1 sm sm1,
    split sm sm1 sm2
    -> stars' ps1 sm1
    -> stars' ps2 sm2
    -> stars' (ps1 ++ ps2) sm.
    induction ps1; simpl; firstorder.

    replace sm with sm2; auto.
    extensionality a; splitmaster.

    exists x; exists (fun a => match sm2 a with
                                 | None => x0 a
                                 | v => v
                               end); intuition eauto.

    unfold split, disjoint in *; intuition.
    erewrite H.
    eauto.
    rewrite H4.
    rewrite H6.
    eauto.

    splitmaster.

    eapply IHps1; eauto.
    unfold split, disjoint in *; intuition.
    eapply H.
    rewrite H4.
    specialize (H0 a0).
    destruct (x a0); eauto.
    specialize (H0 _ (refl_equal _)); congruence.

    splitmaster.
  Qed.

  Lemma sep'_ex : forall p k, sep' p k
    -> exists P, exists ps, k P ps
      /\ forall sm, P
        -> stars ps sm
        -> sep p sm.
    induction p; simpl; firstorder.

    specialize (IHp1 _ H); clear H; firstorder.
    specialize (IHp2 _ H); clear H; firstorder.
    do 2 eexists; split.
    eauto.
    rewrite stars_def; unfold sep; firstorder.
    apply stars'_app_fwd in H3; firstorder.
    rewrite stars_def in *.
    specialize (H1 _ H4 H7).
    specialize (H0 _ H2 H5).
    simpl.
    eapply sep'_weaken; [ eassumption | clear H0; firstorder ].
    eapply sep'_weaken; [ eassumption | clear H1; firstorder ].
    rewrite stars_def in *.
    eapply stars'_app_bwd; eauto.
    split; auto.

    specialize (H _ _ H0); clear H0; firstorder.
    do 2 eexists; split.
    eauto.
    intuition.
    specialize (H0 _ H1 H2).
    exists x.
    eauto.
  Qed.

  Lemma stars'_sep_bwd : forall ps2 sm,
    sep (fold_right Star (Pure True) (map Impure ps2)) sm
    -> stars' ps2 sm.
    induction ps2; simpl; firstorder.

    rewrite stars_def in *; firstorder.

    unfold sep in *; simpl in *.
    apply sep'_ex in H; firstorder.
    rewrite stars_def in *; firstorder.
    do 2 eexists; split.
    split; eauto.
    intuition.
    apply IHps2.
    specialize (H0 _ H2 H5).
    eapply sep'_weaken; [ eassumption | ].
    simpl; intuition.
    rewrite stars_def in *; assumption.
  Qed.
  
  Theorem desep_bwd : forall p ps2 ps1 sm,
    sep (fold_right Star (Pure True)
      (map Impure ps1 ++ p :: map Impure ps2)) sm
    -> stars (ps1 ++ sep p :: ps2) sm.
    induction ps1; simpl; firstorder.

    rewrite stars_def; firstorder.
    unfold sep in H; simpl in H.
    apply sep'_ex in H; firstorder.
    apply sep'_ex in H; firstorder.
    rewrite stars_def in *.
    apply stars'_app_fwd in H2; firstorder.
    do 2 eexists; split.
    split; eassumption.
    intuition.
    specialize (H1 _ H3 H6).
    apply stars'_sep_bwd; assumption.

    rewrite stars_def in *; unfold sep in *; firstorder.
    apply sep'_ex in H; firstorder.
    rewrite stars_def in *; firstorder.

    simpl.
    specialize (H0 _ H H1).
    unfold sep in H0; simpl in H0.
    apply sep'_ex in H0; firstorder.
    rewrite stars_def in *; firstorder.
    exists x3; exists x4; intuition.
    split; auto.
    apply IHps1.
    specialize (H2 _ H4 H7).
    eapply sep'_weaken.
    eassumption.
    simpl; intuition.
    rewrite stars_def in *; assumption.
  Qed.

  Theorem unfold_sep_bwd : forall p p' ps2 ps1 sm,
    sep (fold_right Star (Pure True)
      (map Impure ps1 ++ p :: map Impure ps2)) sm
    -> p ===> p'
    -> stars (ps1 ++ sep p' :: ps2) sm.
    intros; apply desep_bwd.

    generalize dependent sm.
    induction ps1; simpl; firstorder.
    unfold sep in *; simpl in *.
    red in H0.
    apply sep'_ex in H; firstorder.
    apply sep'_ex in H; firstorder.
    rewrite stars_def in *.
    apply stars'_app_fwd in H3; firstorder.
    specialize (H2 _ H4 H7).
    specialize (H1 _ H H5).
    apply sep'_weaken with (fun P ps => P /\ stars ps x3).
    apply H0; auto.
    intuition.
    eapply sep'_weaken; [ eauto | ].
    simpl; intuition.
    rewrite stars_def in *.
    eapply stars'_app_bwd; eauto.
    split; auto.

    unfold sep in H; simpl in H.
    apply sep'_ex in H; firstorder.
    rewrite stars_def in *; firstorder.
    specialize (H1 _ H3 H6).
    specialize (IHps1 _ H1).
    unfold sep; simpl.
    eapply sep'_weaken; [ eauto | ].
    rewrite stars_def in *; firstorder.
  Qed.

  Lemma stars_intro : forall p sm,
    sep p sm
    -> stars (sep p :: nil) sm.
    rewrite stars_def; firstorder.
    exists sm; exists (fun _ => None); intuition.
    splitmaster.
    constructor; auto.
  Qed.

  Lemma stars_elim : forall p sm,
    stars (sep p :: nil) sm
    -> sep p sm.
    rewrite stars_def; firstorder.
    replace sm with x; auto.
    extensionality a; splitmaster.
  Qed.

  Definition mem := M.addr -> M.byte.

  Definition msel' (m : mem) (a : M.addr) (sz : M.size) : M.word sz :=
    M.implode (map m (M.addresses a sz)) sz.

  Definition mupd' (m : mem) (a : M.addr) sz (w : M.word sz) : mem :=
    fold_left (fun m p a' => if M.addr_eq a' (fst p) then snd p else m a') (M.explode a w) m.

  Module Type MOPS.
    Parameter msel : mem -> M.addr -> forall sz, M.word sz.
    Parameter mupd : mem -> M.addr -> forall sz, M.word sz -> mem.

    Axiom msel_def : msel = msel'.
    Axiom mupd_def : mupd = mupd'.
  End MOPS.

  Module Mops : MOPS.
    Definition msel := msel'.
    Definition mupd := mupd'.

    Theorem msel_def : msel = msel'.
      reflexivity.
    Qed.

    Theorem mupd_def : mupd = mupd'.
      reflexivity.
    Qed.
  End Mops.

  Import Mops.
  Export Mops.

  Definition msel := Mops.msel.
  Definition mupd := Mops.mupd.
  Definition msel_def : msel = msel' := Mops.msel_def.
  Definition mupd_def : mupd = mupd' := Mops.mupd_def.

  Lemma mupd_eq'' : forall a ls (m : mem),
    (forall b', In (a, b') ls -> b' = m a)
    -> fold_left (fun m p a' => if M.addr_eq a' (fst p) then snd p else m a') ls m a = m a.
    induction ls; simpl; intuition.

    rewrite IHls; simpl; intuition.

    destruct (M.addr_eq a a1); intuition; subst; auto.

    destruct (M.addr_eq a a1); intuition; subst.
    generalize (H _ (or_intror _ H0)).
    specialize (H _ (or_introl _ (refl_equal _))).
    congruence.
  Qed.

  Lemma mupd_eq' : forall a sz (w : M.word sz) m,
    map (fold_left (fun m p a' => if M.addr_eq a' (fst p) then snd p else m a') 
      (M.explode a w) m) (M.addresses a sz) = map (@snd _ _) (M.explode a w).
    intros; generalize (M.explode_addresses a w).
    generalize (M.explode_functional a w).
    generalize (M.addresses a sz).
    generalize m.
    induction (M.explode a w); simpl; intuition; subst; simpl; auto.

    f_equal.

    rewrite mupd_eq''.
    destruct (M.addr_eq a1 a1); tauto.
    intros.
    destruct (M.addr_eq a1 a1); intuition.
    specialize (H a1 b b'); intuition.

    apply IHl; auto.
    intros.
    specialize (H a' b0 b'); tauto.
  Qed.

  Theorem mupd_eq : forall m a sz (w : M.word sz),
    msel (mupd m a w) a sz = w.
    rewrite msel_def; rewrite mupd_def; unfold msel', mupd'; intros.
    rewrite mupd_eq'.
    apply M.implode_explode.
  Qed.

  Theorem map_agree : forall A B (f1 f2 : A -> B) ls,
    AllS (fun x => f1 x = f2 x) ls
    -> map f1 ls = map f2 ls.
    induction 1; simpl; intuition congruence.
  Qed.

  Theorem mupd_ne' : forall m m' a1 sz1 (w : M.word sz1) a2 sz2,
    noOverlap (M.addresses a1 sz1) (M.addresses a2 sz2)
    -> AllS (fun a => m a = m' a) (M.addresses a2 sz2)
    -> msel (mupd m a1 w) a2 sz2 = msel m' a2 sz2.
    rewrite msel_def; rewrite mupd_def; unfold msel', mupd'; intros.
    f_equal.
    apply map_agree.
    
    generalize (M.explode_addresses a1 w).
    generalize dependent (M.addresses a1 sz1).
    generalize dependent (M.addresses a2 sz2).
    generalize dependent m.
    generalize dependent m'.
    induction (M.explode a1 w); simpl; intros; subst; simpl in *.

    auto.

    destruct (In_dec M.addr_eq (fst a) l0); intuition.
    match goal with
      | [ |- context[fold_left _ _ ?m _ ] ] =>
        specialize (IHl m' m l0)
    end.
    match type of IHl with
      | ?P -> _ => assert P; [ | intuition ]
    end.
    eapply (AllS_weaken H0); simpl; intros.
    destruct (M.addr_eq x (fst a)); subst; intuition.
    eauto.
  Qed.

  Theorem AllS_obvious : forall A (P : A -> Prop) ls,
    (forall x, P x)
    -> AllS P ls.
    induction ls; simpl; intuition.
  Qed.

  Theorem mupd_ne : forall m a1 sz1 (w : M.word sz1) a2 sz2,
    noOverlap (M.addresses a1 sz1) (M.addresses a2 sz2)
    -> msel (mupd m a1 w) a2 sz2 = msel m a2 sz2.
    intros; apply mupd_ne'; auto.
    apply AllS_obvious; auto.
  Qed.

  Theorem noOverlap_sym : forall al al', noOverlap al al'
    -> noOverlap al' al.
    induction al; simpl; intuition.
    apply noOverlap_nil.
    destruct (In_dec M.addr_eq a al'); intuition.
    apply noOverlap_cons; auto.
  Qed.

  Lemma collect_map : forall m l,
    collect (fun a : M.addr => Some (m a)) l = Some (map m l).
  Proof.
    induction l. auto.
    simpl. rewrite IHl. auto.
  Qed.

  Lemma readWord_msel : forall w a M v,
    readWord (fun a0 : M.addr => Some (M a0)) a w = Some v ->
    msel M a w = v.
  Proof.
    unfold readWord. rewrite msel_def. unfold msel'.
    intros. generalize dependent (M.addresses a w).
    intro. clear a. 
    rewrite collect_map. congruence.
  Qed.

  Lemma writeWord_mupd : forall sz M M' a a' (v : M.word sz) x,
    a = a' ->
    (forall x, M x = Some (M' x)) ->
    writeWord M a v x = Some (mupd M' a' v x).
  Proof.
    unfold writeWord. rewrite mupd_def. unfold mupd'. intros. subst.
    generalize dependent (M.explode a' v). intros. generalize dependent M. generalize dependent M'.
    induction l; simpl; intros; auto.
    erewrite IHl. eauto.
    intros. simpl. destruct (M.addr_eq x0 (fst a)); auto.
  Qed.

  (** Join Lemmas **)
  Lemma split_join : forall sm0 x x0 x1 x2,
    split sm0 x x0 ->
    split x0 x1 x2 ->
    split sm0 (join x x1) x2.
  Proof.
    unfold split. intros.
    unfold disjoint, join in *; intuition;
    repeat match goal with
             | [ a : M.addr , H : forall a, _ |- _ ] =>
               specialize (H a)
             | [ H : context [ match ?X with 
                                 | None => _ 
                                 | Some _ => _ 
                               end ] |- _ ] => 
               case_eq (X); [ intro | ]; let H' := fresh in intro H'; rewrite H' in *
             | [ H : forall _, _ , H' : _ |- _ ] => apply H in H'
             | [ H : _ = _ |- _ ] => rewrite H in *
           end; try discriminate; intuition. 
  Qed.

  Lemma split_disjoint : forall a b c, 
    split a b c ->
    disjoint b c.
  Proof.
    unfold split in *. intuition.
  Qed.

  Lemma read_join_r : forall sz m1 m2 p (v : M.word sz),
    readWord' m1 p v ->
    readWord' (join m1 m2) p v.
  Proof.
    intros. unfold readWord' in *.
    generalize dependent (M.explode p v). induction l. eauto.
    intros. inversion H; clear H; subst. apply IHl in H3.
    econstructor. unfold join. rewrite H2. auto.
    auto.
  Qed.
  Lemma read_join_l : forall sz m1 m2 p (v : M.word sz),
    disjoint m2 m1 ->
    readWord' m2 p v ->
    readWord' (join m1 m2) p v.
  Proof.
    intros. unfold readWord' in *.
    generalize dependent (M.explode p v). induction l. eauto.
    intros. inversion H0; clear H0; subst. apply IHl in H4.
    econstructor; eauto.
    unfold disjoint in H. unfold join. rewrite H3. erewrite H; eauto.
  Qed.
  (** End Join Lemmas **)


  Ltac simplifyMem' x a H' ls sm :=
    let Heq := fresh "Heq" in generalize H'; intro Heq;
      let rec finder pre post :=
        match eval hnf in post with
          | ptsTo ?a' (sz := ?sz) ?w :: ?post =>
            apply (read (a := a') (a' := a) (sz := sz) w post (rev pre) (sm := sm)) in Heq;
              [ | (* unfold M.addr; *) solve [ auto ] ]
          | ?p :: ?post => finder (p :: pre) post
        end in
        finder (@nil hprop) ls; 
        (   rewrite (readWord_msel _ _ Heq) in *
         || (injection Heq; clear Heq; intro Heq; try autorewrite with SimplifyMem in Heq;
           try match type of Heq with
                 | Some _ = Some _ => injection Heq; clear Heq; intro Heq
               end; rewrite Heq in *)); clear Heq.

  Ltac doMupd m a sz w a' sz' :=
    match goal with
      | [ _ : stars ?ls _ |- _ ] =>
        (let rec walk pre post :=
          match eval hnf in post with
            | ptsTo _ _ :: ?post =>
              let rec walk' pre' post :=
                match eval hnf in post with
                  | ptsTo _ _ :: ?post =>
                    let finishIt := eapply (ptrsNeq (rev pre) (rev pre') post); simpl; [
                      eassumption | solve [ instantiate; auto ] | solve [ instantiate; auto ] ] in
                    finishIt || (apply noOverlap_sym; finishIt)
                  | ?p :: ?post =>
                    walk' (p :: pre') post
                end in
                walk' (@nil hprop) post
            | ?p :: ?post => walk (p :: pre) post
          end in
          let H := fresh "H" in assert (H : noOverlap (M.addresses a sz) (M.addresses a' sz')); [ walk (@nil hprop) ls
            | rewrite (@mupd_ne m a _ _ a' _ H) in *; clear H ]) || fail 1
    end.

  Ltac simplifyMem :=
    match goal with
      | [ H : stars ?ls ?sm |- context[msel ?x ?a _] ] => simplifyMem' x a H ls sm
      | [ _ : context[msel ?x ?a _], H : stars ?ls ?sm |- _ ] => simplifyMem' x a H ls sm
      | [ |- context[msel (mupd ?m ?a (sz := ?sz) ?v) ?a' ?sz'] ] => doMupd m a sz v a' sz'
      | [ _ : context[msel (mupd ?m ?a (sz := ?sz) ?v) ?a' ?sz'] |- _ ] => doMupd m a sz v a' sz'
    end.

  Ltac ensureStars := match goal with
                        | [ |- stars _ _ ] => idtac
                      end.

  Ltac propSimpFwd := try tauto;
    repeat match goal with
             | [ H : True |- _ ] => clear H
             | [ H : ex _ |- _ ] => destruct H
             | [ H : _ /\ _ |- _ ] => destruct H
             | [ |- _ /\ _ ] => split
           end; try (tauto || (ensureStars; intuition auto)).

  Ltac propSimp := try tauto;
    repeat match goal with
             | [ H : True |- _ ] => clear H
             | [ H : ex _ |- _ ] => destruct H
             | [ H : _ /\ _ |- _ ] => destruct H
             | [ |- ex _ ] => esplit
             | [ |- _ /\ _ ] => split
           end; try (tauto || (ensureStars; intuition auto)).

  Ltac sepSimp'' := simpl in *; propSimpFwd; try subst.

  Ltac sepSimp' := sepSimp'';
    repeat match goal with
             | [ |- sep _ _ ] => hnf
             | [ H : sep _ _ |- _ ] => hnf in H
           end; sepSimp''.

  Ltac sepSimp := sepSimp'; repeat simplifyMem.

  Ltac sepSimpFull'' := simpl in *; propSimp; try subst.

  Ltac sepSimpFull' := sepSimpFull'';
    repeat match goal with
             | [ |- sep _ _ ] => hnf
             | [ H : sep _ _ |- _ ] => hnf in H
           end; sepSimpFull''.

  Inductive hide (P : Prop) := Hide : P -> hide P.
  Theorem hide_inv : forall P, hide P -> P.
    inversion 1; auto.
  Qed.

  Ltac propxFoHyps := apply hide_inv; propxFo; constructor.

  Ltac sepSimpFull := propxFoHyps; sepSimpFull'; repeat simplifyMem.

  Ltac mupdOut E :=
    match E with
      | _ ?m ?a ?v => constr:(m, a, v)
      | _ ?m ?a _ ?v => constr:(m, a, v)
    end.

(*
  Ltac ensureNoUnifs E :=
    match E with
      | context[?x] => match x with
                         | x => fail 1
                         | _ => fail 2
                       end
      | _ => idtac
    end.
*)

  Ltac equate x y := let H := fresh "H" in assert (H : x = y) by reflexivity; clear H.
  Ltac ensureEq x y := ensureNoUnifs x; ensureNoUnifs y; let H := fresh "H" in assert (H : x = y) by ( (*unfold M.addr, M.byte in *;*) solve [ auto ]); clear H.

  Ltac memsEq := intros;
    try (let a := fresh "a" in extensionality a);
      repeat (apply writeWord_mupd; [ solve [ auto ] | intros ]); auto;
      repeat rewrite msel_def; repeat rewrite mupd_def; unfold msel', mupd', writeWord, readWord (*, M.addr_eq *);
      trivial; intros; simpl;
      solve [ auto with memsEq ].

  Ltac matchPtsTo :=
    repeat match goal with
             | [ _ : stars ?ls1 ?m1 |- stars ?ls2 ?m2 ] =>
               let H := fresh "H" in assert (H : m1 = m2) by memsEq; clear H;
                 match ls2 with
                   | context[ptsTo ?a ?v] =>
                     match v with
                       | v => fail 1
                       | _ => match ls1 with
                                | context [ptsTo ?a' ?v'] =>
                                  match v' with
                                    | v => fail 1
                                    | _ => ensureEq a a'; equate v v'
                                  end
                              end
                     end
                 end
           end.

  Module Type UNFOLD.
    Parameter should_unfold : sprop -> Prop.

    Axiom should_unfold_any : forall p, should_unfold p.
  End UNFOLD.

  Module Unfold : UNFOLD.
    Definition should_unfold (_ : sprop) := True.

    Theorem should_unfold_any : forall p, should_unfold p.
      red; auto.
    Qed.
  End Unfold.

  Import Unfold.
  Export Unfold.

  Lemma should_unfold_emp : should_unfold emp.
    intros; apply should_unfold_any.
  Qed.

  Lemma should_unfold_pure : forall P, should_unfold (Pure P).
    intros; apply should_unfold_any.
  Qed.

  Lemma should_unfold_star : forall p1 p2, should_unfold (p1 * p2).
    intros; apply should_unfold_any.
  Qed.

  Lemma should_unfold_ex : forall T (p1 : T -> _), should_unfold (Exis p1).
    intros; apply should_unfold_any.
  Qed.

  Lemma should_unfold_sep : forall p, should_unfold !{p}.
    intros; apply should_unfold_any.
  Qed.

  Hint Immediate should_unfold_emp should_unfold_pure should_unfold_star should_unfold_ex should_unfold_sep : Forward Backward.

  Ltac unfolderF useDb :=
    match goal with
      | [ H : stars ?ls _ |- _ ] =>
        let rec loop pre post :=
          match eval hnf in post with
            | ?p :: ?post =>
              match p with
                | sep ?p' =>
                  (match p' with
                     | Pure ?P => apply (stars_elim_Pure P post (rev pre)) in H
                   end)
                  || (let H' := fresh "H" in assert (H' : should_unfold p'); [ solve [ eauto with Forward ] |
                    clear H'; apply (desep_fwd p' post (rev pre)) in H ])
                  || match goal with
                       | [ H' : ?P |- _ ] =>
                         match type of P with
                           | Prop => eapply (unfold_sep_fwd (p := p') post (rev pre)) in H; [ | eapply H'; solve [ eauto ] ]; clear H'
                         end
                     end
                  || (eapply (unfold_sep_fwd (p := p') post (rev pre)) in H; [ | solve [ useDb ] ]);
                  sepSimp
                | _ => loop (p :: pre) post
              end
          end in
          loop (@nil hprop) ls
    end.

  Ltac updater E :=
    try (let p := mupdOut E in
      match p with
        | (?m, ?a, ?v) => updater m;
          match goal with
            | [ H : stars ?ls _ |- _ ] =>
              let rec overwriter pre post :=
                match eval hnf in post with
                  | nil => idtac
                  | ptsTo ?a' (sz := ?sz) ?v' :: ?post => 
                    apply (overwrite (a := a') (a' := a) (sz := sz)
                      v' v post (rev pre)) in H;
                    [ | solve [ auto ] ]
                  | ?p :: ?post => overwriter (p :: pre) post
                end in
                overwriter (@nil hprop) ls
          end
      end).

  Ltac sepUpdate memOut :=
    match goal with
      | [ |- stars _ ?E ] => let m := memOut E in updater m; simpl in *; matchPtsTo
      | _ => matchPtsTo
    end.

  Ltac unfolderB :=
    match goal with
      | [ |- stars ?ls _ ] =>
        let rec loop pre post :=
          match eval hnf in post with
            | ?p :: ?post =>
              match p with
                | sep ?p' =>
                  (let H := fresh "H" in assert (H : should_unfold p'); [ solve [ auto with Backward ] |
                    clear H; apply (desep_bwd p' post (rev pre)) ])
                  || match goal with
                       | [ H : ?P |- _ ] =>
                         match type of P with
                           | Prop => eapply (unfold_sep_bwd (p' := p') post (rev pre)); [ clear H |
                             eapply H; clear H; solve [ eauto ] ]
                         end
                     end
                  || (eapply (unfold_sep_bwd (p' := p') post (rev pre)); [ |
                    solve [ eauto with Backward ] ]);
                  sepSimpFull
                | _ => loop (p :: pre) post
              end
          end in
          loop (@nil hprop) ls
    end.

  Ltac sepFwd1 := unfolderF ltac:(eauto with Forward); try autorewrite with InSep in *.
  Ltac sepFwd := repeat sepFwd1.

  Ltac sepBwd1 := unfolderB; repeat simplifyMem; matchPtsTo; try autorewrite with InSep in *.
  Ltac sepBwd := repeat sepBwd1.

  Theorem sep_cong : forall x y, x = y -> sep x = sep y.
    congruence.
  Qed.

  Ltac eqer := (* unfold M.addr;*) solve [ auto; repeat ((apply sep_cong || (progress f_equal)); auto) ].

  Ltac canceler :=
    repeat match goal with
             | _ => simple apply himp_refl
             | _ => simple apply frame_finish
             | [ |- ?ps1 ---> ?ps2 ] =>
               let rec loop1 pre1 post1 :=
                 match eval hnf in post1 with
                   | ?p1 :: ?post1 =>
                     let rec loop2 pre2 post2 :=
                       match eval hnf in post2 with
                         | ?p2 :: ?post2 =>
                            (ensureNotUnif p2; let Ht := fresh "Ht" in
                             generalize (himp_cancel_ptsTo (rev pre1) post1 (rev pre2) post2); intro Ht; simpl in Ht;
                               apply Ht; clear Ht; [ eqer | | (reflexivity || eauto) ])

                            || (ensureNotUnif p2; let Ht := fresh "Ht" in
                             generalize (himp_cancel_eq (rev pre1) post1 (rev pre2) post2); intro Ht; simpl in Ht;
                               apply Ht; clear Ht; [ eqer | ])
                           || loop2 (p2 :: pre2) post2
                       end in
                       loop2 (@nil hprop) ps2
                       || loop1 (p1 :: pre1) post1
                 end in
                 loop1 (@nil hprop) ps1
           end.
(*
    try match goal with
          | _ => simple apply himp_refl
          | _ => simple apply frame_finish
          | [ |- ?ps1 ---> ?ps2 ] =>
            let rec loop2 pre2 post2 ps1 :=
              match eval hnf in post2 with
                | ?p2 :: ?post2 => 
                  (ensureNotUnif p2;
                   let rec loop1 pre1 post1 :=
                     match eval hnf in post1 with
                       | ?p1 :: ?post1 => 
                         (let Ht := fresh "Ht" in
                          generalize (himp_cancel_eq (rev pre1) post1 (rev pre2) post2); intro Ht; simpl in Ht;
                          apply Ht; clear Ht; 
                          [ eqer | try (loop2 pre2 post2 (rev pre1 ++ post1)) ])
                         || loop1 (p1 :: pre1) post1
                    end
                  in loop1 (@nil hprop) ps1 || loop2 (p2 :: pre2) post2 ps1)
                  || loop2 (p2 :: pre2) post2 ps1
                end 
              in loop2 (@nil hprop) ps2 ps1
        end;
    try (simple apply himp_refl || simple apply frame_finish).
*)
  Ltac sepCancel := try apply stars_elim;
    try match goal with
          | [ H : sep _ _ |- _ ] => apply stars_intro in H
          | [ H : sep' _ _ |- _ ] => apply stars_intro in H
        end;
    try match goal with
          | [ H : stars _ _ |- _ ] => apply (stars_final _ H); [ memsEq | clear H; canceler ]
        end.


  Ltac sepLemma := unfold himp, Himp; intuition auto; sepSimp; auto; sepFwd; sepSimpFull; sepBwd; sepCancel.
  Ltac sep memOut tac := sepSimp; try autorewrite with InSep in *; sepFwd; tac; sepSimpFull;
    sepUpdate memOut; try autorewrite with InSep in *; sepBwd; tac; sepCancel.

  Hint Extern 2 (@eq nat _ _) => omega.
  Hint Extern 2 (not (@eq nat _ _)) => omega.

  Definition sempty : smem := fun _ => None.

  (** Himp Lemmas **)
  Lemma Himp_trans : forall a b c,
    (a ===> b) ->
    (b ===> c) ->
    (a ===> c).
  Proof.
    unfold Himp. firstorder.
  Qed.
  Lemma Himp_elim_guard_r : forall s s',
    s ===> s' ->
    s ===> !{s'}.
  Proof.
    sepLemma. rewrite stars_def in H0. simpl in H0. unfold star in H0. destruct H0.
    destruct H0. intuition. unfold sep in H0.
    eapply sep'_weaken. eapply H0. intros. simpl in *. intuition.
    rewrite stars_def in *. eapply stars'_app_bwd. eauto. eauto. auto.
  Qed.
  Lemma Himp_intro_guard_r : forall s s',
    s ===> !{s'} ->
    s ===> s'.
  Proof.
    sepLemma. unfold himp. intros. rewrite stars_def in *. simpl in *.
    unfold star in *. do 2 destruct H0. intuition. do 2 eexists. eapply H in H0.
    split. 2: split. 3: eassumption. eassumption. clear H. unfold sep in *.
    simpl in H0. destruct H0. rewrite stars_def in H0. simpl in H0. unfold star in H0.
    destruct H0. destruct H0. destruct H0. destruct H2. 
    eapply sep'_weaken. eapply H2. intros. simpl in *; intuition.
    rewrite <- (app_nil_r ps). rewrite stars_def. eapply stars'_app_bwd. eauto. eauto. eauto.
  Qed.
  Lemma Himp_elim_guard_l : forall s s',
    s ===> s' ->
    !{s} ===> s'.
  Proof.
    sepLemma. rewrite stars_def in *. simpl in *. unfold star in *. 
    eapply sep'_ex in H1. destruct H1. destruct H0. simpl in *; intuition.
    eapply stars'_app_fwd in H3. destruct H3. destruct H0.
    do 2 eexists; intuition. eassumption. eapply H2; eauto. rewrite stars_def. auto.
    simpl in H6. auto.
  Qed.
  Lemma Himp_intro_guard_l : forall s s',
    (!{s} ===> s') ->
    (s ===> s').
  Proof.
    sepLemma. unfold himp. intros. rewrite stars_def in *. simpl in *.
    unfold star in *. do 2 destruct H0. intuition. do 2 eexists. intuition; try eassumption.
    eapply H.  clear H.
    unfold sep in *. simpl in *. intuition. 
    eapply sep'_ex in H0. destruct H0. destruct H. simpl in *. intuition.
    change ((fun sm1 : smem =>
       sep' s (fun (P : Prop) (ps : list hprop) => P /\ stars ps sm1))) with (sep s).
    eapply stars_intro. eauto.
  Qed.
  Lemma Himp_split : forall s s' s'' s''',
    s ===> s' ->
    s'' ===> s''' ->
    s * s'' ===> s' * s'''.
  Proof.
    unfold Himp. intros. unfold sep in *. simpl in *. 
    repeat match goal with 
             | [ H : exists x , _ |- _ ] => destruct H
             | [ H : _ /\ _ |- _ ] => destruct H
             | [ H : sep' _ _ |- _ ] => eapply sep'_ex in H
           end.
    rewrite stars_def in H4.
    eapply stars'_app_fwd in H4. destruct H4; destruct H4. intuition.
    rewrite <- stars_def in *.
    specialize (H3 _ H5 H8). specialize (H2 _ H1 H4).
    unfold sep in *. eapply H in H2. eapply H0 in H3.
    eapply sep'_weaken. eassumption. intros. simpl in *. eapply sep'_weaken. eassumption.
    simpl. intros. intuition. rewrite stars_def in *. eapply stars'_app_bwd; eauto. 
  Qed.


End Make.
