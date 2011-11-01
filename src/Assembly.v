(** Certified assembly language packages *)

Require Import List String TheoryList.
Require Import PropX Machine.

Set Implicit Arguments.


Section AllS.
  Variable A : Type.
  Variable P : A -> Prop.

  Theorem AllS_app : forall ls2, AllS P ls2
    -> forall ls1, AllS P ls1
      -> AllS P (ls1 ++ ls2).
    induction 2; simpl; intuition.
  Qed.
End AllS.

Section AllS_map.
  Variables A B : Type.
  Variable f : A -> B.
  Variable P : A -> Prop.
  Variable P' : B -> Prop.

  Hypothesis P_f : forall x, P x -> P' (f x).

  Theorem AllS_map : forall ls, AllS P ls -> AllS P' (map f ls).
    induction 1; simpl; intuition.
  Qed.
End AllS_map.

Section Machine.
  Variables pc state block : Type.
  Variable step : block -> state -> pc -> state -> Prop.
  Variable pc_eq : forall x y : pc, {x = y} + {x <> y}.

  Section labelT.
    Variable labelT : Type.

    Inductive label : Type :=
    | Global : string -> label
    | Local : labelT -> label.

    Definition layout := label -> pc.
    Definition injective (lo : layout) := forall L1 L2, lo L1 = lo L2 -> L1 = L2.

    Record import := Imp {
      ILabel : string;
      ISpec : spec pc state
    }.

    Record local := Loc {
      LLabel : labelT;
      LSpec : spec pc state;
      LBlock : layout -> block
    }.

    Record export := Exp {
      ELabel : string;
      ESpec : spec pc state;
      EBlock : layout -> block
    }.
  End labelT.

  Implicit Arguments Global [labelT].

  Record module := Mod {
    LabelT : Type;
    Imports : list import;
    Locals : list (local LabelT);
    Exports : list (export LabelT)
  }.

  Section module.
    Variable m : module.

    Section lo.
      Variable lo : layout (LabelT m).

      Section i.
        Variable i : pc.

        Fixpoint specOfI (Is : list import) : option (spec pc state) :=
          match Is with
            | nil => None
            | Imp L p :: Is' => if pc_eq i (lo (Global L)) then Some p else specOfI Is'
          end.
        
        Fixpoint specOfL (Ls : list (local (LabelT m))) : option (spec pc state) :=
          match Ls with
            | nil => None
            | Loc L p _ :: Ls' => if pc_eq i (lo (Local L)) then Some p else specOfL Ls'
          end.

        Fixpoint specOfE (Es : list (export (LabelT m))) : option (spec pc state) :=
          match Es with
            | nil => None
            | Exp L p _ :: Es' => if pc_eq i (lo (Global L)) then Some p else specOfE Es'
          end.

        Definition specOf := match specOfI (Imports m) with
                               | None => match specOfL (Locals m) with
                                           | None => specOfE (Exports m)
                                           | x => x
                                         end
                               | x => x
                             end.

        Fixpoint blockOfL (Ls : list (local (LabelT m))) : option block :=
          match Ls with
            | nil => None
            | Loc L _ b :: Ls' => if pc_eq i (lo (Local L)) then Some (b lo) else blockOfL Ls'
          end.

        Fixpoint blockOfE (Es : list (export (LabelT m))) : option block :=
          match Es with
            | nil => None
            | Exp L _ b :: Es' => if pc_eq i (lo (Global L)) then Some (b lo) else blockOfE Es'
          end.

        Definition blockOf := match blockOfL (Locals m) with
                                | None => blockOfE (Exports m)
                                | x => x
                              end.
      End i.

      Definition assemble := Bedrock.Machine.Mod blockOf specOf.

      Record blockOk (p : spec pc state) (b : block) : Prop := {
        Progress : forall specs, mIncl specOf specs
          -> forall s, interp specs (p s)
            -> exists i', exists s', step b s i' s';
        Preservation : forall specs, mIncl specOf specs
          -> forall s, interp specs (p s)
            -> forall i' s', step b s i' s'
              -> exists p', specs i' = Some p' /\ interp specs (p' s')
      }.

      Record blocksOk : Prop := {
        LocalsOk : AllS (fun L => blockOk (LSpec L) (LBlock L lo)) (Locals m);
        ExportsOk : AllS (fun L => blockOk (ESpec L) (EBlock L lo)) (Exports m)
      }.
    End lo.

    Record moduleOk : Prop := {
      NoDupsL : forall L1 L2, In L1 (Locals m) -> In L2 (Locals m) -> LLabel L1 = LLabel L2 -> L1 = L2;
      NoDupsE : forall E1 E2, In E1 (Exports m) -> In E2 (Exports m) -> ELabel E1 = ELabel E2 -> E1 = E2;
      BlocksOk : forall lo, injective lo -> blocksOk lo
    }.

    Variable lo : layout (LabelT m).
    Hypothesis lo_injective : injective lo.

    Ltac specOf_inclusion :=
      let x := fresh "x" in intros ? x; induction x as [| []]; simpl; intuition;
        match goal with
          | [ |- context[if ?E then Some _ else _ ] ] => destruct E
        end; eauto.

    Lemma specOfI_inclusion : forall i Is,
      match specOfI lo i Is with
        | Some p => exists v, i = lo (Global v) /\ In (Imp v p) Is
        | None => True
      end.
      specOf_inclusion.
      destruct (specOfI lo i x); firstorder.
    Qed.

    Lemma specOfL_inclusion : forall i Ls,
      match blockOfL lo i Ls with
        | Some _ => (exists p, specOfL lo i Ls = Some p)
          /\ (exists v, i = lo (Local v))
        | None => specOfL lo i Ls = None
      end.
      specOf_inclusion.
    Qed.

    Lemma specOfE_inclusion : forall i Es,
      match blockOfE lo i Es with
        | Some _ => (exists p, specOfE lo i Es = Some p)
          /\ (exists s, i = lo (Global s))
        | None => specOfE lo i Es = None
      end.
      specOf_inclusion.
    Qed.

    Lemma assemble_Inclusion : forall i b,
      Blocks (assemble lo) i = Some b
      -> exists p, Specs (assemble lo) i = Some p.
      simpl; unfold blockOf, specOf; intros.
      specialize (specOfI_inclusion i (Imports m)); destruct (specOfI lo i (Imports m)); intuition eauto.
      specialize (specOfL_inclusion i (Locals m)); destruct (blockOfL lo i (Locals m)); firstorder.
      rewrite H1; eauto.
      rewrite H1.
      specialize (specOfE_inclusion i (Exports m)); destruct (blockOfE lo i (Exports m)); firstorder.
      discriminate.
    Qed.

    Ltac specOf_inclusion' :=
      induction 1 as [| []]; simpl; intuition;
        match goal with
          | [ |- context[if ?E then Some _ else _ ] ] => destruct E
        end; eauto.

    Lemma specOfL_inclusion' : forall i Ls,
      AllS (fun L => blockOk lo (LSpec L) (LBlock L lo)) Ls
      -> match blockOfL lo i Ls with
           | Some b => (exists p, specOfL lo i Ls = Some p /\ blockOk lo p b)
             /\ (exists v, i = lo (Local v))
           | None => specOfL lo i Ls = None
         end.
      specOf_inclusion'.
    Qed.

    Lemma specOfE_inclusion' : forall i Es,
      AllS (fun E => blockOk lo (ESpec E) (EBlock E lo)) Es
      -> match blockOfE lo i Es with
           | Some b => (exists p, specOfE lo i Es = Some p /\ blockOk lo p b)
             /\ (exists s, i = lo (Global s))
           | None => specOfE lo i Es = None
         end.
      specOf_inclusion'.
    Qed.

    Hypothesis mOk : moduleOk.

    Hypothesis Hclosed : Imports m = nil.

    Lemma assemble_Progress : forall i b p, Blocks (assemble lo) i = Some b -> Specs (assemble lo) i = Some p
      -> forall specs, mIncl (Specs (assemble lo)) specs
        -> forall s, interp specs (p s)
          -> exists i', exists s', step b s i' s'.
      simpl; intros.
      unfold blockOf in H.
      unfold specOf in H0.
      specialize (specOfI_inclusion i (Imports m)); destruct (specOfI lo i (Imports m)); intuition eauto.

      rewrite Hclosed in H3; firstorder.

      specialize (specOfL_inclusion' i (LocalsOk (BlocksOk mOk lo_injective)));
        destruct (blockOfL lo i (Locals m)); intuition.
      destruct H5; destruct H6; intuition; subst.
      rewrite H6 in H0.
      injection H; clear H; intro; subst.
      injection H0; clear H0; intro; subst.
      eapply (Progress H7); eauto.

      rewrite H4 in H0.

      specialize (specOfE_inclusion' i (ExportsOk (BlocksOk mOk lo_injective))); rewrite H; intuition.
      destruct H6; destruct H7; intuition; subst.
      rewrite H0 in H7; injection H7; clear H7; intro; subst.
      eapply (Progress H8); eauto.
    Qed.

    Lemma assemble_Preservation : forall i b p, Blocks (assemble lo) i = Some b -> Specs (assemble lo) i = Some p
      -> forall specs, mIncl (Specs (assemble lo)) specs
        -> forall s, interp specs (p s)
          -> forall i' s', step b s i' s'
            -> exists p', specs i' = Some p' /\ interp specs (p' s').
      simpl; intros.
      unfold blockOf in H.
      unfold specOf in H0.
      specialize (specOfI_inclusion i (Imports m)); destruct (specOfI lo i (Imports m)); intuition eauto.

      rewrite Hclosed in H4; firstorder.

      specialize (specOfL_inclusion' i (LocalsOk (BlocksOk mOk lo_injective)));
        destruct (blockOfL lo i (Locals m)); intuition.
      destruct H6; destruct H7; intuition; subst.
      rewrite H7 in H0.
      injection H; clear H; intro; subst.
      injection H0; clear H0; intro; subst.
      eapply (Preservation H8); eauto.

      rewrite H5 in H0.

      specialize (specOfE_inclusion' i (ExportsOk (BlocksOk mOk lo_injective))); rewrite H; intuition.
      destruct H7; destruct H8; intuition; subst.
      rewrite H0 in H8; injection H8; clear H8; intro; subst.
      eapply (Preservation H9); eauto.
    Qed.
      
    Theorem assembleOk : Machine.moduleOk step (assemble lo).
      split.

      apply assemble_Inclusion.

      apply assemble_Progress.

      apply assemble_Preservation.
    Qed.

    Theorem safety : forall i p, specOf lo i = Some p
      -> forall s, interp (specOf lo) (p s)
        -> safe step (assemble lo) i s.
      intros; eapply safety; eauto.
      apply assembleOk.
      simpl in *.
      intros.
      unfold specOf in H1.
      unfold blockOf.
      rewrite Hclosed in H1; simpl in H1.
      specialize (specOfL_inclusion i0 (Locals m)); destruct (blockOfL lo i0 (Locals m)); intuition eauto.
      rewrite H2 in H1.
      specialize (specOfE_inclusion i0 (Exports m)); destruct (blockOfE lo i0 (Exports m)); intuition eauto.
      congruence.
    Qed.

  End module.

  Fixpoint amongExports T (s : string) (Es : list (export T)) : bool :=
    match Es with
      | nil => false
      | Exp s' _ _ :: Es' => if string_dec s' s then true else amongExports s Es'
    end.

  Definition thinImports T (Es : list (export T)) (Is : list import) : list import :=
    filter (fun i => negb (amongExports (ILabel i) Es)) Is.

  Section link.
    Variables m1 m2 : module.

    Section layouts.
      Variable lo : layout (LabelT m1 + LabelT m2).

      Definition lo1 : layout (LabelT m1) := fun L =>
        lo (match L with
              | Global s => Global s
              | Local v => Local (inl _ v)
            end).

      Definition lo2 : layout (LabelT m2) := fun L =>
        lo (match L with
              | Global s => Global s
              | Local v => Local (inr _ v)
            end).

      Theorem lo1_injective : injective lo -> injective lo1.
        unfold injective, lo1; intros H L1 L2 H0; destruct L1; destruct L2;
          specialize (H _ _ H0); congruence.
      Qed.

      Theorem lo2_injective : injective lo -> injective lo2.
        unfold injective, lo2; intros H L1 L2 H0; destruct L1; destruct L2;
          specialize (H _ _ H0); congruence.
      Qed.
    End layouts.

    Definition link : module := Mod (LabelT := LabelT m1 + LabelT m2)
      (thinImports (Exports m2) (Imports m1)
        ++ thinImports (Exports m1) (Imports m2))
      (map (fun L => Loc (inl _ (LLabel L)) (LSpec L) (fun lo => LBlock L (lo1 lo))) (Locals m1)
        ++ map (fun L => Loc (inr _ (LLabel L)) (LSpec L) (fun lo => LBlock L (lo2 lo))) (Locals m2))
      (map (fun E => Exp (ELabel E) (ESpec E) (fun lo => EBlock E (lo1 lo))) (Exports m1)
        ++ map (fun E => Exp (ELabel E) (ESpec E) (fun lo => EBlock E (lo2 lo))) (Exports m2)).

    Hypothesis imports_agree : forall I1 I2,
      In I1 (Imports m1)
      -> In I2 (Imports m2)
      -> ILabel I1 = ILabel I2
      -> I1 = I2.

    Hypothesis exports_noDup1 : forall E1 E2,
      In E1 (Exports m1)
      -> In E2 (Exports m1)
      -> ELabel E1 = ELabel E2
      -> ESpec E1 = ESpec E2.

    Hypothesis exports_noDup2 : forall E1 E2,
      In E1 (Exports m2)
      -> In E2 (Exports m2)
      -> ELabel E1 = ELabel E2
      -> ESpec E1 = ESpec E2.

    Hypothesis exports_unique : forall E1 E2,
      In E1 (Exports m1)
      -> In E2 (Exports m2)
      -> ELabel E1 <> ELabel E2.

    Hypothesis imports_exports_agree1 : forall I E,
      In I (Imports m1)
      -> In E (Exports m2)
      -> ILabel I = ELabel E
      -> ISpec I = ESpec E.

    Hypothesis imports_exports_agree2 : forall I E,
      In I (Imports m2)
      -> In E (Exports m1)
      -> ILabel I = ELabel E
      -> ISpec I = ESpec E.

    Hypothesis imports_exports_disjoint1 : forall I E,
      In I (Imports m1)
      -> In E (Exports m1)
      -> ILabel I <> ELabel E.

    Hypothesis imports_exports_disjoint2 : forall I E,
      In I (Imports m2)
      -> In E (Exports m2)
      -> ILabel I <> ELabel E.

    Lemma specOf_Imports : forall lo (Hinj : injective lo) T1 T2 i
      (Es2 : list (export T1)) (Es1 : list (export T2)) Is2 Is1,
      (forall I1 I2, In I1 Is1
        -> In I2 Is2
        -> ILabel I1 = ILabel I2
        -> I1 = I2)
      -> match specOfI m2 (lo2 lo) i Is2 with
           | Some p => exists s, i = lo (Global s)
             /\ (amongExports s Es1 = false
               -> specOfI link lo i (thinImports Es2 Is1 ++
                 thinImports Es1 Is2) = Some p)
           | None => True
         end.
      induction Is1 as [ | []]; simpl; intuition.

      induction Is2 as [ | []]; simpl; intuition.
      match type of IHIs2 with
        | ?P -> _ => assert P by tauto; intuition
      end.
      destruct (pc_eq i (lo2 lo (Global ILabel0))); subst.
      
      unfold lo2.
      eexists; intuition eauto 1.
      rewrite H2; simpl.
      destruct (pc_eq (lo (Global ILabel0)) (lo (Global ILabel0))); intuition.

      destruct (specOfI m2 (lo2 lo) i Is2); auto.
      destruct H1; intuition; subst.
      eexists; intuition eauto 1.
      intuition.
      case_eq (amongExports ILabel0 Es1); intro Heq; simpl; auto.
      destruct (pc_eq (lo (Global x)) (lo (Global ILabel0))); intuition.

      match type of IHIs1 with
        | ?P -> _ => assert P by auto; intuition
      end.

      generalize (specOfI_inclusion m2 (lo2 lo) i Is2).
      destruct (specOfI m2 (lo2 lo) i Is2); auto.
      destruct H1; intuition; subst.
      destruct H2; intuition; subst.
      unfold lo2 in H2.
      generalize (Hinj _ _ H2); injection 1; intro; subst.
      specialize (H _ _ (or_introl _ (refl_equal _)) H3); simpl in H.
      eexists; intuition eauto 1.
      intuition.
      case_eq (amongExports ILabel0 Es2); intro Heq; simpl; auto.
      destruct (pc_eq (lo (Global x0)) (lo (Global ILabel0))); auto.
      specialize (Hinj _ _ e).
      injection Hinj; intuition.
      specialize (H (sym_eq H4)); congruence.
    Qed.

    Lemma specOf_Imports2 : forall lo (Hinj : injective lo) i,
      match specOfI m2 (lo2 lo) i (Imports m2) with
        | Some p => exists s, i = lo (Global s)
          /\ (amongExports s (Exports m1) = false
            -> specOfI link lo i (thinImports (Exports m2) (Imports m1) ++
              thinImports (Exports m1) (Imports m2)) = Some p)
        | None => True
      end.
      intros; apply specOf_Imports; auto.
    Qed.

    Lemma specOf_Locals2 : forall lo (Hinj : injective lo) i,
      match specOfL m2 (lo2 lo) i (Locals m2) with
        | Some p => exists v, i = lo (Local (inr _ v))
          /\ specOfL link lo i
          (map (fun L => Loc (inl _ (LLabel L)) (LSpec L) (fun lo => LBlock L (lo1 lo))) (Locals m1)
            ++ map (fun L => Loc (inr _ (LLabel L)) (LSpec L) (fun lo => LBlock L (lo2 lo))) (Locals m2)) = Some p
        | None => True
      end.
      induction (Locals m1) as [ | []]; simpl; intuition.

      induction (Locals m2) as [ | []]; simpl; intuition.

      change (lo2 lo (Local LLabel0)) with (lo (Local (inr _ LLabel0))).
      match goal with
        | [ |- context[if ?E then Some _ else _ ] ] => destruct E
      end; subst; eauto.

      specialize (IHl _ Hinj i).
      destruct (specOfL m2 (lo2 lo) i (Locals m2)); auto.
      destruct IHl; intuition; subst.
      eexists; intuition eauto 1.
      match goal with
        | [ |- context[if ?E then Some _ else _ ] ] => destruct E
      end; intuition.

      specialize (Hinj _ _ e); discriminate.
    Qed.

    Lemma specOfE_In : forall m lo (Hinj : injective lo) x s Es,
      specOfE m lo (lo (Global x)) Es = Some s
      -> exists E, In E Es /\ ELabel E = x.
      induction Es as [ | []]; simpl; intuition; try discriminate.
      destruct (pc_eq (lo (Global x)) (lo (Global ELabel0))).

      specialize (Hinj _ _ e); injection Hinj; clear Hinj; intro; subst; eauto.

      firstorder.
    Qed.

    Lemma specOf_Exports2 : forall lo (Hinj : injective lo) i,
      match specOfE m2 (lo2 lo) i (Exports m2) with
        | Some p => exists s, i = lo (Global s)
          /\ specOfE link lo i
          (map (fun E => Exp (ELabel E) (ESpec E) (fun lo => EBlock E (lo1 lo))) (Exports m1)
            ++ map (fun E => Exp (ELabel E) (ESpec E) (fun lo => EBlock E (lo2 lo))) (Exports m2)) = Some p
        | None => True
      end.
      clear exports_noDup1 exports_noDup2 imports_exports_agree1 imports_exports_agree2
        imports_exports_disjoint1 imports_exports_disjoint2.

      intros; induction (Exports m1) as [ | []]; simpl; intuition.

      induction (Exports m2) as [ | []]; simpl; intuition.
      
      match type of IHl with
        | ?P -> _ => assert P by auto; intuition
      end.
      change (lo2 lo (Global ELabel0)) with (lo (Global ELabel0)).
      match goal with
        | [ |- context[if ?E then Some _ else _ ] ] => destruct E
      end; eauto.

      simpl in *.
      match type of IHl with
        | ?P -> _ => assert P by eauto; intuition
      end.
      case_eq (specOfE m2 (lo2 lo) i (Exports m2)); auto.
      intros ? Heq.
      rewrite Heq in H0.
      destruct H0; intuition; subst.
      eexists; intuition eauto 1.
      match goal with
        | [ |- context[if ?E then Some _ else _ ] ] => destruct E
      end; auto.
      destruct (specOfE_In _ (lo2_injective Hinj) _ _ Heq); intuition; subst.
      specialize (Hinj _ _ e); injection Hinj; clear Hinj; intro; subst.
      elimtype False; eauto.
    Qed.

    Lemma amongExports_In : forall T x (Es : list (export T)),
      amongExports x Es = true
      -> exists E, In E Es /\ ELabel E = x.
      induction Es as [| []]; simpl; intuition.
      discriminate.
      destruct (string_dec ELabel0 x); subst; eauto.
      intuition.
      firstorder.
    Qed.

    Lemma amongExports_notIn : forall T x (Es : list (export T)),
      amongExports x Es = false
      -> forall E, In E Es
        -> ELabel E = x
        -> False.
      induction Es as [| []]; simpl; intuition; subst; simpl in *.
      destruct (string_dec ELabel0 ELabel0); subst; try discriminate; intuition.
      destruct (string_dec ELabel0 (ELabel E)); subst; try discriminate; intuition eauto.
    Qed.

    Lemma dropped_import2 : forall lo (Hinj : injective lo)
      x T1 (Es1 : list (export T1)) T2 (Es2 : list (export T2)) Is2 Is1,
      (forall I E, In I Is1
        -> In E Es1
        -> ILabel I <> ELabel E)
      -> amongExports x Es1 = true
      -> specOfI link lo (lo (Global x)) (thinImports Es2 Is1 ++ thinImports Es1 Is2) = None.
      induction Is1 as [| []]; simpl; intuition.

      induction Is2 as [| []]; simpl; intuition.
      case_eq (amongExports ILabel0 Es1); intro Heq; simpl; auto.
      match goal with
        | [ |- context[if ?E then Some _ else _ ] ] => destruct E; auto
      end.
      specialize (Hinj _ _ e); congruence.
      
      case_eq (amongExports ILabel0 Es2); intro Heq; simpl; eauto.
      match goal with
        | [ |- context[if ?E then Some _ else _ ] ] => destruct E; eauto
      end.
      destruct (amongExports_In _ _ H0); intuition.
      subst.
      specialize (Hinj _ _ e); injection Hinj; clear Hinj; intro; subst.
      elimtype False; eauto.
    Qed.

    Lemma specOfL_Global : forall m lo (Hinj : injective lo) x Ls,
      specOfL m lo (lo (Global x)) Ls = None.
      induction Ls as [| []]; simpl; intuition.
      match goal with
        | [ |- context[if ?E then Some _ else _ ] ] => destruct E; eauto
      end.
      specialize (Hinj _ _ e); discriminate.
    Qed.

    Lemma specOfI_Local : forall m lo (Hinj : injective lo) x Ls,
      specOfI m lo (lo (Local x)) Ls = None.
      induction Ls as [| []]; simpl; intuition.
      match goal with
        | [ |- context[if ?E then Some _ else _ ] ] => destruct E; eauto
      end.
      specialize (Hinj _ _ e); discriminate.
    Qed.

    Theorem specOf_link2 : forall lo (Hinj : injective lo),
      mIncl (specOf m2 (lo2 lo)) (specOf link lo).
      unfold mIncl, specOf; simpl; intros.

      specialize (specOf_Imports2 Hinj i).
      specialize (specOfI_inclusion m2 (lo2 lo) i (Imports m2)).
      destruct (specOfI m2 (lo2 lo) i (Imports m2)); intros.

      (* It's an import. *)

      destruct H0; intuition; subst.
      destruct H1; intuition; subst.
      unfold lo2 in H1.
      generalize (Hinj _ _ H1); clear H1; injection 1; intro; subst.
      injection H; clear H; intro; subst.
      change (lo2 lo (Global x0)) with (lo (Global x0)).
      change (lo2 lo (Global x0)) with (lo (Global x0)) in H2.
      case_eq (amongExports x0 (Exports m1)); intro Heq.

      2: destruct (specOfI link lo (lo (Global x0))
        (thinImports (Exports m2) (Imports m1) ++
          thinImports (Exports m1) (Imports m2))); intuition congruence.

      rewrite dropped_import2 by auto.
      rewrite specOfL_Global by auto.
      destruct (amongExports_In _ _ Heq); intuition; subst.
      specialize (imports_exports_agree2 _ _ H3 H1 (refl_equal _)).
      simpl in imports_exports_agree2; subst.

      generalize H1 exports_noDup1 Hinj; repeat match goal with
                                                  | [ x : _ |- _ ] => clear x
                                                end.
      destruct x; simpl in *.
      induction (Exports m1) as [ | []]; simpl; intuition; subst; simpl.
      injection H; clear H; intros; subst.
      match goal with
        | [ |- context[if ?E then Some _ else _ ] ] => destruct E; intuition
      end.
      
      match goal with
        | [ |- context[if ?E then Some _ else _ ] ] => destruct E; auto
      end.
      specialize (Hinj _ _ e); clear e; injection Hinj; clear Hinj; intro; subst.
      specialize (exports_noDup1 _ _ (or_introl _ (refl_equal _)) (or_intror _ H) (refl_equal _)).
      simpl in exports_noDup1; congruence.

      specialize (specOf_Locals2 Hinj i).
      specialize (specOfL_inclusion m2 (lo2 lo) i (Locals m2)).
      destruct (specOfL m2 (lo2 lo) i (Locals m2)); intros.

      (* It's a local. *)
      destruct (blockOfL m2 (lo2 lo) i (Locals m2)); intuition; try discriminate.
      destruct H4; destruct H5; subst.
      injection H2; clear H2; intro; subst.
      injection H; clear H; intro; subst.
      change (lo2 lo (Local x0)) with (lo (Local (inr _ x0))).
      rewrite specOfI_Local by auto.
      destruct H3; intuition.
      unfold lo2 in H2; specialize (Hinj _ _ H2); injection Hinj; clear Hinj; intros; subst.
      change (lo2 lo (Local x)) with (lo (Local (inr _ x))) in H3.
      rewrite H3; reflexivity.

      specialize (specOf_Exports2 Hinj i).
      specialize (specOfE_inclusion m2 (lo2 lo) i (Exports m2)).
      rewrite H.
      
      (* It's an export. *)
      destruct (blockOfE m2 (lo2 lo) i (Exports m2)); try discriminate; intuition.
      destruct H6; destruct H7; subst.
      injection H4; clear H4; intro; subst.
      destruct H5; intuition.
      generalize (Hinj _ _ H5); injection 1; intro; subst.
      change (lo2 lo (Global x1)) with (lo (Global x1)).
      change (lo2 lo (Global x1)) with (lo (Global x1)) in H6.
      rewrite H6; clear H6.
      rewrite specOfL_Global by auto.
      generalize H imports_exports_disjoint2 Hinj; repeat match goal with
                                                            | [ x : _ |- _ ] => clear x
                                                          end.
      induction (Imports m1) as [ | []]; simpl; intuition.
      induction (Imports m2) as [ | []]; simpl; intuition.
      simpl in *.
      match type of IHl with
        | ?P -> _ => assert P by eauto; intuition
      end.
      case_eq (amongExports ILabel0 (Exports m1)); intro Heq; simpl; auto.
      match goal with
        | [ |- context[if ?E then Some _ else _ ] ] => destruct E
      end; auto.
      generalize (Hinj _ _ e); injection 1; intro; subst.
      destruct (specOfE_In _ (lo2_injective Hinj) _ _ H); intuition; subst.
      elimtype False; eauto.

      case_eq (amongExports ILabel0 (Exports m2)); intro Heq; simpl; auto.
      match goal with
        | [ |- context[if ?E then Some _ else _ ] ] => destruct E
      end; auto.
      generalize (Hinj _ _ e); injection 1; intro; subst.
      specialize (amongExports_notIn _ Heq); intro.
      destruct (specOfE_In _ (lo2_injective Hinj) _ _ H); intuition.
      elimtype False; eauto.

(*      discriminate. *)
    Qed.

    Lemma specOf_Imports1' : forall lo (Hinj : injective lo) T1 T2 i
      (Es2 : list (export T1)) (Es1 : list (export T2)) Is2 Is1,
      (forall I1 I2, In I1 Is1
        -> In I2 Is2
        -> ILabel I1 = ILabel I2
        -> I1 = I2)
      -> match specOfI m1 (lo1 lo) i Is1 with
           | Some p => exists s, i = lo (Global s)
             /\ (amongExports s Es2 = false
               -> specOfI link lo i (thinImports Es2 Is1 ++
                 thinImports Es1 Is2) = Some p)
           | None => True
         end.
      induction Is1 as [ | []]; simpl; intuition.

      match type of IHIs1 with
        | ?P -> _ => assert P by auto; intuition
      end.
      destruct (pc_eq i (lo1 lo (Global ILabel0))); subst.
      
      unfold lo1.
      eexists; intuition eauto 1.
      rewrite H2; simpl.
      destruct (pc_eq (lo (Global ILabel0)) (lo (Global ILabel0))); intuition.

      destruct (specOfI m1 (lo1 lo) i Is1); auto.
      destruct H1; intuition; subst.
      eexists; intuition eauto 1.
      intuition.
      case_eq (amongExports ILabel0 Es2); intro Heq; simpl; auto.
      destruct (pc_eq (lo (Global x)) (lo (Global ILabel0))); intuition.
    Qed.

    Lemma specOf_Imports1 : forall lo (Hinj : injective lo) i,
      match specOfI m1 (lo1 lo) i (Imports m1) with
        | Some p => exists s, i = lo (Global s)
          /\ (amongExports s (Exports m2) = false
            -> specOfI link lo i (thinImports (Exports m2) (Imports m1) ++
              thinImports (Exports m1) (Imports m2)) = Some p)
        | None => True
      end.
      intros; apply specOf_Imports1'; auto.
    Qed.

    Lemma dropped_import1 : forall lo (Hinj : injective lo)
      x T1 (Es1 : list (export T1)) T2 (Es2 : list (export T2)) Is2 Is1,
      (forall I E, In I Is2
        -> In E Es2
        -> ILabel I <> ELabel E)
      -> amongExports x Es2 = true
      -> specOfI link lo (lo (Global x)) (thinImports Es2 Is1 ++ thinImports Es1 Is2) = None.
      induction Is1 as [| []]; simpl; intuition.

      induction Is2 as [| []]; simpl; intuition.
      case_eq (amongExports ILabel0 Es1); intro Heq; simpl in *; eauto.
      match goal with
        | [ |- context[if ?E then Some _ else _ ] ] => destruct E; eauto
      end.
      generalize (Hinj _ _ e); injection 1; intro; subst.
      destruct (amongExports_In _ _ H0); intuition; subst.
      elimtype False; eauto.

      case_eq (amongExports ILabel0 Es2); intro Heq; simpl; eauto.
      match goal with
        | [ |- context[if ?E then Some _ else _ ] ] => destruct E; eauto
      end.
      destruct (amongExports_In _ _ H0); intuition; subst.
      specialize (Hinj _ _ e); injection Hinj; clear Hinj; intro; subst.
      congruence.
    Qed.

    Lemma specOf_Locals1 : forall lo (Hinj : injective lo) i,
      match specOfL m1 (lo1 lo) i (Locals m1) with
        | Some p => exists v, i = lo (Local (inl _ v))
          /\ specOfL link lo i
          (map (fun L => Loc (inl _ (LLabel L)) (LSpec L) (fun lo => LBlock L (lo1 lo))) (Locals m1)
            ++ map (fun L => Loc (inr _ (LLabel L)) (LSpec L) (fun lo => LBlock L (lo2 lo))) (Locals m2)) = Some p
        | None => True
      end.
      intros; induction (Locals m1) as [ | []]; simpl; intuition.

      change (lo1 lo (Local LLabel0)) with (lo (Local (inl _ LLabel0))).
      match goal with
        | [ |- context[if ?E then Some _ else _ ] ] => destruct E
      end; subst; eauto.
    Qed.

    Lemma specOf_Exports1 : forall lo (Hinj : injective lo) i,
      match specOfE m1 (lo1 lo) i (Exports m1) with
        | Some p => exists s, i = lo (Global s)
          /\ specOfE link lo i
          (map (fun E => Exp (ELabel E) (ESpec E) (fun lo => EBlock E (lo1 lo))) (Exports m1)
            ++ map (fun E => Exp (ELabel E) (ESpec E) (fun lo => EBlock E (lo2 lo))) (Exports m2)) = Some p
        | None => True
      end.
      clear imports_agree exports_noDup1 exports_noDup2 exports_unique imports_exports_agree1 imports_exports_agree2
        imports_exports_disjoint1 imports_exports_disjoint2.

      intros; induction (Exports m1) as [ | []]; simpl; intuition.

      change (lo1 lo (Global ELabel0)) with (lo (Global ELabel0)).      
      match goal with
        | [ |- context[if ?E then Some _ else _ ] ] => destruct E
      end; eauto.
    Qed.

    Theorem specOf_link1 : forall lo (Hinj : injective lo),
      mIncl (specOf m1 (lo1 lo)) (specOf link lo).

      unfold mIncl, specOf; simpl; intros.

      specialize (specOf_Imports1 Hinj i).
      specialize (specOfI_inclusion m1 (lo1 lo) i (Imports m1)).
      destruct (specOfI m1 (lo1 lo) i (Imports m1)); intros.      

      (* It's an import. *)

      destruct H0; intuition; subst.
      destruct H1; intuition; subst.
      unfold lo1 in H1.
      generalize (Hinj _ _ H1); clear H1; injection 1; intro; subst.
      injection H; clear H; intro; subst.
      change (lo1 lo (Global x0)) with (lo (Global x0)).
      change (lo1 lo (Global x0)) with (lo (Global x0)) in H2.
      case_eq (amongExports x0 (Exports m2)); intro Heq.

      2: destruct (specOfI link lo (lo (Global x0))
        (thinImports (Exports m2) (Imports m1) ++
          thinImports (Exports m1) (Imports m2))); intuition congruence.

      rewrite dropped_import1 by auto.
      rewrite specOfL_Global by auto.
      destruct (amongExports_In _ _ Heq); intuition; subst.
      specialize (imports_exports_agree1 _ _ H3 H1 (refl_equal _)).
      simpl in imports_exports_agree1; subst.

      generalize H1 exports_noDup2 exports_unique Hinj;
        repeat match goal with
                 | [ x : _ |- _ ] => clear x
               end.
      destruct x; simpl in *.
      induction (Exports m1) as [ | []]; simpl; intuition; subst.

      induction (Exports m2) as [ | []]; simpl in *; intuition; subst.

      injection H; clear H; intros; subst.
      match goal with
        | [ |- context[if ?E then Some _ else _ ] ] => destruct E; intuition
      end.
      
      match goal with
        | [ |- context[if ?E then Some _ else _ ] ] => destruct E; auto
      end.
      specialize (Hinj _ _ e); clear e; injection Hinj; clear Hinj; intro; subst.
      specialize (exports_noDup2 _ _ (or_introl _ (refl_equal _)) (or_intror _ H) (refl_equal _)).
      simpl in exports_noDup2; congruence.

      match type of H0 with
        | ?P -> _ => assert P by eauto; intuition
      end.
      match goal with
        | [ |- context[if ?E then Some _ else _ ] ] => destruct E; auto
      end.
      specialize (Hinj _ _ e); clear e; injection Hinj; clear Hinj; intro; subst.
      specialize (exports_unique _ _ (or_introl _ (refl_equal _)) H1 (refl_equal _)); tauto.

      specialize (specOf_Locals1 Hinj i).
      specialize (specOfL_inclusion m1 (lo1 lo) i (Locals m1)).
      destruct (specOfL m1 (lo1 lo) i (Locals m1)); intros.

      (* It's a local. *)
      destruct (blockOfL m1 (lo1 lo) i (Locals m1)); intuition; try discriminate.
      destruct H4; destruct H5; subst.
      injection H2; clear H2; intro; subst.
      injection H; clear H; intro; subst.
      change (lo1 lo (Local x0)) with (lo (Local (inl _ x0))).
      rewrite specOfI_Local by auto.
      destruct H3; intuition.
      unfold lo1 in H2; specialize (Hinj _ _ H2); injection Hinj; clear Hinj; intros; subst.
      change (lo1 lo (Local x)) with (lo (Local (inl _ x))) in H3.
      rewrite H3; reflexivity.

      specialize (specOf_Exports1 Hinj i).
      specialize (specOfE_inclusion m1 (lo1 lo) i (Exports m1)).
      rewrite H.
      
      (* It's an export. *)
      destruct (blockOfE m1 (lo1 lo) i (Exports m1)); try discriminate; intuition.
      destruct H6; destruct H7; subst.
      injection H4; clear H4; intro; subst.
      destruct H5; intuition.
      generalize (Hinj _ _ H5); injection 1; intro; subst.
      change (lo1 lo (Global x1)) with (lo (Global x1)).
      change (lo1 lo (Global x1)) with (lo (Global x1)) in H6.
      rewrite H6; clear H6.
      rewrite specOfL_Global by auto.
      generalize H imports_exports_disjoint1 exports_unique Hinj;
        repeat match goal with
                 | [ x : _ |- _ ] => clear x
               end.
      induction (Imports m1) as [ | []]; simpl; intuition.
      induction (Imports m2) as [ | []]; simpl; intuition.
      simpl in *.
      case_eq (amongExports ILabel0 (Exports m1)); intro Heq; simpl; auto.
      match goal with
        | [ |- context[if ?E then Some _ else _ ] ] => destruct E
      end; auto.
      generalize (Hinj _ _ e); injection 1; intro; subst.
      destruct (specOfE_In _ (lo1_injective Hinj) _ _ H); intuition; subst.
      specialize (amongExports_notIn _ Heq); intro.
      elimtype False; eauto.

      case_eq (amongExports ILabel0 (Exports m2)); intro Heq; simpl; eauto.
      match goal with
        | [ |- context[if ?E then Some _ else _ ] ] => destruct E
      end; eauto.
      destruct (specOfE_In _ (lo1_injective Hinj) _ _ H); intuition.
      specialize (Hinj _ _ e); injection Hinj; intro; subst.
      elimtype False; eauto.

(*      discriminate. *)
    Qed.

    Hypothesis m1Ok : moduleOk m1.
    Hypothesis m2Ok : moduleOk m2.

    Theorem linkOk : moduleOk link.
      destruct m1Ok; destruct m2Ok; split; simpl; intros;
        repeat match goal with
                 | [ H : In _ _ |- _ ] => apply in_app_or in H
               end; intuition;
        repeat match goal with
                 | [ H : In _ _ |- _ ] => apply (proj1 (in_map_iff _ _ _)) in H; destruct H
               end; intuition; subst; simpl in *; try discriminate.

      injection H1; clear H1; intro.
      specialize (NoDupsL0 _ _ H4 H3 H).
      subst; reflexivity.

      injection H1; clear H1; intro.
      specialize (NoDupsL1 _ _ H4 H3 H).
      subst; reflexivity.

      specialize (NoDupsE0 _ _ H4 H3 H1).
      subst; reflexivity.

      elimtype False; eauto.

      elimtype False; eauto.

      specialize (NoDupsE1 _ _ H4 H3 H1).
      subst; reflexivity.


      specialize (BlocksOk0 _ (lo1_injective H)).
      specialize (BlocksOk1 _ (lo2_injective H)).
      destruct BlocksOk0.
      destruct BlocksOk1.
      apply AllS_app.

      eapply AllS_map; try eassumption; cbv beta; simpl; intros.
      destruct H0.
      split; intros.
      eapply Progress0; eauto.
      eapply mIncl_trans; try apply specOf_link2; auto.
      eapply Preservation0; eauto.
      eapply mIncl_trans; try apply specOf_link2; auto.

      eapply AllS_map; try eassumption; cbv beta; simpl; intros.
      destruct H0.
      split; intros.
      eapply Progress0; eauto.
      eapply mIncl_trans; try apply specOf_link1; auto.
      eapply Preservation0; eauto.
      eapply mIncl_trans; try apply specOf_link1; auto.


      specialize (BlocksOk0 _ (lo1_injective H)).
      specialize (BlocksOk1 _ (lo2_injective H)).
      destruct BlocksOk0.
      destruct BlocksOk1.
      apply AllS_app.

      eapply AllS_map; try eassumption; cbv beta; simpl; intros.
      destruct H0.
      split; intros.
      eapply Progress0; eauto.
      eapply mIncl_trans; try apply specOf_link2; auto.
      eapply Preservation0; eauto.
      eapply mIncl_trans; try apply specOf_link2; auto.

      eapply AllS_map; try eassumption; cbv beta; simpl; intros.
      destruct H0.
      split; intros.
      eapply Progress0; eauto.
      eapply mIncl_trans; try apply specOf_link1; auto.
      eapply Preservation0; eauto.
      eapply mIncl_trans; try apply specOf_link1; auto.
    Qed.

  End link.

End Machine.

Implicit Arguments Global [labelT].
