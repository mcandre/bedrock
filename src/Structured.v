Require Import List String TheoryList FunctionalExtensionality.

Require Import PropX PropXTac Machine Assembly.

Set Implicit Arguments.


Section AllS.
  Variable A : Type.
  Variable P : A -> Prop.

  Theorem AllS_In : forall ls, AllS P ls
    -> forall x, In x ls
      -> P x.
    induction 1; simpl; intuition; congruence.
  Qed.

  Theorem AllS_deapp : forall ls1 ls2, AllS P (ls1 ++ ls2)
    -> AllS P ls1 /\ AllS P ls2.
    induction ls1; inversion 1; simpl; intuition; subst; simpl in *.
    constructor; auto.
    specialize (IHls1 _ H3); tauto.
    specialize (IHls1 _ H3); tauto.
  Qed.

  Variable P' : A -> Prop.

  Theorem AllS_weaken : forall ls, AllS P ls
    -> (forall x, P x -> P' x)
    -> AllS P' ls.
    induction 1; simpl; intuition.
  Qed.

  Theorem AllS_weaken' : forall ls, AllS P ls
    -> (forall x, In x ls -> P x -> P' x)
    -> AllS P' ls.
    induction 1; simpl; intuition.
  Qed.
End AllS.

Implicit Arguments AllS_In [A P ls x].

Fixpoint execs instr state (exec : instr -> state -> state -> Prop) (is : list instr) (s s' : state) : Prop :=
  match is with
    | nil => s' = s
    | i :: is' => exists s'', exec i s s'' /\ execs exec is' s'' s'
  end.

Fixpoint lookup A (s : string) (ls : list (string * A)) : option A :=
  match ls with
    | nil => None
    | (s', v) :: ls' => if string_dec s s' then Some v else lookup s ls'
  end.

Theorem lookup_correct : forall A x (ls : list (string * A)),
  match lookup x ls with
    | Some y => List.In (x, y) ls
    | None => forall y, ~List.In (x, y) ls
  end.
  induction ls; simpl; intuition;
    match goal with
      | [ |- context[if ?E then _ else _] ] => destruct E
    end; subst; intuition;
    match goal with
      | [ |- context[match ?E with None => _ | Some _ => _ end] ] => destruct E
    end; intuition eauto; congruence.
Qed.

Module Type S.
  Parameters pc state instr jmp : Type.
  Parameter exec : instr -> state -> state -> Prop.
  Parameter resolve : jmp -> state -> pc -> Prop.
  Parameter pc_eq : forall x y : pc, {x = y} + {x <> y}.

  Parameter directJump : pc -> jmp.
  Axiom resolve_directJump : forall i s, resolve (directJump i) s i.
  Axiom resolve_directJump_unique : forall i s i', resolve (directJump i) s i' -> i' = i.

  Parameter exp : Type.
  Parameter eval : exp -> state -> pc -> Prop.

  Parameter indirectJump : exp -> jmp.
  Axiom resolve_indirectJump : forall e s i, eval e s i
    -> resolve (indirectJump e) s i.
  Axiom resolve_indirectJump_unique : forall e s i, resolve (indirectJump e) s i
    -> eval e s i.

  Parameter cond : Type.
  Parameter decide : cond -> state -> bool -> state -> Prop.

  Parameter conditionalJump : cond -> pc -> pc -> list instr * jmp.
  Axiom resolve_conditionalJump : forall b s s' i1 i2 b', decide b s b' s'
    -> execs exec (fst (conditionalJump b i1 i2)) s s'
    /\ resolve (snd (conditionalJump b i1 i2)) s' (if b' then i1 else i2).
  Axiom resolve_conditionalJump_unique : forall b s s' i1 i2 i, 
       execs exec (fst (conditionalJump b i1 i2)) s s'
    -> resolve (snd (conditionalJump b i1 i2)) s' i
    -> exists b', decide b s b' s' /\ i = if b' then i1 else i2.
End S.

Module Make (M : S).
  Definition prop := spec M.pc M.state.
  Definition block := (list M.instr * M.jmp)%type.
  Definition step (b : block) (s : M.state) (i : M.pc) (s' : M.state) :=
    execs M.exec (fst b) s s' /\ M.resolve (snd b) s' i.

  Section imports.
    Variable imports : list (string * prop).

    Section exports.
      Variable exports : list (string * prop).

      Definition instrsIn := prop.

      Record instrsOut := InsOut {
        IoutPostcondition : prop;
        IoutCode : forall LT, layout M.pc LT -> list M.instr
      }.

      Definition instrs := instrsIn -> instrsOut.

      Definition instrsOk (i : instrs) := forall LT ii, let iout := i ii in
        forall (lo : layout _ LT) specs st st',
          AllS (fun p => specs (lo (Global (fst p))) = Some (snd p)) imports
          -> AllS (fun p => specs (lo (Global (fst p))) = Some (snd p)) exports
          -> interp specs (ii st)
          -> execs M.exec (IoutCode iout lo) st st'
          -> interp specs (IoutPostcondition iout st').

      Record compileIn (LT GT : Type) := CompIn {
        CinPrecondition : prop;
        CinExit : GT;
        CinInject : LT -> GT
      }.

      Record compileOut (GT : Type) := CompOut {
        CoutPostcondition : option prop;
        CoutCode : list (local M.pc M.state block GT);
        CoutConditions : list (layout M.pc GT -> prop * prop)
      }.

      Record scodeR := Scode {
        ScLabT : Type;
        ScEntry : ScLabT;
        ScCompile : forall GT, (instrsIn -> instrsOut) -> compileIn ScLabT GT -> compileOut GT
      }.

      Record scodeROk (sc : scodeR) := ScodeOk {
        ScInclude : forall GT is (cin : compileIn _ GT), let cout := ScCompile sc is cin in
          AllS (fun p' => forall specs lo st, interp specs (fst (p' lo) st) -> interp specs (snd (p' lo) st))
          (CoutConditions cout)
          -> exists p, exists cd, In (Loc (CinInject cin (ScEntry sc)) p cd) (CoutCode cout)
            /\ forall specs st, interp specs (CinPrecondition cin st --> p st);
        ScInject : forall GT is (cin : compileIn _ GT), let cout := ScCompile sc is cin in
          AllS (fun L => exists x, LLabel L = CinInject cin x) (CoutCode cout);
        ScNoDups : forall GT is (cin : compileIn _ GT) L1 L2, let cout := ScCompile sc is cin in
          (forall x1 x2, CinInject cin x1 = CinInject cin x2 -> x1 = x2)
          -> In L1 (CoutCode cout)
          -> In L2 (CoutCode cout)
          -> LLabel L1 = LLabel L2
          -> L1 = L2;
        ScVerified : forall (m : Assembly.module M.pc M.state block)
          is cin lo, let cout := ScCompile sc is cin in
            AllS (fun p => In (Imp (fst p) (snd p)) (Imports m)) imports
            -> AllS (fun p => exists cd, In (Exp (fst p) (snd p) cd) (Exports m)) exports
            -> (forall im1 im2, In im1 (Imports m)
              -> In im2 (Imports m)
              -> ILabel im1 = ILabel im2
              -> ISpec im1 = ISpec im2)
            -> (forall im1 im2, In im1 (Exports m)
              -> In im2 (Exports m)
              -> ELabel im1 = ELabel im2
              -> ESpec im1 = ESpec im2)
            -> (forall im1 im2, In im1 (Imports m)
              -> In im2 (Exports m)
              -> ILabel im1 <> ELabel im2)
            -> (forall pre, let iout := is pre in
              forall specs st st',
                AllS (fun p => specs (lo (Global (fst p))) = Some (snd p)) imports
                -> AllS (fun p => specs (lo (Global (fst p))) = Some (snd p)) exports
                -> interp specs (pre st)
                -> execs M.exec (IoutCode iout lo) st st'
                -> interp specs (IoutPostcondition iout st'))
            -> (forall L1, In L1 (Locals m) -> forall L2, In L2 (Locals m) -> LLabel L1 = LLabel L2 -> L1 = L2)
            -> injective lo
            -> AllS (fun vc => forall specs lo st, interp specs (fst (vc lo) st) -> interp specs (snd (vc lo) st)) (CoutConditions cout)
            -> incl (CoutCode cout) (Locals m)
            -> AllS (fun L => forall v, LLabel L = CinInject cin v -> In L (CoutCode cout)) (Locals m)
            -> (forall v1 v2, CinInject cin v1 = CinInject cin v2 -> v1 = v2)
            -> match CoutPostcondition cout with
                 | None => True
                 | Some post => exists p, exists cd, In (Loc (CinExit cin) p cd) (Locals m)
                   /\ (forall specs st, interp specs (post st --> (p st)))
               end
            -> AllS (fun L => blockOk step M.pc_eq m lo (LSpec L) (LBlock L lo)) (CoutCode cout)
      }.

      Inductive scode :=
      | SStraightline : instrs -> scode
      | SStructured : scodeR -> scode.

      Definition scodeOk (sc : scode) :=
        match sc with
          | SStraightline i => instrsOk i
          | SStructured r => scodeROk r
        end.

      Lemma imp_refl : forall specs (p : PropX M.pc M.state), interp specs (p --> p).
        red; intros; apply Imply_I; apply Env; simpl; tauto.
      Qed.

      Lemma local_spec : forall (m : Assembly.module M.pc M.state block) layout specs l p cd,
        injective layout
        -> In (Loc l p cd) (Locals m)
        -> (forall L1, In L1 (Locals m) -> forall L2, In L2 (Locals m) -> LLabel L1 = LLabel L2 -> L1 = L2)
        -> mIncl (specOf M.pc_eq m layout) specs
        -> specs (layout (Local l)) = Some p.
        intros until cd; intros Hinj Hin Hnd Hincl; apply Hincl; clear Hincl; unfold specOf;
          rewrite specOfI_Local by auto; specialize (Hnd _ Hin); simpl in Hnd.
        induction (Locals m) as [ | []]; simpl in *; intuition;
          match goal with
            | [ |- context[if ?E then _ else _] ] => destruct E; try congruence
          end; eauto.
        specialize (Hinj _ _ e); injection Hinj; clear Hinj; intro; subst;
          specialize (Hnd _ (or_introl _ (refl_equal _)) (refl_equal _)); congruence.
      Qed.

      Hint Resolve imp_refl local_spec.
      Hint Extern 1 (_ = _) => progress simpl.
      Hint Constructors AllS.
      Hint Unfold step.
      Hint Immediate simplify_fwd.

      Hint Extern 1 (interp _ _) => eapply Imply_E; [ match goal with
                                                        | [ H : _ |- _ ] => solve [ apply H ]
                                                      end | propxFo ].

      Lemma incl_cons : forall A (x : A) ls1 ls2,
        incl (x :: ls1) ls2
        -> In x ls2 /\ incl ls1 ls2.
        unfold incl; simpl; intuition.
      Qed.

      Hint Resolve M.resolve_directJump.

      Ltac newStructured' := simpl; intuition auto; simpl in *; subst; eauto.

      Ltac newStructured :=
        newStructured';
          repeat match goal with
                   | [ |- instrsOk _ ] => red; newStructured'
                   | [ |- scodeROk _ ] => split; newStructured'
                   | [ H : True |- _ ] => clear H
                   | [ H : ex _ |- _ ] => destruct H; intuition auto
                   | [ H : incl nil _ |- _ ] => clear H
                   | [ H : incl _ _ |- _ ] => destruct (incl_cons H); clear H
                   | [ H : AllS _ nil |- _ ] => clear H
                   | [ H : AllS _ (_ :: _) |- _ ] => inversion H; clear H; subst
                   | [ |- AllS _ nil ] => constructor
                   | [ |- AllS _ (_ :: _) ] => constructor; simpl
                   | [ |- blockOk _ _ _ _ _ _ ] => split; unfold step; intuition auto; subst; simpl in *
                   | [ H : M.resolve (M.directJump _) _ _ |- _ ] => apply M.resolve_directJump_unique in H; subst
                 end; eauto 7.

      Definition notStuck LT (iout : instrsOut) (lo : layout M.pc LT) : prop := (fun st =>
        [< exists st', execs M.exec (IoutCode iout lo) st st' >])%PropX.

      Definition makeIin LT GT (cin : compileIn LT GT) := CinPrecondition cin.

      Definition Skip := SStraightline (fun iin => InsOut iin (fun _ _ => nil)).

      Theorem SkipOk : scodeOk Skip.
        newStructured.
      Qed.

      Definition Halt := SStructured (Scode true (fun _ is cin =>
        let iout := is (makeIin cin) in
          CompOut None
          (Loc (CinInject cin true) (CinPrecondition cin)
            (fun lo => (IoutCode iout lo, M.directJump (lo (Local (CinInject cin false)))))
            :: Loc (CinInject cin false) (fun _ => [< True >])%PropX
            (fun lo => (nil, M.directJump (lo (Local (CinInject cin false))))) :: nil)
          ((fun lo => (CinPrecondition cin, notStuck iout lo)) :: nil))).

      Theorem HaltOk : scodeOk Halt.
        newStructured.

        simpl in *.
        specialize (H _ _ H2); discriminate.

        simpl in *.
        specialize (H _ _ H2); discriminate.

        destruct (Inj_sound (H14 _ lo _ H12)); intuition eauto 6.

        repeat esplit.
        eapply local_spec; eauto.
        propxFo.
      Qed.

      Section StraightLine.
        Variable i : M.instr.

        Definition StraightLine := SStraightline (fun iin => InsOut (fun st => Ex st', iin st' /\ [<M.exec i st' st>])%PropX
          (fun _ _ => i :: nil)).

        Theorem StraightLineOk : scodeOk StraightLine.
          newStructured; subst; propxFo; eauto.
        Qed.
      End StraightLine.

      Hint Resolve M.resolve_indirectJump.

      Lemma specOfI_in : forall (m : module M.pc M.state block) lo (Hinj : injective lo) l p lps,
        In (Imp l p) lps
        -> (forall im1 im2, In im1 lps
          -> In im2 lps
          -> ILabel im1 = ILabel im2
          -> ISpec im1 = ISpec im2)
        -> specOfI M.pc_eq m lo (lo (Global l)) lps = Some p.
        induction lps as [ | []]; simpl; intuition; subst;
          match goal with
            | [ |- context[if ?E then _ else _] ] => destruct E
          end; intuition; try congruence.

        specialize (Hinj _ _ e); injection Hinj; clear Hinj; intros; subst.
        specialize (H0 _ _ (or_introl _ (refl_equal _)) (or_intror _ H1) (refl_equal _)); simpl in H0; congruence.
      Qed.

      Lemma imports_in : forall (m : module M.pc M.state block) specs lo (Hinj : injective lo)
        (imps : list (string * spec M.pc M.state)),
        mIncl (specOf M.pc_eq m lo) specs
        -> AllS (fun p => In (Imp (fst p) (snd p)) (Imports m)) imps
        -> (forall im1 im2, In im1 (Imports m)
          -> In im2 (Imports m)
          -> ILabel im1 = ILabel im2
          -> ISpec im1 = ISpec im2)
        -> AllS (fun p => specs (lo (Global (fst p))) = Some (snd p)) imps.
        intros; eapply AllS_weaken; [ eassumption | ].
        clear H0; simpl; intros.
        apply H; clear H.
        unfold specOf.
        rewrite specOfI_in with (p := snd x); intuition.
      Qed.

      Lemma specOfI_notIn : forall (m : module M.pc M.state block) lo (Hinj : injective lo) l lps,
        (forall im, In im lps
          -> ILabel im <> l)
        -> specOfI M.pc_eq m lo (lo (Global l)) lps = None.
        induction lps as [ | []]; simpl; intuition; subst;
          match goal with
            | [ |- context[if ?E then _ else _] ] => destruct E
          end; intuition; try congruence.

        specialize (Hinj _ _ e); injection Hinj; clear Hinj; intros; subst.
        destruct (H _ (or_introl _ (refl_equal _)) (refl_equal _)).

        eauto.
      Qed.

      Lemma specOfE_in : forall (m : module M.pc M.state block) lo (Hinj : injective lo) l p cd lps,
        In (Exp l p cd) lps
        -> (forall im1 im2, In im1 lps
          -> In im2 lps
          -> ELabel im1 = ELabel im2
          -> ESpec im1 = ESpec im2)
        -> specOfE M.pc_eq m lo (lo (Global l)) lps = Some p.
        induction lps as [ | []]; simpl; intuition; subst;
          match goal with
            | [ |- context[if ?E then _ else _] ] => destruct E
          end; intuition; try congruence.

        specialize (Hinj _ _ e); injection Hinj; clear Hinj; intros; subst.
        specialize (H0 _ _ (or_introl _ (refl_equal _)) (or_intror _ H1) (refl_equal _)); simpl in H0; congruence.
      Qed.

      Lemma exports_in : forall (m : module M.pc M.state block) specs lo (Hinj : injective lo)
        (exps : list (string * spec M.pc M.state)),
        mIncl (specOf M.pc_eq m lo) specs
        -> AllS (fun p => exists cd, In (Exp (fst p) (snd p) cd) (Exports m)) exps
        -> (forall im1 im2, In im1 (Exports m)
          -> In im2 (Exports m)
          -> ELabel im1 = ELabel im2
          -> ESpec im1 = ESpec im2)
        -> (forall im1 im2, In im1 (Imports m)
          -> In im2 (Exports m)
          -> ILabel im1 <> ELabel im2)
        -> AllS (fun p => specs (lo (Global (fst p))) = Some (snd p)) exps.
        intros; eapply AllS_weaken; [ eassumption | ].
        clear H0; simpl; intros.
        apply H; clear H.
        unfold specOf.
        destruct H0.
        rewrite specOfI_notIn; intuition.
        rewrite (specOfL_Global step); intuition.
        rewrite specOfE_in with (p := snd x) (cd := x0); intuition.
        eauto.
      Qed.

      Section GotoI.
        Variable e : M.exp.

        Definition GotoI := SStructured (Scode tt (fun _ is cin =>
          let iout := is (makeIin cin) in
            CompOut None
            (Loc (CinInject cin tt) (CinPrecondition cin)
              (fun lo => (IoutCode iout lo, M.indirectJump e)) :: nil)
            ((fun lo => (CinPrecondition cin, fun st => [< exists st',
              execs M.exec (IoutCode iout lo) st st' /\ exists i, M.eval e st' i >]%type)%PropX)
            :: (fun _ => (IoutPostcondition iout, fun st => Al i, [< M.eval e st i >]
              --> ExX, Cptr i (Var VO) /\ VO @ st)%PropX)
            :: nil))).

        Theorem GotoIOk : scodeOk GotoI.
          newStructured.

          specialize (H13 _ lo _ H8); propxFo.
          eauto.

          apply M.resolve_indirectJump_unique in H16.
          generalize (H12 _ lo _ (H4 _ _ _ _ (imports_in H6 H7 H H1) (exports_in H6 H7 H0 H2 H3) H8 H15)); clear H4 H12; propxFo.
          generalize (Imply_sound (H4 _) (Inj_I _ _ H16)); propxFo.
          repeat esplit; eauto.
          autorewrite with PropXF.
          assumption.
        Qed.
      End GotoI.

      Lemma Some_inj : forall A (x y : A),
        Some x = Some y
        -> x = y.
        intros; congruence.
      Qed.

      Lemma incl_app : forall A (ls1 ls2 ls : list A),
        incl (ls1 ++ ls2) ls
        -> incl ls1 ls /\ incl ls2 ls.
        unfold incl; simpl; intuition.
      Qed.

      Definition lookupS (s : string) :=
        match lookup s exports with
          | None => lookup s imports
          | v => v
        end.

      Lemma lookupS_correct : forall s LT (lo : layout M.pc LT) specs,
        AllS (fun p => specs (lo (Global (fst p))) = Some (snd p)) imports
        -> AllS (fun p => specs (lo (Global (fst p))) = Some (snd p)) exports
        -> match lookupS s with
             | None => True
             | Some p => specs (lo (Global s)) = Some p
           end.
        unfold lookupS; intros.

        generalize (lookup_correct s exports).
        destruct (lookup s exports); simpl; intuition.
        apply (AllS_In H0 H1).

        generalize (lookup_correct s imports).
        destruct (lookup s imports); simpl; intuition.
        apply (AllS_In H H2).
      Qed.

      Inductive uhoh (A : Type) (v : A) :=
      | Uhoh : uhoh v.

      Hint Constructors uhoh.

      Section WithCode.
        Variables (s : string) (i : M.pc -> M.instr).

        Definition WithCode := SStraightline (match lookupS s with
                                                | None => fun _ => InsOut (fun _ => [<uhoh (s, i)>])%PropX (fun _ _ => nil)
                                                | Some p => fun ii => InsOut
                                                  (fun st => Ex n, Cptr n p /\ Ex st', ii st' /\ [< M.exec (i n) st' st >])%PropX
                                                  (fun _ lo => i (lo (Global s)) :: nil)
                                              end).

        Theorem WithCodeOk : scodeOk WithCode.
          simpl.

          generalize (@lookupS_correct s).
          destruct (lookupS s); simpl in *; propxFo; subst; red; propxFo.
          rewrite <- (eta_expansion p).
          repeat esplit.
          simpl in *.
          apply (H _ lo); auto.
          apply simplify_fwd; eassumption.
          simpl in *; propxFo; subst; assumption.
        Qed.
      End WithCode.

      Hint Resolve imports_in exports_in.

      Inductive uhoh' (A : Type) (v : A) :=.

      Section Goto.
        Variable s : string.

        Definition Goto := SStructured (Scode tt (fun _ is cin =>
          let iout := is (makeIin cin) in
            CompOut None
            (Loc (CinInject cin tt) (CinPrecondition cin)
              (fun lo => (IoutCode iout lo, M.directJump (lo (Global s)))) :: nil)
            ((fun lo => (CinPrecondition cin, notStuck iout lo))
              :: (fun _ => (IoutPostcondition iout, match lookupS s with
                                                      | None => fun _ => [< uhoh' s >]
                                                      | Some p => p
                                                    end)%PropX)
              :: nil))).

        Theorem GotoOk : scodeOk Goto.
          newStructured.

          specialize (H13 _ lo _ H8); propxFo; eauto.

          generalize (@lookupS_correct s); intro Hl.
          destruct (lookupS s).
          repeat esplit; eauto.
          eauto.

          assert (interp specs [<uhoh' s>]) by eauto.
          propxFo.
        Qed.
      End Goto.

      Lemma execs_app : forall is2 is1 st st', execs M.exec (is1 ++ is2) st st'
        -> exists st'', execs M.exec is1 st st'' /\ execs M.exec is2 st'' st'.
        induction is1; simpl; propxFo; eauto.
        specialize (IHis1 _ _ H1); propxFo; eauto.
      Qed.

      Lemma execs_app' : forall is2 is1 st st'' st',
        execs M.exec is1 st st''
        -> execs M.exec is2 st'' st'
        -> execs M.exec (is1 ++ is2) st st'.
        induction is1; simpl; propxFo; subst; eauto.
      Qed.

      Hint Immediate execs_app'.

      Theorem specOfL_In : forall (m : module M.pc M.state block) lo l p cd ls,
        injective lo
        -> In (Loc l p cd) ls
        -> (forall L1 L2, In L1 ls -> In L2 ls -> LLabel L1 = LLabel L2 -> L1 = L2)
        -> specOfL M.pc_eq m lo (lo (Local l)) ls = Some p.
        induction ls as [| []]; simpl; intuition;
          match goal with
            | [ |- context[if ?E then _ else _] ] => destruct E
          end; intuition; try congruence.

        specialize (H _ _ e); injection H; clear H; intro; subst.
        specialize (H1 _ _ (or_introl _ (refl_equal _)) (or_intror _ H2) (refl_equal _)).
        congruence.
      Qed.

      Section Assert_.
        Variables (inv : prop).

        Definition Assert_ := SStructured (Scode tt (fun _ is' cin =>
          let iout := is' (makeIin cin) in
            CompOut (Some inv)
            (Loc (CinInject cin tt) (CinPrecondition cin)
              (fun lo => (IoutCode iout lo, M.directJump (lo (Local (CinExit cin))))) :: nil)
            ((fun lo => (CinPrecondition cin, notStuck iout lo))
              :: (fun lo => (IoutPostcondition iout, inv))
              :: nil))).

        Theorem Assert_Ok : scodeOk Assert_.
          newStructured.

          specialize (H15 _ lo _ H8); propxFo.
          eauto.
          
          do 2 esplit; eauto.
          apply (Imply_sound (H13 _ _)).
          eauto.
        Qed.
      End Assert_.

      Section Call_.
        Variables (is : M.pc -> list M.instr) (s : string) (post : prop).

        Definition Call_ := SStructured (Scode tt (fun _ is' cin =>
          let iout := is' (makeIin cin) in
            CompOut (Some post)
            (Loc (CinInject cin tt) (CinPrecondition cin)
              (fun lo => (IoutCode iout lo ++ is (lo (Local (CinExit cin))), M.directJump (lo (Global s)))) :: nil)
            ((fun lo => (CinPrecondition cin, notStuck iout lo))
              :: (fun lo => (IoutPostcondition iout, fun st => Ex st', [< execs M.exec (is (lo (Local (CinExit cin)))) st st' >]))%PropX
              :: (fun lo => (fun st => Ex st', IoutPostcondition iout st' /\ [< execs M.exec (is (lo (Local (CinExit cin)))) st' st >]
                /\ lo (Local (CinExit cin)) @@ (fun st => ^[post st]), match lookupS s with
                                                       | None => fun _ => [< uhoh' s >]
                                                       | Some p => p
                                                     end)%PropX)
              :: nil))).

        Theorem Call_Ok : scodeOk Call_.
          newStructured.

          specialize (H15 _ lo _ H8); propxFo.
          assert (interp specs (IoutPostcondition (is0 CinPrecondition0) x1)) by eauto.
          specialize (H14 _ lo _ H17); propxFo.
          eauto.

          apply execs_app in H18; destruct H18; intuition.
          assert (interp specs (IoutPostcondition (is0 CinPrecondition0) x1)) by eauto.
          specialize (H16 specs lo s').
          match type of H16 with
            | ?P -> _ => assert P
          end.
          propxFo.
          esplit; intuition.
          propxFo; eauto.
          auto.
          esplit; intuition.
          rewrite lift_nadaF.
          eauto.
          autorewrite with PropX.
          auto.
          intuition.

          generalize (lookupS_correct s); intro Hs.
          destruct (lookupS s).
          repeat esplit.
          eauto.
          auto.
          
          propxFo.
        Qed.
      End Call_.

      Section CallI.
        Variables (is : M.pc -> list M.instr) (e : M.exp) (post : prop).

        Definition CallI := SStructured (Scode tt (fun _ is' cin =>
          let iout := is' (makeIin cin) in
            CompOut (Some post)
            (Loc (CinInject cin tt) (CinPrecondition cin)
              (fun lo => (IoutCode iout lo ++ is (lo (Local (CinExit cin))), M.indirectJump e)) :: nil)
            ((fun lo => (CinPrecondition cin, notStuck iout lo))
              :: (fun lo => (IoutPostcondition iout, fun st => Ex st', [< execs M.exec (is (lo (Local (CinExit cin)))) st st' >]))%PropX
              :: (fun lo => (fun st => Ex st', IoutPostcondition iout st' /\ [< execs M.exec (is (lo (Local (CinExit cin)))) st' st >]
                /\ lo (Local (CinExit cin)) @@ (fun st => ^[post st]),
                fun st => Ex i, [< M.eval e st i >])%PropX)
              :: (fun lo => (fun st => Ex st', IoutPostcondition iout st' /\ [< execs M.exec (is (lo (Local (CinExit cin)))) st' st >]
                /\ lo (Local (CinExit cin)) @@ (fun st => ^[post st]),
                fun st => Al i, [< M.eval e st i >] --> ExX, Cptr i (Var VO) /\ VO @ st)%PropX)
              :: nil))).

        Theorem CallIOk : scodeOk CallI.
          newStructured.

          specialize (H15 _ lo _ H8); propxFo.
          specialize (H4 _ _ _ _ (imports_in H6 H7 H H1) (exports_in H6 H7 H0 H2 H3) H8 H15).
          specialize (H14 _ lo _ H4); propxFo.
          assert (interp specs (Ex i, [< M.eval e x2 i >]))%PropX.
          eapply H16.
          propxFo.
          repeat esplit.
          propxFo; eauto.
          eauto.
          rewrite lift_nadaF.
          eauto.
          intro; autorewrite with PropX; auto.

          propxFo; eauto.

          apply execs_app in H19; destruct H19; intuition.
          assert (interp specs (IoutPostcondition (is0 CinPrecondition0) x1)) by eauto.
          specialize (H16 specs lo s').
          match type of H16 with
            | ?P -> _ => assert P
          end.
          propxFo.
          esplit; intuition.
          propxFo; eauto.
          auto.
          esplit; intuition.
          rewrite lift_nadaF.
          eauto.
          autorewrite with PropX.
          auto.
          intuition.

          propxFo.
          apply M.resolve_indirectJump_unique in H20.
          specialize (H17 specs lo s').
          match type of H17 with
            | ?P -> _ => assert P
          end.

          propxFo.
          esplit; intuition.
          propxFo; eauto.
          auto.
          esplit; intuition.
          auto.
          propxFo.
          generalize (Imply_sound (H27 _) (Inj_I _ _ H20)); propxFo.
          autorewrite with PropXF in H31.
          eauto.
        Qed.
      End CallI.

      Section Use_.
        Variable lemma : M.state -> Prop.

        Definition Use_ (proof : forall st, lemma st) := SStraightline (fun iin => InsOut (fun st => iin st /\ [< lemma st >])%PropX
          (fun _ _ => nil)).

        Theorem Use_Ok : forall proof, scodeOk (Use_ proof).
          newStructured; propxFo.
        Qed.
      End Use_.

      Section SeqI.
        Variables is1 is2 : instrs.

        Definition SeqI (ii : instrsIn) :=
          let iout1 := is1 ii in
            let iout2 := is2 (IoutPostcondition iout1) in
              InsOut (IoutPostcondition iout2) (fun _ lo => IoutCode iout1 lo ++ IoutCode iout2 lo).

        Hypotheses (His1 : instrsOk is1) (His2 : instrsOk is2).

        Theorem SeqIOk : instrsOk SeqI.
          red; simpl; intros.
          apply execs_app in H2; destruct H2; intuition eauto.
        Qed.
      End SeqI.

      Hint Immediate imports_in exports_in.

      Definition nullInstrs (ii : instrsIn) := InsOut ii (fun _ _ => nil).

      Section Seq.
        Variables c1 c2 : scode.

        Definition Seq := match c1, c2 with
                            | SStraightline is1, SStraightline is2 =>
                              SStraightline (SeqI is1 is2)
                            | SStraightline is, SStructured r =>
                              SStructured (Scode (ScEntry r)
                                (fun _ is' cin => ScCompile r (SeqI is' is) cin))
                            | SStructured r, SStraightline is =>
                              SStructured (Scode (Some (ScEntry r))
                                (fun _ is' cin =>
                                  let cout := ScCompile r is' (CompIn (CinPrecondition cin)
                                    (CinInject cin None) (fun v => CinInject cin (Some v))) in
                                  match CoutPostcondition cout with
                                    | None => cout
                                    | Some post =>
                                      let iout := is post in
                                        CompOut (Some (IoutPostcondition iout))
                                        (Loc (CinInject cin None) post
                                          (fun lo => (IoutCode iout lo, M.directJump (lo (Local (CinExit cin)))))
                                          :: CoutCode cout)
                                        ((fun lo => (post, notStuck iout lo)) :: CoutConditions cout)
                                  end))
                            | SStructured r1, SStructured r2 =>
                              SStructured (Scode (inl _ (ScEntry r1))
                                (fun _ is cin =>
                                  let cout1 := ScCompile r1 is (CompIn (CinPrecondition cin)
                                    (CinInject cin (inr _ (ScEntry r2)))
                                    (fun v => CinInject cin (inl _ v))) in
                                  match CoutPostcondition cout1 with
                                    | None => cout1
                                    | Some post1 =>
                                      let cout2 := ScCompile r2 nullInstrs
                                        (CompIn post1 (CinExit cin) (fun v => CinInject cin (inr _ v))) in
                                        CompOut (CoutPostcondition cout2)
                                        (CoutCode cout1 ++ CoutCode cout2)
                                        (CoutConditions cout1 ++ CoutConditions cout2)
                                  end))
                          end.

        Hypotheses (Hc1 : scodeOk c1) (Hc2 : scodeOk c2).

        Theorem SeqOk : scodeOk Seq.
          unfold Seq; destruct c1; destruct c2; split || red; intros.

          red; simpl; intros.
          apply execs_app in H2; destruct H2; intuition eauto.

          Ltac comp r1 Hr1 cout := destruct r1 as [? ? ScCompile0]; destruct Hr1; simpl ScCompile in *;
            simpl in cout;
              let e := eval unfold cout in cout in
                match e with
                  | context[match CoutPostcondition ?E with None => _ | Some _ => _ end] =>
                    match E with
                      | ScCompile0 ?T ?is ?cin =>
                        repeat match goal with
                                 | [ H : _ |- _ ] =>
                                   generalize (H T is cin);
                                     match goal with
                                       | [ |- ?P -> _ ] => (assert P by assumption; fail 1)
                                         || intro
                                     end
                                 | [ m : module _ _ _, H : _ |- _ ] =>
                                   generalize (H m is cin);
                                     match goal with
                                       | [ |- ?P -> _ ] => (assert P by assumption; fail 1)
                                         || intro
                                     end
                               end; destruct E; simpl in *
                    end;
                    match goal with
                      | [ p : option _ |- _ ] => destruct p; subst cout; simpl in *
                    end
                end.

          apply (ScInclude Hc2); auto.
          apply (ScInject Hc2); auto.
          eapply (ScNoDups Hc2); eauto.
          eapply (ScVerified Hc2); eauto.
          simpl in *; intros.
          apply execs_app in H15; destruct H15; intuition eauto.

          comp s Hc1 cout; newStructured;
          match goal with
            | [ H : AllS _ _, H2 : _ |- _ ] => destruct (H2 H) as [? [? []]]; eauto
          end.

          comp s Hc1 cout; try constructor; eauto;
            (eapply AllS_weaken; [ eauto | ];
              simpl; intuition; destruct H2; rewrite H2; eauto).

          comp s Hc1 cout; intuition; subst; simpl in *; auto;
            try match goal with
                  | [ H : AllS _ ?L, H' : In _ ?L |- _ ] =>
                    destruct (AllS_In H H');
                      match goal with
                        | [ H : forall x1 x2, _ -> x1 = x2, H1 : _ = ?E, H2 : ?E = _ |- _ ] =>
                          rewrite H2 in H1; specialize (H _ _ H1); discriminate
                        | [ H : forall x1 x2, _ -> x1 = x2, H1 : ?E = _, H2 : ?E = _ |- _ ] =>
                          rewrite H2 in H1; specialize (H _ _ H1); discriminate
                      end
                  | [ H : forall L1 L2 : local _ _ _ _, _ |- _ ] => apply H; auto; intros; apply Some_inj; auto
                end.

          comp s Hc1 cout; repeat match goal with
                                    | [ H : AllS _ (_ :: _) |- _ ] => inversion H; clear H; intros; subst
                                    | [ H : incl _ _ |- _ ] => apply incl_cons in H; destruct H
                                  end; try constructor; simpl in *.

          unfold step; split; simpl; intuition.
          destruct (Inj_sound (H18 _ lo _ H17)); eauto.
          apply M.resolve_directJump_unique in H22; subst.
          destruct H11 as [? []]; intuition.
          rewrite (local_spec _ _ _ H6 H20 H5 H14); repeat esplit.
          eapply Imply_sound; eauto.

          apply H15; intuition.
          eapply AllS_weaken; [ eauto | ].
          simpl; intuition.
          specialize (H14 _ H17); intuition.
          subst; simpl in *.
          specialize (H10 _ _ H17); discriminate.
          specialize (H10 _ _ H14); congruence.
          eauto.

          apply H15; intuition.
          eapply AllS_weaken; [ eauto | ].
          simpl; intuition.
          specialize (H14 _ H17); intuition.
          subst; simpl in *.
          specialize (H10 _ _ H14); congruence.

          comp s Hc1 cout; eauto.

          apply AllS_deapp in H; destruct H.
          destruct (H2 H) as [? []]; clear H2; intuition.
          repeat esplit.
          apply in_or_app; eauto.
          assumption.

          comp s Hc1 cout.

          Ltac comp' r2 Hr2 := destruct r2; destruct Hr2; simpl in *;
            let doit E :=
              match E with
                | _ ?T ?is ?cin =>
                  repeat match goal with
                           | [ H : ?P |- _ ] =>
                             match type of P with
                               | Prop =>
                                 generalize (H T is cin);
                                   match goal with
                                     | [ |- ?P -> _ ] => (assert P by assumption; fail 1)
                                       || intro
                                   end
                             end
                           | [ m : module _ _ _, H : _ |- _ ] =>
                             generalize (H m is cin);
                               match goal with
                                 | [ |- ?P -> _ ] => (assert P by assumption; fail 1)
                                   || intro
                               end
                         end; destruct E; simpl in *
              end in
              match goal with
                | [ |- context[CoutCode ?E] ] => doit E
                | [ _ : context[CoutCode ?E] |- _ ] => doit E
              end.

          comp' s0 Hc2.

          apply AllS_app; auto.
          eapply AllS_weaken; [ eauto | ].
          simpl; destruct 1.
          rewrite H5; eauto.
          eapply AllS_weaken; [ eauto | ].
          simpl; destruct 1.
          rewrite H5; eauto.

          eapply AllS_weaken; [ eauto | ].
          simpl; destruct 1.
          rewrite H2; eauto.

          comp s Hc1 cout.

          comp' s0 Hc2.
          apply in_app_or in H0.
          apply in_app_or in H1.
          intuition.

          apply H3; intuition.
          specialize (H _ _ H1); congruence.

          destruct (AllS_In H4 H9).
          destruct (AllS_In H7 H0).
          rewrite H2 in *.
          rewrite H1 in H10.
          specialize (H _ _ H10); discriminate.

          destruct (AllS_In H4 H0).
          destruct (AllS_In H7 H9).
          rewrite H2 in *.
          rewrite H1 in H10.
          specialize (H _ _ H10); discriminate.

          apply H6; intuition.
          specialize (H _ _ H1); congruence.

          apply H3; intuition.
          specialize (H _ _ H6); congruence.

          comp s Hc1 cout.
          comp' s0 Hc2.
          apply AllS_deapp in H7; destruct H7.
          apply incl_app in H8; destruct H8.
          apply AllS_app.

          apply H19; intuition; subst; auto.
          eapply AllS_weaken; [ eauto | ].
          simpl; intuition.
          specialize (H18 _ H23).
          apply in_app_or in H18; intuition.
          destruct (AllS_In H13 H24).
          rewrite H23 in H18.
          specialize (H10 _ _ H18); discriminate.
          specialize (H10 _ _ H18); congruence.

          apply H15; intuition.
          eapply AllS_weaken; [ eauto | ].
          simpl; intuition.
          specialize (H18 _ H23).
          apply in_app_or in H18; intuition.
          destruct (AllS_In H17 H24).
          rewrite H23 in H18.
          specialize (H10 _ _ H18); discriminate.
          specialize (H10 _ _ H18); congruence.

          destruct H14 as [? []]; intuition eauto.

          apply H15; intuition.
          eapply AllS_weaken; [ eauto | ].
          simpl; intuition eauto.
          specialize (H10 _ _ H14); congruence.
        Qed.
      End Seq.

      Section toStructured.
        Variable c : scode.

        Definition toStructured := match c with
                                     | SStraightline is => Scode tt
                                       (fun _ is' cin =>
                                         let iout' := is' (makeIin cin) in
                                           let iout := is (IoutPostcondition iout') in
                                             CompOut (Some (IoutPostcondition iout))
                                             (Loc (CinInject cin tt) (CinPrecondition cin)
                                               (fun lo => (IoutCode iout' lo ++ IoutCode iout lo,
                                                 M.directJump (lo (Local (CinExit cin))))) :: nil)
                                             ((fun lo => (CinPrecondition cin, notStuck iout' lo))
                                               :: (fun lo => (IoutPostcondition iout', notStuck iout lo))
                                               :: nil))
                                     | SStructured r => r
                                   end.

        Hypothesis Hc : scodeOk c.

        Theorem toStructuredOk : scodeROk toStructured.
          unfold toStructured; destruct c; simpl in *; intuition; simpl in *; eauto; split; simpl in *; intuition eauto.

          congruence.

          constructor; [ simpl | constructor ].
          destruct H11 as [? []]; intuition.
          apply incl_cons in H8; destruct H8.
          inversion H7; clear H7; intros; subst; simpl in *.
          inversion H17; clear H17; intros; subst; simpl in *.
          unfold step; split; simpl; intuition.

          destruct (Inj_sound (H16 _ lo _ H14)).
          destruct (Inj_sound (H15 _ lo _ (H4 _ _ _ _ (imports_in H6 H7 H H1) (exports_in H6 H7 H0 H2 H3) H14 H17))).
          eauto.

          apply M.resolve_directJump_unique in H20; subst.
          repeat esplit.
          eapply local_spec; eauto.
          apply (Imply_sound (H13 _ _)).
          apply execs_app in H19; destruct H19; intuition eauto.
        Qed.
      End toStructured.

      Inductive if_label (A B : Type) :=
      | IfTest : if_label A B
      | IfThen : A -> if_label A B
      | IfElse : B -> if_label A B.

      Implicit Arguments IfTest [A B].
      Implicit Arguments IfThen [A B].
      Implicit Arguments IfElse [A B].

      Section If_.
        Variables (b : M.cond) (c1 c2 : scode).

        Definition If_ := let r1 := toStructured c1 in
          let r2 := toStructured c2 in
            SStructured (Scode IfTest (fun _ is cin =>
              let iout := is (makeIin cin) in
                let pre1 st := (Ex st', IoutPostcondition iout st' /\ [< M.decide b st' true st >])%PropX in
                  let pre2 st := (Ex st', IoutPostcondition iout st' /\ [< M.decide b st' false st >])%PropX in
                    let cout1 := ScCompile r1 nullInstrs
                      (CompIn pre1 (CinExit cin) (fun v => CinInject cin (IfThen v))) in
                      let cout2 := ScCompile r2 nullInstrs
                        (CompIn pre2 (CinExit cin) (fun v => CinInject cin (IfElse v))) in
                        CompOut (match CoutPostcondition cout1, CoutPostcondition cout2 with
                                   | None, None => None
                                   | Some post1, None => Some post1
                                   | None, Some post2 => Some post2
                                   | Some post1, Some post2 => Some (fun st => post1 st \/ post2 st)%PropX
                                 end)
                        (Loc (CinInject cin IfTest) (CinPrecondition cin)
                          (fun lo =>
                           let (ins, jmp) := M.conditionalJump b
                             (lo (Local (CinInject cin (IfThen (ScEntry r1)))))
                             (lo (Local (CinInject cin (IfElse (ScEntry r2)))))
                           in
                           (IoutCode iout lo ++ ins, jmp))
                           :: CoutCode cout1 ++ CoutCode cout2)
                        ((fun lo => (CinPrecondition cin, fun st => [<exists st', execs M.exec (IoutCode iout lo) st st'
                          /\ exists b', exists st'', M.decide b st' b' st''>]%type)%PropX)
                        :: CoutConditions cout1 ++ CoutConditions cout2))).

        Hypotheses (Hc1 : scodeOk c1) (Hc2 : scodeOk c2).

        Theorem If_Ok : scodeOk If_.
          unfold If_.
          generalize (toStructuredOk _ Hc1).
          generalize (toStructuredOk _ Hc2).
          generalize (toStructured c1).
          generalize (toStructured c2).
          intros c2' c1' Hc2' Hc1'; simpl in *; eauto.

          split; simpl; intros.
          eauto.
          constructor; simpl.
          eauto.
          apply AllS_app.
          eapply AllS_weaken; [ apply (ScInject Hc2') | ].
          simpl; intuition.
          destruct H; rewrite H; eauto.
          eapply AllS_weaken; [ apply (ScInject Hc1') | ].
          simpl; intuition.
          destruct H; rewrite H; eauto.

          intuition; subst; try congruence.

          apply in_app_or in H0; intuition; simpl in *.
          destruct (AllS_In (ScInject Hc1' _ _) H1); simpl in *.
          rewrite <- H2 in H0; specialize (H _ _ H0); discriminate.
          destruct (AllS_In (ScInject Hc2' _ _) H1); simpl in *.
          rewrite <- H2 in H0; specialize (H _ _ H0); discriminate.

          apply in_app_or in H3; intuition; simpl in *.
          destruct (AllS_In (ScInject Hc1' _ _) H0); simpl in *.
          rewrite H2 in H1; specialize (H _ _ H1); discriminate.
          destruct (AllS_In (ScInject Hc2' _ _) H0); simpl in *.
          rewrite H2 in H1; specialize (H _ _ H1); discriminate.

          apply in_app_or in H3; apply in_app_or in H0; intuition; simpl in *.
          destruct (AllS_In (ScInject Hc1' _ _) H1); simpl in *.
          destruct (AllS_In (ScInject Hc1' _ _) H3); simpl in *.
          rewrite H2 in *.
          rewrite H0 in H4.
          eapply (ScNoDups Hc1'); eauto.
          simpl; intros.
          specialize (H _ _ H5); congruence.

          destruct (AllS_In (ScInject Hc1' _ _) H1); simpl in *.
          destruct (AllS_In (ScInject Hc2' _ _) H3); simpl in *.
          rewrite H2 in *.
          rewrite H0 in H4.
          specialize (H _ _ H4); discriminate.

          destruct (AllS_In (ScInject Hc2' _ _) H1); simpl in *.
          destruct (AllS_In (ScInject Hc1' _ _) H3); simpl in *.
          rewrite H2 in *.
          rewrite H0 in H4.
          specialize (H _ _ H4); discriminate.

          destruct (AllS_In (ScInject Hc2' _ _) H1); simpl in *.
          destruct (AllS_In (ScInject Hc2' _ _) H3); simpl in *.
          rewrite H2 in *.
          rewrite H0 in H4.
          eapply (ScNoDups Hc2'); eauto.
          simpl; intros.
          specialize (H _ _ H5); congruence.

          constructor; simpl.
          apply incl_cons in H8; destruct H8.
          apply incl_app in H12; destruct H12.
          inversion H7; clear H7; intros; subst.
          apply AllS_deapp in H17; destruct H17.
          simpl in *.

          unfold step; split; simpl; intros.
          destruct (Inj_sound (H16 _ lo _ H17)); intuition.
          destruct H20 as [ ? [] ].
          destruct (M.resolve_conditionalJump (lo (Local (CinInject cin (IfThen (ScEntry c1')))))
            (lo (Local (CinInject cin (IfElse (ScEntry c2'))))) H18).
          destruct (M.conditionalJump b
               (lo (Local (CinInject cin (IfThen (ScEntry c1')))))
               (lo (Local (CinInject cin (IfElse (ScEntry c2')))))). simpl.
          eauto.

          intuition.
          specialize (fun x => @M.resolve_conditionalJump_unique b x s'
               (lo (Local (CinInject cin (IfThen (ScEntry c1')))))
               (lo (Local (CinInject cin (IfElse (ScEntry c2')))))); intro HH.
          destruct (M.conditionalJump b
               (lo (Local (CinInject cin (IfThen (ScEntry c1')))))
               (lo (Local (CinInject cin (IfElse (ScEntry c2')))))).
          apply execs_app in H19. destruct H19 as [ ? [ ] ]. 
          apply (HH _ _ H19) in H20; destruct H20; intuition; subst.
          destruct x0.
          match type of H7 with
            | context[ScCompile _ ?cin ?is] => generalize (ScInclude Hc1' cin is); intro Hinc
          end.
          simpl in Hinc.
          match type of Hinc with
            | ?P -> _ => assert P
          end.
          eapply AllS_weaken; [ eauto | ].
          simpl; intuition.
          intuition.
          destruct H22 as [? []]; intuition.
          repeat esplit.
          eapply local_spec; eauto.
          apply (Imply_sound (H24 _ _)).
          propxFo; eauto. eexists; split; [ | eassumption ]. propxFo; eauto.

          match type of H14 with
            | context[ScCompile _ ?cin ?is] => generalize (ScInclude Hc2' cin is); intro Hinc
          end.
          simpl in Hinc.
          match type of Hinc with
            | ?P -> _ => assert P
          end.
          eapply AllS_weaken; [ eauto | ].
          simpl; intuition.
          intuition.
          destruct H22 as [? []]; intuition.
          repeat esplit.
          eapply local_spec; eauto.
          apply (Imply_sound (H24 _ _)).
          propxFo. eexists; split; [ | eassumption ]. propxFo; eauto.

          inversion H7; clear H7; intros; subst; simpl in *.
          apply AllS_deapp in H15; destruct H15.
          apply incl_cons in H8; destruct H8.
          apply incl_app in H13; destruct H13.
          apply AllS_app.

          match goal with
            | [ |- context[ScCompile _ ?cin ?is] ] => apply (ScVerified Hc2' m cin is); simpl; intuition; subst; auto
          end.
          eapply AllS_weaken; [ eauto | ].
          simpl; intuition.
          specialize (H16 _ H17); intuition; subst; simpl in *.
          specialize (H10 _ _ H17); discriminate.
          apply in_app_or in H18; intuition.
          destruct (AllS_In (ScInject Hc1' _ _) H16); simpl in *.
          rewrite H17 in H18.
          specialize (H10 _ _ H18); discriminate.
          specialize (H10 _ _ H16); congruence.
          simpl in *.
          match type of H11 with
            | match match ?E with Some _ => _ | None => _ end with Some _ => _ | None => _ end => destruct E; auto
          end;
          match goal with
            | [ |- match ?E with Some _ => _ | None => _ end ] => destruct E; auto
          end.
          destruct H11 as [? []]; intuition.
          repeat esplit.
          eauto.
          intros.
          apply Imply_I.
          apply (Imply_E (interp_weaken (H17 _ _) _)).
          apply Or_I2.
          apply Env; simpl; tauto.

          match goal with
            | [ |- context[ScCompile _ ?cin ?is] ] => apply (ScVerified Hc1' m cin is); simpl; intuition; subst; auto
          end.
          eapply AllS_weaken; [ eauto | ].
          simpl; intuition.
          specialize (H16 _ H17); intuition; subst; simpl in *.
          specialize (H10 _ _ H17); discriminate.
          apply in_app_or in H18; intuition.
          destruct (AllS_In (ScInject Hc2' _ _) H16); simpl in *.
          rewrite H17 in H18.
          specialize (H10 _ _ H18); discriminate.
          specialize (H10 _ _ H16); congruence.
          match goal with
            | [ |- match ?E with Some _ => _ | None => _ end ] => destruct E; auto
          end;
          match type of H11 with
            | match match ?E with Some _ => _ | None => _ end with Some _ => _ | None => _ end => destruct E; auto
          end.

          destruct H11 as [? []]; intuition.
          repeat esplit.
          eauto.
          intros.
          apply Imply_I.
          apply (Imply_E (interp_weaken (H17 _ _) _)).
          apply Or_I1.
          apply Env; simpl; tauto.
        Qed.
      End If_.

      Inductive while_label (A : Type) :=
      | WhileEntry : while_label A
      | WhileTest : while_label A
      | WhileBody : A -> while_label A.

      Implicit Arguments WhileEntry [A].
      Implicit Arguments WhileTest [A].

      Section While_.
        Variables (p : prop) (b : M.cond) (c : scode).

        Definition While_ := let r := toStructured c in
          SStructured (Scode WhileEntry (fun _ is cin =>
            let iout := is (makeIin cin) in
              let cout := ScCompile r nullInstrs
                (CompIn (fun st => Ex st', p st' /\ [<M.decide b st' true st>])%PropX
                  (CinInject cin WhileTest) (fun v => CinInject cin (WhileBody v))) in
                let post := match CoutPostcondition cout with
                              | None => p
                              | Some post => (fun st => p st \/ post st)%PropX
                            end in
                CompOut (Some (fun st => Ex st', p st' /\ [<M.decide b st' false st>])%PropX)
                (Loc (CinInject cin WhileEntry) (CinPrecondition cin)
                  (fun lo => (IoutCode iout lo, M.directJump (lo (Local (CinInject cin WhileTest)))))
                  :: Loc (CinInject cin WhileTest) post
                  (fun lo => M.conditionalJump b
                    (lo (Local (CinInject cin (WhileBody (ScEntry r)))))
                    (lo (Local (CinExit cin))))
                  :: CoutCode cout)
                ((fun lo => (CinPrecondition cin, notStuck iout lo)%PropX)
                  :: (fun _ => (IoutPostcondition iout, p)%PropX)
                  :: (fun _ => (post, fun st => [<exists b', exists st', M.decide b st b' st'>])%PropX)
                  :: match CoutPostcondition cout with
                       | None => nil
                       | Some p' => (fun _ => (p', p)) :: nil
                     end
                  ++ CoutConditions cout))).

        Hypothesis Hc : scodeOk c.

        Theorem While_Ok : scodeOk While_.
          unfold While_.
          generalize (toStructuredOk _ Hc).
          generalize dependent c.
          intros c' _ Hc'; simpl in *; intuition eauto.
          split; simpl; intuition; subst; simpl in *.

          eauto.

          repeat constructor; simpl; eauto.
          eapply AllS_weaken.
          match goal with
            | [ |- context[ScCompile _ ?cin ?is] ] => apply (ScInject Hc' cin is)
          end.
          simpl; intuition.
          destruct H; rewrite H; eauto.

          intuition; subst; simpl in *; auto.
          specialize (H _ _ H2); discriminate.
          destruct (AllS_In (ScInject Hc' _ _) H1); simpl in *.
          rewrite <- H2 in H0; specialize (H _ _ H0); discriminate.
          specialize (H _ _ H2); discriminate.
          destruct (AllS_In (ScInject Hc' _ _) H1); simpl in *.
          rewrite H2 in H0; specialize (H _ _ H0); discriminate.
          reflexivity.
          destruct (AllS_In (ScInject Hc' _ _) H3); simpl in *.
          rewrite <- H2 in H0; specialize (H _ _ H0); discriminate.
          destruct (AllS_In (ScInject Hc' _ _) H1); simpl in *.
          rewrite H2 in H0; specialize (H _ _ H0); discriminate.
          eapply ScNoDups; eauto; simpl.
          intros.
          specialize (H _ _ H0); congruence.

          apply incl_cons in H8; destruct H8.
          apply incl_cons in H12; destruct H12.
          inversion H7; clear H7; intros; subst; simpl in *.
          inversion H17; clear H17; intros; subst; simpl in *.
          inversion H18; clear H18; intros; subst; simpl in *.
          apply AllS_deapp in H19; destruct H19.
          repeat constructor; simpl; intuition.

          generalize (H16 _ lo _ H19); propxFo.
          unfold step; simpl; eauto.

          unfold step in H20; simpl in H20; intuition.
          apply M.resolve_directJump_unique in H22; subst.
          repeat esplit.
          eapply local_spec; eauto.
          specialize (H15 _ lo _ (H4 _ _ _ _ (imports_in H6 H18 H H1) (exports_in H6 H18 H0 H2 H3) H19 H21)); propxFo.
          match goal with
            | [ |- context[match ?E with Some _ => _ | None => _ end] ] => destruct E
          end.
          apply Or_I1; auto.
          assumption.

          unfold step; simpl.
          destruct (Inj_sound (H17 _ lo _ H19)).
          destruct H20.
          destruct (M.resolve_conditionalJump (lo (Local (CinInject0 (WhileBody (ScEntry (toStructured c'))))))
            (lo (Local CinExit0)) H20).
          destruct (M.conditionalJump b
               (lo (Local (CinInject0 (WhileBody (ScEntry (toStructured c'))))))
               (lo (Local CinExit0))); simpl in *.
          eauto.

          unfold step in H20; simpl in H20; intuition; subst.
          apply (M.resolve_conditionalJump_unique _ _ _ _ H21) in H22; destruct H22; intuition; subst.

          destruct (ScInclude Hc' _ _ H14) as [? []]; simpl in *; intuition.
          destruct H11 as [? []]; intuition.

          destruct x; repeat esplit.
          eapply local_spec; eauto.
          apply (Imply_sound (H24 _ _)); propxFo.
          match type of H19 with
            | context[match ?E with Some _ => _ | None => _ end] => destruct E; propxFo; eauto
          end.
          inversion H7; clear H7; intros; subst; simpl in *; eauto.
          eexists; split; eauto. propxFo.          
          eapply local_spec; eauto.
          apply (Imply_sound (H25 _ _)); propxFo.
          match type of H19 with
            | context[match ?E with Some _ => _ | None => _ end] => destruct E; propxFo; eauto
          end.
          inversion H7; clear H7; intros; subst; simpl in *; auto.
          eexists; split; eauto. propxFo.

          apply (ScVerified Hc'); simpl; intuition; subst; auto.

          eapply AllS_weaken; [ eassumption | ].
          simpl; intuition.
          specialize (H18 _ H19); simpl in H18; intuition; subst; simpl in *.
          specialize (H10 _ _ H19); discriminate.
          specialize (H10 _ _ H19); discriminate.

          simpl in *.
          specialize (H10 _ _ H18); congruence.

          match goal with
            | [ |- match ?E with Some _ => _ | None => _ end ] => destruct E; auto
          end.
          simpl.
          inversion H7; clear H7; intros; subst; simpl in *.
          clear H21.
          repeat esplit.
          eauto.
          intros; apply Imply_I; apply Or_I2; apply Env; simpl; tauto.
        Qed.
      End While_.
    End exports.

    Record sfunc := Sfunc {
      SName : string;
      SSpec : prop;
      SCode : list (string * prop) -> list (string * prop) -> scode
    }.

    Section bmodule.
      Variable funcs : list sfunc.

      Definition exports := map (fun sf => (SName sf, SSpec sf)) funcs.

      Fixpoint labelT (fs : list sfunc) : Type :=
        match fs with
          | nil => Empty_set
          | f :: fs => ScLabT (toStructured (SCode f imports exports)) + labelT fs
        end%type.

      Record doFuncs_out (GT : Type) := Df {
        Locs : list (local M.pc M.state block GT);
        Exps : list (export M.pc M.state block GT)
      }.

      Fixpoint doFuncs GT (fs : list sfunc) : (labelT fs -> GT) -> doFuncs_out GT :=
        match fs with
          | nil => fun _ => Df nil nil
          | f :: fs' => fun inj =>
            let r := toStructured (SCode f imports exports) in
            let cout := ScCompile r nullInstrs (CompIn (SSpec f)
              (inj (inl _ (ScEntry r)))
              (fun x => inj (inl _ x))) in
            let df := doFuncs fs' (fun x => inj (inr _ x)) in
              Df (CoutCode cout ++ Locs df)
              (Exp (SName f) (SSpec f) (fun lo => (nil, M.directJump (lo (Local (inj (inl _ (ScEntry r))))))) :: Exps df)
        end.

      Definition vcPasses (f : sfunc) := forall GT (inj : ScLabT (toStructured (SCode f imports exports)) -> GT),
        let r := toStructured (SCode f imports exports) in
        let cout := ScCompile r nullInstrs (CompIn (SSpec f)
          (inj (ScEntry r)) inj) in
        AllS (fun p' => forall specs lo st, interp specs (fst (p' lo) st) -> interp specs (snd (p' lo) st))
        (CoutConditions cout).

      Definition bmodule_ : module M.pc M.state block :=
        let df := doFuncs funcs (fun x => x) in
          Mod (map (fun p => Imp (fst p) (snd p)) imports)
          (Locs df) (Exps df).

      Lemma doFuncs_inj : forall GT fs (inj : _ -> GT),
        AllS (fun f => scodeOk exports (SCode f imports exports)) fs
        -> AllS (fun L => exists v, LLabel L = inj v) (Locs (doFuncs fs inj)).
        induction fs; simpl; intuition; fold labelT in *.

        inversion H; clear H; subst.

        apply AllS_app.
        
        specialize (IHfs (fun x => inj (inr _ x)) H3).
        eapply AllS_weaken; [ eassumption | ].
        simpl; intuition.
        destruct H; eauto.

        eapply AllS_weaken.
        apply (ScInject (toStructuredOk _ _ H2)).
        simpl; intuition.
        destruct H; eauto.
      Qed.

      Lemma doFuncs_NoDupsL : forall GT (L1 L2 : local M.pc M.state block GT) fs inj,
        (forall x y, inj x = inj y -> x = y)
        -> In L1 (Locs (doFuncs fs inj))
        -> In L2 (Locs (doFuncs fs inj))
        -> LLabel L1 = LLabel L2
        -> AllS (fun f => scodeOk exports (SCode f imports exports)) fs
        -> L1 = L2.
        induction fs; simpl; intuition; fold labelT in *.

        inversion H3; clear H3; subst.

        apply in_app_or in H0; apply in_app_or in H1; intuition.

        match type of H3 with
          | context[ScCompile _ ?is ?cin] => pose is; pose cin
        end.
        eapply (ScNoDups (toStructuredOk _ _ H6)) with (is := i) (cin := c); subst i c; simpl; intuition.
        apply H in H1; congruence.

        destruct (AllS_In (doFuncs_inj _ H7) H0).
        match type of H3 with
          | context[ScCompile _ ?is ?cin] => apply (AllS_In (ScInject (toStructuredOk _ _ H6) is cin)) in H3
        end.        
        simpl in H3; destruct H3.
        rewrite H2 in H3; rewrite H3 in H1.
        apply H in H1; discriminate.

        destruct (AllS_In (doFuncs_inj _ H7) H3).
        match type of H0 with
          | context[ScCompile _ ?is ?cin] => apply (AllS_In (ScInject (toStructuredOk _ _ H6) is cin)) in H0
        end.        
        simpl in H0; destruct H0.
        rewrite H2 in H1; rewrite H1 in H0.
        apply H in H0; discriminate.

        destruct (AllS_In (doFuncs_inj _ H7) H3).
        destruct (AllS_In (doFuncs_inj _ H7) H0).
        rewrite H2 in H1; rewrite H1 in H4.
        apply IHfs with (fun x => inj (inr _ x)); intuition.
        apply H in H5; congruence.
      Qed.

      Fixpoint noDups A (ls : list (string * A)) : bool :=
        match ls with
          | nil => true
          | (s, v) :: ls' =>
            match lookup s ls' with
              | None => noDups ls'
              | Some _ => false
            end
        end.

      Lemma In_Exps : forall GT E fs (inj : _ -> GT),
        In E (Exps (doFuncs fs inj))
        -> exists p, In (ELabel E, p) (map (fun sf => (SName sf, SSpec sf)) fs).
        induction fs; simpl; intuition; subst; simpl; eauto.

        apply IHfs in H0.
        destruct H0; eauto.
      Qed.

      Lemma doFuncs_NoDupsE : forall GT E1 E2 fs (inj : _ -> GT),
        noDups (map (fun sf => (SName sf, SSpec sf)) fs) = true
        -> In E1 (Exps (doFuncs fs inj))
        -> In E2 (Exps (doFuncs fs inj))
        -> ELabel E1 = ELabel E2
        -> E1 = E2.
        induction fs; simpl; intuition; fold labelT in *; subst; simpl in *; intuition.

        specialize (IHfs (fun x => inj (inr _ x))).
        generalize (lookup_correct (SName a) (map (fun sf => (SName sf, SSpec sf)) fs)); intro Hl.
        destruct (lookup (SName a) (map (fun sf => (SName sf, SSpec sf)) fs)); try discriminate.
        apply In_Exps in H0; destruct H0.
        rewrite H2 in Hl.
        elimtype False; eapply Hl; eauto.

        specialize (IHfs (fun x => inj (inr _ x))).
        generalize (lookup_correct (SName a) (map (fun sf => (SName sf, SSpec sf)) fs)); intro Hl.
        destruct (lookup (SName a) (map (fun sf => (SName sf, SSpec sf)) fs)); try discriminate.
        apply In_Exps in H3; destruct H3.
        rewrite <- H2 in Hl.
        elimtype False; eapply Hl; eauto.

        destruct (lookup (SName a) (map (fun sf => (SName sf, SSpec sf)) fs)); try discriminate.
        eauto.
      Qed.

      Lemma bmodule_ExpsOk : forall m lo (Hlo : injective lo)
        (Hnd : forall L1 L2, In L1 (Locals m) -> In L2 (Locals m) -> LLabel L1 = LLabel L2 -> L1 = L2)
        fs (inj : _ -> LabelT m),
        incl (Locs (doFuncs fs inj)) (Locals m)
        -> AllS vcPasses fs
        -> AllS (fun f => scodeOk exports (SCode f imports exports)) fs
        -> AllS (fun L => blockOk step M.pc_eq m lo (ESpec L) (EBlock L lo)) (Exps (doFuncs fs inj)).
        induction fs; simpl; intuition; fold labelT in *.

        inversion H1; clear H1; subst.
        
        constructor; simpl; intuition.

        split; simpl; intuition.
        unfold step; simpl.
        repeat esplit.
        apply M.resolve_directJump.

        unfold step in H3; simpl in H3; intuition; subst.
        apply M.resolve_directJump_unique in H7; subst.
        inversion H0; clear H0; subst.
        destruct (ScInclude (toStructuredOk _ _ H4) nullInstrs
          (CompIn (SSpec a) (inj (inl _ (ScEntry (toStructured (SCode a imports exports))))) (fun x => inj (inl _ x)))
          (H7 _ (fun x => inj (inl _ x))))
        as [? []]; intuition.
        repeat esplit.
        apply H1.
        unfold specOf.
        rewrite specOfI_Local by auto.
        erewrite specOfL_In; eauto.
        apply H; simpl.
        apply in_or_app; eauto.
        simpl in *.
        apply (Imply_sound (H6 _ _)); assumption.

        apply IHfs.
        apply incl_app in H; tauto.
        inversion H0; tauto.

        assumption.
      Qed.

      Fixpoint doFuncs_ok GT (fs : list sfunc) : (labelT fs -> GT) -> bool :=
        match fs with
          | nil => fun _ => true
          | f :: fs' => fun inj =>
            let r := toStructured (SCode f imports exports) in
            let cout := ScCompile r nullInstrs (CompIn (SSpec f)
              (inj (inl _ (ScEntry r)))
              (fun x => inj (inl _ x))) in
            match CoutPostcondition cout with
              | Some _ => false
              | None => doFuncs_ok fs' (fun x => inj (inr _ x))
            end
        end.

      Lemma bmodule_LocalsOk : forall m lo (Hlo : injective lo)
        (Hnd : forall L1 L2, In L1 (Locals m) -> In L2 (Locals m) -> LLabel L1 = LLabel L2 -> L1 = L2)
        (Himps : AllS (fun p => In (Imp (fst p) (snd p)) (Imports m)) imports)
        (Hexps : AllS (fun p => exists cd : layout M.pc (LabelT m) -> block,
          In (Exp (fst p) (snd p) cd) (Exports m)) exports)
        (HimpNd : forall im1 im2, In im1 (Imports m)
          -> In im2 (Imports m)
          -> ILabel im1 = ILabel im2
          -> ISpec im1 = ISpec im2)
        (HexpNd : forall im1 im2, In im1 (Exports m)
          -> In im2 (Exports m)
          -> ELabel im1 = ELabel im2
          -> ESpec im1 = ESpec im2)
        (HimpExp : forall im1 im2, In im1 (Imports m)
          -> In im2 (Exports m)
          -> ILabel im1 <> ELabel im2)
        fs (inj : _ -> LabelT m) (Hinj : forall x y, inj x = inj y -> x = y),
        incl (Locs (doFuncs fs inj)) (Locals m)
        -> AllS vcPasses fs
        -> AllS (fun L => forall v, LLabel L = inj v -> In L (Locs (doFuncs fs inj))) (Locals m)
        -> doFuncs_ok fs inj = true
        -> AllS (fun f => scodeOk exports (SCode f imports exports)) fs
        -> AllS (fun L => blockOk step M.pc_eq m lo (LSpec L) (LBlock L lo)) (Locs (doFuncs fs inj)).
        induction fs; simpl; intuition; fold labelT in *.

        inversion H3; clear H3; subst.

        match type of H2 with
          | context[match ?E with Some _ => _ | None => _ end] => case_eq E
        end; [ intros ? Heq | intro Heq ]; rewrite Heq in H2; try discriminate.

        apply AllS_app.

        apply IHfs.
        intros.
        apply Hinj in H3; congruence.
        apply incl_app in H; tauto.
        inversion H0; tauto.

        inversion H0; clear H0; subst.
        apply incl_app in H; destruct H.
        eapply AllS_weaken; [ eassumption | ].
        simpl; intuition.
        specialize (H3 _ H4); simpl in H4.
        apply in_app_or in H3; intuition.
        match type of H9 with
          | context[ScCompile ?r ?is ?cin] =>
            destruct (AllS_In (ScInject (toStructuredOk _ _ H6) is cin) H9); simpl in *
        end.
        rewrite H4 in H3.
        apply Hinj in H3; discriminate.

        auto.

        assumption.
        inversion H0; clear H0; subst.
        apply incl_app in H; destruct H.
        apply (ScVerified (toStructuredOk _ _ H6)); simpl; intuition; simpl in *; subst; auto.

        apply (H5 _ (fun x => inj (inl _ x))).

        eapply AllS_weaken; [ eassumption | ].
        simpl; intuition.
        specialize (H3 _ H4).
        apply in_app_or in H3; intuition.
        apply (AllS_In (doFuncs_inj _ H7)) in H9; destruct H9.
        rewrite H4 in H3.
        apply Hinj in H3; discriminate.

        apply Hinj in H3; congruence.

        rewrite Heq; split.
      Qed.

      Lemma more_exports : forall GT funcs (inj : _ -> GT),
        AllS (fun p => exists cd, In (Exp (fst p) (snd p) cd)
          (Exps (doFuncs funcs inj)))
        (map (fun sf => (SName sf, SSpec sf)) funcs).
        induction funcs0; simpl; intuition; fold labelT in *.
        constructor; simpl; intuition eauto.
        specialize (IHfuncs0 (fun x => inj (inr _ x))).
        eapply AllS_weaken; [ eassumption | ].
        simpl; intuition.
        destruct H; eauto.
      Qed.

      Lemma use_noDups_imports : forall (L1 L2 : import M.pc M.state) imps,
        noDups imps = true
        -> In L1 (map (fun p => Imp (fst p) (snd p)) imps)
        -> In L2 (map (fun p => Imp (fst p) (snd p)) imps)
        -> ILabel L1 = ILabel L2
        -> ISpec L1 = ISpec L2.
        induction imps as [ | []]; simpl; intuition; subst; simpl in *; subst; intuition.

        generalize (lookup_correct (ILabel L2) imps); intro Hl.
        destruct (lookup (ILabel L2) imps); try discriminate.
        apply in_map_iff in H0; destruct H0; intuition; subst; simpl in *.
        destruct x; simpl in *; elimtype False; eapply Hl; eauto.

        generalize (lookup_correct (ILabel L1) imps); intro Hl.
        destruct (lookup (ILabel L1) imps); try discriminate.
        apply in_map_iff in H3; destruct H3; intuition; subst; simpl in *.
        destruct x; simpl in *; elimtype False; eapply Hl; eauto.

        destruct (lookup s imps); try discriminate.
        auto.
      Qed.

      Lemma more_exports' : forall GT fs (inj : _ -> GT),
        AllS (fun p => In (ELabel p, ESpec p)
          (map (fun sf => (SName sf, SSpec sf)) fs))
        (Exps (doFuncs fs inj)).
        induction fs; simpl; intuition; fold labelT in *.
        constructor; simpl; intuition eauto.
        specialize (IHfs (fun x => inj (inr _ x))).
        eapply AllS_weaken; [ eassumption | ].
        simpl; intuition.
      Qed.

      Lemma use_noDups_exports : forall GT L1 L2 fs (inj : _ -> GT),
        noDups (map (fun sf => (SName sf, SSpec sf)) fs) = true
        -> In L1 (Exps (doFuncs fs inj))
        -> In L2 (Exps (doFuncs fs inj))
        -> ELabel L1 = ELabel L2
        -> ESpec L1 = ESpec L2.
        induction fs; simpl; intuition; subst; simpl in *; auto.

        generalize (lookup_correct (SName a) (map (fun sf => (SName sf, SSpec sf)) fs)); intro Hl.
        destruct (lookup (SName a) (map (fun sf => (SName sf, SSpec sf)) fs)); try discriminate.
        generalize (AllS_In (more_exports' fs (fun x => inj (inr _ x))) H0); intro.
        rewrite <- H2 in H1.
        elimtype False; eapply Hl; eauto.

        generalize (lookup_correct (SName a) (map (fun sf => (SName sf, SSpec sf)) fs)); intro Hl.
        destruct (lookup (SName a) (map (fun sf => (SName sf, SSpec sf)) fs)); try discriminate.
        generalize (AllS_In (more_exports' fs (fun x => inj (inr _ x))) H3); intro.
        rewrite H2 in H0.
        elimtype False; eapply Hl; eauto.

        destruct (lookup (SName a) (map (fun sf => (SName sf, SSpec sf)) fs)); try discriminate.
        eauto.
      Qed.

      Fixpoint noOverlap A (ls1 ls2 : list (string * A)) : bool :=
        match ls1 with
          | nil => true
          | (s, v) :: ls1' =>
            match lookup s ls2 with
              | None => noOverlap ls1' ls2
              | Some _ => false
            end
        end.

      Lemma no_overlap : forall GT L1 L2 imps fs (inj : _ -> GT),
        noOverlap (map (fun sf => (SName sf, SSpec sf)) fs) imps = true
        -> In L1 (Exps (doFuncs fs inj))
        -> In L2 (map (fun p => Imp (fst p) (snd p)) imps)
        -> ELabel L1 = ILabel L2
        -> False.
        induction fs; simpl; intuition; subst; simpl in *.

        generalize (lookup_correct (SName a) imps); intro Hl.
        destruct (lookup (SName a) imps); try discriminate.
        apply in_map_iff in H1; destruct H1; intuition; subst; simpl in *.
        destruct x; simpl in *; subst; eauto.

        destruct (lookup (SName a) imps); try discriminate.
        eauto.
      Qed.

      Theorem bmoduleOk : andb (doFuncs_ok funcs (fun x => x))
        (andb (noOverlap exports imports) (andb (noDups imports) (noDups exports))) = true
        -> AllS (fun f => scodeOk exports (SCode f imports exports)) funcs
        -> AllS vcPasses funcs
        -> moduleOk step M.pc_eq bmodule_.
        case_eq (doFuncs_ok funcs (fun x => x)); simpl; try (intros; discriminate).
        case_eq (noOverlap exports imports); simpl; try (intros; discriminate).
        case_eq (noDups imports); simpl; intuition; try discriminate.

        split; simpl; intuition.

        apply (doFuncs_NoDupsL L1 L2 (fun x => x)); auto.

        eapply doFuncs_NoDupsE; eauto.

        split.

        simpl Locals; apply bmodule_LocalsOk; intuition.
        apply (doFuncs_NoDupsL L1 L2 (fun x => x)); auto.
        simpl.
        clear H H0 H3; induction imports; simpl; intuition; constructor; simpl; intuition.
        intuition.
        eapply AllS_weaken; [ eassumption | ]; intuition.
        simpl.
        apply more_exports; auto.
        simpl in *; subst.
        apply (use_noDups_imports _ _ _ H H6 H7); auto.
        apply (use_noDups_exports _ _ _ _ H2 H6 H7); auto.
        simpl in *; subst.
        eapply no_overlap; eauto.
        simpl.
        eapply AllS_weaken'.
        apply doFuncs_inj.
        simpl; intuition.

        intuition.

        simpl Exports; eapply bmodule_ExpsOk; eauto.
        intros; apply (doFuncs_NoDupsL L1 L2 (fun x => x)); auto.
        unfold incl; auto.
      Qed.
    End bmodule.
  End imports.

  Hint Resolve HaltOk SkipOk StraightLineOk GotoOk GotoIOk WithCodeOk Assert_Ok Call_Ok CallIOk Use_Ok SeqOk If_Ok While_Ok : Structured.

  Implicit Arguments Goto [imports exports].
  Implicit Arguments WithCode [imports exports].
  Implicit Arguments Call_ [imports exports].

  Ltac structured tac :=
    apply bmoduleOk; [ reflexivity |
      simpl exports; tac; repeat match goal with
                                   | [ |- AllS _ _ ] => constructor
                                 end; unfold SCode; auto 999999 with Structured |
      tac; unfold vcPasses; simpl exports;
        cbv beta iota zeta delta [IoutPostcondition IoutCode
          CinPrecondition CinExit CinInject
          CoutPostcondition CoutCode CoutConditions
          ScLabT ScEntry ScCompile
          Skip Halt StraightLine GotoI WithCode Goto Assert_ Call_ CallI Use_
          SeqI Seq toStructured If_ While_
          exports
          SName SSpec SCode 
          Locs Exps
          nullInstrs makeIin labelT]; simpl;
        repeat match goal with
                 | [ |- AllS _ _ ] => constructor; intros
               end; simpl in * ].

  Ltac postStructured tac := propxFo;
    (* unfold M.eval, M.exec, M.resolve, M.decide in *; *) 
    intuition auto; try subst; simpl in *;
      tac; intuition auto; try subst; simpl in *; try autorewrite with Mac in *.
End Make.

Ltac use E := generalize E; intro.
