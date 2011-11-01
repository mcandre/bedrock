Require Import Arith FunctionalExtensionality Malloc Typed Impure Lambda IfStar Wrap SqlTree.
Import SP.


Lemma allocated_mid_fwd' : forall pos len base,
  base <= pos < base + len
  -> allocated base len ===> Ex v, !{allocated base (pos-base)} * pos ==> v * !{allocated (pos+1) (len-(pos-base)-1)}.
  induction len; intros.
  elimtype False; omega.
  destruct (eq_nat_dec base pos); subst.
  rewrite minus_diag.
  sepLemma.
  specialize (IHlen (S base)).
  match type of IHlen with
    | ?P -> _ => assert P; intuition
  end.
  sepLemma.
  case_eq (pos - base)%nat; intros.
  elimtype False; omega.
  sepLemma.
Qed.

Theorem allocated_mid_fwd : forall pos base len,
  base <= pos < base + len
  -> allocated base len ===> Ex v, !{allocated base (pos-base)} * pos ==> v * !{allocated (pos+1) (len-(pos-base)-1)}.
  intros; apply allocated_mid_fwd'; auto.
Qed.

Lemma allocated_mid_bwd' : forall pos len base,
  base <= pos < base + len
  -> Ex v, !{allocated base (pos-base)} * pos ==> v * !{allocated (pos+1) (len-(pos-base)-1)} ===> allocated base len.
  induction len; intros.
  elimtype False; omega.
  destruct (eq_nat_dec base pos); subst.
  rewrite minus_diag.
  sepLemma.
  specialize (IHlen (S base)).
  match type of IHlen with
    | ?P -> _ => assert P; intuition
  end.
  case_eq (pos - base)%nat; intros.
  elimtype False; omega.
  sepLemma.
Qed.

Theorem allocated_mid_bwd : forall pos base len,
  base <= pos < base + len
  -> Ex v, !{allocated base (pos-base)} * pos ==> v * !{allocated (pos+1) (len-(pos-base)-1)} ===> allocated base len.
  intros; apply allocated_mid_bwd'; auto.
Qed.

Theorem typingHolds'_fwd : forall specs m fr ms tp,
  interp specs (typingHolds' m fr ms tp)
  -> interp specs (Ex xs, ![ Impure (tp xs) * ![fr] ] m /\ Pure (tp xs))%PropX.
  induction ms; simpl; propxFo.
  eauto.
  apply IHms in H; propxFo; eauto.
Qed.

Theorem typingHolds'_bwd : forall specs m fr ms tp,
  interp specs (Ex xs, ![ Impure (tp xs) * ![fr] ] m /\ Pure (tp xs))%PropX
  -> interp specs (typingHolds' m fr ms tp).
  induction ms; simpl; propxFo.
  destruct x; auto.
  destruct x; auto.
  destruct x; simpl in *.
  eexists; apply simplify_fwd; apply IHms.
  propxFo.
  eauto.
Qed.

Theorem typingHolds'_fwd' : forall specs m fr ms tp,
  interp specs (typingHolds' m fr ms tp
    --> Ex xs, ![ Impure (tp xs) * ![fr] ] m /\ Pure (tp xs))%PropX.
  induction ms; simpl; intros.

  apply Imply_I.
  apply Exists_I with tt.
  apply Env; simpl; auto.

  apply Imply_I.
  eapply Exists_E.
  apply Env; simpl; auto.
  simpl; intro x.
  eapply Exists_E.
  eapply Imply_E.
  specialize (IHms (fun ms0 => tp (x, ms0))).
  simpl in IHms.
  apply interp_weaken.
  eauto.
  apply Env; simpl; auto.
  simpl; intro ms'.
  apply Exists_I with (x, ms').
  apply Env; simpl; auto.
Qed.

Theorem sep_lockstep : forall p2 p2',
  p2 ===> p2'
  -> forall p1 p1',
    p1 ===> p1'
    -> p1 * p2 ===> p1' * p2'.
  unfold Himp, sep; simpl; intros.

  apply sep'_ex in H1; firstorder.
  apply sep'_ex in H1; firstorder.
  unfold sep in *.
  rewrite stars_def in *.
  apply stars'_app_fwd in H4.
  firstorder.
  apply sep'_weaken with (fun (P : Prop) (ps : list hprop) => P /\ stars' ps x3); auto.
  intuition.
  apply sep'_weaken with (fun (P : Prop) (ps : list hprop) => P /\ stars' ps x4); auto.
  intuition.
  eapply stars'_app_bwd; eauto.
  red; eauto.
Qed.

Ltac hide_fwd := intros; repeat apply sep_lockstep; red; auto;
  unfold sep; simpl; intuition;
    rewrite stars_def in *; simpl; red;
      match goal with
        | [ sm : _ |- _ ] => exists sm; exists (fun _ => None); intuition; splitmaster
      end.

Theorem bwd_final : forall p sm,
  stars (p :: nil) sm
  -> p sm.
  rewrite stars_def; simpl; intros.
  destruct H as [ ? [ ? [ ? [ ] ] ] ].
  replace sm with x.
  auto.
  extensionality v.
  red in H; intuition.
  rewrite H3.
  red in H1; intuition.
  rewrite H4.
  destruct (x v); auto.
Qed.

Ltac hide_bwd := intros; repeat apply sep_lockstep; red; auto;
  unfold sep; simpl; intuition;
    match goal with
      | [ H : _ |- _ ] => apply bwd_final in H; auto
    end.

Theorem sep_hide_fwd : forall p1 p2 p3 p4,
  ((p1 * (p2 * p3)) * p4)%Sep ===> ((p1 * (p2 * !{p3})) * p4)%Sep.
  hide_fwd.
Qed.

Theorem sep_hide_bwd : forall p1 p2 p3 p4 p5,
  ((p1 * (p2 * (p3 * !{p4}))) * p5)%Sep ===> ((p1 * (p2 * (p3 * p4))) * p5)%Sep.
  hide_bwd.
Qed.

Theorem sep_hide_fwd1 : forall p1 p2 p3 p4 p5,
  ((p1 * (p2 * (p3 * p4))) * p5)%Sep ===> ((p1 * (p2 * (p3 * !{p4}))) * p5)%Sep.
  hide_fwd.
Qed.

Theorem sep_hide_bwd1 : forall p1 p2 p3 p4,
  ((p1 * (p2 * !{p3})) * p4)%Sep ===> ((p1 * (p2 * p3)) * p4)%Sep.
  hide_bwd.
Qed.


Fixpoint tuple (T : Type) (n : nat) : Type :=
  match n with
    | O => unit
    | S n' => T * tuple T n'
  end%type.

Definition scode' := list (string * prop) -> list (string * prop) -> scode.

Section Insert.
  Variable numCols : nat.
  Variable table : var.
  Variable fields : tuple exp (numCols + 2).
  Variable inv : frame -> type0.
  Variable post : frame -> word -> type0.

  Open Scope Mir_scope.

  Fixpoint Insert'' (n : nat) : tuple exp n -> list cmd :=
    match n with
      | O => fun _ => nil
      | S n' => fun es => Write (Retv + n') (fst es) :: Insert'' n' (snd es)
    end.

  Definition Insert' :=
    SStraightline (fun iin => InsOut (fun st => Ex st', iin st' /\ [< execs SPArg.exec (Insert'' _ fields) st' st >])%PropX
      (fun _ _ => Insert'' _ fields)).

  Definition Insert0 :=
    Call "malloc" Args #0, #numCols
    [TYPEDc
      PRE [arg, rv']
        heap,,
        arg table :: sqlTree (numCols + 2),,
        rv' :: chunk (numCols + 2),,
        inv arg
      POST [rv]
        post arg rv];;
    (fun _ _ => Insert');;
    Call "insert" Args #numCols, $ table, Retv
    [TYPEDi
      PRE [arg]
        heap,,
        arg table :: sqlTree (numCols + 2),,
        inv arg
      POST [rv]
        post arg rv].

  Variables imports exports : list (string * prop).

  Theorem Insert'Ok : scodeOk imports exports Insert'.
    unfold Insert'; do 2 red; propxFo; eauto.
  Qed.

  Theorem Insert0Ok : scodeOk imports exports (Insert0 imports exports).
    apply SeqOk.
    apply Call_Ok.
    apply SeqOk.
    apply Insert'Ok.
    apply Call_Ok.
  Qed.

  Definition Insert := Wrap (Insert0 imports exports) (fun _ cin iout =>
    (fun _ => (fun _ => [< True >], fun _ => [< lookupS imports exports "malloc" = Some mallocS >]))%PropX
    :: (fun _ => (fun _ => [< True >], fun _ => [< lookupS imports exports "insert" = Some insertS >]))%PropX
    :: (fun lo => (CinPrecondition cin, notStuck iout lo))
    :: (fun _ => (IoutPostcondition iout, TYPEDi
      PRE [arg]
        heap,,
        arg table :: sqlTree (numCols + 2),,
        inv arg
      POST [rv]
        post arg rv))
    :: (fun _ => (TYPEDc
      PRE [arg, rv']
        heap,,
        arg table :: sqlTree (numCols + 2),,
        rv' :: chunk (numCols + 2),,
        inv arg
      POST [rv]
        post arg rv,
        fun st => [< exists st', execs SPArg.exec (Insert'' _ fields) st st' >]))%PropX
    :: nil).

  Fixpoint mupds (rv : word) (ws : list word) (n : nat) : tuple exp n -> mem -> mem :=
    match ws, n return tuple exp n -> mem -> mem with
      | w :: ws', S n' => fun es m => mupds rv ws' n' (snd es) (Mir.mupd m (rv + n')%nat w)
      | _, _ => fun _ m => m
    end.
    
  Lemma execs_Insert'' : forall n tuple st st',
    execs SPArg.exec (Insert'' n tuple) st st'
    -> exists ws, Mem st' = mupds (Retval st) ws n tuple (Mem st)
      /\ Frames st' = Frames st
      /\ Retval st' = Retval st.
    induction n; simpl; intuition; subst.

    exists nil; eauto.

    destruct H; intuition.
    unfold SPArg.exec in H0; simpl in H0.
    repeat (match goal with
              | [ _ : match ?E with None => _ | Some _ => _ end = Some _ |- _ ] => destruct E
              | [ _ : (if ?E then _ else _) = Some _ |- _ ] => destruct E
            end; try discriminate).
    injection H0; clear H0; intros; subst.
    apply IHn in H1; simpl in H1; destruct H1; intuition.
    rewrite H0.
    exists (w :: x); auto.
  Qed.

  Theorem stepper : forall p1 p2 p3 p4 p5 rv n tuple ls base len m,
    (base <= rv)%nat
    -> (rv + n <= base + len)%nat
    -> stars (p1 :: p2 :: p3 :: p4 :: sep (allocated base len) :: p5 :: nil)
    (fun a : word => if Compare_dec.le_lt_dec MemHigh a then None else Some (m a))
    -> stars (p1 :: p2 :: p3 :: p4 :: sep (allocated base len) :: p5 :: nil)
    (fun a : word => if Compare_dec.le_lt_dec MemHigh a then None else Some (mupds rv ls n tuple m a)).
    induction n; destruct ls; simpl; intuition.
    apply IHn; auto.
    use (allocated_mid_fwd (rv + n)%nat).
    use (allocated_mid_bwd (rv + n)%nat).
    sepFwd.

    assert (rv + n < MemHigh)%nat.
    apply (@read (rv + n)%nat (rv + n)%nat tt x
      (sep (allocated (rv + n + 1) (len - (rv + n - base) - 1)) :: p5 :: nil)
      (p1 :: p2 :: p3 :: p4 :: sep (allocated base (rv + n - base)) :: nil)) in H2.
    rewrite readWord_eq in H2.
    destruct (Compare_dec.le_lt_dec MemHigh (rv + n)); [ discriminate | eauto ].
    auto.

    sep1.
  Qed.

  Theorem InsertOk : scodeOk imports exports Insert.
    apply WrapOk; intuition.

    repeat match goal with
             | [ H : AllS _ _ |- _ ] => inversion H; clear H; subst
           end; simpl in *.

    unfold Insert0.
    simpl; repeat match goal with
                    | [ |- AllS _ _ ] => constructor; simpl
                  end; intuition.

    propxFo.
    unfold SPArg.exec; simpl; eauto 10.

    specialize (H2 specs lo st (Inj_I _ _ I)).
    apply Inj_sound in H2; rewrite H2.
    pre.
    specialize (H4 _ lo _ H0); propxFo.
    destruct (Frames x); propxFo.
    destruct f0; propxFo.

    specialize (typingHolds'_fwd _ _ _ _ _ H); propxFo.

    apply sep_hide_fwd in H10.
    pre.
    sep1.
    sep0.
    sep0.
    autorewrite with PropX.
    apply simplify_fwd; apply typingHolds'_bwd; propxFo.
    eexists; repeat split.

    apply sep_hide_bwd.
    sep1.
    auto.
    auto.
    sep0.
    intros.
    simpl.

    let T := type of (H9 x10) in
      match goal with
        | [ |- ?G ] => replace G with T; auto
      end.
    repeat f_equal.

    match goal with
      | [ |- context [subst (lift ?p ?G) ?p'] ] =>
        generalize (lift_cons' p G (refl_equal _) p')
    end.
    intros.
    eapply eq_trans; [ | symmetry; apply H12 ].
    simpl.
    match goal with
      | [ |- context [lift ?p nil] ] =>
        generalize (lift_nada' p (refl_equal _)); auto
    end.

    propxFo.
    unfold SPArg.exec; simpl.

    case_eq (Frames x); [ intro Heq | intros ? ? Heq ]; rewrite Heq in *; propxFo.
    repeat esplit.
    simpl.

    apply execs_Insert'' in H6; destruct H6; intuition.
    rewrite H0.
    rewrite Heq.
    eauto.

    specialize (H1 specs lo st (Inj_I _ _ I)).
    apply Inj_sound in H1; rewrite H1.
    pre.
    apply execs_Insert'' in H13; simpl in H13; destruct H13; intuition.
    injection H0; clear H0; intros; subst.

    pre.
    apply typingHolds'_fwd in H; propxFo.

    apply sep_hide_fwd1 in H0.
    sepSimp.
    sepSimpFull.
    apply stepper; auto.
    sepCancel.

    sep0.
    sep0.
    autorewrite with PropX.
    apply simplify_fwd; apply typingHolds'_bwd; propxFo.
    eexists; repeat split.

    apply sep_hide_bwd1.
    sep1.
    auto.
    sep0.
    intros.
    simpl.

    let T := type of (H10 x13) in
      match goal with
        | [ |- ?G ] => replace G with T; auto
      end.
    repeat f_equal.

    match goal with
      | [ |- context [subst (lift ?p ?G) ?p'] ] =>
        generalize (lift_cons' p G (refl_equal _) p')
    end.
    intros.
    eapply eq_trans; [ | symmetry; apply H ].
    simpl.
    match goal with
      | [ |- context [lift ?p nil] ] =>
        generalize (lift_nada' p (refl_equal _)); auto
    end.

    constructor.

    apply Insert0Ok.
  Qed.
End Insert.

Hint Resolve InsertOk : Structured.

Notation "'INSERT' 'INTO' table 'VALUES' ( e1 , .. , eN ) 'INVARIANT' [ fr ] pre 'POST' [ rv ] post" :=
  (Insert ((fun _ => S) e1 .. ((fun _ => S) eN O) .. - 2) table (pair e1 .. (pair eN tt) ..) (fun fr => pre%Typed) (fun fr rv => post%Typed))
  (no associativity, at level 95) : Mir_scope.


Section traversals.
  Variable numCols : nat.
  Variable table : var.
  Variable capture : list var.
  Variable inv : frame -> type0.
  Variable post : frame -> word -> type0.

  Inductive nexp : Type :=
  | NConst : nat -> nexp
  | NCol : forall n : nat, leb (numCols + 2) n = false -> nexp
  | NBinop : nexp -> binop -> nexp -> nexp
  | NVar : var -> nexp.

  Inductive bexp : Type :=
  | BRel : nexp -> rel -> nexp -> bexp
  | BNot : bexp -> bexp
  | BAnd : bexp -> bexp -> bexp
  | BOr : bexp -> bexp -> bexp.

  Fixpoint nexpOut (base : exp) (ne : nexp) : exp :=
    match ne with
      | NConst n => n
      | NCol n _ => $[base + n]
      | NBinop ne1 bo ne2 => Binop (nexpOut base ne1) bo (nexpOut base ne2)
      | NVar x => $ x
    end%Mir.

  Fixpoint bexpOut (base : exp) (be : bexp) : test :=
    match be with
      | BRel ne1 r ne2 => TCond {| SPArg.CondOp1 := nexpOut base ne1;
        SPArg.CondRel := r;
        SPArg.CondOp2 := nexpOut base ne2 |}
      | BNot be1 => TNot (bexpOut base be1)
      | BAnd be1 be2 => TAnd (bexpOut base be1) (bexpOut base be2)
      | BOr be1 be2 => TOr (bexpOut base be1) (bexpOut base be2)
    end.

  Fixpoint nvars (ne : nexp) : list var :=
    match ne with
      | NConst _ => nil
      | NCol _ _ => nil
      | NBinop ne1 _ ne2 => nvars ne1 ++ nvars ne2
      | NVar x => x :: nil
    end.

  Fixpoint bvars (be : bexp) : list var :=
    match be with
      | BRel ne1 _ ne2 => nvars ne1 ++ nvars ne2
      | BNot be1 => bvars be1
      | BAnd be1 be2 => bvars be1 ++ bvars be2
      | BOr be1 be2 => bvars be1 ++ bvars be2
    end.

  Fixpoint expKey (ne : nexp) : option exp :=
    match ne with
      | NConst n => Some (Const n)
      | NCol _ _ => None
      | NBinop ne1 bo ne2 =>
        match expKey ne1, expKey ne2 with
          | Some e1, Some e2 => Some (Binop e1 bo e2)
          | _, _ => None
        end
      | NVar x => Some ($ x)
    end%Mir.

  Fixpoint keyIs (be : bexp) : option exp :=
    match be with
      | BRel (NCol 0 _) Eq ne => expKey ne
      | BRel _ _ _ => None
      | BNot _ => None
      | BAnd be1 be2 => match keyIs be1 with
                          | None => keyIs be2
                          | x => x
                        end
      | BOr _ _ => None
    end.

  Section Select.
    Variable wher : bexp.
    Variable body : scode.

    Fixpoint Pack' (cap : list var) : list cmd :=
      match cap with
        | nil => nil
        | x :: cap' => Write (Retv + 2 + length cap')%Mir (Var x) :: Pack' cap'
      end.

    Definition Pack :=
      SStraightline (fun iin => InsOut (fun st => Ex st', iin st' /\ [< execs SPArg.exec (Pack' capture) st' st >])%PropX
        (fun _ _ => Pack' capture)).

    Fixpoint Unpack' (cap : list var) : list cmd :=
      match cap with
        | nil => nil
        | x :: cap' => Assign x ($[Arg 1 + length cap'])%Mir :: Unpack' cap'
      end.

    Definition Unpack :=
      SStraightline (fun iin => InsOut (fun st => Ex st', iin st' /\ [< execs SPArg.exec (Unpack' capture) st' st >])%PropX
        (fun _ _ => Unpack' capture)).

    Fixpoint makeFrame (m : mem) (base : word) (cap : list var) (fr : frame) : frame :=
      match cap with
        | nil => fr
        | x :: cap' => makeFrame m base cap' (fupd fr x (m (base + length cap')))
      end.

    Definition Select0 := (
      Call "malloc" Args #0, #(length capture)
      [TYPEDc
        PRE [arg, rv']
          heap,,
          arg table :: sqlTree (numCols + 2),,
          rv' :: chunk (length capture + 2),,
          inv arg
        POST [rv]
          post arg rv];;

      "_callback" <-- blambda [["tuple", "env"]] [(st ~> (TYPED
        PRE [arg]
          heap,,
          arg 0 :: chunk (numCols + 2),,
          inv (makeFrame (Mem st) (arg 1) capture fempty)
        POST [_]
          heap,,
          arg 0 :: chunk (numCols + 2),,
          inv (makeFrame (Mem st) (arg 1) capture fempty)) st
      /\ [< capture <> nil -> Argl st 1 + Datatypes.length capture <= MemHigh >])%PropX] {
          (fun _ _ => Unpack);;
          (fun _ _ => Assert_ (TYPEDi
            PRE [x]
              heap,,
              x "tuple" :: chunk (numCols + 2),,
              inv x
            POST [_]
              heap,,
              x "tuple" :: chunk (numCols + 2),,
              inv x));;
          If* (bexpOut (Var "tuple") wher) {
            fun _ _ => body
          } else {
            fun _ _ => Skip
          };;
          Return 0
        };;

      (fun _ _ => Pack);;
      "env" <- Retv;;

      Call (match keyIs wher with
              | None => "iter"
              | Some _ => "pointQuery"
            end) Args #numCols, $ table, $"_callback", $"env"+2,
      (match keyIs wher with
         | None => #0
         | Some e => e
       end)
      [TYPEDi
        PRE [x]
          heap,,
          x table :: sqlTree (numCols + 2),,
          x "env" :: chunk (length capture + 2),,
          inv x
        POST [rv]
          post x rv];;

      Call "free" Args #0, $"env", #(length capture)
      [TYPEDi
        PRE [x]
          heap,,
          x table :: sqlTree (numCols + 2),,
          inv x
        POST [rv]
          post x rv]
    )%Mir.

    Variables imports exports : list (string * prop).

    Theorem PackOk : scodeOk imports exports Pack.
      unfold Pack; do 2 red; propxFo; eauto.
    Qed.

    Theorem UnpackOk : scodeOk imports exports Unpack.
      unfold Pack; hnf; simpl; propxFo; eauto.
    Qed.

    Lemma Seq_None : forall c1 c2 GT is cin,
      (forall GT is cin, CoutPostcondition (ScCompile (GT := GT) (toStructured c2) is cin) = None)
      -> CoutPostcondition (ScCompile (GT := GT) (toStructured (Seq c1 c2)) is cin) = None.
      destruct c1; destruct c2; simpl; intuition.
      specialize (H _ is (CompIn CinPrecondition0 CinExit0 CinInject0)); discriminate.
      specialize (H _ is (CompIn (fun _ => Inj True) CinExit0 (fun _ => CinInject0 None))); discriminate.

      match goal with
        | [ |- context[match ?E with Some _ => _ | None => _ end] ] => case_eq E; simpl; intuition
      end.
    Qed.

    Hypothesis bodyOk : scodeOk imports exports body.

    Opaque IfStar.

    Theorem Select0Ok : scodeOk imports exports (Select0 imports exports).
      repeat apply SeqOk.
      apply Call_Ok.
      apply LambdaOk.
      repeat apply SeqOk.
      apply StraightLineOk.
      apply StraightLineOk.
      unfold fold_right, getArgs.
      repeat (apply SeqOk || apply StraightLineOk).
      apply UnpackOk.
      apply Assert_Ok.
      apply IfStarOk.
      assumption.
      apply SkipOk.
      apply GotoIOk.
      intros.
      unfold fold_right, getArgs.
      repeat (apply Seq_None; intros).
      reflexivity.
      apply PackOk.
      apply StraightLineOk.
      apply Call_Ok.
      apply Call_Ok.
    Qed.

    Definition Select := Wrap (Select0 imports exports) (fun _ cin iout =>
      (fun _ => (fun _ => [< True >], fun _ => [< lookupS imports exports "malloc" = Some mallocS >]))%PropX
      :: (fun _ => (fun _ => [< True >], fun _ => [< lookupS imports exports "free" = Some freeS >]))%PropX
      :: (fun _ => (fun _ => [< True >], fun _ => [< lookupS imports exports "iter" = Some iterS >]))%PropX
      :: (fun _ => (fun _ => [< True >], fun _ => [< lookupS imports exports "pointQuery" = Some iterS >]))%PropX
      :: (fun lo => (CinPrecondition cin, notStuck iout lo))
      :: (fun _ => (fun _ => [< True >], fun _ => [< table <> "env" /\ table <> "_callback" >]))%PropX
      :: (fun _ => (fun _ => [< True >], fun _ => [< AllS (fun x => x <> "env" /\ x <> "_callback" /\ x <> "tuple" /\ x <> "rp")%type
        capture >]))%PropX
      :: (fun _ => (fun _ => [< True >], fun _ => [< forall fr1 fr2, AllS (fun x => fr1 x = fr2 x) capture -> inv fr1 = inv fr2 >]))%PropX
      :: (fun _ => (fun _ => [< True >], fun _ => [< NoDup capture >]))%PropX
      :: (fun _ => (fun _ => [< True >], fun _ => [< forall fr1 fr2, (forall x, x <> "env" -> x <> "_callback" -> fr1 x = fr2 x)
        -> forall rv, post fr1 rv = post fr2 rv >]))%PropX
      :: (fun _ => (fun _ => [< True >], fun _ => [< forall specs f m1 m2,
        interp specs (Pure (Typing0 (inv f) m1))
        -> interp specs (Pure (Typing0 (inv f) m2)) >]))%PropX
      :: (fun _ => (IoutPostcondition iout, TYPEDi
        PRE [x]
          heap,,
          x table :: sqlTree (numCols + 2),,
          inv x
        POST [rv]
          post x rv))
      :: (fun _ => (fun _ => [<True>], fun _ => match CoutPostcondition (ScCompile (toStructured body) nullInstrs
        (CompIn (fun st => ((Ex fr : hprop,
          match Frames st with
            | nil => [<False>]
            | xs0 :: nil => [<False>]
            | xs0 :: xs' :: xss =>
              typingHolds
              (heap,,
                xs0 "tuple" :: chunk (numCols + 2),, 
                inv xs0)%Typed 
              (Mem st) fr /\
              (ExX  : state,
                Cptr (xs0 "rp") (PropX.Var VO) /\
                (Al st0 : state,
                  [<Frames st0 = xs' :: xss>] /\
                  ^[typingHolds
                    (heap,,
                      xs0 "tuple" :: chunk (numCols + 2),,
                      inv xs0)%Typed 
                    (Mem st0) fr] --> 
                  VO @ st0))
          end) /\
        [<evalTest
          (bexpOut ($%Mir "tuple") wher) st =
          Some true>])%PropX)
        (CinInject cin
          (inr unit
            (inl (unit + unit)
              (Some
                (inr unit
                  (inr
                    (option
                      (labelsOf
                        (bexpOut 
                          (Var "tuple") wher) +
                        (ScLabT (toStructured body) + unit))) tt))))))
        (fun v : ScLabT (toStructured body) =>
          CinInject cin
          (inr unit
            (inl (unit + unit)
              (Some
                (inr unit
                  (inl unit
                    (Some
                      (inr
                        (labelsOf
                          (bexpOut 
                            ($%Mir "tuple") wher))
                        (inl unit v))))))))))) with
                                                  | None => [< False >]
                                                  | Some pcond => Al st, pcond st -->
                                                    (TYPEDi
                                                      PRE [x]
                                                        heap,,
                                                        x "tuple" :: chunk (numCols + 2),,
                                                        inv x
                                                      POST [_]
                                                        heap,,
                                                        x "tuple" :: chunk (numCols + 2),,
                                                        inv x) st
                                                end))%PropX
      :: CoutConditions (ScCompile (toStructured body) nullInstrs (CompIn
        (fun st => ((Ex fr : hprop,
          match Frames st with
            | nil => [<False>]
            | xs0 :: nil => [<False>]
            | xs0 :: xs' :: xss =>
              typingHolds
              (heap,,
                xs0 "tuple" :: chunk (numCols + 2),, 
                inv xs0)%Typed 
              (Mem st) fr /\
              (ExX  : state,
                Cptr (xs0 "rp") (PropX.Var VO) /\
                (Al st0 : state,
                  [<Frames st0 = xs' :: xss>] /\
                  ^[typingHolds
                    (heap,,
                      xs0 "tuple" :: 
                      chunk (numCols + 2),,
                      inv xs0)%Typed 
                    (Mem st0) fr] --> 
                  VO @ st0))
          end) /\
        [<evalTest
          (bexpOut ($%Mir "tuple") wher) st =
          Some true>])%PropX)
        (CinInject cin
          (inr unit
            (inl (unit + unit)
              (Some
                (inr unit
                  (inr
                    (option
                      (labelsOf
                        (bexpOut 
                          (Var "tuple") wher) +
                        (ScLabT (toStructured body) + unit))) tt))))))
        (fun v : ScLabT (toStructured body) =>
          CinInject cin
          (inr unit
            (inl (unit + unit)
              (Some
                (inr unit
                  (inl unit
                    (Some
                      (inr
                        (labelsOf
                          (bexpOut 
                            ($%Mir "tuple") wher))
                        (inl unit v)))))))))))).

    Theorem Forall_inv: forall (A : Type) (P : A -> Prop) (a : A) (l : list A),
      Forall P (a :: l) -> P a /\ Forall P l.
      inversion 1; auto.
    Qed.

    Fixpoint pupds (base : word) (cap : list var) (fr : frame) (m : mem) : mem :=
      match cap with
        | nil => m
        | x :: cap' => pupds base cap' fr (Mir.mupd m (base + length cap') (fr x))
      end.

    Lemma Pack'_fwd : forall frs cap st st' fr,
      Frames st = fr :: frs
      -> execs SPArg.exec (Pack' cap) st st'
      -> Mem st' = pupds (Retval st + 2) cap fr (Mem st)
      /\ Frames st' = fr :: frs
      /\ Retval st' = Retval st.
      induction cap; simpl; intros.

      subst; tauto.

      destruct H0 as [ ? [ ] ].
      unfold SPArg.exec in H0; simpl in H0.
      rewrite H in H0.
      match goal with
        | [ _ : (if ?E then _ else _) = Some _ |- _ ] => destruct E
      end; try discriminate.
      injection H0; clear H0; intros; subst.
      eapply IHcap in H1; simpl; eauto.
    Qed.

    Lemma Pack'_bwd : forall fr frs cap st,
      Retval st + 2 + Datatypes.length cap <= MemHigh
      -> Frames st = fr :: frs
      -> execs SPArg.exec (Pack' cap) st {| Mem := pupds (Retval st + 2) cap fr (Mem st);
        Frames := fr :: frs;
        Retval := Retval st;
        Retptr := Retptr st;
        Argl := Argl st |}.
      induction cap; simpl; intuition.

      destruct st; simpl in *; congruence.

      repeat esplit.
      unfold SPArg.exec; simpl.
      rewrite H0.
      match goal with
        | [ |- (if ?E then _ else _) = Some _ ] => destruct E
      end; try tauto.
      elimtype False; womega.
      match goal with
        | [ |- execs _ _ ?st _ ] => specialize (IHcap st)
      end; simpl in IHcap.
      intuition.
    Qed.

    Theorem awful_case : forall (body' : scodeR) GT (cin : compileIn
      (unit +
        (option
          (unit +
            (option
              (labelsOf (bexpOut ($%Mir "tuple") wher) +
                ((let (ScLabT, _, _) := body' in ScLabT) + unit)) + unit)) +
          (unit + unit))) GT)
      (Hiter : forall specs : codeSpec SPArg.pc SPArg.state,
        layout pc GT ->
        SPArg.state ->
        interp specs [<True>] ->
        interp specs [<lookupS imports exports "iter" = Some iterS>])
      (HpointQuery : forall specs : codeSpec SPArg.pc SPArg.state,
        layout pc GT ->
        SPArg.state ->
        interp specs [<True>] ->
        interp specs [<lookupS imports exports "pointQuery" = Some iterS>])
      (Htable : forall specs : codeSpec SPArg.pc SPArg.state,
        layout pc GT ->
        SPArg.state ->
        interp specs [<True>] ->
        interp specs
        [<(table = "env" -> False) /\ (table = "_callback" -> False)>])
      (Hcapture : forall specs : codeSpec SPArg.pc SPArg.state,
        layout pc GT ->
        SPArg.state ->
        interp specs [<True>] ->
        interp specs
        [<Forall
          (fun x : string =>
            (x = "env" -> False) /\
            (x = "_callback" -> False) /\
            (x = "tuple" -> False) /\ (x = "rp" -> False)) capture>])
      (Hdup : forall specs : codeSpec SPArg.pc SPArg.state,
        layout pc GT ->
        SPArg.state ->
        interp specs [<True>] -> interp specs [<NoDup capture>])
      (Hinv : forall specs : codeSpec SPArg.pc SPArg.state,
        layout pc GT ->
        SPArg.state ->
        interp specs [<True>] ->
        interp specs
        [<forall fr1 fr2 : var -> word,
          Forall (fun x : var => fr1 x = fr2 x) capture ->
          inv fr1 = inv fr2>])
      (Hpure : forall specs : codeSpec SPArg.pc SPArg.state,
        layout pc GT ->
        SPArg.state ->
        interp specs [<True>] -> interp specs [< forall specs f m1 m2,
          interp specs (Pure (Typing0 (inv f) m1))
          -> interp specs (Pure (Typing0 (inv f) m2)) >])
      (Hposte : forall specs : codeSpec SPArg.pc SPArg.state,
        layout pc GT ->
        SPArg.state ->
        interp specs [<True>] ->
        interp specs [< forall fr1 fr2, (forall x, x <> "env" -> x <> "_callback" -> fr1 x = fr2 x)
          -> forall rv, post fr1 rv = post fr2 rv >]),
  forall (specs : codeSpec SPArg.pc SPArg.state) (lo : layout SPArg.pc GT)
     (st : SPArg.state),
   interp specs
     (Ex st' : SPArg.state,
      ((Ex st'0 : SPArg.state,
        (Ex st'1 : SPArg.state,
         (Ex st'2 : state,
          (Ex i : word,
           [<match Frames st'2 with
             | nil => None
             | fr :: frs =>
                 Some
                   {|
                   Mem := Mem st'2;
                   Frames := fupd fr "_callback" i :: frs;
                   Retval := Retval st'2;
                   Retptr := Retptr st'2;
                   Argl := Argl st'2 |}
             end = Some st'1>] /\
           (Ex fr : hprop,
            match Frames st'2 with
            | nil => [<False>]
            | xs0 :: nil => [<False>]
            | xs0 :: xs' :: xss =>
                typingHolds
                  (heap,,
                   xs0 table :: sqlTree (numCols + 2),,
                   Retval st'2 :: chunk (Datatypes.length capture + 2),,
                   inv xs0)%Typed (Mem st'2) fr /\
                (ExX  : state,
                 Cptr (xs0 "rp") (PropX.Var VO) /\
                 (Al st0 : state,
                  [<Frames st0 = xs' :: xss>] /\
                  ^[typingHolds (post xs0 (Retval st0)) (Mem st0) fr] -->
                  VO @ st0))
            end) /\
           (ExX  : state,
            Cptr i (PropX.Var VO) /\
            (Al st0 : state,
             (Ex x : hprop,
              ^[match Frames st0 with
                | nil => [<False>]
                | _ :: _ =>
                    typingHolds
                      (heap,,
                        Argl st0 0 :: chunk (numCols + 2),,
                        inv (makeFrame (Mem st0) (Argl st0 1) capture fempty))%Typed
                      (Mem st0) x /\
                    (ExX  : state,
                     Cptr (Retptr st0) (PropX.Var VO) /\
                     (Al st2 : state,
                      [<Frames st2 = Frames st0>] /\
                      ^[typingHolds
                          (heap,,
                            Argl st0 0 :: chunk (numCols + 2),,
                            inv (makeFrame (Mem st0) (Argl st0 1) capture fempty))%Typed
                          (Mem st2) x] --> VO @ st2))
                end]) /\
             [<capture <> nil -> Argl st0 1 + Datatypes.length capture <= MemHigh>] -->
             VO @ st0)))) /\
         [<execs SPArg.exec
             ((fix Pack' (cap : list var) : list cmd :=
                 match cap with
                 | nil => nil
                 | x :: cap' =>
                     Write (Retv + 2 + Datatypes.length cap')%Mir ($%Mir x)
                     :: Pack' cap'
                 end) capture) st'1 st'0>]) /\
        [<SPArg.exec (Assign "env" Retv) st'0 st'>]) /\
       [<exists s'' : SPArg.state,
           (SPArg.exec (SetArg 0 numCols) st' s'' /\
            (exists s''0 : SPArg.state,
               SPArg.exec (SetArg 1 ($%Mir table)) s'' s''0 /\
               (exists s''1 : SPArg.state,
                  SPArg.exec (SetArg 2 ($%Mir "_callback")) s''0 s''1 /\
                  (exists s''2 : SPArg.state,
                     SPArg.exec (SetArg 3 ($ "env" + 2)%Mir) s''1 s''2 /\
                     (exists s''2' : SPArg.state,
                       SPArg.exec (SetArg 4 (match keyIs wher with
                                               | None => Const 0
                                               | Some e => e
                                             end)) s''2 s''2' /\
                       (exists s''3 : SPArg.state,
                         SPArg.exec
                         (SetRetp
                           (lo
                             (Local
                               ((let (_, _, CinInject) := cin in
                                 CinInject)
                               (inr unit
                                 (inr
                                   (option
                                     (unit +
                                       (option
                                         (labelsOf
                                           (bexpOut 
                                             ($%Mir "tuple") wher) +
                                           ((let 
                                             (ScLabT, _, _) := body' in
                                             ScLabT) + unit)) + unit)))
                                   (inr unit tt))))))) s''2' s''3 /\
                        st = s''3))))))%type>] /\
       (ExX  : SPArg.state,
        Cptr
          (lo
             (Local
                ((let (_, _, CinInject) := cin in CinInject)
                   (inr unit
                      (inr
                         (option
                            (unit +
                             (option
                                (labelsOf (bexpOut ($%Mir "tuple") wher) +
                                 ((let (ScLabT, _, _) := body' in ScLabT) +
                                  unit)) + unit))) 
                         (inr unit tt)))))) (PropX.Var VO) /\
        (Al st0 : SPArg.state,
         (Ex x : hprop,
          ^[match Frames st0 with
            | nil => [<False>]
            | xs0 :: nil => [<False>]
            | xs0 :: xs' :: xss =>
                typingHolds
                  (heap,,
                   xs0 table :: sqlTree (numCols + 2),,
                   xs0 "env" :: chunk (Datatypes.length capture + 2),,
                   inv xs0)%Typed (Mem st0) x /\
                (ExX  : state,
                 Cptr (xs0 "rp") (PropX.Var VO) /\
                 (Al st1 : state,
                  [<Frames st1 = xs' :: xss>] /\
                  ^[typingHolds (post xs0 (Retval st1)) (Mem st1) x] -->
                  VO @ st1))
            end]) --> VO @ st0)))%PropX) ->
   interp specs
     (match lookupS imports exports (match keyIs wher with
                                       | None => "iter"
                                       | Some _ => "pointQuery"
                                     end) with
      | Some p => p
      | None => fun _ : SPArg.state => [<uhoh' match keyIs wher with
                                                 | Some _ => "pointQuery"
                                                 | None => "iter"
                                               end>]%PropX
      end st).
    Proof.
      intros; pre.

      replace (lookupS imports exports match keyIs wher with
                                         | None => "iter"
                                         | Some _ => "pointQuery"
                                       end) with (Some iterS).
      Focus 2.
      destruct (keyIs wher); symmetry.
      apply (Inj_sound (HpointQuery _ lo {| Mem := Mem; Frames := nil; Retval := 0; Retptr := 0; Argl := Argl |} (Inj_I specs _ I))).
      apply (Inj_sound (Hiter _ lo {| Mem := Mem; Frames := nil; Retval := 0; Retptr := 0; Argl := Argl |} (Inj_I specs _ I))).

      pre.

      match type of H7 with
        | match ?E with None => _ | Some _ => _ end = _ => destruct E; try discriminate
      end.
      injection H7; clear H7; intros; subst; simpl in *.

      destruct (Inj_sound (Htable _ lo {| Mem := Mem; Frames := nil; Retval := 0; Retptr := 0; Argl := Argl |} (Inj_I specs _ I))).
      eapply Pack'_fwd in H11; [ | simpl; reflexivity ].
      pre.
      apply typingHolds'_fwd in H; propxFo.
      apply sep_hide_fwd1 in H4.
      sepSimp.
      sepFwd.

      Fixpoint pupds_present (base : nat) (cap : list var) (fr : frame) : sprop :=
        match cap with
          | nil => emp
          | x :: cap' => (base + length cap') ==> fr x * !{pupds_present base cap' fr}
        end%Sep.

      Theorem pupds_mupd_comm : forall rv fr p v cap m,
        p >= rv + Datatypes.length cap
        -> pupds rv cap fr (Mir.mupd m p v)
        = Mir.mupd (pupds rv cap fr m) p v.
        induction cap; simpl; intuition.
        rewrite <- IHcap by auto.
        f_equal.
        extensionality a'.
        unfold Mir.mupd.
        repeat match goal with
                 | [ |- context[if ?E then _ else _] ] => destruct E
               end; auto.
      Qed.

      Theorem allocated_exposeLast_fwd : forall len base, len > 0
        -> allocated base len ===> Ex v, !{allocated base (len - 1)} * (base + len - 1) ==> v.
        induction len; intros.
        inversion H.
        destruct len.
        sepLemma.
        change (allocated base (S (S len))) with ((Ex v, base ==> v) * !{allocated (S base) (S len)})%Sep.
        Opaque allocated.
        sepLemma.
        Transparent allocated.
        sepLemma.
      Qed.

      Lemma pupds_stepper' : forall p1 p2 p3 p4 p5 p6 p7 fr cap p8 rv m,
        stars (p1 :: p2 :: p3 :: p4 :: p5 :: p6 :: sep (allocated rv (length cap)) :: p7 :: p8 :: nil)
        (fun a : word => if Compare_dec.le_lt_dec MemHigh a then None else Some (m a))
        -> stars (p1 :: p2 :: p3 :: p4 :: p5 :: p6 :: sep (pupds_present rv cap fr) :: p7 :: p8 :: nil)
        (fun a : word => if Compare_dec.le_lt_dec MemHigh a then None else Some (pupds rv cap fr m a)).
        Opaque allocated.
        induction cap; simpl; intuition.

        use allocated_exposeLast_fwd; sepFwd.
        rewrite <- minus_n_O in H0.
        assert (Hstars : stars (p1 :: p2 :: p3 :: p4 :: p5 :: p6
          :: sep (allocated rv (Datatypes.length cap))
          :: p7 :: sep (![p8] * (rv + S (Datatypes.length cap) - 1) ==> x) :: nil)%Sep
         (fun a : word => if le_lt_dec MemHigh a then None else Some (m a))) by sepLemma.
        clear H0.
        apply IHcap in Hstars; auto.

        sepSimp.
        sepFwd.
        assert (rv + Datatypes.length cap < MemHigh)%nat.
        apply (@read (rv + S (Datatypes.length cap) - 1)%nat (rv + Datatypes.length cap)%nat tt x nil
          (p1 :: p2 :: p3 :: p4 :: p5 :: p6 :: sep (pupds_present rv cap fr)
            :: p7 :: p8:: nil)) in H0; auto.
        rewrite readWord_eq in H0.
        destruct (Compare_dec.le_lt_dec MemHigh (rv + Datatypes.length cap)); [ discriminate | eauto ].

        rewrite pupds_mupd_comm by auto.

        sep1.
      Qed.

      Theorem pupds_stepper : forall rv fr cap p1 p2 p3 p4 p5 p6 p7 p8 m,
        stars (p1 :: p2 :: p3 :: p4 :: p5 :: p6 :: sep (allocated rv (length cap)) :: p7 :: p8 :: nil)
        (fun a : word => if Compare_dec.le_lt_dec MemHigh a then None else Some (m a))
        -> stars (p1 :: p2 :: p3 :: p4 :: p5 :: p6 :: sep (pupds_present rv cap fr) :: p7 :: p8 :: nil)
        (fun a : word => if Compare_dec.le_lt_dec MemHigh a then None else Some (pupds rv cap fr m a)).
        intros; eapply pupds_stepper'; eauto.
      Qed.

      replace (S (S Retval)) with (Retval + 2) in H4 by omega;
        replace (length capture + 2 - 2) with (length capture) in H4 by omega;
          apply (pupds_stepper (Retval + 2) (fupd f "_callback" x10) capture) in H4.
      sep1.
      instantiate (2 := fun env => sep (!{mallocHeap 0}
        * !{pupds_present env capture (fupd f "_callback" x10)}
        * Ex x, !{Impure (Typing0 (inv f) x)})%Sep).
      sepLemma.

      sep0.

      intros.
      apply Imply_easy; intro.
      specialize (H14 x7).
      destruct (Frames x7); try tauto.
      simpl in H14.
      apply ForallX_I; intro p.
      unfold Subst; simpl.
      apply Forall_I; intro hp.
      autorewrite with PropX.
      rewrite <- (lift_nada (x11 x7)).
      eapply Imply_trans; [ | eauto ].

      Theorem Imply_Ex : forall pc state specs (p : PropX pc state) A (fp : A -> _) x,
        interp specs (p --> fp x)
        -> interp specs (p --> PropX.Exists fp).
        intros; apply Imply_I.
        apply Exists_I with x.
        eapply Imply_E; eauto.
      Qed.

      Theorem Imply_And : forall pc state specs (p p1 p2 : PropX pc state),
        interp specs (p --> p2)
        -> interp specs (p --> p1)
        -> interp specs (p --> p1 /\ p2)%PropX.
        intros; apply Imply_I.
        apply And_I.
        eapply Imply_E; eauto.
        eapply Imply_E; eauto.
      Qed.

      apply Imply_And.

      apply Imply_I.
      eapply Inj_E.
      do 2 eapply And_E1; apply Env; simpl; eauto.
      intro Hsep; apply Inj_I; intro Hlen.

      Theorem allocated_exposeLast_bwd : forall len base, len > 0
        -> Ex v, !{allocated base (len - 1)} * (base + len - 1) ==> v ===> allocated base len.
        induction len; intros.
        inversion H.
        destruct len.
        Transparent allocated.
        sepLemma.
        change (allocated base (S (S len))) with ((Ex v, base ==> v) * !{allocated (S base) (S len)})%Sep.
        Opaque allocated.
        do 2 intro.
        sepSimp.
        Transparent allocated.
        simpl in H1.
        Opaque allocated.
        sepLemma.
      Qed.

      Theorem pupds_present_allocated : forall base fr cap,
        pupds_present base cap fr ===> !{allocated base (length cap)}.
        induction cap.
        Transparent allocated.
        sepLemma.
        Opaque allocated.
        use allocated_exposeLast_bwd.
        sepLemma.
      Qed.
      Transparent allocated.
      
      use pupds_present_allocated; sepSimp; sepFwd.
      apply (touchAllocated (Mir.Argl x7 1) (Datatypes.length capture) (Mir.Argl x7 1 + Datatypes.length capture - 1)
        (sep (Impure (Typing0 (inv f) x13)) :: hp :: nil)
        (ptsTo (Mir.Argl x7 0) x8
          :: ptsTo (S (Mir.Argl x7 0)) x9
          :: sep (allocated (S (S (Mir.Argl x7 0))) (numCols + 2 - 2))
          :: sep (mallocHeap 0) :: nil)) in H7.
      destruct (le_lt_dec MemHigh (Mir.Argl x7 1 + Datatypes.length capture - 1)); try tauto.
      omega.
      destruct capture; try tauto.
      simpl; omega.

      
      Opaque allocated.
      apply Imply_Ex with (sep (![hp] * !{pupds_present (Mir.Argl x7 1) capture f})%Sep).
      autorewrite with PropX.
      apply Imply_I.

      eapply Inj_E; [ eapply And_E1; eapply And_E1; apply Env; simpl; eauto | intro ].

      Theorem pupd_unused : forall aux v rv fr cap,
        AllS (fun x => x <> aux) cap
        -> pupds_present rv cap (fupd fr aux v) = pupds_present rv cap fr.
        induction 1; simpl; intuition.
        autorewrite with Mac.
        congruence.
      Qed.

      Theorem pupds_out : forall m rv f cap,
        NoDup cap
        -> forall sm f', sep (pupds_present rv cap f) sm
          -> (forall a v, sm a = Some v -> m a = v)
          -> Forall (fun x => f x = makeFrame m rv cap f' x) cap.
        induction 1; simpl; intuition.

        destruct H1.
        rewrite stars_def in H3.
        destruct H3 as [ ? [ ? [ ? [ ] ] ] ].
        destruct H5 as [ ? [ ? [ ? [ ] ] ] ].
        assert (x2 = x1).
        destruct H7.
        destruct H5.
        extensionality qq.
        rewrite H9.
        rewrite H8.
        destruct (x2 qq); reflexivity.
        subst.
        clear x3 H5 H7.
        
        constructor.

        destruct H4.
        hnf in H4.
        inversion H4; clear H4; subst.
        clear H10.
        simpl in *.
        destruct H3.
        specialize (H4 (rv + Datatypes.length l)).
        destruct (x0 (rv + Datatypes.length l)); try discriminate.
        injection H4; clear H4; intros; subst.
        injection H9; clear H9; intros; subst.
        rewrite (H2 _ _ H4).

        Lemma makeFrame_keep : forall x m rv cap f,
          ~In x cap
          -> makeFrame m rv cap f x = f x.
          induction cap; simpl; intuition.
          rewrite IHcap by auto.
          autorewrite with Mac; reflexivity.
        Qed.

        rewrite makeFrame_keep by assumption.
        autorewrite with Mac; reflexivity.

        eapply IHNoDup; eauto.
        intros.
        apply H2.
        destruct H3.
        rewrite H7.
        specialize (H3 a).
        splitmaster.
      Qed.

      rewrite pupd_unused in H5 by (eapply AllS_weaken; [ apply (Inj_sound (Hcapture specs lo x7 (Inj_I _ _ I))) | cbv beta; simpl; intuition ]).
      generalize (Inj_sound (Hinv specs lo x7 (Inj_I _ _ I)) f (makeFrame (SepArg.Mem x7) (Mir.Argl x7 1) capture fempty)).
      generalize dependent (inv f); intros.

      match type of H7 with
        | ?P -> _ => assert P
      end.

      sepSimp.
      sepFwd.
      apply (himp_pullout1 (sep (Impure (Typing0 t x8)) :: hp :: nil)
        (sep (pupds_present (Mir.Argl x7 1) capture f))
        (sep (allocated (Mir.Argl x7 0) (S (S (numCols + 2 - 2)))) :: sep (mallocHeap 0) :: nil)) in H11.
      rewrite stars_def in H11.
      destruct H11 as [ ? [ ? [ ? [ ] ] ] ].
      eapply pupds_out; [ | eassumption | ].
      apply (Inj_sound (Hdup specs lo x7 (Inj_I _ _ I))).
      generalize H5; clear.
      destruct 1; intros.
      specialize (H0 a).
      rewrite H1 in H0.
      destruct (le_lt_dec MemHigh a); congruence.
      intuition; subst.

      apply And_I.
      eapply Inj_E; [ eapply And_E1; eapply And_E2; eapply And_E1; apply Env; simpl; eauto | intro ].
      apply interp_weaken; propxFo.
      apply typingHolds'_bwd; propxFo.

      sepSimp; sepFwd.
      eexists; repeat split.

      apply sep_hide_bwd1.
      sep1.
      auto.
      apply simplify_fwd.
      eapply (Inj_sound (Hpure specs lo x7 (Inj_I _ _ I))); eauto.

      eapply ExistsX_I.
      unfold Subst; simpl.
      apply And_I.
      eapply And_E1; eapply And_E2.
      apply Env; simpl; eauto.
      rewrite pupd_unused by (eapply AllS_weaken; [ apply (Inj_sound (Hcapture specs lo x7 (Inj_I _ _ I))) | cbv beta; intuition ]).

      Theorem use_Forall_Imply : forall pc state specs G A (p1 p1' p2 : A -> PropX pc state),
        valid specs G (Al x, p1 x --> p2 x)%PropX
        -> (forall x, valid specs G (p1' x --> p1 x))
        -> valid specs G (Al x, p1' x --> p2 x)%PropX.
        intros; apply Forall_I; intro x; apply Imply_I.
        apply Imply_E with (p1 x).
        apply (Forall_E (P := fun x => p1 x --> p2 x)%PropX).
        eapply valid_weaken; eauto.
        intuition.
        eapply Imply_E; eauto.
        eapply valid_weaken; eauto.
        intuition.
      Qed.

      apply use_Forall_Imply with (fun x8 =>
        [<Frames x8 = f1 :: f2>] /\
        [<sep
          ((!{allocated (Mir.Argl x7 0) (numCols + 2)} *
            !{!{mallocHeap 0} * !{pupds_present (Mir.Argl x7 1) capture f} *
              Ex x8, !{Impure (Typing0 (inv (makeFrame (SepArg.Mem x7) 
                           (Mir.Argl x7 1) capture fempty)) x8)} })%Sep * ![hp]%Sep)
          (fun a : word =>
            if le_lt_dec MemHigh a then None else Some (SepArg.Mem x8 a))>] /\
        [<Mir.Argl x7 0 = 0 -> False>] /\ [<True>])%PropX.
      do 2 eapply And_E2; apply Env; simpl; eauto.
      intro.
      apply Imply_I.
      repeat apply And_I.
      eapply And_E1; apply Env; simpl; eauto.

      unfold typingHolds.
      match goal with
        | [ |- valid specs (?x :: _) _ ] =>
          match x with
            | context[typingHolds' ?a ?b ?c ?d] => specialize (typingHolds'_fwd' specs a b c d)
          end
      end; match goal with
             | [ |- interp _ (Imply ?Q ?P) -> _ ] => intro; apply Imply_E with P
           end.
      apply Imply_I.
      eapply Exists_E.
      apply Env; simpl; eauto.
      intro ms.
      simpl.
      eapply Inj_E.
      eapply And_E1; apply Env; simpl; eauto.
      intro Hsep.
      apply Inj_I.

      apply sep_hide_fwd in Hsep.
      sep1.

      eapply Imply_E.
      apply interp_weaken; eassumption.
      match goal with
        | [ |- valid _ ((_ /\ ?P)%PropX :: _) ?Q ] => replace P with Q
      end.
      eapply And_E2; apply Env; simpl; eauto.
      
      simpl.
      match goal with
        | [ |- context C [?E] ] =>
          match E with
            | subst (lift ?p ?G) ?p' =>
              generalize (lift_cons' p G (refl_equal _) p'); let He := fresh "He" in intro He;
                match type of He with
                  | _ = ?y => replace E with y
                end
          end
      end.
      simpl.
      match goal with
        | [ |- context C [?E] ] =>
          match E with
            | lift ?p nil =>
              generalize (lift_nada' p (refl_equal _)); let H := fresh "H" in intro H;
                match type of H with
                  | _ = ?y => replace E with y
                end
          end
      end.
      match goal with
        | [ |- context C [?E] ] =>
          match E with
            | subst (lift ?p ?G) ?p' =>
              generalize (lift_cons' p G (refl_equal _) p'); let He := fresh "He" in intro He;
                match type of He with
                  | _ = ?y => replace E with y
                end
          end
      end.
      autorewrite with PropX; reflexivity.

      eapply And_E1; eapply And_E2; eapply And_E1; apply Env; simpl; eauto.
      apply Inj_I; tauto.

      sep0.
      sep0.
      autorewrite with PropX.
      apply simplify_fwd; apply typingHolds'_bwd; propxFo.

      match goal with
        | [ |- context[inv ?f'] ] =>
          match f' with
            | f => fail 1
            | _ => generalize (Inj_sound (Hinv specs lo x7 (Inj_I _ _ I)) f f'); generalize dependent (inv f)
          end
      end.
      intros.
      match type of H with
        | ?P -> _ => assert P
      end.
      eapply AllS_weaken.
      apply (Inj_sound (Hcapture specs lo x7 (Inj_I _ _ I))).
      clear; simpl; intuition.
      intuition; subst.

      eexists; repeat split.
      apply sep_hide_bwd.
      repeat match goal with
               | [ |- context[if ?E then _ else _] ] => destruct E; try tauto
             end.

      Transparent allocated.
      use pupds_present_allocated.
      sepLemma.
      auto.
      apply simplify_fwd; eapply (Inj_sound (Hpure specs lo x7 (Inj_I _ _ I))); eauto.
      sep0.

      intro.
      let T := type of (H9 x15) in
        match goal with
          | [ |- ?G ] => replace G with T; auto
        end.
      repeat f_equal.

      match goal with
        | [ |- context [subst (lift ?p ?G) ?p'] ] =>
          generalize (lift_cons' p G (refl_equal _) p')
      end.
      intros.
      eapply eq_trans; [ | symmetry; apply H ].
      simpl.
      match goal with
        | [ |- context [lift ?p nil] ] =>
          generalize (lift_nada' p (refl_equal _)); auto
      end.
      clear H; intro H.
      match goal with
        | [ |- context[post ?f1 _] ] =>
          match goal with
            | [ |- context[post ?f2 _] ] =>
              match f2 with
                | f1 => fail 1
                | _ => rewrite (Inj_sound (Hposte specs lo x15 (Inj_I _ _ I)) f1 f2)
              end
          end
      end.
      auto.
      simpl; intuition.
    Qed.

    Theorem SelectOk : scodeOk imports exports Select.
      apply WrapOk; [ | constructor | apply Select0Ok ].

      intuition.

      generalize dependent cin.
      Transparent IfStar.
      unfold Select0, Unpack, Pack, Unpack', Pack', Goto_, TailGoto, Skip, Halt, UseVar, fold_right, setArgs, getArgs, IfStar.
      generalize (toStructured body).
      intros body' cin Hconds.
      cbv beta iota zeta delta [IoutCode
        CinExit CinInject
        CoutPostcondition CoutCode
        ScLabT ScEntry ScCompile
        Skip Halt StraightLine GotoI WithCode SP.Goto Assert_ Call_ CallI Use_
        SeqI Seq toStructured If_ While_
        SName SSpec SCode 
        Locs Exps
        nullInstrs makeIin labelT Lambda IfStar] in *.
      simpl in *.

      repeat match goal with
               | [ H : AllS _ _ |- _ ] => apply Forall_inv in H; destruct H
             end; simpl in *.

      rename H into Hmalloc; rename H0 into Hfree; rename H1 into Hiter; rename H2 into HpointQuery;
        rename H3 into Hstuck; rename H4 into Htable; rename H5 into Hcapture; rename H6 into Hinv; rename H7 into Hdup;
          rename H8 into Hposte; rename H9 into Hpure; rename H10 into Hpost;
            rename H11 into HpostOk; rename H12 into Hinherit.

      repeat (apply Forall_nil || ((apply Forall_cons || apply AllS_app); [ simpl | ])).

      Focus 14.
      generalize dependent HpostOk.

      match goal with
        | [ |- context[match ?E with Some _ => _ | None => _ end] ] =>
          match E with
            | match _ with CompOut _ _ _ => _ end =>
                    match goal with
                      | [ |- context[match ?E' with Some _ => _ | None => _ end] ] =>
                        match E' with
                          | E => fail 1
                          | match _ with CompOut _ _ _ => _ end => change E' with E; destruct E
                        end
                    end
          end
      end; simpl; intro HpostOk.

      repeat (apply Forall_nil || ((apply Forall_cons || apply AllS_app); [ simpl | ])).

      pre.
      eauto.

      Theorem evalTest_nexpOut_ok : forall base bv st ne,
        evalExp base st = Some bv
        -> (forall n, n < numCols + 2 -> bv + n < MemHigh)
        -> Frames st <> nil
        -> exists v, evalExp (nexpOut base ne) st = Some v.
        induction ne; pre; eauto.

        rewrite H.
        specialize (H0 _ e).
        match goal with
          | [ |- context[if ?E then _ else _] ] => destruct E; eauto; elimtype False; womega
        end.

        rewrite H3.
        rewrite H2.
        eauto.

        destruct (Frames st); try tauto.
        eauto.
      Qed.

      Theorem evalTest_bexpOut_ok : forall base bv st be,
        evalExp base st = Some bv
        -> (forall n, n < numCols + 2 -> bv + n < MemHigh)
        -> Frames st <> nil
        -> exists b, evalTest (bexpOut base be) st = Some b.
        induction be; pre.

        destruct (evalTest_nexpOut_ok _ _ _ n H H0 H1).
        rewrite H2.
        destruct (evalTest_nexpOut_ok _ _ _ n0 H H0 H1).
        rewrite H3.
        eauto.

        rewrite H2; eauto.

        rewrite H3; rewrite H2.
        destruct x0; eauto.

        rewrite H3; rewrite H2.
        destruct x0; eauto.
      Qed.

      intros.
      apply Imply_I.
      eapply Exists_E.
      apply Env; simpl; eauto.
      intro hp; simpl.
      case_eq (Frames st); intros; [ eapply Inj_E; [ apply Env; simpl; eauto | cbv beta; tauto ] | ].
      destruct l; [ eapply Inj_E; [ apply Env; simpl; eauto | cbv beta; tauto ] | ].
      unfold typingHolds.
      apply Imply_E with (Ex xs, ![ Impure (Typing0 (heap,, f "tuple" :: chunk (numCols + 2),, inv f)%Typed xs) * ![hp] ] (Mem st)
        /\ Pure (Typing0 (heap,, f "tuple" :: chunk (numCols + 2),, inv f)%Typed xs))%PropX.
      apply Imply_I.
      eapply Exists_E.
      apply Env; simpl; eauto.
      intro ms; simpl.
      eapply Inj_E.
      eapply And_E1; apply Env; simpl; eauto.
      intro Hsep.
      apply Inj_I.
      eapply evalTest_bexpOut_ok.
      simpl; rewrite H0; reflexivity.
      intros.

      generalize dependent (numCols + 2); intros.

      apply sep_hide_fwd in Hsep.
      sepSimp; sepFwd.
      apply (touchAllocated (f "tuple") n0 (f "tuple" + n)
        (sep (Impure (Typing0 (inv f) ms)) :: hp :: nil) (sep (mallocHeap 0) :: nil)) in H3.
      destruct (le_lt_dec MemHigh (f "tuple" + n)); tauto.
      omega.
      congruence.

      eapply Imply_E.
      apply interp_weaken; apply typingHolds'_fwd'.
      eapply And_E1; apply Env; simpl; eauto.


      pre.
      destruct (Exists_sound (Imply_sound (Forall_sound (HpostOk specs lo st (Inj_I _ _ I)) st) H0)).
      destruct (Frames st); propxFo.
      destruct f0; propxFo.
      repeat esplit; (simpl; reflexivity).
      repeat esplit; (simpl; reflexivity).

      pre.
      destruct (Exists_sound (Imply_sound (Forall_sound (HpostOk specs lo {| Mem := Mem; Frames := nil; Retval := 0; Retptr := 0; Argl := Argl |}
        (Inj_I _ _ I)) _) H)).
      pre.
      sep1.
      sep0.
      sep0.
      sep1.
      sep0.
      sep0.

      pre.
      eauto.

      pre.
      eauto.

      assumption.

      specialize (HpostOk (fun _ => None) (fun _ => 0) {| Mem := mempty; Frames := nil; Retval := 0; Retptr := 0; Argl := mempty |}
        (Inj_I _ _ I)).
      propxFo.


      Focus.
      pre.

      Focus.
      pre.
      repeat esplit.

      Focus.
      pre.
      rewrite (Inj_sound (Hmalloc _ lo x (Inj_I specs _ I))).
      pre.
      specialize (Hpost _ lo _ H0).
      pre.
      apply typingHolds'_fwd in H; propxFo.
      apply sep_hide_fwd in H1.
      sep1.
      sep0.
      sep0.
      autorewrite with PropX.
      apply simplify_fwd; apply typingHolds'_bwd; propxFo.
      eexists; repeat split.

      apply sep_hide_bwd.
      sep1.
      auto.
      auto.
      sep0.
      intros.
      simpl.

      let T := type of (H5 x9) in
        match goal with
          | [ |- ?G ] => replace G with T; auto
        end.
      repeat f_equal.

      match goal with
        | [ |- context [subst (lift ?p ?G) ?p'] ] =>
          generalize (lift_cons' p G (refl_equal _) p')
      end.
      intros.
      eapply eq_trans; [ | symmetry; apply H7 ].
      simpl.
      match goal with
        | [ |- context [lift ?p nil] ] =>
          generalize (lift_nada' p (refl_equal _)); auto
      end.


      Focus.
      pre.
      eauto.

      Focus.
      pre.
      eauto.

      Focus.
      fold Unpack'.
      pre.
      
      Lemma Unpack'_bwd : forall frs cap fr st,
        Frames st = fr :: frs
        -> (cap <> nil -> Argl st 1 + Datatypes.length cap <= MemHigh)
        -> exists st', execs SPArg.exec (Unpack' cap) st st'.
        induction cap; simpl; intuition.

        eauto.

        match type of H0 with
          | ?P -> _ => assert P by discriminate
        end.
        intuition.
        destruct cap; simpl.
        repeat esplit; eauto.
        red; simpl.
        rewrite H.
        match goal with
          | [ |- context[if ?E then _ else _] ] => destruct E
        end.
        intuition.
        reflexivity.
        destruct (IHcap (fupd fr a (Mem st (Argl st 1 + S (Datatypes.length cap))))
          {| Mem := Mem st; Frames := fupd fr a (Mem st (Argl st 1 + S (Datatypes.length cap))) :: frs;
            Retval := Retval st; Retptr := Retptr st; Argl := Argl st |}).
        reflexivity.
        simpl in *; omega.
        simpl in H0.
        destruct H0; intuition.
        red in H3; simpl in H3.
        match goal with
          | [ _ : context[if ?E then _ else _] |- _ ] => destruct E; try discriminate
        end.
        injection H3; clear H3; intros; subst.
        repeat esplit; eauto.
        unfold SPArg.exec; simpl.
        rewrite H.
        match goal with
          | [ |- context[if ?E then _ else _] ] => destruct E
        end.
        elimtype False; simpl in *; womega.
        reflexivity.
        red; simpl.
        match goal with
          | [ |- context[if ?E then _ else _] ] => destruct E
        end.
        elimtype False; simpl in *; womega.
        eauto.
      Qed.

      destruct (Unpack'_bwd (f :: l) capture
        (fupd (fupd (fupd fempty "rp" Retptr) "tuple" (Argl 0)) "env"
          (Argl 1))
        {| Mem := Mem;
          Frames := fupd (fupd (fupd fempty "rp" Retptr) "tuple" (Argl 0)) "env"
          (Argl 1) :: f :: l;
          Retval := Retval;
          Retptr := Retptr;
          Argl := Argl |}).
      reflexivity.
      assumption.
      repeat esplit.
      red; simpl; reflexivity.
      red; simpl; reflexivity.
      red; simpl; reflexivity.
      eassumption.


      Focus.
      pre.
      fold Unpack' in H1.
      
      Lemma Unpack'_fwd : forall frs cap st st' fr,
        Frames st = fr :: frs
        -> execs SPArg.exec (Unpack' cap) st st'
        -> st' = {| Mem := Mem st;
          Frames := makeFrame (Mem st) (Argl st 1) cap fr :: frs;
          Retval := Retval st;
          Retptr := Retptr st;
          Argl := Argl st |}.
        induction cap; simpl; intuition.

        subst.
        destruct st; simpl in *; congruence.

        destruct H0; intuition.
        unfold SPArg.exec in H1; simpl in H1.
        rewrite H in H1.
        match goal with
          | [ _ : context [if ?E then _ else _] |- _ ] => destruct E
        end; try discriminate.
        injection H1; clear H1; intros; subst.
        eapply IHcap in H2; simpl; eauto.
      Qed.

      eapply Unpack'_fwd in H1; simpl; eauto.
      subst; simpl in *.

      rewrite makeFrame_keep.
      Focus 2.
      intro.
      specialize (AllS_In
        (Inj_sound (Hcapture specs lo {| Mem := mempty; Frames := nil; Retval := 0; Retptr := 0; Argl := mempty |} (Inj_I _ _ I)))
        H).
      tauto.

      autorewrite with Mac.
      rewrite makeFrame_keep.
      Focus 2.
      intro.
      specialize (AllS_In
        (Inj_sound (Hcapture specs lo {| Mem := mempty; Frames := nil; Retval := 0; Retptr := 0; Argl := mempty |} (Inj_I _ _ I)))
        H).
      tauto.

      autorewrite with Mac.
      match goal with
        | [ _ : context[inv ?f1] |- context[inv ?f2] ] => specialize (Inj_sound (Hinv specs lo
          {| Mem := mempty; Frames := nil; Retval := 0; Retptr := 0; Argl := mempty |}
          (Inj_I _ _ I)) f1 f2); generalize dependent (inv f2)
      end.
      intros.
      match type of H with
        | ?P -> _ => assert P
      end.

      eapply AllS_weaken.
      apply (Inj_sound (Hcapture specs lo {| Mem := mempty; Frames := nil; Retval := 0; Retptr := 0; Argl := mempty |} (Inj_I _ _ I))).
      simpl; intuition.
      
      Theorem makeFrame_irrel : forall x m base cap, NoDup cap
        -> forall fr fr', In x cap
          -> makeFrame m base cap fr x = makeFrame m base cap fr' x.
        induction 1; simpl; intuition; subst.
        repeat rewrite makeFrame_keep by assumption.
        autorewrite with Mac; reflexivity.
      Qed.

      apply makeFrame_irrel; auto.

      apply (Inj_sound (Hdup specs lo {| Mem := mempty; Frames := nil; Retval := 0; Retptr := 0; Argl := mempty |} (Inj_I _ _ I))).

      intuition; subst.
      eexists; split.

      apply simplify_fwd; eassumption.
      eauto.


      Focus.
      fold Pack'.
      pre.
      apply typingHolds'_fwd in H; propxFo.
      apply sep_hide_fwd1 in H0.

      esplit.
      eapply execs_app'.
      apply Pack'_bwd; simpl; intuition.
      sep1.
      destruct (Datatypes.length capture).
      apply (read (a := S Retval) (a' := Retval + 1) (sz := tt) x8
        (sep (allocated (S (S Retval)) (0 + 2 - 2))
          :: sep (Impure (Typing0 (inv f) x4)) :: x2 :: nil)
        (sep (mallocHeap 0)
          :: ptsTo (f table) x5
          :: sep (rep (numCols + 2) x3 x5)
          :: ptsTo (f table + 1) x6
          :: ptsTo Retval x7 :: nil)) in H0.
      rewrite readWord_eq in H0.
      destruct (le_lt_dec MemHigh (Retval + 1)); [ discriminate | auto ].
      auto.
      apply (touchAllocated (S (S Retval)) (S n + 2 - 2) (Retval + 2 + n)
        (sep (Impure (Typing0 (inv f) x4)) :: x2 :: nil)
        (sep (mallocHeap 0)
          :: ptsTo (f table) x5
          :: sep (rep (numCols + 2) x3 x5)
          :: ptsTo (f table + 1) x6
          :: ptsTo Retval x7
          :: ptsTo (S Retval) x8 :: nil)) in H0.
      destruct (le_lt_dec MemHigh (Retval + 2 + n)); [ tauto | auto ].
      omega.
      pre.
      eauto.


      Focus.
      pre.

      Theorem expKey_ok : forall st ne e,
        Frames st <> nil
        -> expKey ne = Some e
        -> exists v, evalExp e st = Some v.
        induction ne; simpl; intuition.

        injection H0; clear H0; intros; subst.
        simpl; eauto.

        discriminate.

        destruct (expKey ne1); try discriminate.
        destruct (expKey ne2); try discriminate.
        injection H0; clear H0; intros; subst; simpl.
        destruct (IHne1 _ H (refl_equal _)).
        rewrite H0.
        destruct (IHne2 _ H (refl_equal _)).
        rewrite H1.
        eauto.

        injection H0; clear H0; intros; subst; simpl.
        destruct (Frames st); try tauto.
        eauto.
      Qed.

      Theorem keyIs_ok : forall st be e,
        Frames st <> nil
        -> keyIs be = Some e
        -> exists v, evalExp e st = Some v.
        induction be; simpl; intuition.

        destruct n; try discriminate.
        destruct n; try discriminate.
        destruct r; try discriminate.
        eapply expKey_ok; eauto.

        discriminate.

        destruct (keyIs be1).
        injection H0; clear H0; intros; subst.
        eauto.

        eauto.

        discriminate.
      Qed.

      generalize (keyIs_ok {|
        Mem := Mem0;
        Frames := fupd f1 "env" Retval0 :: l0;
        Retval := Retval0;
        Retptr := Retptr0;
        Argl := Mir.mupd
        (Mir.mupd
          (Mir.mupd (mupd (sz := tt) Argl0 0 numCols) 1
            (fupd f1 "env" Retval0 table)) 2
          (fupd f1 "env" Retval0 "_callback")) 3
        (fupd f1 "env" Retval0 "env" + 2) |} wher).
      destruct (keyIs wher); simpl; intro Hkey.

      destruct (Hkey e).
      discriminate.
      reflexivity.
      repeat esplit; (simpl; try reflexivity).
      match goal with
        | [ |- context[match ?E with None => _ | Some _ => _ end] ] => replace E with (Some x)
      end.
      reflexivity.

      repeat esplit; (simpl; reflexivity).

      Focus.
      intros; eapply awful_case; eassumption.

      Focus.
      pre.
      eauto.

      Focus.
      pre.
      repeat esplit.
      simpl; reflexivity.

      Focus.
      pre.
      rewrite (Inj_sound (Hfree _ lo {| Mem := Mem; Frames := nil; Retval := 0; Retptr := 0; Argl := Argl |} (Inj_I specs _ I))).
      apply typingHolds'_fwd in H; propxFo.
      apply sep_hide_fwd1 in H0.
      sep1.
      sep0.
      sep0.
      autorewrite with PropX.
      apply simplify_fwd; apply typingHolds'_bwd; propxFo.
      eexists; repeat split.

      apply sep_hide_bwd1.
      sep1.
      auto.
      sep0.
      intros.
      simpl.

      let T := type of (H5 x9) in
        match goal with
          | [ |- ?G ] => replace G with T; auto
        end.
      repeat f_equal.

      match goal with
        | [ |- context [subst (lift ?p ?G) ?p'] ] =>
          generalize (lift_cons' p G (refl_equal _) p')
      end.
      intros.
      eapply eq_trans; [ | symmetry; apply H ].
      simpl.
      match goal with
        | [ |- context [lift ?p nil] ] =>
          generalize (lift_nada' p (refl_equal _)); auto
      end.
    Qed.
  End Select.

End traversals.

Hint Resolve SelectOk : Structured.


Implicit Arguments NConst [numCols].
Implicit Arguments NCol [numCols].
Implicit Arguments NBinop [numCols].
Implicit Arguments NVar [numCols].
Implicit Arguments BRel [numCols].
Implicit Arguments BNot [numCols].
Implicit Arguments BAnd [numCols].
Implicit Arguments BOr [numCols].

Notation "#" := NConst : SQL_scope.
Notation "nc .# n" := (NCol (numCols := nc - 2) n (refl_equal _)) (at level 0) : SQL_scope.
Delimit Scope SQL_scope with SQL.
Notation "e1 + e2" := (NBinop e1%SQL Plus e2%SQL) : SQL_scope.
Notation "e1 - e2" := (NBinop e1%SQL Minus e2%SQL) : SQL_scope.
Notation "e1 * e2" := (NBinop e1%SQL Mult e2%SQL) : SQL_scope.
Notation "$" := NVar : SQL_scope.

Notation "e1 == e2" := (BRel e1%SQL Eq e2%SQL) : SQL_scope.
Notation "e1 != e2" := (BRel e1%SQL Ne e2%SQL) : SQL_scope.
Notation "e1 < e2" := (BRel e1%SQL Lt e2%SQL) : SQL_scope.
Notation "e1 <= e2" := (BRel e1%SQL Le e2%SQL) : SQL_scope.
Notation "e1 > e2" := (BRel e1%SQL Gt e2%SQL) : SQL_scope.
Notation "e1 >= e2" := (BRel e1%SQL Ge e2%SQL) : SQL_scope.
Notation "!" := BNot : SQL_scope.
Infix "&&" := BAnd : SQL_scope.
Infix "||" := BOr : SQL_scope.

Notation "'SELECT' * 'FROM' table 'COLUMNS' numCols 'WHERE' wher 'CAPTURING' ( x1 , .. , xN ) 'INVARIANT' [ fr ] pre 'POST' [ rv ] post 'FOREACH' body" :=
  (fun imp exp => let nc := numCols in let inv := (fun fr => pre%Typed) in
    Select (nc-2) table (cons x1 .. (cons xN nil) ..) inv (fun fr rv => post%Typed)
    wher%SQL
    (SP.Seq (body imp exp) (SP.Assert_ (TYPEDi
      PRE [x]
        heap,,
        x "tuple" :: chunk nc,,
        inv x
      POST [_]
        heap,,
        x "tuple" :: chunk nc,,
        inv x)))
    imp exp)
  (no associativity, at level 95) : Mir_scope.

Import SP.

Hint Extern 1 (Forall _ _) => repeat constructor; discriminate : sep0.
Hint Extern 1 (NoDup _) => repeat constructor; simpl; tauto : sep0.
Hint Extern 1 (_ = _) =>
  repeat match goal with
           | [ fr1 : string -> word, fr2 : string -> word |- _ ] =>
             match goal with
               | [ H : forall x, _ -> _ -> fr1 x = fr2 x |- context[fr1 ?x] ] =>
                 rewrite H by discriminate
             end
         end; congruence : sep0.
Hint Extern 1 (_ = _) =>
  repeat match goal with
           | [ H : Forall (fun x => ?fr1 x = ?fr2 x) ?ls |- context[?fr1 ?x] ] =>
             let H' := fresh "H'" in assert (H' : In x ls) by intuition;
               rewrite (AllS_In H H')
         end; reflexivity : sep0.

Theorem Forall_Imply_refl : forall (specs : codeSpec pc state) p,
  interp specs (Al st : state, p st --> p st)%PropX.
  intros; apply Forall_I; intro st.
  apply Imply_I; apply Env; simpl; auto.
Qed.

Hint Resolve Forall_Imply_refl.
