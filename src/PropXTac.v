Require Import List FunctionalExtensionality Eqdep.

Require Import PropX.

Set Implicit Arguments.


Notation "i @@ sp" := (ExX, Cptr i (Var VO) /\ Al st, sp st --> VO @ st)%PropX
  (no associativity, at level 39) : PropX_scope.

Section machine.
  Variables pc state : Type.

  Inductive subs : list Type -> Type :=
  | SNil : subs nil
  | SCons : forall T Ts, (last (T :: Ts) -> PropX pc state) -> subs (eatLast (T :: Ts)) -> subs (T :: Ts).

  Fixpoint Substs G (s : subs G) : propX pc state G -> PropX pc state :=
    match s in subs G return propX pc state G -> PropX pc state with
      | SNil => fun p => p
      | SCons _ _ f s' => fun p => Substs s' (subst p f)
    end.

  Fixpoint svar G T (s : subs G) : var G T -> T -> PropX pc state :=
    match s in subs G return var G T -> T -> PropX pc state with
      | SNil => fun x => varContra x _
      | SCons _ _ f s' => fun x => match substV x with
                                     | inleft x' => svar s' x'
                                     | inright Heq => match sym_eq Heq in _ = T return T -> _ with
                                                        | refl_equal => f
                                                      end
                                   end
    end.

  Fixpoint SPush G T (s : subs G) (f : T -> PropX pc state) : subs (T :: G) :=
    match s in subs G return subs (T :: G) with
      | SNil => SCons _ nil f SNil
      | SCons T' Ts f' s' => SCons T (T' :: Ts) f' (SPush s' f)
    end.

  Section specs.
    Variable specs : codeSpec pc state.

    Section weaken.
      Hint Constructors valid.

      Hint Extern 1 (In _ _) => simpl; tauto.

      Hint Extern 3 (incl _ _) =>
        let x := fresh "x" in intro x;
          repeat match goal with
                   | [ H : incl _ _ |- _ ] => generalize (H x); clear H
                 end; simpl; intuition (subst; assumption).

      Theorem incl_cons : forall A x (G G' : list A),
        incl G G'
        -> incl (x :: G) (x :: G').
        auto.
      Qed.

      Hint Resolve incl_cons.

      Lemma valid_weaken : forall G Q, valid (state := state) specs G Q
        -> forall G', incl G G'
          -> valid specs G' Q.
        induction 1; intuition.

        eapply Inj_E; [ eauto | auto ].
        eapply Cptr_E; [ eauto | auto ].
        eapply And_E1; [ eauto ].
        eapply And_E2; [ eauto ].
        eapply Or_E; [ eauto | auto | auto ].
        eapply Imply_E; [ eauto | auto ].
        eapply Forall_E; [ eauto ].
        eapply Exists_I; eauto.
        eapply Exists_E; eauto.
        eapply ExistsX_I; eauto.
      Qed.

      Theorem interp_weaken : forall Q, interp (state := state) specs Q
        -> forall G, valid specs G Q.
        intros; eapply valid_weaken; eauto.
      Qed.

      Theorem valid_weaken1 : forall G (P : PropX pc state), valid specs G P
        -> forall T, valid specs (T :: G) P.
        intros; eapply valid_weaken; eauto.
      Qed.
    End weaken.

    Fixpoint simplify G (p : propX pc state G) : subs G -> Prop :=
      match p with
        | Inj P => fun _ => P
        | Cptr f a => fun s => specs f = Some (fun x => Substs s (a x))
        | And p1 p2 => fun s => simplify p1 s /\ simplify p2 s
        | Or p1 p2 => fun s => simplify p1 s \/ simplify p2 s
        | Imply p1 p2 => fun s => interp specs (Substs s (Imply p1 p2))
        | Forall _ p1 => fun s => forall x, simplify (p1 x) s
        | Exists _ p1 => fun s => exists x, simplify (p1 x) s
        | Var _ x v => fun s => interp specs (svar s x v)
        | ForallX _ p1 => fun s => forall a, simplify p1 (SPush s a)
        | ExistsX _ p1 => fun s => exists a, simplify p1 (SPush s a)
      end.

    Lemma Substs_Inj : forall G (s : subs G) P,
      Substs s (Inj P) = Inj P.
      induction s; simpl; intuition.
    Qed.

    Lemma Substs_Cptr : forall G (s : subs G) f a,
      Substs s (Cptr f a) = Cptr f (fun x => Substs s (a x)).
      induction s; simpl; intuition.
      f_equal; apply eta_expansion.
    Qed.
    
    Lemma Substs_And : forall G (s : subs G) p1 p2,
      Substs s (And p1 p2) = And (Substs s p1) (Substs s p2).
      induction s; simpl; intuition.
    Qed.

    Lemma Substs_Or : forall G (s : subs G) p1 p2,
      Substs s (Or p1 p2) = Or (Substs s p1) (Substs s p2).
      induction s; simpl; intuition.
    Qed.

    Lemma Substs_Imply : forall G (s : subs G) p1 p2,
      Substs s (Imply p1 p2) = Imply (Substs s p1) (Substs s p2).
      induction s; simpl; intuition.
    Qed.

    Lemma Substs_Forall : forall G (s : subs G) A (p1 : A -> _),
      Substs s (Forall p1) = Forall (fun x => Substs s (p1 x)).
      induction s; simpl; intuition.
      f_equal; apply eta_expansion.
    Qed.

    Lemma Substs_Exists : forall G (s : subs G) A (p1 : A -> _),
      Substs s (Exists p1) = Exists (fun x => Substs s (p1 x)).
      induction s; simpl; intuition.
      f_equal; apply eta_expansion.
    Qed.

    Lemma liftV_nada : forall G T (v : var G T) Heq,
      liftV v nil = match Heq in _ = L return var L _ with
                      | refl_equal => v
                    end.
      induction v; simpl; intuition.

      generalize Heq.
      change ((fun l => forall Heq0 : T :: Ts = T :: l,
        VO = match Heq0 in (_ = L) return (var L T) with
               | refl_equal => VO
             end) (Ts ++ nil)).
      rewrite <- app_nil_end; intros.
      rewrite (UIP_refl _ _ Heq0); trivial.

      rewrite (IHv (app_nil_end _)).
      repeat match goal with
               | [ |- context[match ?pf with refl_equal => _ end] ] => generalize pf
             end.
      change ((fun l => forall (Heq0 : T' :: Ts = T' :: l) (e : Ts = l),
        VS match e in (_ = L) return (var L T) with
             | refl_equal => v
           end =
        match Heq0 in (_ = L) return (var L T) with
          | refl_equal => VS v
        end) (Ts ++ nil)).
      rewrite <- app_nil_end; intros.
      rewrite (UIP_refl _ _ e); rewrite (UIP_refl _ _ Heq0); trivial.
    Qed.

    Lemma lift_nada' : forall G (p : propX pc state G) (Heq : G = G ++ nil),
      lift p nil = match Heq in _ = G return propX pc state G with
                     | refl_equal => p
                   end.
      induction p; simpl; intuition.

      generalize Heq.
      change ((fun l => forall Heq0 : G = l,
        [<P>]%PropX =
        match Heq0 in (_ = G0) return (propX pc state G0) with
          | refl_equal => [<P>]%PropX
        end) (G ++ nil)).
      rewrite <- Heq; intros.
      rewrite (UIP_refl _ _ Heq0); trivial.

      match goal with
        | [ |- Cptr p ?F = _ ] =>
          replace F
        with (fun x => match Heq in (_ = G0) return (propX pc state G0) with
                         | refl_equal => p0 x
                       end)
      end.
      generalize Heq.
      change ((fun l => forall Heq0 : G = l,
        Cptr p
        (fun x : state =>
          match Heq0 in (_ = G0) return (propX pc state G0) with
            | refl_equal => p0 x
          end) =
        match Heq0 in (_ = G0) return (propX pc state G0) with
          | refl_equal => Cptr p p0
        end) (G ++ nil)).
      rewrite <- Heq; intros.
      rewrite (UIP_refl _ _ Heq0); f_equal; symmetry; apply eta_expansion.

      extensionality x; auto.

      rewrite (IHp1 Heq).
      rewrite (IHp2 Heq).
      generalize Heq.
      change ((fun l => forall Heq0 : G = l,
        (match Heq0 in (_ = G0) return (propX pc state G0) with
           | refl_equal => p1
         end /\
        match Heq0 in (_ = G0) return (propX pc state G0) with
          | refl_equal => p2
        end)%PropX =
        match Heq0 in (_ = G0) return (propX pc state G0) with
          | refl_equal => (p1 /\ p2)%PropX
        end) (G ++ nil)).
      rewrite <- Heq; intros.
      rewrite (UIP_refl _ _ Heq0); trivial.

      rewrite (IHp1 Heq).
      rewrite (IHp2 Heq).
      generalize Heq.
      change ((fun l => forall Heq0 : G = l,
        (match Heq0 in (_ = G0) return (propX pc state G0) with
           | refl_equal => p1
         end \/
        match Heq0 in (_ = G0) return (propX pc state G0) with
          | refl_equal => p2
        end)%PropX =
        match Heq0 in (_ = G0) return (propX pc state G0) with
          | refl_equal => (p1 \/ p2)%PropX
        end) (G ++ nil)).
      rewrite <- Heq; intros.
      rewrite (UIP_refl _ _ Heq0); trivial.

      rewrite (IHp1 Heq).
      rewrite (IHp2 Heq).
      generalize Heq.
      change ((fun l => forall Heq0 : G = l,
        (match Heq0 in (_ = G0) return (propX pc state G0) with
           | refl_equal => p1
         end -->
        match Heq0 in (_ = G0) return (propX pc state G0) with
          | refl_equal => p2
        end)%PropX =
        match Heq0 in (_ = G0) return (propX pc state G0) with
          | refl_equal => (p1 --> p2)%PropX
        end) (G ++ nil)).
      rewrite <- Heq; intros.
      rewrite (UIP_refl _ _ Heq0); trivial.

      match goal with
        | [ |- Forall ?F = _ ] =>
          replace F
        with (fun x => match Heq in (_ = G0) return (propX pc state G0) with
                         | refl_equal => p x
                       end)
      end.
      generalize Heq.
      change ((fun l => forall Heq0 : G = l,
        (Al x : A,
          match Heq0 in (_ = G0) return (propX pc state G0) with
            | refl_equal => p x
          end)%PropX =
        match Heq0 in (_ = G0) return (propX pc state G0) with
          | refl_equal => Forall p
        end) (G ++ nil)).
      rewrite <- Heq; intros.
      rewrite (UIP_refl _ _ Heq0); f_equal; symmetry; apply eta_expansion.

      extensionality x; auto.

      match goal with
        | [ |- Exists ?F = _ ] =>
          replace F
        with (fun x => match Heq in (_ = G0) return (propX pc state G0) with
                         | refl_equal => p x
                       end)
      end.
      generalize Heq.
      change ((fun l => forall Heq0 : G = l,
        (Ex x : A,
          match Heq0 in (_ = G0) return (propX pc state G0) with
            | refl_equal => p x
          end)%PropX =
        match Heq0 in (_ = G0) return (propX pc state G0) with
          | refl_equal => Exists p
        end) (G ++ nil)).
      rewrite <- Heq; intros.
      rewrite (UIP_refl _ _ Heq0); f_equal; symmetry; apply eta_expansion.

      extensionality x; auto.

      rewrite (liftV_nada _ Heq).
      generalize Heq.
      change ((fun l => forall Heq0 : G = l,
        (match Heq0 in (_ = L) return (var L A) with
           | refl_equal => v
         end @ a)%PropX =
        match Heq0 in (_ = G0) return (propX pc state G0) with
          | refl_equal => (v @ a)%PropX
        end) (G ++ nil)).
      rewrite <- Heq; intros.
      rewrite (UIP_refl _ _ Heq0); trivial.

      assert (A :: G = (A :: G) ++ nil) by (rewrite <- app_nil_end; trivial).
      rewrite (IHp H).
      repeat match goal with
               | [ |- context[match ?pf with refl_equal => _ end] ] => generalize pf
             end.      
      simpl.
      change ((fun l => forall (Heq0 : G = l) (H0 : A :: G = A :: l),
        (AlX  : A,
          match H0 in (_ = G0) return (propX pc state G0) with
            | refl_equal => p
          end)%PropX =
        match Heq0 in (_ = G0) return (propX pc state G0) with
          | refl_equal => (AlX  : A, p)%PropX
        end) (G ++ nil)).
      rewrite <- app_nil_end; intros.
      rewrite (UIP_refl _ _ H0); rewrite (UIP_refl _ _ Heq0); trivial.

      assert (A :: G = (A :: G) ++ nil) by (rewrite <- app_nil_end; trivial).
      rewrite (IHp H).
      repeat match goal with
               | [ |- context[match ?pf with refl_equal => _ end] ] => generalize pf
             end.      
      simpl.
      change ((fun l => forall (Heq0 : G = l) (H0 : A :: G = A :: l),
        (ExX  : A,
          match H0 in (_ = G0) return (propX pc state G0) with
            | refl_equal => p
          end)%PropX =
        match Heq0 in (_ = G0) return (propX pc state G0) with
          | refl_equal => (ExX  : A, p)%PropX
        end) (G ++ nil)).
      rewrite <- app_nil_end; intros.
      rewrite (UIP_refl _ _ H0); rewrite (UIP_refl _ _ Heq0); trivial.
    Qed.

    Lemma lift_nada : forall p : PropX pc state,
      lift p nil = p.
      intros; apply (lift_nada' p (refl_equal _)).
    Qed.

    Lemma liftV_cons : forall G' T (x : var G' T) G Heq,
      substV (liftV x G) = inleft _ (match Heq in _ = L return var L T with
                                       | refl_equal => liftV x (eatLast G)
                                     end).
      induction x; simpl; intuition.
      change ((fix app (l m : list Type) : list Type :=
        match l with
          | nil => m
          | a :: l1 => a :: app l1 m
        end) Ts G) with (Ts ++ G).
      generalize Heq.
      change ((fun L => forall
        Heq0 : T :: Ts ++ eatLast G =
        match L with
          | nil => nil
          | _ :: _ => T :: eatLast L
        end,
        match
          L as Ts0
            return
            (var match Ts0 with
                   | nil => nil
                   | _ :: _ => T :: eatLast Ts0
                 end T + {T = match Ts0 with
                                | nil => T
                                | _ :: _ => last Ts0
                              end})
          with
          | nil => inright (var nil T) (refl_equal T)
          | T0 :: l =>
            inleft (T = match l with
                          | nil => T0
                          | _ :: _ => last l
                        end) VO
        end =
        inleft (T = match L with
                      | nil => T
                      | _ :: _ => last L
                    end)
        match Heq0 in (_ = L) return (var L T) with
          | refl_equal => VO
        end) (Ts ++ G)).
      destruct (Ts ++ G); intros.

      discriminate.

      f_equal.
      injection Heq0; intros; subst.
      generalize Heq0.
      rewrite H; intros.
      rewrite (UIP_refl _ _ Heq1); trivial.

      assert (Heq' : Ts ++ eatLast G = eatLast (Ts ++ G)).
      destruct Ts; trivial; destruct G; simpl in *.
      injection Heq; trivial.
      injection Heq; trivial.

      rewrite (IHx _ Heq'); clear IHx.
      f_equal.
      generalize Heq Heq'.
      change ((fun L => forall
        (Heq0 : T' :: Ts ++ eatLast G =
          match L with
            | nil => nil
            | _ :: _ => T' :: eatLast L
          end) (Heq'0 : Ts ++ eatLast G = eatLast L),
        substMore L T'
        match Heq'0 in (_ = L) return (var L T) with
          | refl_equal => liftV x (eatLast G)
        end =
        match Heq0 in (_ = L) return (var L T) with
          | refl_equal => VS (liftV x (eatLast G))
        end) (Ts ++ G)).
      destruct (Ts ++ G); intros.
      discriminate.
      simpl.
      destruct l.
      generalize (match Heq'0 in (_ = L) return (var L T) with
                    | refl_equal => liftV x (eatLast G)
                  end); intro v; inversion v.

      generalize (liftV x (eatLast G)) Heq0 Heq'0.
      change ((fun L => forall (v : var L T)
        (Heq1 : T' :: L = T' :: eatLast (T0 :: T1 :: l))
        (Heq'1 : L = eatLast (T0 :: T1 :: l)),
        VS match Heq'1 in (_ = L) return (var L T) with
             | refl_equal => v
           end =
        match Heq1 in (_ = L) return (var L T) with
          | refl_equal => VS v
        end) (Ts ++ eatLast G)).
      rewrite Heq'0; intros.
      rewrite (UIP_refl _ _ Heq1); rewrite (UIP_refl _ _ Heq'1); trivial.
    Qed.

    Lemma nilEat : forall G G0,
      G ++ G0 = nil -> eatLast G0 = G0.
      induction G; simpl; intuition.
      subst; trivial.
      discriminate.
    Qed.

    Implicit Arguments nilEat [G G0].

    Lemma lift_cons' : forall G' (p : propX pc state G') G Heq p',
      subst (lift p G) p' = match Heq in _ = L return propX pc state L with
                              | refl_equal => lift p (eatLast G)
                            end.
      induction p; simpl; intuition.

      generalize Heq.
      change ((fun l => forall Heq0 : G ++ eatLast G0 = l,
        [<P>]%PropX =
        match Heq0 in (_ = L) return (propX pc state L) with
          | refl_equal => [<P>]%PropX
        end) (eatLast (G ++ G0))).
      rewrite <- Heq; intros.
      rewrite (UIP_refl _ _ Heq0); trivial.

      match goal with
        | [ |- Cptr p ?F = _ ] =>
          replace F
        with (fun x => match Heq in (_ = G0) return (propX pc state G0) with
                         | refl_equal => lift (p0 x) _
                       end)
      end.
      generalize Heq.
      change ((fun l => forall Heq0 : G ++ eatLast G0 = l,
        Cptr p
        (fun x : state =>
          match Heq0 in (_ = G1) return (propX pc state G1) with
            | refl_equal => ^[p0 x]%PropX
          end) =
        match Heq0 in (_ = L) return (propX pc state L) with
          | refl_equal => Cptr p (fun x : state => ^[p0 x]%PropX)
        end) (eatLast (G ++ G0))).
      rewrite <- Heq; intros.
      rewrite (UIP_refl _ _ Heq0); f_equal; symmetry; apply eta_expansion.

      extensionality x; auto.

      rewrite (IHp1 _ Heq).
      rewrite (IHp2 _ Heq).
      generalize Heq.
      change ((fun l => forall Heq0 : G ++ eatLast G0 = l,
        (match Heq0 in (_ = L) return (propX pc state L) with
           | refl_equal => ^[p1]
         end /\
        match Heq0 in (_ = L) return (propX pc state L) with
          | refl_equal => ^[p2]
        end)%PropX =
        match Heq0 in (_ = L) return (propX pc state L) with
          | refl_equal => (^[p1] /\ ^[p2])%PropX
        end) (eatLast (G ++ G0))).
      rewrite <- Heq; intros.
      rewrite (UIP_refl _ _ Heq0); trivial.

      rewrite (IHp1 _ Heq).
      rewrite (IHp2 _ Heq).
      generalize Heq.
      change ((fun l => forall Heq0 : G ++ eatLast G0 = l,
        (match Heq0 in (_ = L) return (propX pc state L) with
           | refl_equal => ^[p1]
         end \/
        match Heq0 in (_ = L) return (propX pc state L) with
          | refl_equal => ^[p2]
        end)%PropX =
        match Heq0 in (_ = L) return (propX pc state L) with
          | refl_equal => (^[p1] \/ ^[p2])%PropX
        end) (eatLast (G ++ G0))).
      rewrite <- Heq; intros.
      rewrite (UIP_refl _ _ Heq0); trivial.

      rewrite (IHp1 _ Heq).
      rewrite (IHp2 _ Heq).
      generalize Heq.
      change ((fun l => forall Heq0 : G ++ eatLast G0 = l,
        (match Heq0 in (_ = L) return (propX pc state L) with
           | refl_equal => ^[p1]
         end -->
        match Heq0 in (_ = L) return (propX pc state L) with
          | refl_equal => ^[p2]
        end)%PropX =
        match Heq0 in (_ = L) return (propX pc state L) with
          | refl_equal => (^[p1] --> ^[p2])%PropX
        end) (eatLast (G ++ G0))).
      rewrite <- Heq; intros.
      rewrite (UIP_refl _ _ Heq0); trivial.

      match goal with
        | [ |- Forall ?F = _ ] =>
          replace F
        with (fun x => match Heq in (_ = G0) return (propX pc state G0) with
                         | refl_equal => lift (p x) _
                       end)
      end.
      generalize Heq.
      change ((fun l => forall Heq0 : G ++ eatLast G0 = l,
        (Al x : A,
          match Heq0 in (_ = G1) return (propX pc state G1) with
            | refl_equal => ^[p x]
          end)%PropX =
        match Heq0 in (_ = L) return (propX pc state L) with
          | refl_equal => (Al x : A, ^[p x])%PropX
        end) (eatLast (G ++ G0))).
      rewrite <- Heq; intros.
      rewrite (UIP_refl _ _ Heq0); f_equal; symmetry; apply eta_expansion.

      extensionality x; auto.

      match goal with
        | [ |- Exists ?F = _ ] =>
          replace F
        with (fun x => match Heq in (_ = G0) return (propX pc state G0) with
                         | refl_equal => lift (p x) _
                       end)
      end.
      generalize Heq.
      change ((fun l => forall Heq0 : G ++ eatLast G0 = l,
        (Ex x : A,
          match Heq0 in (_ = G1) return (propX pc state G1) with
            | refl_equal => ^[p x]
          end)%PropX =
        match Heq0 in (_ = L) return (propX pc state L) with
          | refl_equal => (Ex x : A, ^[p x])%PropX
        end) (eatLast (G ++ G0))).
      rewrite <- Heq; intros.
      rewrite (UIP_refl _ _ Heq0); f_equal; symmetry; apply eta_expansion.

      extensionality x; auto.

      rewrite (liftV_cons _ _ Heq).
      generalize (liftV v (eatLast G0)).
      generalize Heq.
      rewrite <- Heq; intros.
      rewrite (UIP_refl _ _ Heq0); trivial.

      specialize (IHp G0).
      generalize dependent IHp.
      Require Import JMeq.
      assert (Hextra : G ++ G0 = nil -> JMeq (lift p G0) (lift p (eatLast G0))).
      intros.
      assert (G0 = nil).
      destruct G; simpl in *; trivial; discriminate.
      subst.
      trivial.
      generalize Heq p' (lift p G0) (lift p (eatLast G0)) Hextra; simpl.

      change ((fun L => forall (Heq0 : G ++ eatLast G0 = eatLast L)
        (p'0 : last L -> PropX pc state)
        (p0 : propX pc state (A :: L))
        (p1 : propX pc state (A :: G ++ eatLast G0)),
        (L = nil -> JMeq p0 p1) ->
        (forall
          (Heq1 : A :: G ++ eatLast G0 =
            match L with
              | nil => nil
              | _ :: _ => A :: eatLast L
            end)
          (p'1 : match L with
                   | nil => A
                   | _ :: _ => last L
                 end -> PropX pc state),
          subst p0 p'1 =
            match Heq1 in (_ = L) return (propX pc state L) with
              | refl_equal => p1
            end) ->
        match
          L as G1
            return
            (propX pc state (A :: G1) ->
              propX pc state
              match G1 with
                | nil => nil
                | _ :: _ => A :: eatLast G1
              end -> propX pc state (eatLast G1))
          with
          | nil =>
            fun (p2 : propX pc state (A :: nil)) (_ : propX pc state nil) =>
              (AlX  : A, p2)%PropX
          | T :: l =>
            fun (_ : propX pc state (A :: T :: l))
              (rc : propX pc state
                (A
                  :: match l with
                       | nil => nil
                       | _ :: _ => T :: eatLast l
                     end)) => (AlX  : A, rc)%PropX
        end p0
        (subst p0
          (match
             L as G1
               return
               ((last G1 -> PropX pc state) ->
                 match G1 with
                   | nil => A
                   | _ :: _ => last G1
                 end -> PropX pc state)
             with
             | nil => fun (_ : unit -> PropX pc state) (_ : A) => [<True>]%PropX
             | T :: l =>
               fun
                 p'1 : match l with
                         | nil => T
                         | _ :: _ => last l
                       end -> PropX pc state => p'1
           end p'0)) =
        match Heq0 in (_ = L) return (propX pc state L) with
          | refl_equal => (AlX  : A, p1)%PropX
        end) (G ++ G0)).
      destruct (G ++ G0); simpl; intuition.

      generalize p0 p1 H1 Heq0.
      change ((fun L => forall (p2 : propX pc state (A :: nil))
        (p3 : propX pc state (A :: L)),
        JMeq p2 p3 ->
        forall Heq1 : L = nil,
          (AlX  : A, p2)%PropX =
          match Heq1 in (_ = L) return (propX pc state L) with
            | refl_equal => (AlX  : A, p3)%PropX
          end) (G ++ eatLast G0)).
      rewrite Heq0; intros.
      rewrite (UIP_refl _ _ Heq1); f_equal; rewrite H; trivial.

      assert (Heq' : A :: G ++ eatLast G0 =
        A
        :: match l with
             | nil => nil
             | _ :: _ => T :: eatLast l
           end) by (f_equal; assumption).
      rewrite (H0 Heq'); clear H0.
      generalize Heq' Heq0 p1.
      change ((fun L => forall
        (Heq'0 : A :: L =
          A :: match l with
                 | nil => nil
                 | _ :: _ => T :: eatLast l
               end)
        (Heq1 : L =
          match l with
            | nil => nil
            | _ :: _ => T :: eatLast l
          end) (p2 : propX pc state (A :: L)),
        (AlX  : A,
          match Heq'0 in (_ = L) return (propX pc state L) with
            | refl_equal => p2
          end)%PropX =
        match Heq1 in (_ = L) return (propX pc state L) with
          | refl_equal => (AlX  : A, p2)%PropX
        end) (G ++ eatLast G0)).
      rewrite Heq0; intros.
      rewrite (UIP_refl _ _ Heq'0); rewrite (UIP_refl _ _ Heq1); trivial.

      specialize (IHp G0).
      generalize dependent IHp.
      assert (Hextra : G ++ G0 = nil -> JMeq (lift p G0) (lift p (eatLast G0))).
      intros.
      assert (G0 = nil).
      destruct G; simpl in *; trivial; discriminate.
      subst.
      trivial.
      generalize Heq p' (lift p G0) (lift p (eatLast G0)) Hextra; simpl.

      change ((fun L => forall (Heq0 : G ++ eatLast G0 = eatLast L)
        (p'0 : last L -> PropX pc state)
        (p0 : propX pc state (A :: L))
        (p1 : propX pc state (A :: G ++ eatLast G0)),
        (L = nil -> JMeq p0 p1) ->
        (forall
          (Heq1 : A :: G ++ eatLast G0 =
            match L with
              | nil => nil
              | _ :: _ => A :: eatLast L
            end)
          (p'1 : match L with
                   | nil => A
                   | _ :: _ => last L
                 end -> PropX pc state),
          subst p0 p'1 =
            match Heq1 in (_ = L) return (propX pc state L) with
              | refl_equal => p1
            end) ->
        match
          L as G1
            return
            (propX pc state (A :: G1) ->
              propX pc state
              match G1 with
                | nil => nil
                | _ :: _ => A :: eatLast G1
              end -> propX pc state (eatLast G1))
          with
          | nil =>
            fun (p2 : propX pc state (A :: nil)) (_ : propX pc state nil) =>
              (ExX  : A, p2)%PropX
          | T :: l =>
            fun (_ : propX pc state (A :: T :: l))
              (rc : propX pc state
                (A
                  :: match l with
                       | nil => nil
                       | _ :: _ => T :: eatLast l
                     end)) => (ExX  : A, rc)%PropX
        end p0
        (subst p0
          (match
             L as G1
               return
               ((last G1 -> PropX pc state) ->
                 match G1 with
                   | nil => A
                   | _ :: _ => last G1
                 end -> PropX pc state)
             with
             | nil => fun (_ : unit -> PropX pc state) (_ : A) => [<True>]%PropX
             | T :: l =>
               fun
                 p'1 : match l with
                         | nil => T
                         | _ :: _ => last l
                       end -> PropX pc state => p'1
           end p'0)) =
        match Heq0 in (_ = L) return (propX pc state L) with
          | refl_equal => (ExX  : A, p1)%PropX
        end) (G ++ G0)).
      destruct (G ++ G0); simpl; intuition.

      generalize p0 p1 H1 Heq0.
      change ((fun L => forall (p2 : propX pc state (A :: nil))
        (p3 : propX pc state (A :: L)),
        JMeq p2 p3 ->
        forall Heq1 : L = nil,
          (ExX  : A, p2)%PropX =
          match Heq1 in (_ = L) return (propX pc state L) with
            | refl_equal => (ExX  : A, p3)%PropX
          end) (G ++ eatLast G0)).
      rewrite Heq0; intros.
      rewrite (UIP_refl _ _ Heq1); f_equal; rewrite H; trivial.

      assert (Heq' : A :: G ++ eatLast G0 =
        A
        :: match l with
             | nil => nil
             | _ :: _ => T :: eatLast l
           end) by (f_equal; assumption).
      rewrite (H0 Heq'); clear H0.
      generalize Heq' Heq0 p1.
      change ((fun L => forall
        (Heq'0 : A :: L =
          A :: match l with
                 | nil => nil
                 | _ :: _ => T :: eatLast l
               end)
        (Heq1 : L =
          match l with
            | nil => nil
            | _ :: _ => T :: eatLast l
          end) (p2 : propX pc state (A :: L)),
        (ExX  : A,
          match Heq'0 in (_ = L) return (propX pc state L) with
            | refl_equal => p2
          end)%PropX =
        match Heq1 in (_ = L) return (propX pc state L) with
          | refl_equal => (ExX  : A, p2)%PropX
        end) (G ++ eatLast G0)).
      rewrite Heq0; intros.
      rewrite (UIP_refl _ _ Heq'0); rewrite (UIP_refl _ _ Heq1); trivial.
    Qed.

    Lemma lift_cons : forall (p : PropX pc state) G (p' : last G -> PropX pc state),
      subst (G := G) (lift p G) p' = lift p (eatLast G).
      intros; apply (lift_cons' p G (refl_equal _)).
    Qed.

    Lemma lift_cons2 : forall T1 T2 (p : propX pc state (T1 :: nil))
      (p1 : T2 -> PropX pc state) (p2 : T1 -> PropX pc state),
      subst (G := T1 :: nil) (subst (G := T1 :: T2 :: nil) (lift p (T2 :: nil)) p1) p2
      = subst p p2.
      intros; rewrite (lift_cons' p (T2 :: nil) (refl_equal _)).
      f_equal.
      apply (lift_nada' p (refl_equal _)).
    Qed.

    Lemma lift_cons3 : forall T1 T2 T3 (p : propX pc state (T1 :: T2 :: nil))
      (p1 : T3 -> PropX pc state) (p2 : T2 -> PropX pc state) (p3 : T1 -> PropX pc state),
      subst (G := T1 :: nil) (subst (G := T1 :: T2 :: nil) (subst (G := T1 :: T2 :: T3 :: nil)
        (lift p (T3 :: nil)) p1) p2) p3
      = subst (subst p p2) p3.
      intros; rewrite (lift_cons' p (T3 :: nil) (refl_equal _)).
      repeat f_equal.
      apply (lift_nada' p (refl_equal _)).
    Qed.

    Theorem Imply_easyL'' : forall G (p1 p2 p : PropX pc state),
      valid specs G (Imply p1 (Imply p2 p))
      -> valid specs G (Imply (And p1 p2) p).
      intros.
      apply Imply_I.
      eapply Imply_E.
      eapply Imply_E.
      apply valid_weaken1; eauto.
      eapply And_E1; apply Env; simpl; tauto.
      eapply And_E2; apply Env; simpl; tauto.
    Qed.

    Lemma Substs_lift : forall G s p,
      Substs s (lift p G) = p.
      simpl; induction s; simpl; intuition.

      apply lift_nada.

      assert (Substs s (subst ^[p0]%PropX p) = Substs s ^[p0]).
      f_equal.
      apply lift_cons.
      transitivity (Substs s ^[p0]); auto.
    Qed.

    Lemma Substs_Var : forall G (s : subs G) A (x : var G A) v,
      Substs s (Var x v) = svar s x v.
      induction s; simpl; intuition.
      inversion x.
      destruct (substV x); intuition.
      eapply trans_eq.
      apply Substs_lift.
      generalize e p.
      subst; intros.
      rewrite (UIP_refl _ _ e); trivial.
    Qed.

    Hint Rewrite Substs_Inj Substs_Cptr Substs_And Substs_Or Substs_Imply
      Substs_Forall Substs_Exists Substs_Var : Substs.

    Hint Resolve interp_weaken valid_weaken1.

    Lemma simplify_bwd_ForallX : forall G A s (p : propX pc state (A :: G)),
      (forall a, interp specs (Substs (SPush s a) p))
      -> interp specs (Substs s (AlX  : A, p)).
      induction s; simpl; intuition.
      apply ForallX_I; auto.
    Qed.

    Lemma simplify_bwd_ExistsX : forall G A a s (p : propX pc state (A :: G)),
      interp specs (Substs (SPush s a) p)
      -> interp specs (Substs s (ExX  : A, p)).
      induction s; simpl; intuition.
      apply ExistsX_I with a; auto.
    Qed.

    Lemma simplify_bwd' : forall G (p : propX pc state G) s,
      simplify p s
      -> interp specs (Substs s p).
      unfold interp; induction p; simpl; intuition; autorewrite with Substs in *.

      apply Inj_I; auto.
      apply Cptr_I; auto.
      apply And_I; auto.
      apply Or_I1; auto.
      apply Or_I2; auto.
      apply Forall_I; auto.
      destruct H0 as [x]; apply Exists_I with x; auto.
      assumption.
      apply simplify_bwd_ForallX; firstorder.
      destruct H as [x]; apply simplify_bwd_ExistsX with x; firstorder.
    Qed.

    Lemma simplify_bwd : forall p,
      simplify p SNil
      -> interp specs p.
      intros; change (interp specs (Substs SNil p)); apply simplify_bwd'; auto.
    Qed.

    Lemma simplify_fwd_ForallX : forall G A a s (p : propX pc state (A :: G)),
      interp specs (Substs s (AlX  : A, p))
      -> interp specs (Substs (SPush s a) p).
      induction s; simpl; intuition.
      apply ForallX_sound; auto.
    Qed.

    Lemma simplify_fwd_ExistsX : forall G A s (p : propX pc state (A :: G)),
      interp specs (Substs s (ExX  : A, p))
      -> exists a, interp specs (Substs (SPush s a) p).
      induction s; simpl; intuition.
      apply ExistsX_sound; auto.
    Qed.

    Lemma simplify_fwd' : forall G (p : propX pc state G) s,
      interp specs (Substs s p)
      -> simplify p s.
      induction p; simpl; intuition; autorewrite with Substs in *.

      apply (Inj_sound H).
      apply (Cptr_sound H0).
      apply And_sound in H; intuition.
      apply And_sound in H; intuition.
      apply Or_sound in H; intuition.
      specialize (Forall_sound H0); intuition.
      specialize (Exists_sound H0); firstorder.
      assumption.
      apply IHp; apply simplify_fwd_ForallX; auto.
      apply simplify_fwd_ExistsX in H; firstorder.
    Qed.

    Lemma simplify_fwd : forall p,
      interp specs p
      -> simplify p SNil.
      intros; apply simplify_fwd'; auto.
    Qed.

    Fixpoint simplifyH G (p : propX pc state G) : subs G -> Prop :=
      match p with
        | Inj P => fun _ => P
        | Cptr f a => fun s => specs f = Some (fun x => Substs s (a x))
        | And p1 p2 => fun s => simplifyH p1 s /\ simplifyH p2 s
        | Or p1 p2 => fun s => simplifyH p1 s \/ simplifyH p2 s
        | Imply p1 p2 => fun _ => True
        | Forall _ p1 => fun _ => True
        | Exists _ p1 => fun s => exists x, simplifyH (p1 x) s
        | Var _ x v => fun _ => True
        | ForallX _ p1 => fun _ => True
        | ExistsX _ p1 => fun _ => True
      end.

    Lemma simplifyH_ok : forall G (p : propX pc state G) s PG p',
      In (Substs s p) PG
      -> (simplifyH p s -> valid specs PG (Substs s p'))
      -> valid specs PG (Substs s p').
      induction p; simpl; intuition; autorewrite with Substs in *.

      eapply Inj_E; [ constructor; eauto | auto ].

      eapply Cptr_E; [ constructor; eauto | auto ].

      assert (valid specs PG (Substs s p1 --> Substs s p2 --> Substs s p')%PropX).
      repeat apply Imply_I.
      apply IHp1.
      simpl; tauto.
      intro.
      apply IHp2.
      simpl; tauto.
      eauto.
      eapply Imply_E.
      eapply Imply_E.
      eassumption.
      eapply And_E1; econstructor; eauto.
      eapply And_E2; econstructor; eauto.

      eapply Or_E.
      constructor; eauto.
      intuition.
      intuition.

      eapply Exists_E.
      constructor; eauto.
      simpl; intros.
      apply H with B; intuition.
      eauto.
    Qed.

    Theorem simplify_Imply : forall p1 p2,
      (simplifyH p1 SNil -> simplify p2 SNil)
      -> interp specs (Imply p1 p2).
      intros.
      change (interp specs (Imply (Substs SNil p1) (Substs SNil p2))).
      apply Imply_I.
      eapply simplifyH_ok.
      simpl; tauto.
      intros.
      apply valid_weaken1.
      apply simplify_bwd.
      auto.
    Qed.

    Theorem Imply_easyL' : forall G (p1 p2 p : PropX pc state),
      (simplifyH p1 SNil -> valid specs G (Imply p2 p))
      -> valid specs G (Imply (And p1 p2) p).
      intros; apply Imply_easyL''.
      apply Imply_I.
      change (p2 --> p)%PropX with (Substs SNil (p2 --> p)%PropX).
      eapply simplifyH_ok.
      simpl; tauto.
      intro.
      simpl.
      apply valid_weaken1; auto.
    Qed.

    Theorem Imply_easyL : forall (p1 p2 p : PropX pc state),
      (simplifyH p1 SNil -> interp specs (Imply p2 p))
      -> interp specs (Imply (And p1 p2) p).
      intros; apply Imply_easyL'; auto.
    Qed.

    Theorem Imply_trans' : forall G (p1 p2 p3 : PropX pc state),
      valid specs G (Imply p1 p2)
      -> valid specs G (Imply p2 p3)
      -> valid specs G (Imply p1 p3).
      intros; apply Imply_I.
      eapply Imply_E.
      apply valid_weaken1; eassumption.
      eapply Imply_E.
      apply valid_weaken1; eassumption.
      apply Env; simpl; tauto.
    Qed.

    Theorem Imply_trans : forall p1 p2 p3 : PropX pc state,
      interp specs (Imply p1 p2)
      -> interp specs (Imply p2 p3)
      -> interp specs (Imply p1 p3).
      unfold interp; intros; eapply Imply_trans'; eauto.
    Qed.

    Theorem Imply_easyEx' : forall G T (p1 : T -> _) (p : PropX pc state),
      (forall x, valid specs G (Imply (p1 x) p))
      -> valid specs G (Imply (Exists p1) p).
      intros; apply Imply_I.
      eapply Exists_E.
      apply Env; simpl; tauto.
      intros.
      eapply Imply_E.
      eapply valid_weaken.
      apply H.
      red; intuition.
      apply Env; simpl; tauto.
    Qed.

    Theorem Imply_easyEx : forall T (p1 : T -> _) (p : PropX pc state),
      (forall x, interp specs (Imply (p1 x) p))
      -> interp specs (Imply (Exists p1) p).
      unfold interp; intros; apply Imply_easyEx'; auto.
    Qed.

    Theorem Env1 : forall (G : list (PropX pc state)) P, valid specs (P :: G) P.
      intros; apply Env; simpl; tauto.
    Qed.
  End specs.

  Lemma lift_nadaF : forall A (f : A -> PropX pc state),
    (fun x => lift (f x) nil) = f.
    intros; extensionality x; apply lift_nada.
  Qed.

  Lemma lift_consF : forall A (p : A -> PropX pc state) G (p' : last G -> PropX pc state),
    (fun x => subst (G := G) (lift (p x) G) p') = (fun x => lift (p x) (eatLast G)).
    intros; extensionality x; apply lift_cons.
  Qed.

  Lemma lift_consF2 : forall A (p : A -> PropX pc state) T1 T2
    (p1 : T2 -> PropX pc state) (p2 : T1 -> PropX pc state),
    (fun x => subst (G := T1 :: nil) (subst (G := T1 :: T2 :: nil) (lift (p x) (T1 :: T2 :: nil)) p1) p2)
    = p.
    intros; extensionality x; repeat rewrite lift_cons; apply lift_nada.
  Qed.
End machine.

Ltac propx :=
  repeat match goal with
           | [ H : interp _ _ |- _ ] => apply simplify_fwd in H; progress simpl in H
         end;
  try (apply simplify_bwd; simpl;
    repeat (apply simplify_Imply; simpl; intro)).

Hint Rewrite lift_nada lift_cons : PropX.
Hint Rewrite lift_nadaF lift_consF lift_consF2 : PropXF.

Ltac propxR := autorewrite with PropX in *.

Ltac propxFo' := intuition auto; propxR.

Ltac doImply H := eapply Imply_E; [ apply H | apply simplify_bwd; simpl; propxFo' ].

Ltac propxFo := propxFo'; repeat progress (propx; propxFo');
  repeat match goal with
           | [ H : True |- _ ] => clear H
           | [ |- simplify _ _ _ ] => apply simplify_fwd';
             repeat progress (simpl; propxR); auto
           | [ H : simplify _ _ _ |- _ ] => apply simplify_bwd' in H;
             repeat progress (simpl in H; propxR)
           | [ H : ex _ |- _ ] => destruct H; propxFo'
         end.

Hint Resolve interp_weaken Env1.

Ltac ensureNoUnifs E :=
  first [ has_evar E; fail 1 | idtac ].

Ltac ensureNotUnif E :=
  first [ ensureNoUnifs E
        | match E with
            | ?f _ => ensureNotUnif f
            | ?f _ _ => ensureNotUnif f
            | ?f _ _ _ => ensureNotUnif f
            | ?f _ _ _ _ => ensureNotUnif f
          end ].
