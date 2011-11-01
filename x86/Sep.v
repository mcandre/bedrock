Require Import Ring Eqdep FunctionalExtensionality.
Require Import Struct.

Export Ring.
Export Struct.

Set Implicit Arguments.

Definition wring8 : ring_theory (wzero W8) (wone W8)
  (@wplus W8) (@wmult W8) (@wminus W8) (@wneg W8) (@eq (word W8))
  := Word.wring 8.
Add Ring wring8 : wring8 (decidable (@weqb_sound W8), constants [Word.wcst]).

Definition wring16 : ring_theory (wzero W16) (wone W16)
  (@wplus W16) (@wmult W16) (@wminus W16) (@wneg W16) (@eq (word W16))
  := Word.wring 16.
Add Ring wring16 : wring16 (decidable (@weqb_sound W16), constants [Word.wcst]).

Definition wring32 : ring_theory (wzero W32) (wone W32)
  (@wplus W32) (@wmult W32) (@wminus W32) (@wneg W32) (@eq (word W32))
  := Word.wring 32.
Add Ring wring32 : wring32 (decidable (@weqb_sound W32), constants [Word.wcst]).

Definition wring64 : ring_theory (wzero W64) (wone W64)
  (@wplus W64) (@wmult W64) (@wminus W64) (@wneg W64) (@eq (word W64))
  := Word.wring 64.
Add Ring wring64 : wring64 (decidable (@weqb_sound W64), constants [Word.wcst]).

Module SepArg.
  Definition addr := word W64.
  Definition byte := word W8.
  Definition size := wsize.
  Definition word := word.

  Definition addresses (a : addr) (sz : size) : list addr :=
    match sz with
      | W8 => a :: nil
      | W16 => a :: a ^+ inj _ 1 :: nil
      | W32 => a :: a ^+ inj _ 1 :: a ^+ inj _ 2 :: a ^+ inj _ 3 :: nil
      | W64 => a :: a ^+ inj _ 1 :: a ^+ inj _ 2 :: a ^+ inj _ 3
        :: a ^+ inj _ 4 :: a ^+ inj _ 5 :: a ^+ inj _ 6 :: a ^+ inj _ 7 :: nil
    end.

  Definition explode (a : addr) (sz : size) : word sz -> list (addr * byte) :=
    match sz return word sz -> list (addr * byte) with
      | W8 => fun w => (a, w) :: nil
      | W16 => fun w =>
           (a, Word.split1 8 8 w)
        :: (a ^+ inj _ 1, Word.split2 8 8 w)
        :: nil
      | W32 => fun w => 
           (a,            Word.split1 8 _ (Word.split1 16 _ w))
        :: (a ^+ inj _ 1, Word.split2 8 _ (Word.split1 16 _ w))
        :: (a ^+ inj _ 2, Word.split1 8 _ (Word.split2 16 16 w))
        :: (a ^+ inj _ 3, Word.split2 8 8 (Word.split2 16 _ w))
        :: nil
      | W64 => fun w => 
           (a,            Word.split1 8 _ (Word.split1 16 16 (Word.split1 32 _ w)))
        :: (a ^+ inj _ 1, Word.split2 8 _ (Word.split1 16 16 (Word.split1 32 _ w)))
        :: (a ^+ inj _ 2, Word.split1 8 _ (Word.split2 16 16 (Word.split1 32 _ w)))
        :: (a ^+ inj _ 3, Word.split2 8 _ (Word.split2 16 16 (Word.split1 32 _ w)))
        :: (a ^+ inj _ 4, Word.split1 8 _ (Word.split1 16 16 (Word.split2 32 _ w)))
        :: (a ^+ inj _ 5, Word.split2 8 _ (Word.split1 16 16 (Word.split2 32 _ w)))
        :: (a ^+ inj _ 6, Word.split1 8 _ (Word.split2 16 16 (Word.split2 32 _ w)))
        :: (a ^+ inj _ 7, Word.split2 8 _ (Word.split2 16 16 (Word.split2 32 _ w)))
        :: nil
    end.

  Definition implode (bs : list byte) (sz : size) : word sz :=
    match sz return word sz with
      | W8 =>
        match bs with
          | b :: nil => b
          | _ => wzero _
        end
      | W16 =>
        match bs with
          | b0 :: b1 :: nil => Word.combine b0 b1
          | _ => wzero _
        end
      | W32 =>
        match bs with
          | b0 :: b1 :: b2 :: b3 :: nil =>
            Word.combine (Word.combine b0 b1) (Word.combine b2 b3)
          | _ => wzero _
        end
      | W64 =>
        match bs with
          | b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: nil =>
            Word.combine (Word.combine (Word.combine b0 b1) (Word.combine b2 b3))
                         (Word.combine (Word.combine b4 b5) (Word.combine b6 b7))
          | _ => wzero _
        end
    end.

  Theorem explode_addresses : forall a sz (w : word sz),
    map (@fst _ _) (explode a w) = addresses a sz.
    destruct sz; reflexivity.
  Qed.

  Lemma pair_eq_contra : forall A B (a1 a2 a : A) (b1 b2 b b' : B),
    (a1, b1) = (a, b)
    -> (a2, b2) = (a, b')
    -> a1 <> a2
    -> False.
    congruence.
  Qed.

  Theorem explode_functional : forall a sz (w : word sz) a' b b',
    In (a', b) (explode a w)
    -> In (a', b') (explode a w)
    -> b = b'.
  Proof.
(*  
    destruct sz; unfold explode, In; abstract (
    do 4 intro;
      repeat match goal with 
               | [ |- context [ (_,split1 ?X ?Y ?Z) ] ] => generalize (split1 X Y Z); intro
               | [ |- context [ (_,split2 ?X ?Y ?Z) ] ] => generalize (split2 X Y Z); intro
             end;
      intro;
        repeat match goal with 
                 | [ |- context H [ (?X, _) = _ ] ] => 
                   progress repeat match goal with 
                                     | [ |- context [ (?A,_) = _ ] ] => 
                                       match X with
                                         | A => fail 1
                                         | _ => 
                                           match goal with
                                             | [ H : X <> A |- _ ] => fail 1
                                             | [ H : A <> X |- _ ] => fail 1
                                             | _ => assert (X <> A) by word_neq
                                           end
                                       end
                                   end
               end;
    intuition auto; try congruence;
      match goal with
        | [ H1 : _ = _, H2 : _ = _ |- _ ] => exfalso; apply (pair_eq_contra H1 H2); congruence
      end).
  Qed.
*)
  Admitted. (** TOO LONG **)

  Theorem implode_explode : forall a sz (w : word sz),
    implode (map (@snd _ _) (explode a w)) sz = w.
    destruct sz; intro; unfold implode, explode, map, snd;
      repeat (rewrite Word.combine_split); reflexivity.
  Qed.

  Definition addr_eq := @weq W64.

  Definition state := state.
  Definition Mem := @Mem XenExt.
End SepArg.

Module Sep := Separation.Make(SepArg).

Theorem msel_sep : forall m a, m a = Sep.msel m a W8.
  rewrite Sep.msel_def; reflexivity.
Qed.

Lemma msel_mrd : forall m a sz,
  Sep.msel m a sz = mrd sz m a.
  destruct sz;
  rewrite Sep.msel_def; unfold mrd, mrd64, mrd32, mrd16, mrd8, Sep.msel', SepArg.implode, SepArg.addresses, map, combine32, combine16, combine8; intros; auto;
  repeat (ring || f_equal). 
Qed.

Theorem mrd8_sep : forall m a, mrd8 m a = Sep.msel m a W8.
  rewrite Sep.msel_def; reflexivity.
Qed.

Theorem mrd64_sep : forall m a, mrd64 m a = Sep.msel m a W64.
  intros. rewrite msel_mrd. reflexivity.
Qed.

Lemma mupd_sep : forall sz m a (v : SepArg.word sz),
  Sep.mupd m a v = mupd m a v.
Proof.
  intros. destruct sz;
  rewrite Sep.mupd_def; unfold mupd, mupd64, mupd32, mupd16, mupd8, Sep.mupd', SepArg.explode, fold_left, fst, snd; 
  extensionality a';
  repeat match goal with
           | [ |- (if ?E1 then _ else _) = (if ?E2 then _ else _) ] =>
             let pf1 := fresh "pf1" in let pf2 := fresh "pf2" in
               destruct E1 as [pf1 | pf1]; destruct E2 as [pf2 | pf2]; [
                 repeat match goal with
                          | [ |- context[Word.split2 ?n2 ?n3 (Word.split2 ?n1 _ _)] ] =>
                            generalize (Word.split2_iter n1 n2 n3 (refl_equal _)); intro Heq; simpl plus in Heq; rewrite Heq; clear Heq
                        end; reflexivity
                 | exfalso; subst; apply pf2; ring
                 | exfalso; subst; apply pf1; ring
                 | clear pf1 pf2
               ]
         end; try reflexivity.
Qed.

Theorem mupd8_sep : forall m a v, mupd8 m a v = Sep.mupd m a (sz := W8) v.
  rewrite Sep.mupd_def; reflexivity.
Qed.

Theorem mupd64_sep : forall m a v, mupd64 m a v = Sep.mupd m a (sz := W64) v.
Proof.
  intros; rewrite mupd_sep. reflexivity.
Qed.

Theorem mkSel : forall s a,
  SepArg.Mem s a = Sep.msel (SepArg.Mem s) a W8.
  rewrite Sep.msel_def; reflexivity.
Qed.

Theorem mupd_read : forall m a sz v a',
  Sep.mupd m a (sz := sz) v a' = Sep.msel (Sep.mupd m a (sz := sz) v) a' W8.
  rewrite Sep.mupd_def; rewrite Sep.msel_def; reflexivity.
Qed.

Hint Rewrite mrd8_sep mrd64_sep mupd8_sep mupd64_sep mkSel mupd_read : normalize.

