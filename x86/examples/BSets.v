Require Import Arith FunctionalExtensionality.

Require Import x86.
Require Import Allocated.
Require Import WordView.
Require Import Null.

Set Implicit Arguments.
Set Strict Implicit.


Definition set := word W64 -> bool.
Definition empty : set := fun _ => false.
Definition add (s : set) (n : word W64) : set := fun n' => if weq n' n then true else s n'.
Definition del (s : set) (n : word W64) : set := fun n' => if weq n' n then false else s n'.
Definition all (s : set) (f : word W64 -> Prop) := forall x, s x = true -> f x.

Notation "s -<- n" := (fun n' => if wlt_dec n' n then s n' else false) (at level 50, left associativity).
Notation "s ->- n" := (fun n' => if wlt_dec n n' then s n' else false) (at level 50, left associativity).

Ltac setsIf E := match E with
                   | context[if _ then _ else _] => fail 1
                   | _ => let Heq := fresh "Heq" in
                     case_eq E; ((intros ? Heq; try rewrite Heq in *) || (intro Heq; try rewrite Heq in *))
                 end.

Ltac sets := unfold empty, add, del, all in *; intros; try subst;
  repeat match goal with
           | [ |- _ = _ ] => let x := fresh "x" in extensionality x
           | [ |- context[if ?E then _ else _] ] => setsIf E
           | [ _ : context[if ?E then _ else _] |- _ ] => setsIf E
         end; congruence || (exfalso; omega)
  || (eauto with worder) || (try solve [ exfalso; eauto with worder ]).

Lemma CompOpp_neq : forall a b,
  a <> b -> CompOpp a <> CompOpp b.
Proof.
  destruct a; destruct b; simpl; congruence.
Qed.
Lemma le_le_eq : forall sz (a b : word sz),
  a <= b -> b <= a -> a = b.
Proof.
  unfold wlt, BinNat.Nlt. intros.
  eapply wordToN_inj. eapply BinNat.Ncompare_eq_correct.
  apply CompOpp_neq in H.
  rewrite BinNat.Ncompare_antisym in H.
  destruct (BinNat.Ncompare (wordToN a) (wordToN b)); simpl in *; auto; congruence.
Qed.
Hint Resolve le_le_eq : worder.


Theorem add_idem : forall s x, s x = true -> add s x = s.
  sets.
Qed.

Theorem add_keep : forall s x x', s x = true -> add s x' x = true.
  sets.
Qed.

Theorem add_lt : forall x y s,
  wlt x y
  -> add (s -<- y) x = add s x -<- y.
  sets.
Qed.

Theorem add_gt : forall x y s,
  x > y
  -> add (s ->- y) x = add s x ->- y.
  sets.
Qed.

Theorem del_lt : forall x y s,
  del (s -<- y) x = del s x -<- y.
  sets.
Qed.

Theorem del_gt : forall x y s,
  del (s ->- y) x = del s x ->- y.
  sets.
Qed.

Lemma lt_not_eq : forall sz (a b : word sz),
  a < b -> a <> b.
Proof.
  intros. intro. subst. unfold wlt, BinNat.Nlt in H.
  rewrite BinNat.Ncompare_refl in H. congruence.
Qed.
Lemma lt_not_eq' : forall sz (a b : word sz),
  a < b -> a = b -> False.
Proof.
  intros; eapply lt_not_eq; eauto.
Qed.
Lemma lt_trans : forall sz (a b c : word sz),
  a < b -> b < c -> a < c.
Admitted.
Hint Resolve lt_not_eq lt_not_eq' lt_trans : worder.

Theorem drop_add_lt : forall x y s,
  x > y
  -> add s x -<- y = s -<- y.
  sets.
Qed.

Theorem drop_add_gt : forall x y s,
  x < y
  -> add s x ->- y = s ->- y.
  sets.
Qed.

Theorem drop_del_lt : forall x y s,
  x > y
  -> del s x -<- y = s -<- y.
  sets.
Qed.

Theorem drop_del_gt : forall x y s,
  x < y
  -> del s x ->- y = s ->- y.
  sets.
Qed.

Hint Rewrite add_idem add_keep using assumption : InSep.
Hint Rewrite add_lt add_gt del_lt del_gt drop_add_lt drop_add_gt drop_del_lt drop_del_gt using omega : InSep.

Theorem empty_contra : forall x s,
  s = empty
  -> s x = true
  -> False.
  sets.
Qed.

Hint Immediate empty_contra.

Theorem all_split : forall s P n,
  all (s -<- n) P
  -> P n
  -> all (s ->- n) P
  -> all s P.
  unfold all; intros.
  specialize (H x).
  specialize (H1 x).
  destruct (wlt_dec n x); auto.
  destruct (wlt_dec x n); auto.
  replace x with n; auto with worder.
Qed.

Theorem add_del : forall s x, s x = false
  -> del (add s x) x = s.
  sets.
Qed.

Hint Rewrite add_del using assumption : InSep.

Theorem del_del : forall s x y, del (del s x) y = del (del s y) x.
  sets.
Qed.

Theorem del_base_lt : forall s x,
  s ->- x = empty
  -> s -<- x = del s x.
  intros ? ? H; extensionality a; generalize (f_equal (fun f => f a) H); sets.
Qed.

Theorem del_base_gt : forall s x,
  s -<- x = empty
  -> s ->- x = del s x.
  intros ? ? H; extensionality a; generalize (f_equal (fun f => f a) H); sets.
Qed.

Hint Rewrite del_base_lt del_base_gt using congruence : InSep.

Theorem del_left : forall s x y,
  y > x
  -> s x = true
  -> all (s -<- y) (fun x' => x >= x')
  -> del s x -<- y = del s y -<- x.
  intros ? ? ? ? ? H; extensionality a; specialize (H a); simpl in H; unfold del;
    simpl in *;
    repeat match goal with
             | [ |- context[if ?E then _ else _] ] => destruct E
           end; destruct (s a); intuition; exfalso; (eauto with worder).
Qed.

Theorem del_left' : forall s x y,
  x > y
  -> all (s -<- x) (fun x' => y >= x')
  -> del s x ->- y = s ->- x.
  intros ? ? ? ? H; extensionality a; generalize (H a); unfold del; simpl in *;
    repeat match goal with
             | [ |- context[if ?E then _ else _] ] => destruct E
           end; destruct (s a); intuition.
  exfalso; eauto with worder.
  exfalso. eapply n0. eauto with worder.
Qed.

Theorem get_greater1 : forall sz x (y : word sz) b,
  (if wlt_dec y x then b else false) = true
  -> x > y.
  intros; destruct (wlt_dec y x); discriminate || auto.
Qed.

Theorem get_greater2 : forall sz x (y : word sz) b,
  (if wlt_dec y x then b else false) = true
  -> b = true.
  intros; destruct (wlt_dec y x); discriminate || auto.
Qed.

Theorem mustBeIn : forall n (s : set) x,
  n = (if s x then 1 else 0)
  -> n <> 0
  -> s x = true.
  sets.
Qed.

Hint Immediate get_greater1 get_greater2.

Hint Rewrite add_idem using solve [ eapply mustBeIn; eauto ] : InSep.

Require Import Malloc.

Section specs.
  Variable adt : set -> SepArg.addr -> sprop.

  (** NOTE: Return address in RBP **)

  Definition constructorS : state -> PropX pc state := st ~> Ex fr, Ex n, [< n >= 8 >]
    /\ ![ !{mallocHeap NULL} * !{rallocated st#RSP n} * ![fr] ] st
    /\ st#RBP @@ (st' ~> [< st'#RSP = st#RSP >]
      /\ ![ !{mallocHeap NULL} * !{rallocated st#RSP n} * !{if weq st'#RAX NULL then emp else adt empty st'#RAX} * ![fr] ] st').

  Definition containsS : state -> PropX pc state := st ~> Ex fr, Ex s, ![ !{adt s st#RAX} * ![fr] ] st
    /\ st#RBP @@ (st' ~> [< st'#RSP = st#RSP /\ st'#RAX = if s st#RBX then wone _ else wzero _ >]
      /\ ![ !{adt s st#RAX} * ![fr] ] st').

  Definition addS : state -> PropX pc state := st ~> Ex fr, Ex n, Ex s, [< n >= 24 >]
    /\ ![ !{mallocHeap (##0)} * !{rallocated st#RSP n} * !{adt s st#RAX} * ![fr] ] st
    /\ st#RBP @@ (st' ~> [< st'#RSP = st#RSP >]
      /\ ![ !{mallocHeap (##0)} * !{rallocated st#RSP n} * !{if weq st'#RAX NULL then adt s st#RAX else adt (add s st#RBX) st#RAX} * ![fr] ] st').

  Definition removeS : state -> PropX pc state := st ~> Ex fr, Ex n, Ex s, [< n >= 4 >]
    /\ ![ !{mallocHeap (##0)} * !{rallocated st#RSP n} * !{adt s st#RAX} * ![fr] ] st
    /\ st#RBP @@ (st' ~> [< st'#RSP = st#RSP >]
      /\ ![ !{mallocHeap (##0)} * !{rallocated st#RSP n} * !{adt (del s st#RBX) st#RAX} * ![fr] ] st').
End specs.
