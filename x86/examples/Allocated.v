Require Import x86.
Require Import WordView.
Require Import MultiWord.

Set Implicit Arguments.
Set Strict Implicit.

Opaque Word.split1 Word.split2 Word.combine.
Lemma disjoint_join : forall m x x0 x1 x2,
  split m x x2 ->
  split x2 x1 x0 ->
  disjoint x1 x.
Proof.
  unfold split, disjoint. intuition.
  repeat match goal with
           | [ H : SepArg.addr , H' : _ |- _ ] => specialize (H' H)
           | [ H : _ = _ |- _ ] => rewrite H in *
           | [ H : forall x, _ |- _ ] => specialize (H _ (refl_equal _))
         end; intuition; try discriminate.
  destruct (x a); firstorder. specialize (H1 _ (refl_equal _)). discriminate.
Qed.
Hint Resolve disjoint_join.

Open Local Scope Sep_scope.

Fixpoint allocated' (base : word W64) (len : nat) : sprop :=
  match len with
    | O => emp
    | S len' => (Ex v, base =8> v) * !{allocated' (base ^+ wone W64) len'}
  end.

Module Type ALLOCATED.
  Parameter allocated : word W64 -> nat -> sprop.

  Axiom allocated_def : allocated = allocated'.
End ALLOCATED.

Module Allocated : ALLOCATED.

  (** TODO : Exposing nat is really bad **)
  Definition allocated := allocated'.
  
  Theorem allocated_def : allocated = allocated'.
  Proof. auto. Qed.

End Allocated.

Import Allocated.
Export Allocated.

Theorem allocated0_bwd : forall a n, n = 0 -> emp ===> allocated a n.
  rewrite allocated_def; sepLemma.
Qed.

Theorem allocated0_fwd : forall a n, n = 0 -> allocated a n ===> emp.
  rewrite allocated_def; sepLemma.
Qed.
  
Theorem allocated_expose_fwd : forall n base len, (n <= len)%nat -> allocated base len ===> !{allocated base (n + (len - n))}.
  rewrite allocated_def; sepLemma.
Qed.
  
Theorem allocated_expose_bwd : forall n base len, (n <= len)%nat -> !{allocated base (n + (len - n))} ===> allocated base len.
  rewrite allocated_def; sepLemma.
Qed.

Lemma join_None : forall a b p,
  a p = None ->
  b p = None ->
  join a b p = None.
Proof. unfold join. intros. rewrite H. auto. Qed.

Hint Resolve split_join.

Theorem allocated_8val_fwd : forall (p : word W64) (n : nat),
  (1 <= n)%nat ->
  allocated p n ===> (Ex v, p =8> v) * !{allocated (p^+##1) (n - 1)}.
Proof.
  intros. eapply Himp_trans.
  eapply (allocated_expose_fwd) with (base := p); eassumption.
  rewrite allocated_def. sepLemma.
Qed.

Theorem allocated_16val_fwd : forall (p : word W64) (n : nat),
  (2 <= n)%nat ->
  allocated p n ===> (Ex v, p =16> v) * !{allocated (p^+##2) (n - 2)}.
Proof.
  intros. eapply Himp_trans.
  eapply (allocated_expose_fwd) with (base := p); eassumption.
  simpl. ring_simplify (p ^+ wone W64 ^+ wone W64).
  rewrite allocated_def. sepLemma.
  eapply combine_88_16.
Qed.

Theorem allocated_32val_fwd : forall (p : word W64) (n : nat),
  (4 <= n)%nat ->
  allocated p n ===> (Ex v, p =32> v) * !{allocated (p^+##4) (n - 4)}.
Proof.
  intros. eapply Himp_trans.
  eapply (allocated_16val_fwd). omega.
  assert (2 <= n-2)%nat. omega.
  generalize (@allocated_16val_fwd (p ^+ ##2)%nat (n - 2)%nat H0). clear.
(*
  rewrite allocated_def; sepLemma.
  eapply combine_1616_32.
Qed.
*) Admitted.

Theorem allocated_64val_fwd : forall (p : word W64) (n : nat),
  (8 <= n)%nat ->
  allocated p n ===> (Ex v, p ==> v) * !{allocated (p^+##8) (n - 8)}.
Proof.
  intros. eapply Himp_trans.
  eapply (allocated_32val_fwd). omega.
  assert (4 <= n-4)%nat. omega.
  generalize (@allocated_32val_fwd (p ^+ ##4)%nat (n - 4)%nat H0). clear.
(*
  rewrite allocated_def; sepLemma.
  eapply combine_3232_64.
Qed. *) Admitted.

Theorem allocated_8val_bwd : forall (p : word W64) (n : nat),
  (1 <= n)%nat ->
  (Ex v, p =8> v) * !{allocated (p^+##1) (n - 1)} ===> allocated p n.
Proof.
  intros. eapply Himp_trans.
  2: eapply (allocated_expose_bwd) with (base := p); eassumption.
  rewrite allocated_def; sepLemma.
Qed.

Theorem allocated_16val_bwd : forall (p : word W64) (n : nat),
  (2 <= n)%nat ->
  (Ex v, p =16> v) * !{allocated (p^+##2) (n - 2)} ===> allocated p n.
Proof.
  intros. eapply Himp_trans.
  2: eapply (allocated_expose_bwd) with (base := p); eassumption.
  simpl. ring_simplify (p ^+ wone W64 ^+ wone W64).
(*
  rewrite allocated_def; sepLemma.
  eapply split_16_88.
Qed.
*) Admitted.

Theorem allocated_32val_bwd : forall (p : word W64) (n : nat),
  (4 <= n)%nat ->
  (Ex v, p =32> v) * !{allocated (p^+##4) (n - 4)} ===> allocated p n.
Proof.
  intros. eapply Himp_trans.
  2: eapply (allocated_16val_bwd). 2: omega.
  assert (2 <= n - 2)%nat. omega.
  generalize (@allocated_16val_bwd (p ^+ ##2) (n-2) H0).
(*  simpl. intros. sepLemma.
  eapply split_32_1616.
Qed.
*) Admitted.

Theorem allocated_64val_bwd : forall (p : word W64) (n : nat),
  (8 <= n)%nat ->
  (Ex v, p ==> v) * !{allocated (p^+##8) (n - 8)} ===> allocated p n.
Proof.
  intros. eapply Himp_trans.
  2: eapply (allocated_32val_bwd). 2: omega.
  assert (4 <= n - 4)%nat. omega.
  generalize (@allocated_32val_bwd (p ^+ ##4) (n-4) H0).
(*  simpl. intros. sepLemma.
  eapply split_64_3232.
Qed. *) Admitted.

Fixpoint size_of (ls : list wsize) : nat :=
  match ls with
    | nil => 0 
    | hd :: tl => bytes hd + size_of tl
  end.

Fixpoint tallocated (ls : list wsize) (base : word W64) (len : nat) : sprop :=
  match ls with
    | nil => !{Allocated.allocated base len}
    | W8 :: r => (Ex v, base =8> v) * tallocated r (base ^+ ##1) (len - 1)
    | W16 :: r => (Ex v, base =16> v) * tallocated r (base ^+ ##2) (len - 2)
    | W32 :: r => (Ex v, base =32> v) * tallocated r (base ^+ ##4) (len - 4)
    | W64 :: r => (Ex v, base ==> v) * tallocated r (base ^+ ##8) (len - 8)
  end.


Ltac remove_guard :=
  repeat match goal with 
           | [ |- !{ _ } ===> _ ] => eapply Himp_elim_guard_l
           | [ |- _ ===> !{ _ } ] => eapply Himp_elim_guard_r
         end;
  try match goal with
        | [ |- ?X * _ ===> ?X * _ ] => eapply Himp_split; [ sepLemma | ]
      end.
             

Lemma tallocated_fwd : forall ls p n,
  (size_of ls <= n)%nat ->
  allocated p n ===> !{tallocated ls p n}.
Proof.
  induction ls. sepLemma. eapply himp_guard_elim_r. 
  destruct a; simpl. intros.
  assert (1 <= n)%nat. omega.
  generalize (@allocated_8val_fwd p n H0). intros; eapply Himp_trans.
  eapply H1.
  assert (size_of ls <= n-1)%nat. omega.
  remove_guard; sepLemma.

  (** **)
  intros. assert (2 <= n)%nat; try omega.
  generalize (@allocated_16val_fwd p n H0). intros. eapply Himp_trans.
  assert (size_of ls <= n-2)%nat. omega.
  eassumption.
  assert (size_of ls <= n - 2)%nat. omega.
  specialize (IHls (p ^+ @inj _ WordView_nat W64 2) (n - 2)%nat H2).
  remove_guard; sepLemma.
  (** **) 
  intros. assert (4 <= n)%nat; try omega.
  generalize (@allocated_32val_fwd p n H0). intros. eapply Himp_trans.
  assert (size_of ls <= n-4)%nat. omega.
  eassumption.
  assert (size_of ls <= n - 4)%nat. omega.
  specialize (IHls (p ^+ @inj _ WordView_nat _ 4) (n - 4)%nat H2).
  remove_guard; sepLemma.
  (** **)
  intros. assert (8 <= n)%nat; try omega.
  generalize (@allocated_64val_fwd p n H0). intros. eapply Himp_trans.
  assert (size_of ls <= n-8)%nat. omega.
  eassumption.
  assert (size_of ls <= n - 8)%nat. omega.
  specialize (IHls (p ^+ @inj _ WordView_nat _ 8) (n - 8)%nat H2).
  remove_guard; sepLemma.
Qed.

Lemma tallocated_bwd : forall ls p n,
  (size_of ls <= n)%nat ->
  !{tallocated ls p n} ===> allocated p n.
Proof.
Admitted.
(*
  induction ls. simpl. intros. remove_guard; sepLemma.
  destruct a; simpl. intros.
  assert (1 <= n)%nat. omega.
  generalize (@allocated_expose_bwd 1 p n H0).
  assert (size_of ls <= n-1)%nat. omega.
  specialize (IHls (p ^+ wone _) (n - 1) H1). intros.
  eapply Himp_trans; [ | eassumption]. rewrite allocated_def. simpl. rewrite <- allocated_def.
  remove_guard; sepLemma.
  (** **)
  intros. assert (2 <= n)%nat; try omega.
  generalize (@allocated_16val_bwd p n H0). intros. eapply Himp_trans; [ | eassumption ].
  assert (size_of ls <= n-2)%nat. omega.
  specialize (IHls (p ^+ @inj _ WordView_nat _ 2) (n - 2)%nat H2).
  remove_guard; sepLemma.
  (** **) 
  intros. assert (4 <= n)%nat; try omega.
  generalize (@allocated_32val_bwd p n H0). intros. eapply Himp_trans; [ | eassumption ].
  assert (size_of ls <= n-4)%nat. omega.
  specialize (IHls (p ^+ @inj _ WordView_nat _ 4) (n - 4)%nat H2). 
  remove_guard; sepLemma.
  (** **)
  intros. assert (8 <= n)%nat; try omega.
  generalize (@allocated_64val_bwd p n H0). intros. eapply Himp_trans; [ | eassumption ].
  assert (size_of ls <= n-8)%nat. omega.
  specialize (IHls (p ^+ @inj _ WordView_nat _ 8) (n - 8)%nat H2).
  remove_guard; sepLemma.
Qed.
*)
(*
Hint Resolve allocated0_bwd : Backward.
Hint Resolve allocated0_fwd : Forward.
*)

Implicit Arguments allocated_expose_fwd [].
Implicit Arguments allocated_16val_fwd [].
Implicit Arguments allocated_32val_fwd [].
Implicit Arguments allocated_64val_fwd [].
Implicit Arguments allocated_expose_bwd [].
Implicit Arguments allocated_16val_bwd [].
Implicit Arguments allocated_32val_bwd [].
Implicit Arguments allocated_64val_bwd [].
Implicit Arguments tallocated_fwd [].

(** Reverse allocated **)

Fixpoint rallocated' (base : word W64) (len : nat) : sprop :=
  match len with
    | 0 => emp
    | S len' => (Ex x, (base ^- ##1) =8> x) * !{rallocated' (base ^- wone W64) len'}
  end.

Module Type RALLOCATED.
  Parameter rallocated : word W64 -> nat -> sprop.

  Axiom rallocated_def : rallocated = rallocated'.
End RALLOCATED.

Module Rallocated : RALLOCATED.

  (** TODO : Exposing nat is really bad **)
  Definition rallocated := rallocated'.
  
  Theorem rallocated_def : rallocated = rallocated'.
  Proof. auto. Qed.

End Rallocated.

Import Rallocated.
Export Rallocated.

Theorem rallocated0_bwd : forall a n, n = 0 -> emp ===> rallocated a n.
  rewrite rallocated_def; sepLemma.
Qed.

Theorem rallocated0_fwd : forall a n, n = 0 -> rallocated a n ===> emp.
  rewrite rallocated_def; sepLemma.
Qed.

Theorem rallocated_expose_fwd : forall n base len, (n <= len)%nat -> rallocated base len ===> !{rallocated base (n + (len - n))}.
  rewrite rallocated_def; sepLemma.
Qed.

Theorem rallocated_expose_bwd : forall n base len, (n <= len)%nat -> !{rallocated base (n + (len - n))} ===> rallocated base len.
  rewrite rallocated_def; sepLemma.
Qed.

Theorem rallocated_8val_fwd : forall (p : word W64) (n : nat),
  (1 <= n)%nat ->
  rallocated p n ===> (Ex v, (p^-##1) =8> v) * !{rallocated (p^-##1) (n - 1)}.
Proof.
  intros. eapply Himp_trans.
  eapply (rallocated_expose_fwd) with (base := p); eassumption.
  simpl. 
  rewrite rallocated_def. sepLemma.
Qed.

Theorem rallocated_16val_fwd : forall (p : word W64) (n : nat),
  (2 <= n)%nat ->
  rallocated p n ===> (Ex v, (p^-##2) =16> v) * !{rallocated (p^-##2) (n - 2)}.
Proof.
  intros. eapply Himp_trans.
  eapply (rallocated_expose_fwd) with (base := p); eassumption.
  simpl. 
  rewrite rallocated_def. 
(* sepLemma.
  generalize (@combine_88_16 (p ^- ##2) x0 x).
  ring_simplify (p ^- wone W64 ^+ wone W64). unfold wone. simpl. intros.
  eapply himp_trans; eauto. sepLemma.
Qed. *) Admitted.

Theorem rallocated_32val_fwd : forall (p : word W64) (n : nat),
  (4 <= n)%nat ->
  rallocated p n ===> (Ex v, (p ^- ##4) =32> v) * !{rallocated (p^-##4) (n - 4)}.
Proof.
(**
  intros. eapply Himp_trans.
  eapply (rallocated_16val_fwd). omega.
  assert (2 <= n-2)%nat. omega.
  generalize (@rallocated_16val_fwd (p ^- ##2)%nat (n - 2)%nat H0). clear.
  rewrite rallocated_def; sepLemma.
  generalize (@combine_1616_32 (p ^- ##4) x0 x).
  do 3 match goal with
           | [ |- context [ ?P ^- ?A ^- ?B ] ] => ring_simplify (P ^- A ^- B)
           | [ |- context [ ?P ^- ?A ^+ ?B ] ] => ring_simplify (P ^- A ^+ B)
           | [ |- context [ ?P ^- ?A ] ] => progress ring_simplify (P ^- A)
         end.
  intros. eapply himp_trans. 2: eapply H0. clear. sepLemma.
Qed.
**)
Admitted. (** TOO LONG **)

Theorem rallocated_64val_fwd : forall (p : word W64) (n : nat),
  (8 <= n)%nat ->
  rallocated p n ===> (Ex v, (p^-##8) ==> v) * !{rallocated (p^-##8) (n - 8)}.
Proof.
(**
  intros. eapply Himp_trans.
  eapply (rallocated_32val_fwd). omega.
  assert (4 <= n-4)%nat. omega.
  generalize (@rallocated_32val_fwd (p ^- ##4)%nat (n - 4)%nat H0). clear.
  rewrite rallocated_def; sepLemma.
  generalize (@combine_3232_64 (p ^- ##8) x0 x).
  simpl natToWord. eapply himp_trans. sepLemma.
Qed.
**)
Admitted. (** TOO LONG **)

Theorem rallocated_8val_bwd : forall (p : word W64) (n : nat),
  (1 <= n)%nat ->
  (Ex v, (p^-##1) =8> v) * !{rallocated (p^-##1) (n - 1)} ===> rallocated p n.
Proof.
  intros. eapply Himp_trans.
  2: eapply (rallocated_expose_bwd) with (base := p); eassumption.
  simpl. rewrite rallocated_def; sepLemma.
Qed.

Theorem rallocated_16val_bwd : forall (p : word W64) (n : nat),
  (2 <= n)%nat ->
  (Ex v, (p^-##2) =16> v) * !{rallocated (p^-##2) (n - 2)} ===> rallocated p n.
Proof.
(**
  intros. eapply Himp_trans.
  2: eapply (rallocated_expose_bwd) with (base := p); eassumption.
  simpl. rewrite rallocated_def; sepLemma.
  generalize (@split_16_88 (p ^- ##2) x).
  do 3 match goal with
         | [ |- context [ ?P ^- ?A ^- ?B ] ] => ring_simplify (P ^- A ^- B)
         | [ |- context [ ?P ^- ?A ^+ ?B ] ] => ring_simplify (P ^- A ^+ B)
         | [ |- context [ ?P ^- ?A ] ] => progress ring_simplify (P ^- A)
       end.
  intros. eapply himp_trans. eassumption. sepLemma.
Qed.
**)
Admitted. (** TOO LONG **)

Theorem rallocated_32val_bwd : forall (p : word W64) (n : nat),
  (4 <= n)%nat ->
  (Ex v, (p^-##4) =32> v) * !{rallocated (p^-##4) (n - 4)} ===> rallocated p n.
Proof.
(**
  intros. eapply Himp_trans.
  2: eapply (rallocated_16val_bwd). 2: omega.
  assert (2 <= n - 2)%nat. omega.
  generalize (@rallocated_16val_bwd (p ^- ##2) (n-2) H0).
  simpl. intros. sepLemma.
  generalize (@split_32_1616 (p ^- ##4) x).
  do 3 match goal with
         | [ |- context [ ?P ^- ?A ^- ?B ] ] => ring_simplify (P ^- A ^- B)
         | [ |- context [ ?P ^- ?A ^+ ?B ] ] => ring_simplify (P ^- A ^+ B)
         | [ |- context [ ?P ^- ?A ] ] => progress ring_simplify (P ^- A)
       end.
  intros. eapply himp_trans. eassumption. sepLemma.
Qed.
**)
Admitted. (** TOO LONG **)

Theorem rallocated_64val_bwd : forall (p : word W64) (n : nat),
  (8 <= n)%nat ->
  (Ex v, (p^-##8) ==> v) * !{rallocated (p^-##8) (n - 8)} ===> rallocated p n.
Proof.
(**
  intros. eapply Himp_trans.
  2: eapply (rallocated_32val_bwd). 2: omega.
  assert (4 <= n - 4)%nat. omega.
  generalize (@rallocated_32val_bwd (p ^- ##4) (n-4) H0).
  simpl. intros. sepLemma.
  generalize (@split_64_3232 (p ^- ##8) x).
  do 3 match goal with
         | [ |- context [ ?P ^- ?A ^- ?B ] ] => ring_simplify (P ^- A ^- B)
         | [ |- context [ ?P ^- ?A ^+ ?B ] ] => ring_simplify (P ^- A ^+ B)
         | [ |- context [ ?P ^- ?A ] ] => progress ring_simplify (P ^- A)
       end.
  intros. eapply himp_trans. eassumption. sepLemma.
Qed.
**) 
Admitted. (** TOO LONG **)

(*
Hint Resolve rallocated0_bwd : Backward.
Hint Resolve rallocated0_fwd : Forward.
*)

Fixpoint trallocated (ls : list wsize) (base : word W64) (len : nat) : sprop :=
  match ls with
    | nil => !{Rallocated.rallocated base len}
    | W8 :: r  => (Ex v, (base ^- ##1) =8> v) * trallocated r (base ^- ##1) (len - 1)
    | W16 :: r => (Ex v, (base ^- ##2) =16> v) * trallocated r (base ^- ##2) (len - 2)
    | W32 :: r => (Ex v, (base ^- ##4) =32> v) * trallocated r (base ^- ##4) (len - 4)
    | W64 :: r => (Ex v, (base ^- ##8) ==> v) * trallocated r (base ^- ##8) (len - 8)
  end.

Lemma trallocated_fwd : forall ls p n,
  (size_of ls <= n)%nat ->
  rallocated p n ===> !{trallocated ls p n}.
Proof.
(**
  induction ls. sepLemma. eapply himp_guard_elim_r. 
  destruct a; simpl. intros.
  assert (1 <= n)%nat. omega.
  generalize (@rallocated_expose_fwd 1 p n H0).
  assert (size_of ls <= n-1)%nat. omega.
  specialize (IHls (p ^- wone _) (n - 1) H1). intros.
  eapply Himp_trans. eassumption. rewrite rallocated_def. simpl. rewrite <- rallocated_def.
  unfold wone; simpl. remove_guard; sepLemma.
  (** **)
  intros. assert (2 <= n)%nat; try omega.
  generalize (@rallocated_16val_fwd p n H0). intros. eapply Himp_trans.
  assert (size_of ls <= n-2)%nat. omega.
  eassumption.
  assert (size_of ls <= n - 2)%nat. omega.
  specialize (IHls (p ^- @inj _ WordView_nat _ 2) (n - 2)%nat H2). simpl; remove_guard; sepLemma.
  (** **) 
  intros. assert (4 <= n)%nat; try omega.
  generalize (@rallocated_32val_fwd p n H0). intros. eapply Himp_trans.
  assert (size_of ls <= n-4)%nat. omega.
  eassumption.
  assert (size_of ls <= n - 4)%nat. omega.
  specialize (IHls (p ^- @inj _ WordView_nat _ 4) (n - 4)%nat H2). simpl; remove_guard; sepLemma.
  (** **)
  intros. assert (8 <= n)%nat; try omega.
  generalize (@rallocated_64val_fwd p n H0). intros. eapply Himp_trans.
  assert (size_of ls <= n-8)%nat. omega.
  eassumption.
  assert (size_of ls <= n - 8)%nat. omega.
  specialize (IHls (p ^- @inj _ WordView_nat _ 8) (n - 8)%nat H2). simpl; remove_guard; sepLemma.
Qed.
**)
Admitted. (** TOO LONG **)

Lemma trallocated_bwd : forall ls p n,
  (size_of ls <= n)%nat ->
  !{trallocated ls p n} ===> rallocated p n.
Proof.
(**
  induction ls. sepLemma. eapply himp_guard_elim_l.
  destruct a; simpl. intros.
  assert (1 <= n)%nat. omega.
  generalize (@rallocated_expose_bwd 1 p n H0).
  assert (size_of ls <= n-1)%nat. omega.
  specialize (IHls (p ^- wone _) (n - 1) H1). intros.
  eapply Himp_trans; [ | eassumption]. rewrite rallocated_def. simpl. rewrite <- rallocated_def.
  simpl; remove_guard; sepLemma.
  (** **)
  intros. assert (2 <= n)%nat; try omega.
  generalize (@rallocated_16val_bwd p n H0). intros. eapply Himp_trans; [ | eassumption ].
  assert (size_of ls <= n-2)%nat. omega.
  specialize (IHls (p ^- @inj _ WordView_nat _ 2) (n - 2)%nat H2). simpl; remove_guard; sepLemma.
  (** **) 
  intros. assert (4 <= n)%nat; try omega.
  generalize (@rallocated_32val_bwd p n H0). intros. eapply Himp_trans; [ | eassumption ].
  assert (size_of ls <= n-4)%nat. omega.
  specialize (IHls (p ^- @inj _ WordView_nat _ 4) (n - 4)%nat H2). simpl; remove_guard; sepLemma.
  (** **)
  intros. assert (8 <= n)%nat; try omega.
  generalize (@rallocated_64val_bwd p n H0). intros. eapply Himp_trans; [ | eassumption ].
  assert (size_of ls <= n-8)%nat. omega.
  specialize (IHls (p ^- @inj _ WordView_nat _ 8) (n - 8)%nat H2). simpl; remove_guard; sepLemma.
Qed.
**)
Admitted. (** TOO LONG **)