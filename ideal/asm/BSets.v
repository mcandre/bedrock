Require Import Arith FunctionalExtensionality.

Require Import Ideal Malloc.


Definition set := nat -> bool.
Definition empty : set := fun _ => false.
Definition add (s : set) (n : nat) : set := fun n' => if eq_nat_dec n' n then true else s n'.
Definition del (s : set) (n : nat) : set := fun n' => if eq_nat_dec n' n then false else s n'.
Definition all (s : set) (f : nat -> Prop) := forall x, s x = true -> f x.

Notation "s -<- n" := (fun n' => if le_gt_dec n n' then false else s n') (at level 50, left associativity).
Notation "s ->- n" := (fun n' => if le_gt_dec n' n then false else s n') (at level 50, left associativity).

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
         end; congruence || (elimtype False; omega) || omega.

Theorem add_idem : forall s x, s x = true -> add s x = s.
  sets.
Qed.

Theorem add_keep : forall s x x', s x = true -> add s x' x = true.
  sets.
Qed.

Theorem add_lt : forall x y s,
  x < y
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
  destruct (le_gt_dec n x); auto.
  destruct (le_gt_dec x n); auto.
  replace x with n; auto.
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
    repeat match goal with
             | [ |- context[if ?E then _ else _] ] => destruct E
           end; destruct (s a); intuition; elimtype False; omega.
Qed.

Theorem del_left' : forall s x y,
  x > y
  -> all (s -<- x) (fun x' => y >= x')
  -> del s x ->- y = s ->- x.
  intros ? ? ? ? H; extensionality a; generalize (H a); unfold del; simpl;
    repeat match goal with
             | [ |- context[if ?E then _ else _] ] => destruct E
           end; destruct (s a); intuition; try (elimtype False; omega).
Qed.

Theorem get_greater1 : forall x y b,
  (if le_gt_dec x y then false else b) = true
  -> x > y.
  intros; destruct (le_gt_dec x y); discriminate || auto.
Qed.

Theorem get_greater2 : forall x y b,
  (if le_gt_dec x y then false else b) = true
  -> b = true.
  intros; destruct (le_gt_dec x y); discriminate || auto.
Qed.

Theorem mustBeIn : forall n (s : set) x,
  n = (if s x then 1 else 0)
  -> n <> 0
  -> s x = true.
  sets.
Qed.

Hint Immediate get_greater1 get_greater2.

Hint Rewrite add_idem using solve [ eapply mustBeIn; eauto ] : InSep.


Section specs.
  Variable adt : set -> nat -> sprop.

  Definition constructorS : state -> PropX pc state := st ~> Ex fr, Ex n, [< n >= 1 >]
    /\ ![ !{mallocHeap 0} * !{allocated st#Rsp n} * ![fr] ] st
    /\ st#Rret @@ (st' ~> [< st'#Rsp = st#Rsp >]
      /\ ![ !{mallocHeap 0} * !{allocated st#Rsp n} * !{adt empty st'#R0} * ![fr] ] st').

  Definition containsS : state -> PropX pc state := st ~> Ex fr, Ex s, ![ !{adt s st#R0} * ![fr] ] st
    /\ st#Rret @@ (st' ~> [< st'#Rsp = st#Rsp /\ st'#R0 = if s st#R1 then 1 else 0 >]
      /\ ![ !{adt s st#R0} * ![fr] ] st').

  Definition addS : state -> PropX pc state := st ~> Ex fr, Ex n, Ex s, [< n >= 3 >]
    /\ ![ !{mallocHeap 0} * !{allocated st#Rsp n} * !{adt s st#R0} * ![fr] ] st
    /\ st#Rret @@ (st' ~> [< st'#Rsp = st#Rsp >]
      /\ ![ !{mallocHeap 0} * !{allocated st#Rsp n} * !{adt (add s st#R1) st#R0} * ![fr] ] st').

  Definition removeS : state -> PropX pc state := st ~> Ex fr, Ex n, Ex s, [< n >= 4 >]
    /\ ![ !{mallocHeap 0} * !{allocated st#Rsp n} * !{adt s st#R0} * ![fr] ] st
    /\ st#Rret @@ (st' ~> [< st'#Rsp = st#Rsp >]
      /\ ![ !{mallocHeap 0} * !{allocated st#Rsp n} * !{adt (del s st#R1) st#R0} * ![fr] ] st').
End specs.
