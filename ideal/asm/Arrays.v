Require Import Ideal Malloc.

Require Import Arith List.

Definition isVar A (n : A) := True.

Hint Extern 1 (isVar _ ?n) => match goal with
                                | [ x : _ |- _ ] => match x with
                                                      | n => constructor
                                                    end
                              end.

Local Open Scope Sep_scope.

Fixpoint array (ls : list nat) (a : nat) : sprop :=
  match ls with
    | nil => emp
    | x :: ls' => a ==> x * !{array ls' (a+1)}
  end.

Theorem length_nil : forall A, length (@nil A) = O.
  auto.
Qed.

Theorem length_cons : forall A (x : A) ls, length (x :: ls) = S (length ls).
  auto.
Qed.

Local Hint Resolve length_nil length_cons.

Lemma allocated_array' : forall len a, allocated a len ===> Ex ls, [< length ls = len >] * !{array ls a}.
  induction len; sepLemma; eauto; sepLemma.
Qed.

Theorem allocated_array : forall a len, allocated a len ===> Ex ls, [< length ls = len >] * !{array ls a}.
  intros; apply allocated_array'.
Qed.

Lemma array_allocated' : forall ls a, array ls a ===> !{allocated a (length ls)}.
  induction ls; sepLemma.
Qed.

Theorem array_allocated : forall a ls, array ls a ===> !{allocated a (length ls)}.
  intros; apply array_allocated'.
Qed.

Definition tl {A} (l:list A) :=
  match l with
    | nil => nil
    | a :: m => m
  end.

Theorem array_head_fwd : forall a ls, length ls > 0
  -> array ls a ===> a ==> hd 0 ls * !{array (tl ls) (a+1)}.
  destruct ls; simpl; intros; try (elimtype False; omega); sepLemma.
Qed.

Theorem array_head_bwd : forall a ls, length ls > 0
  -> (a ==> hd 0 ls * !{array (tl ls) (a+1)}) ===> array ls a.
  destruct ls; simpl; intros; try (elimtype False; omega); sepLemma.
Qed.

Theorem array_last_bwd : forall x ls a,
  !{array ls a} * (a+length ls) ==> x ===> array (ls ++ x :: nil) a.
  induction ls; sepLemma.
Qed.

Theorem array_last_fwd : forall ls a, length ls > 0
  -> array ls a ===> !{array (removelast ls) a} * (a+(length ls-1)) ==> last ls 0.
  induction ls; simpl; intros; try (elimtype False; omega).

  destruct (eq_nat_dec (length ls) 0).
  destruct ls; simpl in *; try discriminate; sepLemma.
  sepLemma; destruct ls; simpl in *; intuition sepLemma.
Qed.

Theorem array_last_fwd' : forall ls a, length ls > 0
  -> array ls a ===> !{array (removelast ls) a} * (a+(length ls-1)) ==> last ls 0.
  induction ls; simpl; intros; try (elimtype False; omega).

  destruct (le_gt_dec (length ls) 0).
  destruct ls; simpl in *; try (elimtype False; omega); sepLemma.
  sepLemma; destruct ls; simpl in *; try (elimtype False; omega); sepLemma.
Qed.

Theorem array_last_bwd' : forall ls a, length ls > 0
  -> !{array (removelast ls) a} * (a+(length ls-1)) ==> last ls 0 ===> array ls a.
  induction ls; simpl; intros; try (elimtype False; omega).

  destruct (le_gt_dec (length ls) 0).
  destruct ls; simpl in *; try (elimtype False; omega); sepLemma.
  sepLemma; destruct ls; simpl in *; try (elimtype False; omega); sepLemma.
Qed.

Theorem array_mid_fwd : forall n a ls, n < length ls
  -> array ls a ===> !{array (firstn n ls) a} * (a+n) ==> nth n ls 0 * !{array (skipn (n+1) ls) (a+n+1)}.
  induction n; destruct ls; simpl; intros; try (elimtype False; omega); sepLemma.
Qed.

Theorem array_mid_bwd : forall n a ls,
  [< n < length ls >] * !{array (firstn n ls) a} * (a+n) ==> nth n ls 0 * !{array (skipn (n+1) ls) (a+n+1)} ===> array ls a.
  induction n; destruct ls; sepLemma; omega || (elimtype False; omega).
Qed.

Theorem array_mid_bwd_upfront : forall n a ls, n < length ls
  -> !{array (firstn n ls) a} * (a+n) ==> nth n ls 0 * !{array (skipn (n+1) ls) (a+n+1)} ===> array ls a.
  induction n; destruct ls; sepLemma; omega || (elimtype False; omega).
Qed.

Theorem array_split_fwd : forall n a ls, n <= length ls
  -> array ls a ===> !{array (firstn n ls) a} * !{array (skipn n ls) (a+n)}.
  induction n; destruct ls; sepLemma.
Qed.

Theorem array_split_fwd_var : forall n a ls, n <= length ls
  -> isVar _ ls
  -> array ls a ===> !{array (firstn n ls) a} * !{array (skipn n ls) (a+n)}.
  intros; apply array_split_fwd; auto.
Qed.

Theorem array_split_bwd : forall n a ls, n <= length ls
  -> !{array (firstn n ls) a} * !{array (skipn n ls) (a+n)} ===> array ls a.
  induction n; destruct ls; sepLemma.
Qed.

Theorem array_nil_fwd : forall ls a, length ls = 0 -> array ls a ===> emp.
  destruct ls; sepLemma; elimtype False; omega.
Qed.

Theorem array_nil_bwd : forall ls a, length ls = 0 -> emp ===> array ls a.
  destruct ls; sepLemma; elimtype False; omega.
Qed.

Theorem allocated_combine : forall len' base len,
  len' <= len
  -> !{allocated base len'} * !{allocated (base + len') (len - len')}
  ===> allocated base len.
  induction len'; [ | intros ? ? H; apply S_le in H ]; sepLemma.
Qed.
