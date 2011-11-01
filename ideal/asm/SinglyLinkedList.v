Require Import Arith List.

Require Import Ideal Malloc BSets.


Module Type LLIST.
  Parameter llist : set -> nat -> sprop.
  Parameter llistOk : set -> list nat -> nat -> sprop.

  Axiom unfold_llist_fwd : forall s a, llist s a ===> Ex a', Ex ls, Ex junk, a ==> a' * (a+1) ==> junk * !{llistOk s ls a'}.
  Axiom unfold_llist_bwd : forall s a, (Ex a', Ex ls, Ex junk, a ==> a' * (a+1) ==> junk * !{llistOk s ls a'}) ===> llist s a.

  Axiom llist_empty_fwd : forall s ls a,
    a = 0
    -> llistOk s ls a ===> [< ls = nil /\ s = empty >].

  Axiom llist_empty_bwd : forall s ls a,
    a = 0
    -> [< ls = nil /\ s = empty >] ===> llistOk s ls a.

  Axiom llist_nonempty_fwd : forall a s ls,
    a <> 0
    -> llistOk s ls a ===> Ex x, Ex ls', Ex a', [< ls = x :: ls' /\ s x = true >] * a ==> x * (a+1) ==> a' * !{llistOk (del s x) ls' a'}.

  Axiom llist_nonempty_bwd : forall a s ls,
    a <> 0
    -> (Ex x, Ex ls', Ex a', [< ls = x :: ls' /\ s x = true >] * a ==> x * (a+1) ==> a' * !{llistOk (del s x) ls' a'}) ===> llistOk s ls a.
End LLIST.

Module LList : LLIST.
  Open Scope Sep_scope.

  Fixpoint llistOk (s : set) (ls : list nat) (a : nat) : sprop :=
    match ls with
      | nil => [< a = 0 /\ s = empty >]
      | x :: ls' => Ex a', [< a <> 0 /\ s x = true >] * a ==> x * (a+1) ==> a' * !{llistOk (del s x) ls' a'}
    end.

  Definition llist (s : set) (a : nat) : sprop := Ex a', Ex ls, Ex junk, a ==> a' * (a+1) ==> junk * !{llistOk s ls a'}.

  Theorem unfold_llist_fwd : forall s a, llist s a ===> Ex a', Ex ls, Ex junk, a ==> a' * (a+1) ==> junk * !{llistOk s ls a'}.
    sepLemma.
  Qed.

  Theorem unfold_llist_bwd : forall s a, (Ex a', Ex ls, Ex junk, a ==> a' * (a+1) ==> junk * !{llistOk s ls a'}) ===> llist s a.
    sepLemma.
  Qed.

  Theorem llist_empty_fwd : forall s ls a,
    a = 0
    -> llistOk s ls a ===> [< ls = nil /\ s = empty >].
    destruct ls; sepLemma.
  Qed.

  Theorem llist_empty_bwd : forall s ls a,
    a = 0
    -> [< ls = nil /\ s = empty >] ===> llistOk s ls a.
    sepLemma.
  Qed.

  Theorem llist_nonempty_fwd : forall a s ls,
    a <> 0
    -> llistOk s ls a ===> Ex x, Ex ls', Ex a', [< ls = x :: ls' /\ s x = true >] * a ==> x * (a+1) ==> a' * !{llistOk (del s x) ls' a'}.
    destruct ls; sepLemma.
  Qed.

  Theorem llist_nonempty_bwd : forall a s ls,
    a <> 0
    -> (Ex x, Ex ls', Ex a', [< ls = x :: ls' /\ s x = true >] * a ==> x * (a+1) ==> a' * !{llistOk (del s x) ls' a'}) ===> llistOk s ls a.
    sepLemma.
  Qed.
End LList.

Import LList.

Local Hint Immediate unfold_llist_fwd : Forward.
Local Hint Immediate unfold_llist_bwd : Backward.

Definition sll := bimport [[ "malloc" @ [mallocS], "free" @ [freeS] ]] bmodule {{
  bfunction "SinglyLinkedList" [constructorS llist] {
    $[Rsp] <- Rret;;

    R0 <- 0;;
    R1 <- 0;;

    Use [allocated_expose_fwd 1];;

    Call "malloc"
    [st ~> Ex n, Ex ret, Ex fr, [< n >= 1 >]
      /\ ![ !{mallocHeap 0} * st#Rsp ==> ret * !{allocated (st#Rsp+1) (n-1)} * !{allocated st#R0 2} * ![fr] ] st
      /\ ret @@ (st' ~> [< st'#Rsp = st#Rsp >]
        /\ ![ !{mallocHeap 0} * !{allocated st#Rsp n} * !{llist empty st'#R0} * ![fr] ] st')];;

    Use [allocated_expose_bwd 1];;
    Use [llist_empty_bwd];;

    $[R0] <- 0;;
    Goto $[Rsp]
  }

  with bfunction "contains" [containsS llist] {
    R0 <- $[R0];;

    [st ~> Ex fr, Ex s, Ex ls, ![ !{llistOk s ls st#R0} * ![fr] ] st
      /\ st#Rret @@ (st' ~> [< st'#Rsp = st#Rsp /\ st'#R0 = if s st#R1 then 1 else 0 >]
        /\ ![ !{llistOk s ls st#R0} * ![fr] ] st')]
    While (R0 != 0) {
      Use [llist_nonempty_fwd];;
      Use [llist_nonempty_bwd];;

      If ($[R0] == R1) {
        R0 <- 1;;
        Goto Rret
      } else {
        R0 <- $[R0+1]
      }
    };;

    Use [llist_empty_fwd];;
    Use [llist_empty_bwd];;

    R0 <- 0;;
    Goto Rret
  }

  with bfunction "add" [addS llist] {
    $[Rsp] <- Rret;;
    $[Rsp+1] <- R0;;
    $[Rsp+2] <- R1;;

    Use [allocated_expose_fwd 3];;
    Call "contains"
    [st ~> Ex fr, Ex n, Ex s : set, Ex ls, Ex ret, Ex base, Ex new, Ex a, [< n >= 3 /\ st#R0 = (if s new then 1 else 0) /\ n >= 0 >]
      /\ ![ !{mallocHeap 0} * st#Rsp ==> ret * (st#Rsp+1) ==> base * (st#Rsp+2) ==> new * !{allocated (st#Rsp+3) (n-3)}
        * base ==> a * !{llistOk s ls a} * ![fr] ] st
      /\ ret @@ (st' ~> [< st'#Rsp = st#Rsp >]
        /\ ![ !{mallocHeap 0} * !{allocated st#Rsp n} * Ex ls', Ex a', base ==> a' * !{llistOk (add s new) ls' a'} * ![fr] ] st')];;

    If (R0 == 0) {
      R1 <- 0;;
      Call "malloc"
      [st ~> Ex fr, Ex n, Ex s, Ex ls, Ex ret, Ex base, Ex new, Ex a, [< n >= 3 /\ s new = false /\ st#R0 <> 0 >]
        /\ ![ !{mallocHeap 0} * st#Rsp ==> ret * (st#Rsp+1) ==> base * (st#Rsp+2) ==> new * !{allocated (st#Rsp+3) (n-3)}
          * base ==> a * !{llistOk s ls a} * !{allocated st#R0 2} * ![fr] ] st
        /\ ret @@ (st' ~> [< st'#Rsp = st#Rsp >]
          /\ ![ !{mallocHeap 0} * !{allocated st#Rsp n} * Ex ls', Ex a', base ==> a' * !{llistOk (add s new) ls' a'} * ![fr] ] st')];;

      $[R0] <- $[Rsp+2];;
      R1 <- $[Rsp+1];;
      $[R0+1] <- $[R1];;
      $[R1] <- R0;;

      Use [llist_nonempty_bwd]
    } else {
      Skip
    };;

    Use [allocated_expose_bwd 3];;
    Goto $[Rsp]
  }

  with bfunction "remove" [removeS llist] {
    R2 <- R0;;
    R0 <- $[R0];;

    [st ~> Ex fr, Ex s, Ex ls, ![ !{mallocHeap 0} * st#R2 ==> st#R0 * !{llistOk s ls st#R0} * ![fr] ] st
      /\ st#Rret @@ (st' ~> [< st'#Rsp = st#Rsp >]
        /\ ![ !{mallocHeap 0} * Ex a, st#R2 ==> a * Ex ls', !{llistOk (del s st#R1) ls' a} * ![fr] ] st')]
    While (R0 != 0) {
      Use [llist_nonempty_fwd];;

      If ($[R0] == R1) {
        $[R2] <- $[R0+1];;

        R1 <- R0;;
        R0 <- 0;;
        R2 <- 0;;
        Goto "free"
      } else {
        Use [llist_nonempty_bwd];;

        R2 <- R0+1;;
        R0 <- $[R2]
      }
    };;

    Use [llist_empty_fwd];;
    Use [llist_empty_bwd];;

    Goto Rret
  }
}}.

Ltac finisher := auto;
  match goal with
    | [ |- _ ---> _ ] => rewrite del_del; apply himp_refl
    | _ => sets
  end.

Theorem sllOk : moduleOk sll.
  structured; abstract (sep; finisher).
Qed.
