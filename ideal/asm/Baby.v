Require Import Ideal.


(** Swapping memory values *)

Definition swap := bmodule {{
  bfunction "swap" [st ~> Ex fr, Ex a, Ex b, ![ st#R0 ==> a * st#R1 ==> b * ![fr] ] st
    /\ st#Rret @@ (st' ~> ![ st#R1 ==> a * st#R0 ==> b * ![fr] ] st') ] {
    R2 <- $[R0];;
    $[R0] <- $[R1];;
    $[R1] <- R2;;
    Goto Rret
  }
}}.

Theorem swapOk : moduleOk swap.
  structured; sep.
Qed.


(** Basic list example *)

Module Type LINKED_LIST.
  Parameter llist : list nat -> nat -> sprop.

  Axiom llist_empty_fwd : forall ls hd, hd = 0
    -> llist ls hd ===> [< ls = nil >].
  Axiom llist_empty_bwd : forall ls hd, hd = 0
    -> [< ls = nil >] ===> llist ls hd.

  Axiom llist_nonempty_fwd : forall ls hd, hd <> 0
    -> llist ls hd ===> Ex x, Ex ls', Ex p, [< ls = x :: ls' /\ hd <> 0 >] * hd ==> x * (hd+1) ==> p * !{llist ls' p}.
  Axiom llist_nonempty_bwd : forall ls hd, hd <> 0
    -> (Ex x, Ex ls', Ex p, [< ls = x :: ls' /\ hd <> 0 >] * hd ==> x * (hd+1) ==> p * !{llist ls' p}) ===> llist ls hd.
End LINKED_LIST.

Module LinkedList : LINKED_LIST.
  Open Scope Sep_scope.

  Fixpoint llist (ls : list nat) (hd : nat) : sprop :=
    match ls with
      | nil => [< hd = 0 >]
      | x :: ls' => Ex p, [< hd <> 0 >] * hd ==> x * (hd+1) ==> p * !{llist ls' p}
    end.

  Theorem llist_empty_fwd : forall ls hd, hd = 0
    -> llist ls hd ===> [< ls = nil >].
    destruct ls; sepLemma.
  Qed.

  Theorem llist_empty_bwd : forall ls hd, hd = 0
    -> [< ls = nil >] ===> llist ls hd.
    sepLemma.
  Qed.

  Theorem llist_nonempty_fwd : forall ls hd, hd <> 0
    -> llist ls hd ===> Ex x, Ex ls', Ex p, [< ls = x :: ls' /\ hd <> 0 >] * hd ==> x * (hd+1) ==> p * !{llist ls' p}.
    destruct ls; sepLemma.
  Qed.

  Theorem llist_nonempty_bwd : forall ls hd, hd <> 0
    -> (Ex x, Ex ls', Ex p, [< ls = x :: ls' /\ hd <> 0 >] * hd ==> x * (hd+1) ==> p * !{llist ls' p}) ===> llist ls hd.
    sepLemma.
  Qed.
End LinkedList.

Import LinkedList.

Definition lincS : state -> PropX pc state := st ~> Ex fr, Ex ls, ![ !{llist ls st#R0} * ![fr] ] st
  /\ st#Rret @@ (st' ~> ![ !{llist (map S ls) st#R0} * ![fr] ] st').

Definition linkedList := bmodule {{
  bfunction "linc" [lincS] {
    [lincS]
    While (R0 != 0) {
      Use [llist_nonempty_fwd];;
      Use [llist_nonempty_bwd];;

      $[R0] <- $[R0] + 1;;
      R0 <- $[R0+1]
    };;

    Use [llist_empty_fwd];;
    Use [llist_empty_bwd];;

    Goto Rret
  }
}}.

Theorem linkedListOk : moduleOk linkedList.
  structured; sep.
Qed.


(** An assertion *)

Definition assertTest := bmodule {{
  bfunction "assertTest" [st ~> [< st#R0 > 2 >] /\ Ex fr, ![ ![fr] ] st
    /\ st#Rret @@ (st' ~> [< st'#R0 > 5 >] /\ ![ ![fr] ] st') ] {
    R0 <- R0 + 1;;
    Assert [st ~> [< st#R0 > 3 >] /\ Ex fr, ![ ![fr] ] st
      /\ st#Rret @@ (st' ~> [< st'#R0 > 5 >] /\ ![ ![fr] ] st') ];;
    R0 <- R0 + 2;;
    Goto Rret
  }
}}.

Theorem assertTestOk : moduleOk assertTest.
  structured; sep; omega.
Qed.
