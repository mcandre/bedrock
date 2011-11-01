Require Import Arith.

Require Import Ideal Malloc.


Module Type LLIST.
  Parameter llist : list nat ->  nat -> sprop.

  Axiom llist_empty_fwd : forall ls a,
    a = 0
    -> llist ls a ===> [< ls = nil >].

  Axiom llist_nonempty_fwd : forall ls a,
    a <> 0
    -> llist ls a ===> Ex x, Ex ls', Ex a', [< ls = x :: ls' /\ a <> 0 >] * a ==> x * (a+1) ==> a' * !{llist ls' a'}.

  Axiom llist_nonempty_bwd : forall ls a,
    a <> 0
    -> (Ex x, Ex ls', Ex a', [< ls = x :: ls' /\ a <> 0 >] * a ==> x * (a+1) ==> a' * !{llist ls' a'}) ===> llist ls a.
End LLIST.

Module LList : LLIST.
  Open Scope Sep_scope.

  Fixpoint llist (ls : list nat) (a : nat) : sprop :=
    match ls with
      | nil => [< a = O >]
      | x :: ls' => Ex a', [< a <> 0 >] * a ==> x * (a+1) ==> a' * !{llist ls' a'}
    end.

  Theorem llist_empty_fwd : forall ls a,
    a = 0
    -> llist ls a ===> [< ls = nil >].
    destruct ls; sepLemma.
  Qed.

  Theorem llist_nonempty_fwd : forall ls a,
    a <> 0
    -> llist ls a ===> Ex x, Ex ls', Ex a', [< ls = x :: ls' /\ a <> 0 >] * a ==> x * (a+1) ==> a' * !{llist ls' a'}.
    destruct ls; sepLemma.
  Qed.

  Theorem llist_nonempty_bwd : forall ls a,
    a <> 0
    -> (Ex x, Ex ls', Ex a', [< ls = x :: ls' /\ a <> 0 >] * a ==> x * (a+1) ==> a' * !{llist ls' a'}) ===> llist ls a.
    sepLemma.
  Qed.
End LList.

Import LList.

Definition appendS : state -> PropX pc state := st ~> Ex fr, Ex ss, Ex ls1, Ex ls2, Ex ret, Ex env, [< ss >= 3 /\ st#Rret <> 0 >]
  /\ ![ !{mallocHeap 0} * !{allocated st#Rsp ss}
    * !{llist ls1 st#R0} * !{llist ls2 st#R1}
    * st#Rret ==> ret * (st#Rret+1) ==> env * ![fr] ] st
  /\ ret @@ (st' ~> [< st'#R0 = env /\ st'#Rsp = st#Rsp >]
    /\ ![ !{mallocHeap 0} * !{allocated st#Rsp ss}
      * !{llist (ls1 ++ ls2) st'#R1} * ![fr] ] st').

Local Open Scope list_scope.

Definition appendCPS := bimport [[ "malloc" @ [mallocS], "free" @ [freeS] ]]
  bmodule {{
    bfunction "k" [st ~> Ex fr, Ex ss, Ex h, Ex p, Ex k, Ex ret, Ex env,
      [< ss >= 3 /\ st#R0 <> 0 /\ h <> 0 /\ k <> 0 >]
      /\ ![ !{mallocHeap 0} * !{allocated st#Rsp ss}
        * st#R0 ==> h * (st#R0+1) ==> k * (h+1) ==> p * k ==> ret * (k+1) ==> env * ![fr] ] st
      /\ ret @@ (st' ~> [< st'#R0 = env /\ st'#R1 = h /\ st'#Rsp = st#Rsp >]
        /\ ![ !{mallocHeap 0} * !{allocated st#Rsp ss} * (h+1) ==> st#R1 * ![fr] ] st')] {
      (* Save the function arguments on the stack. *)
      $[Rsp] <- $[R0+1];;
      $[Rsp+1] <- $[R0];;
      $[Rsp+2] <- R1;;
      (* Free our own environment, now that we've saved its contents. *)
      R1 <- R0;;
      R0 <- 0;;
      R2 <- 0;;

      Use [allocated_expose_fwd 3];;

      Call "free"
      [st ~> Ex fr, Ex ss, Ex h, Ex h', Ex p, Ex k, Ex ret, Ex env, [< ss >= 3 /\ h <> 0 /\ k <> 0 >]
        /\ ![ !{mallocHeap 0} * st#Rsp ==> k * (st#Rsp+1) ==> h * (st#Rsp+2) ==> h' * !{allocated (st#Rsp+3) (ss-3)}
          * (h+1) ==> p * k ==> ret * (k+1) ==> env * ![fr] ] st
        /\ ret @@ (st' ~> [< st'#R0 = env /\ st'#R1 = h /\ st'#Rsp = st#Rsp >]
          /\ ![ !{mallocHeap 0} * !{allocated st#Rsp ss} * (h+1) ==> h' * ![fr] ] st')];;
      (* Redirect the tail pointer of the new list head. *)
      R0 <- $[Rsp+1];;
      $[R0+1] <- $[Rsp+2];;
      (* Extract the contents of the closure, then free it. *)
      R1 <- $[Rsp];;
      $[Rsp+2] <- $[R1+1];;
      $[Rsp] <- $[R1];;
      R0 <- 0;;
      R2 <- 0;;

      Call "free"
      [st ~> Ex fr, Ex ss, Ex h, Ex h', Ex ret, Ex env, [< ss >= 3 /\ h <> 0 >]
        /\ ![ !{mallocHeap 0} * st#Rsp ==> ret * (st#Rsp+1) ==> h * (st#Rsp+2) ==> env * !{allocated (st#Rsp+3) (ss-3)}
          * (h+1) ==> h' * ![fr] ] st
        /\ ret @@ (st' ~> [< st'#R0 = env /\ st'#R1 = h /\ st'#Rsp = st#Rsp >]
          /\ ![ !{mallocHeap 0} * !{allocated st#Rsp ss} * (h+1) ==> h' * ![fr] ] st')];;
      (* Call the closure's code pointer. *)
      R0 <- $[Rsp+2];;
      R1 <- $[Rsp+1];;

      Use [allocated_expose_bwd 3];;

      Goto $[Rsp]
    }
    with bfunction "append" [appendS] {
      (* Save the function arguments on the stack. *)
      $[Rsp] <- Rret;;
      $[Rsp+1] <- R0;;
      $[Rsp+2] <- R1;;
      
      If ($[Rsp+1] == 0) {
        (* Empty list.  Extract the closure contents, then free it. *)
        R1 <- $[Rsp];;
        $[Rsp] <- $[R1];;
        $[Rsp+1] <- $[R1+1];;
        R0 <- 0;;
        R2 <- 0;;

        Use [allocated_expose_fwd 3];;
        Use [llist_empty_fwd];;

        Call "free"
        [st ~> Ex fr, Ex ss, Ex h, Ex ls2, Ex ret, Ex env, [< ss >= 3 >]
          /\ ![ !{mallocHeap 0} * st#Rsp ==> ret * (st#Rsp+1) ==> env * (st#Rsp+2) ==> h * !{allocated (st#Rsp+3) (ss-3)}
            * !{llist ls2 h} * ![fr] ] st
          /\ ret @@ (st' ~> [< st'#R0 = env /\ st'#R1 = h /\ st'#Rsp = st#Rsp >]
            /\ ![ !{mallocHeap 0} * !{allocated st#Rsp ss} * !{llist ls2 h} * ![fr] ] st')];;
        (* Call the closure's code pointer. *)
        R0 <- $[Rsp+1];;
        R1 <- $[Rsp+2];;

        Use [allocated_expose_bwd 3];;

        Goto $[Rsp]
      } else {
        (* Nonempty list.  Build a new closure that captures prepending the
           first list's first element.  First, build the proper environment:
           a pair of the head of the first list and the current continuation's
           environment. *)
        R0 <- 0;;
        R1 <- 0;;

        Use [allocated_expose_fwd 3];;
        Use [llist_nonempty_fwd];;

        Call "malloc"
        [st ~> Ex fr, Ex ss, Ex ls1, Ex ls2, Ex h1, Ex x, Ex h1', Ex h2, Ex k, Ex ret, Ex env,
          [< ss >= 3 /\ h1 <> 0 /\ k <> 0 /\ st#R0 <> 0 >]
          /\ ![ !{mallocHeap 0} * st#Rsp ==> k * (st#Rsp+1) ==> h1 * (st#Rsp+2) ==> h2 * !{allocated (st#Rsp+3) (ss-3)}
            * h1 ==> x * (h1+1) ==> h1' * !{llist ls1 h1'} * !{llist ls2 h2}
            * k ==> ret * (k+1) ==> env * !{allocated st#R0 2} * ![fr] ] st
          /\ ret @@ (st' ~> [< st'#R0 = env /\ st'#R1 = h1 /\ st'#Rsp = st#Rsp >]
            /\ ![ !{mallocHeap 0} * !{allocated st#Rsp ss}
              * !{llist (x :: ls1 ++ ls2) h1} * ![fr] ] st')];;
        (* Initialize the new environment. *)
        $[R0] <- $[Rsp+1];;
        $[R0+1] <- $[Rsp];;
        R1 <- $[Rsp+1];;
        $[Rsp] <- $[Rsp+1];;
        $[Rsp+1] <- R0;;
        (* Allocate a new closure. *)
        R0 <- 0;;
        R1 <- 0;;
        Call "malloc"
        [st ~> Ex fr, Ex ss, Ex ls1, Ex ls2, Ex h1, Ex x, Ex h1', Ex h2, Ex k, Ex ret, Ex env, Ex env',
          [< ss >= 3 /\ h1 <> 0 /\ k <> 0 /\ env' <> 0 /\ st#R0 <> 0 >]
          /\ ![ !{mallocHeap 0} * st#Rsp ==> h1 * (st#Rsp+1) ==> env' * (st#Rsp+2) ==> h2 * !{allocated (st#Rsp+3) (ss-3)}
            * h1 ==> x * (h1+1) ==> h1' * !{llist ls1 h1'} * !{llist ls2 h2}
            * k ==> ret * (k+1) ==> env * env' ==> h1 * (env'+1) ==> k * !{allocated st#R0 2} * ![fr] ] st
          /\ ret @@ (st' ~> [< st'#R0 = env /\ st'#R1 = h1 /\ st'#Rsp = st#Rsp >]
            /\ ![ !{mallocHeap 0} * !{allocated st#Rsp ss}
              * !{llist (x :: ls1 ++ ls2) h1} * ![fr] ] st')];;
        (* Initialize the new closure and recur. *)
        $[R0] <-- "k";;
        $[R0+1] <- $[Rsp+1];;
        Rret <- R0;;
        R0 <- $[Rsp];;
        R0 <- $[R0+1];;
        R1 <- $[Rsp+2];;

        Use [llist_nonempty_fwd];;
        Use [llist_nonempty_bwd];;
        Use [allocated_expose_fwd 3];;
        Use [allocated_expose_fwd 3];;
        Use [allocated_expose_bwd 3];;

        Goto "append"
      }
    }
  }}.

Theorem appendCPSOk : moduleOk appendCPS.
  structured; abstract (sep; auto).
Qed.
