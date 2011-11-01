Require Import Arith List.

Require Import Ideal Malloc OMaps.


Module Type ALIST.
  Parameter alist : map -> nat -> sprop.
  Parameter alistOk : map -> list (nat * nat) -> nat -> sprop.

  Axiom alist_fwd : forall m a, alist m a ===> Ex a', Ex ls, Ex junk, a ==> a' * (a+1) ==> junk * !{alistOk m ls a'}.
  Axiom alist_bwd : forall m a, (Ex a', Ex ls, Ex junk, a ==> a' * (a+1) ==> junk * !{alistOk m ls a'}) ===> alist m a.

  Axiom alist_empty_fwd : forall m ls a, a = 0
    -> alistOk m ls a ===> [< ls = nil /\ m = empty >].
  Axiom alist_empty_bwd : forall m ls a, a = 0
    -> [< ls = nil /\ m = empty >] ===> alistOk m ls a.

  Axiom alist_nonempty_fwd : forall m ls a, a <> 0
    -> alistOk m ls a ===> Ex k, Ex v, Ex ls', Ex a', [< ls = (k, v) :: ls' /\ a <> 0 /\ m k = Some v >]
    * a ==> k * (a+1) ==> v * (a+2) ==> a' * !{alistOk (del m k) ls' a'}.
  Axiom alist_nonempty_bwd : forall m ls a, a <> 0
    -> (Ex k, Ex v, Ex ls', Ex a', [< ls = (k, v) :: ls' /\ a <> 0 /\ m k = Some v >]
      * a ==> k * (a+1) ==> v * (a+2) ==> a' * !{alistOk (del m k) ls' a'}) ===> alistOk m ls a.
End ALIST.

Module AList : ALIST.
  Open Scope Sep_scope.

  Fixpoint alistOk (m : map) (ls : list (nat * nat)) (a : nat) : sprop :=
    match ls with
      | nil => [< a = 0 /\ m = empty >]
      | (k, v) :: ls' => Ex a', [< a <> 0 /\ m k = Some v >] * a ==> k * (a+1) ==> v * (a+2) ==> a' * !{alistOk (del m k) ls' a'}
    end.

  Definition alist (m : map) (a : nat) : sprop := Ex a', Ex ls, Ex junk, a ==> a' * (a+1) ==> junk * !{alistOk m ls a'}.

  Theorem alist_fwd : forall m a, alist m a ===> Ex a', Ex ls, Ex junk, a ==> a' * (a+1) ==> junk * !{alistOk m ls a'}.
    sepLemma.
  Qed.

  Theorem alist_bwd : forall m a, (Ex a', Ex ls, Ex junk, a ==> a' * (a+1) ==> junk * !{alistOk m ls a'}) ===> alist m a.
    sepLemma.
  Qed.

  Theorem alist_empty_fwd : forall m ls a, a = 0
    -> alistOk m ls a ===> [< ls = nil /\ m = empty >].
    destruct ls; sepLemma.
  Qed.

  Theorem alist_empty_bwd : forall m ls a, a = 0
    -> [< ls = nil /\ m = empty >] ===> alistOk m ls a.
    sepLemma.
  Qed.

  Theorem alist_nonempty_fwd : forall m ls a, a <> 0
    -> alistOk m ls a ===> Ex k, Ex v, Ex ls', Ex a', [< ls = (k, v) :: ls' /\ a <> 0 /\ m k = Some v >]
    * a ==> k * (a+1) ==> v * (a+2) ==> a' * !{alistOk (del m k) ls' a'}.
    destruct ls; sepLemma.
  Qed.

  Theorem alist_nonempty_bwd : forall m ls a, a <> 0
    -> (Ex k, Ex v, Ex ls', Ex a', [< ls = (k, v) :: ls' /\ a <> 0 /\ m k = Some v >]
      * a ==> k * (a+1) ==> v * (a+2) ==> a' * !{alistOk (del m k) ls' a'}) ===> alistOk m ls a.
    sepLemma.
  Qed.
End AList.

Import AList.
Export AList.

Local Hint Immediate alist_fwd : Forward.
Local Hint Immediate alist_bwd : Backward.

Definition constructorS : state -> PropX pc state := st ~> Ex fr, Ex n, [< n >= 1 >]
  /\ ![ !{mallocHeap 0} * !{allocated st#Rsp n} * ![fr] ] st
  /\ st#Rret @@ (st' ~> [< st'#Rsp = st#Rsp >]
    /\ ![ !{mallocHeap 0} * !{allocated st#Rsp n} * !{alist empty st'#R0} * ![fr] ] st').

Definition al := bimport [[ "malloc" @ [mallocS], "free" @ [freeS] ]] bmodule {{
  bfunction "AssociationList" [constructorS] {
    $[Rsp] <- Rret;;

    R0 <- 0;;
    R1 <- 0;;

    Use [allocated_expose_fwd 1];;

    Call "malloc"
    [st ~> Ex n, Ex ret, Ex fr, [< n >= 1 >]
      /\ ![ !{mallocHeap 0} * st#Rsp ==> ret * !{allocated (st#Rsp+1) (n-1)} * !{allocated st#R0 2} * ![fr] ] st
      /\ ret @@ (st' ~> [< st'#Rsp = st#Rsp >]
        /\ ![ !{mallocHeap 0} * !{allocated st#Rsp n} * !{alist empty st'#R0} * ![fr] ] st')];;

    Use [allocated_expose_bwd 1];;
    Use [alist_empty_bwd];;

    $[R0] <- 0;;
    Goto $[Rsp]
  }

  with bfunction "isEmpty" [isEmptyS alist 0] {
    If ($[R0] == 0) {
      R0 <- 1;;

      Use [alist_empty_fwd];;
      Use [alist_empty_bwd]
    } else {
      R0 <- 0;;

      Use [alist_nonempty_fwd];;
      Use [alist_nonempty_bwd]
    };;

    Goto Rret
  }

  with bfunction "containsKey" [containsKeyS alist 0] {
    R0 <- $[R0];;

    [st ~> Ex fr, Ex m, Ex ls,
      ![ !{alistOk m ls st#R0} * ![fr] ] st
      /\ st#Rret @@ (st' ~> [< st'#R0 = (match m st#R1 with None => 0 | Some _ => 1 end) /\ st'#Rsp = st#Rsp >]
        /\ ![ !{alistOk m ls st#R0} * ![fr] ] st')]
    While (R0 != 0) {
      Use [alist_nonempty_fwd];;
      Use [alist_nonempty_bwd];;

      If ($[R0] == R1) {
        R0 <- 1;;
        Goto Rret
      } else {
        R0 <- $[R0+2]
      }
    };;

    Use [alist_empty_fwd];;
    Use [alist_empty_bwd];;

    R0 <- 0;;
    Goto Rret
  }

  with bfunction "get" [getS alist 0] {
    R0 <- $[R0];;

    [st ~> Ex fr, Ex m, Ex ls,
      ![ !{alistOk m ls st#R0} * ![fr] ] st
      /\ st#Rret @@ (st' ~> [< st'#R0 = (match m st#R1 with None => 0 | Some v => v end) /\ st'#Rsp = st#Rsp >]
        /\ ![ !{alistOk m ls st#R0} * ![fr] ] st')]
    While (R0 != 0) {
      Use [alist_nonempty_fwd];;
      Use [alist_nonempty_bwd];;

      If ($[R0] == R1) {
        R0 <- $[R0+1];;
        Goto Rret
      } else {
        R0 <- $[R0+2]
      }
    };;

    Use [alist_empty_fwd];;
    Use [alist_empty_bwd];;

    R0 <- 0;;
    Goto Rret
  }

  with bfunction "put" [putS alist 4] {
    R3 <- R0;;
    R0 <- $[R0];;

    [st ~> Ex fr, Ex ss, Ex m, Ex ls, [< ss >= 4 >]
      /\ ![ !{mallocHeap 0} * !{allocated st#Rsp ss} * st#R3 ==> st#R0 * !{alistOk m ls st#R0} * ![fr] ] st
      /\ st#Rret @@ (st' ~> [< st'#Rsp = st#Rsp >]
        /\ ![ !{mallocHeap 0} * !{allocated st#Rsp ss} * Ex a, st#R3 ==> a * Ex ls', !{alistOk (add m st#R1 st#R2) ls' a} * ![fr] ] st')]
    While (R0 != 0) {
      Use [alist_nonempty_fwd];;
      Use [alist_nonempty_bwd];;

      If ($[R0] == R1) {
        $[R0+1] <- R2;;
        Goto Rret
      } else {
        R3 <- R0+2;;
        R0 <- $[R3]
      }
    };;

    $[Rsp] <- Rret;;
    $[Rsp+1] <- R1;;
    $[Rsp+2] <- R2;;
    $[Rsp+3] <- R3;;
    R0 <- 0;;
    R1 <- 1;;

    Use [allocated_expose_fwd 4];;
    Use [alist_empty_fwd];;
    Use [alist_empty_bwd];;
    Use [alist_nonempty_bwd];;

    Call "malloc"
    [st ~> Ex fr, Ex ss, Ex ret, Ex k, Ex v, Ex p, [< ss >= 4 /\ st#R0 <> 0 >]
      /\ ![ !{mallocHeap 0} * st#Rsp ==> ret * (st#Rsp+1) ==> k * (st#Rsp+2) ==> v * (st#Rsp+3) ==> p * !{allocated (st#Rsp+4) (ss-4)}
        * p ==> 0 * !{allocated st#R0 3} * ![fr] ] st
      /\ ret @@ (st' ~> [< st'#Rsp = st#Rsp >]
        /\ ![ !{mallocHeap 0} * !{allocated st#Rsp ss} * p ==> st#R0 * st#R0 ==> k * (st#R0+1) ==> v * (st#R0+2) ==> 0 * ![fr] ] st')];;

    $[R0] <- $[Rsp+1];;
    $[R0+1] <- $[Rsp+2];;
    $[R0+2] <- 0;;
    R1 <- $[Rsp+3];;
    $[R1] <- R0;;

    Use [allocated_expose_fwd 3];;
    Use [allocated_expose_bwd 4];;

    Goto $[Rsp]
  }

  with bfunction "remove" [removeS alist 4] {
    R2 <- R0;;
    R0 <- $[R0];;

    [st ~> Ex fr, Ex m, Ex ls, ![ !{mallocHeap 0} * st#R2 ==> st#R0 * !{alistOk m ls st#R0} * ![fr] ] st
      /\ st#Rret @@ (st' ~> [< st'#Rsp = st#Rsp >]
        /\ ![ !{mallocHeap 0} * Ex a, st#R2 ==> a * Ex ls', !{alistOk (del m st#R1) ls' a} * ![fr] ] st')]
    While (R0 != 0) {
      Use [alist_nonempty_fwd];;

      If ($[R0] == R1) {
        $[R2] <- $[R0+2];;

        R1 <- R0;;
        R0 <- 0;;
        R2 <- 1;;
        Goto "free"
      } else {
        Use [alist_nonempty_bwd];;

        R2 <- R0+2;;
        R0 <- $[R2]
      }
    };;

    Use [alist_empty_fwd];;
    Use [alist_empty_bwd];;

    Goto Rret
  }
}}.

Theorem alOk : moduleOk al.
  structured; abstract (sep; auto; (autorewrite with OMaps; auto; try rewrite del_del; apply himp_refl) || maps).
Qed.
