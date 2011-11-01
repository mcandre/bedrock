Require Import Ideal Malloc Arrays.

Require Import Arith List.


Module Type ARR_LIST.
  Parameter arrList : list nat -> nat -> sprop.

  Axiom arrList_fwd : forall ls a, arrList ls a
    ===> Ex junk, Ex rec, Ex sz, [< rec <> 0 /\ sz >= length ls >]
    * a ==> rec * (a+1) ==> junk * rec ==> sz * (rec+1) ==> length ls * !{array ls (rec+2)} * !{allocated (rec+2+length ls) (sz-length ls)}.
  Axiom arrList_bwd : forall ls a, (Ex junk, Ex rec, Ex sz, [< rec <> 0 /\ sz >= length ls >]
    * a ==> rec * (a+1) ==> junk * rec ==> sz * (rec+1) ==> length ls * !{array ls (rec+2)} * !{allocated (rec+2+length ls) (sz-length ls)})
    ===> arrList ls a.
End ARR_LIST.

Module ArrList : ARR_LIST.
  Open Scope Sep_scope.

  Definition arrList (ls : list nat) (a : nat) : sprop :=
    Ex junk, Ex rec, Ex sz, [< rec <> 0 /\ sz >= length ls >] * a ==> rec * (a+1) ==> junk * rec ==> sz * (rec+1) ==> length ls * !{array ls (rec+2)}
    * !{allocated (rec+2+length ls) (sz-length ls)}.

  Theorem arrList_fwd : forall ls a, arrList ls a
    ===> Ex junk, Ex rec, Ex sz, [< rec <> 0 /\ sz >= length ls >] * a ==> rec * (a+1) ==> junk * rec ==> sz * (rec+1) ==> length ls * !{array ls (rec+2)}
    * !{allocated (rec+2+length ls) (sz-length ls)}.
    sepLemma.
  Qed.

  Theorem arrList_bwd : forall ls a, (Ex junk, Ex rec, Ex sz, [< rec <> 0 /\ sz >= length ls >]
    * a ==> rec * (a+1) ==> junk * rec ==> sz * (rec+1) ==> length ls * !{array ls (rec+2)} * !{allocated (rec+2+length ls) (sz-length ls)})
    ===> arrList ls a.
    sepLemma.
  Qed.
End ArrList.

Import ArrList.
Export ArrList.

Definition constructorS : state -> PropX pc state := st ~> Ex fr, Ex ss, [< ss >= 2 >]
  /\ ![ !{mallocHeap 0} * !{allocated st#Rsp ss} * ![fr] ] st
  /\ st#Rret @@ (st' ~> [< st'#Rsp = st#Rsp >]
    /\ ![ !{mallocHeap 0} * !{allocated st#Rsp ss} * !{arrList nil st'#R0} * ![fr] ] st').
(* Store desired initial size in st#R0. *)

Definition trimToSizeS : state -> PropX pc state := st ~> Ex fr, Ex ss, Ex ls, [< ss >= 3 >]
  /\ ![ !{mallocHeap 0} * !{allocated st#Rsp ss} * !{arrList ls st#R0} * ![fr] ] st
  /\ st#Rret @@ (st' ~> [< st'#Rsp = st#Rsp >]
    /\ ![ !{mallocHeap 0} * !{allocated st#Rsp ss} * !{arrList ls st#R0} * ![fr] ] st').

Definition ensureCapacityS := trimToSizeS.
(* These last two functions do different things, but the difference isn't observable by client code.
   The latter expects a desired size in st#R1, but that doesn't affect the spec. *)

Definition _ensureCapacityS : state -> PropX pc state := st ~> Ex fr, Ex ss, Ex ls, Ex rec, Ex sz, [< ss >= 3 /\ sz >= length ls /\ rec <> 0 >]
  /\ ![ !{mallocHeap 0} * !{allocated st#Rsp ss}
    * st#R0 ==> rec * rec ==> sz * (rec+1) ==> length ls * !{array ls (rec+2)} * !{allocated (rec+2+length ls) (sz-length ls)} * ![fr] ] st
  /\ st#Rret @@ (st' ~> Ex sz', [< st'#Rsp = st#Rsp /\ sz' >= st#R1 /\ sz' >= sz /\ st'#R0 <> 0 >]
    /\ ![ !{mallocHeap 0} * !{allocated st#Rsp ss}
      * st#R0 ==> st'#R0 * st'#R0 ==> sz' * (st'#R0+1) ==> length ls * !{array ls (st'#R0+2)}
      * !{allocated (st'#R0+2+length ls) (sz'-length ls)} * ![fr] ] st').

Definition sizeS : state -> PropX pc state := st ~> Ex fr, Ex ls,
  ![ !{arrList ls st#R0} * ![fr] ] st
  /\ st#Rret @@ (st' ~> [< st'#R0 = length ls >]
    /\ ![ !{arrList ls st#R0} * ![fr] ] st').

Definition isEmptyS : state -> PropX pc state := st ~> Ex fr, Ex ls,
  ![ !{arrList ls st#R0} * ![fr] ] st
  /\ st#Rret @@ (st' ~> [< match st'#R0 with O => length ls > 0 | _ => length ls = 0 end >]
    /\ ![ !{arrList ls st#R0} * ![fr] ] st').

Definition containsS : state -> PropX pc state := st ~> Ex fr, Ex ss, Ex ls, [< ss >= 2 >]
  /\ ![ !{allocated st#Rsp ss} * !{arrList ls st#R0} * ![fr] ] st
  /\ st#Rret @@ (st' ~> [< st'#Rsp = st#Rsp /\ match st'#R0 with O => ~In st#R1 ls | _ => In st#R1 ls end >]
    /\ ![ !{allocated st#Rsp ss} * !{arrList ls st#R0} * ![fr] ] st').

Definition indexOfS : state -> PropX pc state := st ~> Ex fr, Ex ls,
  ![ !{arrList ls st#R0} * ![fr] ] st
  /\ st#Rret @@ (st' ~> [< st'#Rsp = st#Rsp /\ (IF st'#R0 >= length ls then ~In st#R1 ls else nth st'#R0 ls 0 = st#R1 /\ ~In st#R1 (firstn st'#R0 ls)) >]
    /\ ![ !{arrList ls st#R0} * ![fr] ] st').

Definition lastIndexOfS : state -> PropX pc state := st ~> Ex fr, Ex ls,
  ![ !{arrList ls st#R0} * ![fr] ] st
  /\ st#Rret @@ (st' ~> [< st'#Rsp = st#Rsp /\ (IF st'#R0 >= length ls then ~In st#R1 ls
    else nth st'#R0 ls 0 = st#R1 /\ ~In st#R1 (skipn (st'#R0+1) ls)) >]
    /\ ![ !{arrList ls st#R0} * ![fr] ] st').

Definition toArrayS : state -> PropX pc state := st ~> Ex fr, Ex ss, Ex ls, [< ss >= 2 /\ length ls >= 2 >]
  /\ ![ !{mallocHeap 0} * !{allocated st#Rsp ss} * !{arrList ls st#R0} * ![fr] ] st
  /\ st#Rret @@ (st' ~> [< st'#Rsp = st#Rsp >]
    /\ ![ !{mallocHeap 0} * !{allocated st#Rsp ss} * !{arrList ls st#R0} * !{array ls st'#R0} * ![fr] ] st').
(* The list length requirement comes from the malloc library's imposition of a minimum of 2 bytes per block. *)

Definition getS : state -> PropX pc state := st ~> Ex fr, Ex ls, [< st#R1 < length ls >]
  /\ ![ !{arrList ls st#R0} * ![fr] ] st
  /\ st#Rret @@ (st' ~> [< st'#Rsp = st#Rsp /\ st'#R0 = nth st#R1 ls 0 >]
    /\ ![ !{arrList ls st#R0} * ![fr] ] st').

Definition setS : state -> PropX pc state := st ~> Ex fr, Ex ls, [< st#R1 < length ls >]
  /\ ![ !{arrList ls st#R0} * ![fr] ] st
  /\ st#Rret @@ (st' ~> [< st'#Rsp = st#Rsp >]
    /\ ![ !{arrList (firstn st#R1 ls ++ st#R2 :: skipn (st#R1+1) ls) st#R0} * ![fr] ] st').

Definition addS : state -> PropX pc state := st ~> Ex fr, Ex ss, Ex ls, [< ss >= 6 >]
  /\ ![ !{mallocHeap 0} * !{allocated st#Rsp ss} * !{arrList ls st#R0} * ![fr] ] st
  /\ st#Rret @@ (st' ~> [< st'#Rsp = st#Rsp >]
    /\ ![ !{mallocHeap 0} * !{allocated st#Rsp ss} * !{arrList (ls ++ st#R1 :: nil) st#R0} * ![fr] ] st').

Definition addAtS : state -> PropX pc state := st ~> Ex fr, Ex ss, Ex ls, [< ss >= 7 /\ st#R1 <= length ls >]
  /\ ![ !{mallocHeap 0} * !{allocated st#Rsp ss} * !{arrList ls st#R0} * ![fr] ] st
  /\ st#Rret @@ (st' ~> [< st'#Rsp = st#Rsp >]
    /\ ![ !{mallocHeap 0} * !{allocated st#Rsp ss} * !{arrList (firstn st#R1 ls ++ st#R2 :: skipn st#R1 ls) st#R0} * ![fr] ] st').

Definition shiftS : state -> PropX pc state := st ~> Ex fr, Ex ls, Ex junk, [< st#R1 = length ls >]
  /\ ![ st#R0 ==> junk * !{array ls (st#R0+1)} * ![fr] ] st
  /\ st#Rret @@ (st' ~> Ex junk', [< st'#Rsp = st#Rsp >]
    /\ ![ !{array ls st#R0} * (st#R0+length ls) ==> junk' * ![fr] ] st').

Definition removeAtS : state -> PropX pc state := st ~> Ex fr, Ex ls, [< st#R1 < length ls >]
  /\ ![ !{arrList ls st#R0} * ![fr] ] st
  /\ st#Rret @@ (st' ~> [< st'#Rsp = st#Rsp >]
    /\ ![ !{arrList (firstn st#R1 ls ++ skipn (st#R1+1) ls) st#R0} * ![fr] ] st').

Fixpoint remove (ls : list nat) (n : nat) : list nat :=
  match ls with
    | nil => nil
    | x :: ls => if eq_nat_dec x n then ls else x :: remove ls n
  end.

Fixpoint inList (ls : list nat) (n : nat) : nat :=
  match ls with
    | nil => O
    | x :: ls => if eq_nat_dec x n then 1 else inList ls n
  end.

Definition removeS : state -> PropX pc state := st ~> Ex fr, Ex ls,
  ![ !{arrList ls st#R0} * ![fr] ] st
  /\ st#Rret @@ (st' ~> [< st'#Rsp = st#Rsp >]
    /\ ![ !{arrList (remove ls st#R1) st#R0} * ![fr] ] st').

Definition clearS : state -> PropX pc state := st ~> Ex fr, Ex ls,
  ![ !{arrList ls st#R0} * ![fr] ] st
  /\ st#Rret @@ (st' ~> [< st'#Rsp = st#Rsp >]
    /\ ![ !{arrList nil st#R0} * ![fr] ] st').

Definition popLastS : state -> PropX pc state := st ~> Ex fr, Ex ls, [< length ls > 0 >]
  /\ ![ !{arrList ls st#R0} * ![fr] ] st
  /\ st#Rret @@ (st' ~> [< st'#Rsp = st#Rsp /\ st'#R0 = last ls 0 >]
    /\ ![ !{arrList (removelast ls) st#R0} * ![fr] ] st').

Local Hint Immediate arrList_fwd : Forward.
Local Hint Immediate arrList_bwd : Backward.

Theorem array_firstn_nada : forall n ls v,
  emp ===> array (firstn (n - n) ls) v.
  intros; rewrite minus_diag; sepLemma.
Qed.

Theorem array_firstn_end : forall n ls a,
  n < length ls
  -> !{array (firstn n ls) a} * (a + n) ==> nth n ls 0 ===> array (firstn (n + 1) ls) a.
  induction n; destruct ls; simpl; intros; try (elimtype False; omega); sepLemma.
Qed.

Theorem allocated_minus_O : forall a len, !{allocated a len} ===> allocated a (len - 0).
  sepLemma.
Qed.

Theorem allocated_minus_plus : forall a len n m, !{allocated a (len - n - m)} ===> allocated a (len - (n + m)).
  sepLemma.
Qed.

Theorem allocated_expose_fwd' : forall n base (ls : list nat) len,
  n <= len -> allocated (base + length ls) len ===> !{allocated (base + length ls) (n + (len - n))}.
  use allocated_expose_fwd; sepLemma.
Qed.

Theorem firstn_all : forall A (ls : list A) n, n = length ls -> firstn n ls = ls.
  induction ls; intros; subst; simpl; intuition; f_equal; auto.
Qed.

Theorem array_firstn_all : forall a n ls,
  n = length ls
  -> array (firstn n ls) a ===> !{array ls a}.
  intros; rewrite firstn_all; sepLemma.
Qed.

Definition arl := bimport [[ "malloc" @ [mallocS], "free" @ [freeS] ]] bmodule {{
  bfunction "ArrayList" [constructorS] {
    $[Rsp] <- Rret;;
    $[Rsp+1] <- R0;;

    R1 <- R0+2;;
    R0 <- 0;;

    Use [allocated_expose_fwd 2];;

    Call "malloc"
    [st ~> Ex fr, Ex n, Ex ret, Ex sz, [< n >= 2 /\ st#R0 <> 0 >]
      /\ ![ !{mallocHeap 0} * st#Rsp ==> ret * (st#Rsp+1) ==> sz * !{allocated (st#Rsp+2) (n-2)} * !{allocated st#R0 (sz+4)} * ![fr] ] st
      /\ ret @@ (st' ~> [< st'#Rsp = st#Rsp >]
        /\ ![ !{mallocHeap 0} * !{allocated st#Rsp n} * !{arrList nil st'#R0} * ![fr] ] st')];;

    Use [allocated_expose_fwd 4];;
    Use [allocated_expose_bwd 2];;

    $[R0] <- R0+2;;
    $[R0+2] <- $[Rsp+1];;
    $[R0+3] <- 0;;
    Goto $[Rsp]
  }

  with bfunction "trimToSize" [trimToSizeS] {
    R1 <- $[R0];;
    If ($[R1+1] < $[R1]) {
      $[Rsp] <- Rret;;
      $[Rsp+1] <- R0;;

      R1 <- $[R1+1];;
      R0 <- 0;;

      Use [allocated_expose_fwd 2];;

      Call "malloc"
      [st ~> Ex fr, Ex ss, Ex ls, Ex ret, Ex a, [< ss >= 2 /\ st#R0 <> 0 >]
        /\ ![ !{mallocHeap 0} * st#Rsp ==> ret * (st#Rsp+1) ==> a * !{allocated (st#Rsp+2) (ss-2)}
          * !{arrList ls a} * !{allocated st#R0 (length ls+2)} * ![fr] ] st
        /\ ret @@ (st' ~> [< st'#Rsp = st#Rsp >]
          /\ ![ !{mallocHeap 0} * !{allocated st#Rsp ss} * !{arrList ls a} * ![fr] ] st')];;

      R1 <- $[Rsp+1];;
      R2 <- $[R1];;
      $[Rsp+1] <- $[R2];;
      $[R1] <- R0;;
      R3 <- $[R2+1];;
      $[R0] <- R3;;
      $[R0+1] <- R3;;
      R1 <- 0;;

      Use [allocated_expose_fwd 2];;
      Use [array_firstn_nada];;
      Use [allocated0_bwd];;

      [st ~> Ex fr, Ex ss, Ex ls, Ex ret, Ex sz, [< ss >= 2 /\ st#R0 <> 0 /\ st#R2 <> 0 /\ st#R1 <= length ls /\ st#R3 = length ls /\ sz >= length ls >]
        /\ ![ !{mallocHeap 0} * st#Rsp ==> ret * (st#Rsp+1) ==> sz * !{allocated (st#Rsp+2) (ss-2)}
          * st#R2 ==> sz * (st#R2+1) ==> length ls * !{array ls (st#R2+2)} * !{allocated (st#R2+2+length ls) (sz-length ls)}
          * !{array (firstn st#R1 ls) (st#R0+2)} * !{allocated (st#R0+2+st#R1) (length ls - st#R1)} * ![fr] ] st
        /\ ret @@ (st' ~> [< st'#Rsp = st#Rsp >]
          /\ ![ !{mallocHeap 0} * !{allocated st#Rsp ss} * !{array ls (st#R0+2)} * ![fr] ] st')]
      While (R1 < R3) {
        Use st [allocated_expose_fwd 1 (st#R0+2+st#R1)];;
        Use st [array_mid_fwd st#R1];;
        Use st [array_mid_fwd st#R1];;
        Use st [array_mid_bwd st#R1];;
        Use [array_firstn_end];;

        R4 <- R0+R1;;
        R5 <- R2+R1;;
        $[R4+2] <- $[R5+2];;
        R1 <- R1 + 1
      };;

      Use [allocated_expose_bwd 2];;
      Use st [array_allocated (st#R2+2)];;
      Use [allocated_expose_fwd 2];;
      Use st [allocated_combine st#R3 (S (S st#R2))];;
      Use [allocated0_fwd];;
      Use [array_firstn_all];;

      R1 <- R2;;
      R0 <- 0;;
      R2 <- $[Rsp+1];;
      Rret <- $[Rsp];;

      Goto "free"
    } else {
      Goto Rret
    }
  }

  with bfunction "_ensureCapacity" [_ensureCapacityS] {
    R2 <- $[R0];;
    If ($[R2] < R1) {
      R2 <- $[R2];;
      R2 <- R2 * 2;;

      If (R1 <= R2) {
        R1 <- R2
      } else {
        Skip
      };;

      $[Rsp] <- Rret;;
      $[Rsp+1] <- R0;;
      $[Rsp+2] <- R1;;
      R0 <- 0;;

      Use [allocated_expose_fwd 3];;

      Call "malloc"
      [st ~> Ex fr, Ex ss, Ex ret, Ex base, Ex ls, Ex rec, Ex sz, Ex sz', [< ss >= 3 /\ sz >= length ls /\ sz' >= sz /\ rec <> 0 >]
        /\ ![ !{mallocHeap 0} * st#Rsp ==> ret * (st#Rsp+1) ==> base * (st#Rsp+2) ==> sz' * !{allocated (st#Rsp+3) (ss-3)}
          * base ==> rec * rec ==> sz * (rec+1) ==> length ls * !{array ls (rec+2)} * !{allocated (rec+2+length ls) (sz-length ls)}
          * !{allocated st#R0 (sz'+2)} * ![fr] ] st
        /\ ret @@ (st' ~> [< st'#Rsp = st#Rsp /\ st'#R0 = st#R0 >]
          /\ ![ !{mallocHeap 0} * !{allocated st#Rsp ss}
            * base ==> st#R0 * st#R0 ==> sz' * (st#R0+1) ==> length ls * !{array ls (st#R0+2)}
            * !{allocated (st#R0+2+length ls) (sz'-length ls)} * ![fr] ] st')];;

      R1 <- $[Rsp+1];;
      R3 <- $[R1];;
      $[R1] <- R0;;
      R1 <- R3;;
      R2 <- $[Rsp+2];;
      $[R0] <- R2;;
      $[R0+1] <- $[R1+1];;
      R2 <- $[R1+1];;

      Use [allocated_expose_fwd 2];;
      Use [array_firstn_nada];;
      Use [allocated_minus_O];;

      R3 <- 0;;
      [st ~> Ex fr, Ex ss, Ex ls, Ex ret, Ex junk, Ex junk', Ex junk1, Ex sz, Ex sz',
        [< ss >= 3 /\ st#R1 <> 0 /\ st#R3 <= length ls /\ st#R2 = length ls /\ sz >= length ls /\ sz' >= sz >]
        /\ ![ !{mallocHeap 0} * st#Rsp ==> ret * (st#Rsp+1) ==> junk * (st#Rsp+2) ==> junk' * !{allocated (st#Rsp+3) (ss-3)}
          * st#R1 ==> sz * (st#R1+1) ==> junk1 * !{array ls (st#R1+2)} * !{allocated (st#R1+2+length ls) (sz-length ls)}
          * !{array (firstn st#R3 ls) (st#R0+2)} * !{allocated (st#R0+2+st#R3) (sz' - st#R3)} * ![fr] ] st
        /\ ret @@ (st' ~> [< st'#Rsp = st#Rsp /\ st'#R0 = st#R0 >]
          /\ ![ !{mallocHeap 0} * !{allocated st#Rsp ss} * !{array ls (st#R0+2)} * !{allocated (st#R0+2+length ls) (sz' - length ls)} * ![fr] ] st')]
      While (R3 < R2) {
        Use st [allocated_expose_fwd 1 (st#R0+2+st#R3)];;
        Use st [array_mid_fwd st#R3];;
        Use st [array_mid_bwd st#R3];;
        Use [allocated_expose_bwd 1];;
        Use [array_firstn_end];;
        Use [allocated_minus_plus];;

        R4 <- R0+R3;;
        R5 <- R1+R3;;
        $[R4+2] <- $[R5+2];;
        R3 <- R3 + 1
      };;

      Use [allocated_expose_fwd 2];;
      Use [allocated_expose_bwd 2];;
      Use st [array_allocated (st#R1+2)];;
      Use st [allocated_combine st#R2 (S (S st#R1))];;
      Use [array_firstn_all];;

      $[Rsp+1] <- R0;;
      R0 <- 0;;
      R2 <- $[R1];;

      Call "free"
      [st ~> Ex fr, Ex ss, Ex ret, Ex new, Ex junk, [< ss >= 3 >]
        /\ ![ st#Rsp ==> ret * (st#Rsp+1) ==> new * (st#Rsp+2) ==> junk * !{allocated (st#Rsp+3) (ss-3)} * ![fr] ] st
        /\ ret @@ (st' ~> [< st'#Rsp = st#Rsp /\ st'#R0 = new >]
          /\ ![ !{allocated st#Rsp ss} * ![fr] ] st')];;

      Use [allocated_expose_bwd 3];;

      R0 <- $[Rsp+1];;
      Goto $[Rsp]
    } else {
      R0 <- R2;;
      Goto Rret
    }
  }

  with bfunction "ensureCapacity" [ensureCapacityS] {
    Goto "_ensureCapacity"
  }

  with bfunction "size" [sizeS] {
    R0 <- $[R0];;
    R0 <- $[R0+1];;
    Goto Rret
  }

  with bfunction "isEmpty" [isEmptyS] {
    R0 <- $[R0];;
    If (0 < $[R0+1]) {
      R0 <- 0
    } else {
      R0 <- 1
    };;
    Goto Rret
  }

  with bfunction "indexOf" [indexOfS] {
    R0 <- $[R0];;
    R2 <- $[R0+1];;
    R3 <- R0+2;;
    R0 <- 0;;

    [st ~> Ex fr, Ex ls, [< st#R2 = length ls /\ st#R0 <= length ls /\ ~In st#R1 (firstn st#R0 ls) >]
      /\ ![ !{array ls st#R3} * ![fr] ] st
      /\ st#Rret @@ (st' ~> [< st'#Rsp = st#Rsp /\ (IF st'#R0 >= length ls then ~In st#R1 ls
      else nth st'#R0 ls 0 = st#R1 /\ ~In st#R1 (firstn st'#R0 ls)) >]
        /\ ![ !{array ls st#R3} * ![fr] ] st')]
    While (R0 < R2) {
      Use st [array_mid_fwd st#R0];;
      Use st [array_mid_bwd st#R0];;

      R4 <- R3+R0;;
      If ($[R4] == R1) {
        Goto Rret
      } else {
        R0 <- R0 + 1
      }
    };;

    Goto Rret
  }

  with bfunction "contains" [containsS] {
    $[Rsp] <- Rret;;
    $[Rsp+1] <- R0;;

    Use [allocated_expose_fwd 2];;

    Call "indexOf"
    [st ~> Ex fr, Ex ss, Ex ls, Ex ret, Ex root, [< ss >= 2 >]
      /\ ![ st#Rsp ==> ret * (st#Rsp+1) ==> root * !{allocated (st#Rsp+2) (ss-2)} * !{arrList ls root} * ![fr] ] st
      /\ ret @@ (st' ~> [< st'#Rsp = st#Rsp /\ match st'#R0 with O => st#R0 >= length ls | _ => st#R0 < length ls end >]
        /\ ![ !{allocated st#Rsp ss} * !{arrList ls root} * ![fr] ] st')];;

    R1 <- $[Rsp+1];;
    R1 <- $[R1];;
    If (R0 < $[R1+1]) {
      R0 <- 1
    } else {
      R0 <- 0
    };;

    Use [allocated_expose_bwd 2];;
    Goto $[Rsp]
  }

  with bfunction "lastIndexOf" [lastIndexOfS] {
    R0 <- $[R0];;
    R2 <- $[R0+1];;
    R3 <- R0+1;;
    R3 <- R3+R2;;
    R0 <- 0;;

    [st ~> Ex fr, Ex ls, Ex a, [< st#R2 = length ls /\ st#R0 <= length ls /\ st#R3 = a + length ls - 1 /\ ~In st#R1 (skipn (length ls - st#R0) ls) >]
      /\ ![ !{array ls a} * ![fr] ] st
      /\ st#Rret @@ (st' ~> [< st'#Rsp = st#Rsp /\ (IF st'#R0 >= length ls then ~In st#R1 ls
      else nth st'#R0 ls 0 = st#R1 /\ ~In st#R1 (skipn (st'#R0+1) ls)) >]
        /\ ![ !{array ls a} * ![fr] ] st')]
    While (R0 < R2) {
      Use st [array_mid_fwd (st#R2-1-st#R0)];;
      Use st [array_mid_bwd (st#R2-1-st#R0)];;

      R4 <- R3-R0;;
      If ($[R4] == R1) {
        R2 <- R2-1;;
        R0 <- R2-R0;;
        Goto Rret
      } else {
        R0 <- R0 + 1
      }
    };;

    R0 <- R2;;
    Goto Rret
  }

  with bfunction "toArray" [toArrayS] {
    $[Rsp] <- Rret;;
    $[Rsp+1] <- R0;;

    R1 <- $[R0];;
    R1 <- $[R1+1];;
    R1 <- R1-2;;
    R0 <- 0;;

    Use [allocated_expose_fwd 2];;

    Call "malloc"
    [st ~> Ex fr, Ex ss, Ex ret, Ex base, Ex ls, Ex rec, [< ss >= 2 >]
      /\ ![ st#Rsp ==> ret * (st#Rsp+1) ==> base * !{allocated (st#Rsp+2) (ss-2)}
        * base ==> rec * (rec+1) ==> length ls * !{array ls (rec+2)} * !{allocated st#R0 (length ls)} * ![fr] ] st
      /\ ret @@ (st' ~> [< st'#Rsp = st#Rsp /\ st'#R0 = st#R0 >]
        /\ ![ !{allocated st#Rsp ss} * base ==> rec * (rec+1) ==> length ls * !{array ls (rec+2)} * !{array ls st#R0} * ![fr] ] st')];;

    R1 <- $[Rsp+1];;
    R3 <- $[R1];;
    R2 <- $[R3+1];;
    R1 <- R3+2;;

    Use [array_firstn_nada];;

    R3 <- 0;;
    [st ~> Ex fr, Ex ret, Ex ss, Ex ls, Ex junk, [< ss >= 2 /\ st#R2 = length ls /\ st#R3 <= length ls >]
      /\ ![ st#Rsp ==> ret * (st#Rsp+1) ==> junk * !{allocated (st#Rsp+2) (ss-2)} * !{array ls st#R1}
        * !{array (firstn st#R3 ls) st#R0} * !{allocated (st#R0 + st#R3) (length ls - st#R3)} * ![fr] ] st
      /\ ret @@ (st' ~> [< st'#Rsp = st#Rsp /\ st'#R0 = st#R0 >]
        /\ ![ !{allocated st#Rsp ss} * !{array ls st#R1} * !{array ls st#R0} * ![fr] ] st')]
    While (R3 < R2) {
      Use st [allocated_expose_fwd 1 (st#R0+st#R3)];;
      Use st [array_mid_fwd st#R3];;
      Use st [array_mid_bwd st#R3];;
      Use [allocated_expose_bwd 1];;
      Use [array_firstn_end];;

      R4 <- R0+R3;;
      R5 <- R1+R3;;
      $[R4] <- $[R5];;
      R3 <- R3 + 1
    };;

    Use [allocated_expose_bwd 2];;
    Use [allocated0_fwd];;
    Use [array_firstn_all];;

    Goto $[Rsp]
  }

  with bfunction "get" [getS] {
    Use st [array_mid_fwd st#R1];;
    Use st [array_mid_bwd st#R1];;

    R2 <- $[R0];;
    R2 <- R2 + R1;;
    R0 <- $[R2+2];;
    Goto Rret
  }

  with bfunction "set" [setS] {
    Use st [array_mid_fwd st#R1];;
    Use st [array_mid_bwd st#R1];;

    R3 <- $[R0];;
    R3 <- R3 + R1;;
    $[R3+2] <- R2;;
    Goto Rret
  }

  with bfunction "add" [addS] {
    $[Rsp] <- Rret;;
    $[Rsp+1] <- R0;;
    $[Rsp+2] <- R1;;

    R1 <- $[R0];;
    R1 <- $[R1+1];;
    R1 <- R1+1;;
    Rsp <- Rsp+3;;

    Use [allocated_expose_fwd' 1];;
    Use [allocated_expose_fwd 3];;
    Use [array_last_bwd];;

    Call "_ensureCapacity"
    [st ~> Ex fr, Ex ss, Ex len, Ex ret, Ex base, Ex v, Ex avail, [< ss >= 3 /\ st#Rsp >= 3 >]
      /\ ![ !{mallocHeap 0} * (st#Rsp-3) ==> ret * (st#Rsp-2) ==> base * (st#Rsp-1) ==> v * !{allocated st#Rsp (ss-3)}
        * base ==> st#R0 * (st#R0+1) ==> len * (st#R0+2+len) ==> avail * ![fr] ] st
      /\ ret @@ (st' ~> [< st'#Rsp = st#Rsp-3 >]
        /\ ![ !{mallocHeap 0} * !{allocated st'#Rsp ss} * base ==> st#R0 * (st#R0+1) ==> (len+1)
          * (st#R0+2+len) ==> v * ![fr] ] st')];;

    Rsp <- Rsp-3;;
    R1 <- $[Rsp+1];;
    R1 <- $[R1];;
    R2 <- $[R1+1];;
    $[R1+1] <- R2+1;;
    R0 <- R0+R2;;
    $[R0+2] <- $[Rsp+2];;

    Use [allocated_expose_bwd 3];;

    Goto $[Rsp]
  }

  with bfunction "addAt" [addAtS] {
    Use [allocated_expose_fwd 4];;
    Use st [array_split_fwd_var st#R1];;
    Use st [array_split_fwd_var st#R1];;
    Use st [array_split_bwd st#R1];;
    Use [allocated_expose_fwd' 1];;
    Use st [array_mid_bwd_upfront st#R1];;

    $[Rsp] <- Rret;;
    $[Rsp+1] <- R0;;
    $[Rsp+2] <- R1;;
    $[Rsp+3] <- R2;;

    R1 <- $[R0];;
    R1 <- $[R1+1];;
    R1 <- R1+1;;
    Rsp <- Rsp+4;;

    Call "_ensureCapacity"
    [st ~> Ex fr, Ex ss, Ex ls, Ex ret, Ex base, Ex pos, Ex v, Ex avail, [< ss >= 4 /\ st#Rsp >= 4 /\ pos <= length ls >]
      /\ ![ (st#Rsp-4) ==> ret * (st#Rsp-3) ==> base * (st#Rsp-2) ==> pos * (st#Rsp-1) ==> v * !{allocated st#Rsp (ss-4)}
        * base ==> st#R0 * (st#R0+1) ==> length ls * !{array (skipn pos ls) (st#R0+2+pos)} * (st#R0+2+length ls) ==> avail * ![fr] ] st
      /\ ret @@ (st' ~> [< st'#Rsp = st#Rsp-4 >]
        /\ ![ !{allocated st'#Rsp ss} * base ==> st#R0 * (st#R0+1) ==> (length ls+1)
          * (st#R0+2+pos) ==> v * !{array (skipn pos ls) (st#R0+2+pos+1)} * ![fr] ] st')];;

    Rsp <- Rsp-4;;
    R1 <- $[Rsp+1];;
    R1 <- $[R1];;
    R2 <- $[R1+1];;
    $[R1+1] <- R2+1;;
    R1 <- R2 - $[Rsp+2];;

    R2 <- $[Rsp+2];;
    R0 <- R0+R2;;
    R0 <- R0+2;;
    [st ~> Ex fr, Ex ss, Ex ls, Ex ret, Ex base, Ex pos, Ex v, Ex avail, [< ss >= 4 /\ st#R1 = length ls >]
      /\ ![ st#Rsp ==> ret * (st#Rsp+1) ==> base * (st#Rsp+2) ==> pos * (st#Rsp+3) ==> v * !{allocated (st#Rsp+4) (ss-4)}
        * !{array ls st#R0} * (st#R0+length ls) ==> avail * ![fr] ] st
      /\ ret @@ (st' ~> [< st'#Rsp = st#Rsp >]
        /\ ![ !{allocated st'#Rsp ss} * st#R0 ==> v * !{array ls (st#R0+1)} * ![fr] ] st')]
    While (0 < R1) {
      R2 <- R0+R1;;
      R3 <- R2-1;;
      $[R2] <- $[R3];;
      R1 <- R1 - 1;;
      
      Use [array_last_fwd];;
      Use [array_last_bwd']
    };;

    $[R0] <- $[Rsp+3];;

    Use [allocated_expose_bwd 4];;
    Use [array_nil_fwd];;
    Use [array_nil_bwd];;

    Goto $[Rsp]
  }

  with bfunction "shift" [shiftS] {
    [shiftS]
    While (0 < R1) {
      $[R0] <- $[R0+1];;
      R0 <- R0 + 1;;
      R1 <- R1 - 1;;

      Use [array_head_fwd];;
      Use [array_head_bwd]
    };;

    Use [array_nil_fwd];;
    Use [array_nil_bwd];;

    Goto Rret
  }

  with bfunction "removeAt" [removeAtS] {
    Use st [array_mid_fwd st#R1];;
    Use st [array_split_bwd st#R1];;
    Use [allocated_expose_bwd 1];;

    R0 <- $[R0];;
    R2 <- $[R0+1] - R1;;
    $[R0+1] <- $[R0+1] - 1;;
    R0 <- R0 + 2;;
    R0 <- R0 + R1;;
    R1 <- R2 - 1;;

    Goto "shift"
  }

  with bfunction "remove" [removeS] {
    R0 <- $[R0];;
    R3 <- R0+1;;
    R2 <- $[R3];;
    R0 <- R0+2;;

    [st ~> Ex fr, Ex ls, Ex old, [< st#R2 = length ls >]
      /\ ![ st#R3 ==> old * !{array ls st#R0} * ![fr] ] st
      /\ st#Rret @@ (st' ~> [< st'#Rsp = st#Rsp >]
        /\ ![ st#R3 ==> (old - inList ls st#R1) * !{array (remove ls st#R1) st#R0}
          * !{allocated (st#R0 + length ls - 1) (inList ls st#R1)} * ![fr] ] st')]
    While (0 < R2) {
      Use [array_head_fwd];;

      If ($[R0] == R1) {
        $[R3] <- $[R3] - 1;;
        R1 <- R2-1;;
        Goto "shift"
      } else {
        Use st [array_head_bwd st#R0];;
        R0 <- R0 + 1;;
        R2 <- R2 - 1
      }
    };;

    Use [array_nil_fwd];;

    Goto Rret
  }

  with bfunction "clear" [clearS] {
    Use [array_allocated];;
    Use st [allocated_combine st.[st.[st#R0]+1] ];;

    R0 <- $[R0];;
    $[R0+1] <- 0;;

    Goto Rret
  }

  with bfunction "popLast" [popLastS] {
    R0 <- $[R0];;
    $[R0+1] <- $[R0+1] - 1;;
    R0 <- R0 + $[R0+1];;
    R0 <- $[R0+2];;

    Use [array_last_fwd'];;
    Use [allocated_expose_bwd 1];;

    Goto Rret
  }
}}.

Theorem notIn_append : forall v n ls,
  ~In v (firstn n ls)
  -> nth n ls 0 <> v
  -> ~In v (firstn (n + 1) ls).
  induction n; destruct ls; simpl; intuition eauto.
Qed.

Local Hint Extern 1 (False) => eapply notIn_append; eassumption.

Theorem indexOf_to_contains : forall r v r' ls P,
  (IF r >= length ls then In v ls -> False else nth r ls 0 = v /\ P)
  -> match r' with
       | 0 => r >= length ls
       | S _ => r < length ls
     end
  -> match r' with
       | 0 => In v ls -> False
       | S _ => In v ls
     end.
  unfold IF_then_else; intros; destruct r'; intuition; subst; try (elimtype False; omega); apply nth_In; auto.
Qed.

Local Hint Extern 1 (IF _ then _ else _) => unfold IF_then_else in *; try rewrite firstn_all in * by omega; intuition.

Theorem skipn_none : forall A (ls : list A) n, n = length ls -> skipn n ls = nil.
  induction ls; intros; subst; simpl; intuition.
Qed.

Lemma skipn_none_contra : forall A v (ls : list A),
  In v (skipn (length ls - 0) ls) -> False.
  intros; rewrite skipn_none in * by omega; tauto.
Qed.

Local Hint Extern 1 => eapply indexOf_to_contains; eassumption.

Lemma notIn_prepend' : forall (v : nat) n ls,
  In v (skipn n ls)
  -> nth n ls 0 = v \/ In v (skipn (S n) ls).
  induction n; destruct ls; simpl; intuition; specialize (IHn ls); intuition.
Qed.

Theorem notIn_prepend : forall (v : nat) n ls n' n'',
  ~In v (skipn n ls)
  -> n <> 0
  -> nth n' ls 0 <> v
  -> n' = n - 1
  -> In v (skipn n'' ls)
  -> n'' = n - 1
  -> False.
  intros; subst; match goal with
                   | [ H : _ |- _ ] => generalize (notIn_prepend' _ _ _ H); replace (S (n - 1)) with n by omega; tauto
                 end.
Qed.

Local Hint Extern 1 False => eapply notIn_prepend; (eassumption || omega).

Lemma In_skip_replace : forall (v : nat) n n' ls,
  (In v (skipn n ls) -> False)
  -> In v (skipn n' ls)
  -> n' = n
  -> False.
  congruence.
Qed.

Local Hint Extern 1 False => eapply In_skip_replace; [ eassumption | eassumption | omega ].

Theorem In_skip_all : forall (v : nat) n ls,
  (In v (skipn n ls) -> False)
  -> In v ls
  -> n = 0
  -> False.
  intros; subst; auto.
Qed.

Local Hint Extern 1 False => eapply In_skip_all; [ eassumption | eassumption | omega ].

Theorem decomp_eq : forall A v n (ls : list A),
  n < length ls
  -> length (firstn n ls ++ v :: skipn (n + 1) ls) = length ls.
  induction n; destruct ls; simpl; intuition.
Qed.

Theorem double_firstn : forall A ls' n (ls : list A),
  n <= length ls
  -> firstn n (firstn n ls ++ ls') = firstn n ls.
  induction n; destruct ls; simpl; intuition; try (elimtype False; omega); f_equal; auto.
Qed.

Theorem double_nth : forall (v : nat) ls' n ls,
  n <= length ls
  -> nth n (firstn n ls ++ v :: ls') O = v.
  induction n; destruct ls; simpl; intuition.
Qed.

Theorem double_skipn : forall A v ls' n (ls : list A),
  n <= length ls
  -> skipn (n+1) (firstn n ls ++ v :: ls') = ls'.
  induction n; destruct ls; simpl; intuition; try (elimtype False; omega).
Qed.

Theorem skipn_firstn : forall A ls' n (ls : list A),
  n <= length ls
  -> skipn n (firstn n ls ++ ls') = ls'.
  induction n; destruct ls; simpl; intuition; destruct ls'; intuition; try (elimtype False; omega).
Qed.

Ltac miss := simpl; intuition; match goal with
                                 | [ |- context[if ?E then _ else _] ] => destruct E; simpl; intuition
                               end.

Theorem inList_miss : forall n ls, length ls > 0 -> hd 0 ls <> n -> inList (tl ls) n = inList ls n.
  destruct ls; miss.
Qed.

Theorem remove_miss : forall n ls, length ls > 0 -> hd 0 ls <> n -> remove (tl ls) n = tl (remove ls n).
  destruct ls; miss.
Qed.

Theorem hd_miss : forall ls v, hd 0 ls <> v -> hd 0 (remove ls v) = hd 0 ls.
  destruct ls; miss.
Qed.

Theorem inList_nil : forall ls v, length ls = 0 -> inList ls v = 0.
  destruct ls; simpl; auto.
Qed.

Theorem remove_nil : forall ls v, length ls = 0 -> remove ls v = nil.
  destruct ls; simpl; intuition; elimtype False; omega.
Qed.

Hint Rewrite decomp_eq double_firstn double_nth double_skipn skipn_firstn inList_miss remove_miss hd_miss inList_nil remove_nil
  using omega : InSep.

Local Hint Extern 1 False => eapply skipn_none_contra; eassumption.

Theorem length_firstn : forall A n (ls : list A), n <= length ls -> length (firstn n ls) = n.
  induction n; destruct ls; simpl; intuition.
Qed.

Theorem length_skipn : forall A n (ls : list A), n <= length ls -> length (skipn n ls) = length ls - n.
  induction n; destruct ls; simpl; intuition.
Qed.

Theorem length_tl : forall A (ls : list A), length ls > 0 -> length (tl ls) = length ls - 1.
  destruct ls; simpl; auto.
Qed.

Theorem firstn_idem : forall A n (ls : list A), n <= length ls -> firstn n (firstn n ls) = firstn n ls.
  induction n; destruct ls; simpl; intuition; f_equal; auto.
Qed.

Theorem skipn_firstn' : forall A n (ls : list A), n <= length ls -> skipn n (firstn n ls) = nil.
  induction n; destruct ls; simpl; intuition.
Qed.

Hint Rewrite length_firstn length_skipn length_tl firstn_idem skipn_firstn' using omega : InSep.

Theorem length_cons' : forall A (x : A) ls, x = x -> length (x :: ls) = S (length ls).
  auto.
Qed.

Theorem app_length' : forall A (l l' : list A), l = l -> length (l ++ l') = length l + length l'.
  intros; apply app_length.
Qed.

Theorem length_removeLast : forall A (ls : list A), ls = ls -> length (removelast ls) = length ls - 1.
  induction ls; simpl; intuition; destruct ls; simpl in *; auto.
Qed.

Hint Rewrite length_cons' app_length' length_removeLast
  using match goal with
          | [ |- ?X = _ ] => ensureNotUnif X; reflexivity
        end : InSep.

Lemma length_remove' : forall v ls, length (remove ls v) <= length ls.
  induction ls; simpl; intuition; match goal with
                                    | [ |- context[if ?E then _ else _] ] => destruct E
                                  end; simpl; auto.
Qed.

Theorem length_remove : forall v ls n,
  n >= length ls
  -> n >= length (remove ls v).
  intros; generalize (length_remove' v ls); omega.
Qed.

Local Hint Resolve length_remove.

Local Hint Extern 1 (_ < _) => progress autorewrite with InSep; omega.
Local Hint Extern 1 (_ <= _) => progress autorewrite with InSep; omega.

Theorem inList_remove : forall n ls,
  (inList ls n = 1 /\ length ls >= 1 /\ length (remove ls n) = length ls - 1)
  \/ (inList ls n = 0 /\ length (remove ls n) = length ls).
  induction ls; simpl; intuition; match goal with
                                    | [ |- context[if ?E then _ else _] ] => destruct E
                                  end; subst; simpl in *; intuition.
Qed.

Theorem finish_remove : forall p ls v len base,
  len >= length ls
  -> ptsTo p (sz := tt) (length ls - inList ls v) :: sep (allocated (base + length ls - 1) (inList ls v))
  :: sep (allocated (base + length ls) (len - length ls)) :: nil
  ---> ptsTo p (sz := tt) (length (remove ls v)) :: sep (allocated (base + length (remove ls v)) (len - length (remove ls v))) :: nil.
  intros; destruct (inList_remove v ls) as [ [Hin [? Hlen] ] | [Hin Hlen] ]; rewrite Hin in *; rewrite Hlen in *;
    use (allocated_expose_bwd 1); sepLemma.
Qed.

Lemma finish_remove' : forall ls base p v old any,
  length ls > 0
  -> hd 0 ls = v
  -> sep (array (tl ls) base) :: ptsTo (base + (length ls - 1)) (sz := tt) any :: ptsTo p (sz := tt) (old - 1) :: nil
  ---> ptsTo p (sz := tt) (old - inList ls v) :: sep (array (remove ls v) base) :: sep (allocated (base + length ls - 1) (inList ls v)) :: nil.
  destruct ls; simpl; intros; try (elimtype False; omega);
    match goal with
      | [ |- context[if ?E then _ else _] ] => destruct E; subst; tauto || sepLemma
    end.
Qed.

Theorem finish_remove'' : forall ls v len x0,
  len >= length ls
  -> sep (allocated (x0 + Datatypes.length ls - 1) (inList ls v))
  :: sep (allocated (x0 + Datatypes.length ls) (len - Datatypes.length ls))
  :: nil ---> sep (allocated (x0 + Datatypes.length (remove ls v))
    (len - Datatypes.length (remove ls v))) :: nil.
  intros; destruct (inList_remove v ls) as [ [Hin [? Hlen] ] | [Hin Hlen] ]; rewrite Hin; rewrite Hlen;
    use (allocated_expose_bwd 1); sepLemma.
Qed.

Theorem finish_remove_len : forall ls v,
  Datatypes.length (remove ls v) = Datatypes.length ls - inList ls v.
  intros; destruct (inList_remove v ls); omega.
Qed.

Theorem finish_remove''' : forall v len v' p ls,
  0 < len
  -> len = Datatypes.length ls
  -> hd 0 ls = v'
  -> sep (array (Arrays.tl ls) p)
  :: ptsTo (sz := tt) (p + (Datatypes.length ls - 1)) v :: nil --->
  sep (array (remove ls v') p)
  :: sep (allocated (p + Datatypes.length ls - 1) (inList ls v')) :: nil.
  destruct ls; simpl in *; intuition;
    match goal with
      | [ |- context[if ?E then _ else _] ] => destruct E; sepLemma
    end.
Qed.

Hint Extern 1 (_ ---> _) => eapply finish_remove'''; eassumption.

Theorem finish_remove'''' : forall len v' x ls,
  0 < len
  -> len = Datatypes.length ls
  -> hd 0 ls = v'
  -> x - inList ls v' = x - 1.
  destruct ls; simpl in *; intuition.
Qed.

Hint Extern 1 (_ - _ = _ - _) => eapply finish_remove''''; eassumption.

Theorem remove_some : forall ls v,
  hd 0 ls <> v
  -> length ls > 0
  -> length (remove ls v) > 0.
  destruct ls; miss.
Qed.

Lemma sepDuh : forall p1 p2, p1 :: p2 :: nil ---> sep (![p1] * ![p2])%Sep :: nil.
  sepLemma.
Qed.

Local Hint Resolve finish_remove finish_remove' finish_remove'' finish_remove_len remove_some sepDuh.

Theorem arlOk : moduleOk arl.
  structured; abstract (sep; autorewrite with InSep; auto).
Qed.
