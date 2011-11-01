Require Import Arith FunctionalExtensionality.

Require Import Ideal Malloc OMaps AssociationList.


Parameter hash : nat -> nat -> nat.
Axiom hash_bound : forall hmax, hmax > 0 -> forall n, hash hmax n < hmax.
Local Hint Immediate hash_bound.

Definition only (m : map) (hmax n : nat) : map := fun k => if eq_nat_dec (hash hmax k) n then m k else None.

Module Type HTABLE.
  Parameter htableOk : map -> nat -> nat -> nat -> nat -> sprop.
  Parameter htable : map -> nat -> sprop.

  Axiom htable_fwd : forall m a, htable m a ===> Ex hmax, [< hmax > 0 >] * a ==> hmax * !{htableOk m hmax 0 hmax (a+1)}.
  Axiom htable_bwd : forall m a, Ex hmax, [< hmax > 0 >] * a ==> hmax * !{htableOk m hmax 0 hmax (a+1)} ===> htable m a.

  Axiom htableOk_empty_fwd : forall m hmax curHash len a, len = 0
    -> htableOk m hmax curHash len a ===> emp.
  Axiom htableOk_empty_bwd : forall m hmax curHash len a, len = 0
    -> emp ===> htableOk m hmax curHash len a.

  Axiom htableOk_nonempty_fwd : forall m hmax curHash len a, len > 0
    -> htableOk m hmax curHash len a ===> Ex a', a ==> a' * !{alist (only m hmax curHash) a'} * !{htableOk m hmax (S curHash) (len-1) (a+1)}.
  Axiom htableOk_nonempty_bwd : forall m hmax curHash len a, len > 0
    -> Ex a', a ==> a' * !{alist (only m hmax curHash) a'} * !{htableOk m hmax (S curHash) (len-1) (a+1)} ===> htableOk m hmax curHash len a.

  Axiom htableOk_mid_fwd : forall n m hmax curHash len a, n < len
    -> htableOk m hmax curHash len a
    ===> Ex a', !{htableOk m hmax curHash n a} * (a+n) ==> a' * !{alist (only m hmax (curHash+n)) a'}
    * !{htableOk m hmax (curHash+n+1) (len-n-1) (a+n+1)}.
  Axiom htableOk_mid_bwd : forall n m hmax curHash len a, n < len
    -> Ex a', !{htableOk m hmax curHash n a} * (a+n) ==> a' * !{alist (only m hmax (curHash+n)) a'} * !{htableOk m hmax (curHash+n+1) (len-n-1) (a+n+1)}
    ===> htableOk m hmax curHash len a.

  Axiom htableOk_mid_fwd_change : forall n m m' hmax curHash len a, n < len
    -> (forall k, k <> curHash + n -> only m' hmax k = only m hmax k)
    -> htableOk m hmax curHash len a
    ===> Ex a', !{htableOk m' hmax curHash n a} * (a+n) ==> a' * !{alist (only m hmax (curHash+n)) a'}
    * !{htableOk m' hmax (curHash+n+1) (len-n-1) (a+n+1)}.
End HTABLE.

Module HTable : HTABLE.
  Open Scope Sep_scope.

  Fixpoint htableOk (m : map) (hmax curHash len a : nat) : sprop :=
    match len with
      | O => emp
      | S len' => Ex a', a ==> a' * !{alist (only m hmax curHash) a'} * !{htableOk m hmax (S curHash) len' (a+1)}
    end.

  Definition htable (m : map) (a : nat) : sprop := Ex hmax, [< hmax > 0 >] * a ==> hmax * !{htableOk m hmax 0 hmax (a+1)}.

  Theorem htable_fwd : forall m a, htable m a ===> Ex hmax, [< hmax > 0 >] * a ==> hmax * !{htableOk m hmax 0 hmax (a+1)}.
    sepLemma.
  Qed.

  Theorem htable_bwd : forall m a, Ex hmax, [< hmax > 0 >] * a ==> hmax * !{htableOk m hmax 0 hmax (a+1)} ===> htable m a.
    sepLemma.
  Qed.

  Theorem htableOk_empty_fwd : forall m hmax curHash len a, len = 0
    -> htableOk m hmax curHash len a ===> emp.
    sepLemma.
  Qed.

  Theorem htableOk_empty_bwd : forall m hmax curHash len a, len = 0
    -> emp ===> htableOk m hmax curHash len a.
    sepLemma.
  Qed.

  Theorem htableOk_nonempty_fwd : forall m hmax curHash len a, len > 0
    -> htableOk m hmax curHash len a ===> Ex a', a ==> a' * !{alist (only m hmax curHash) a'} * !{htableOk m hmax (S curHash) (len-1) (a+1)}.
    destruct 1; sepLemma.
  Qed.

  Theorem htableOk_nonempty_bwd : forall m hmax curHash len a, len > 0
    -> Ex a', a ==> a' * !{alist (only m hmax curHash) a'} * !{htableOk m hmax (S curHash) (len-1) (a+1)} ===> htableOk m hmax curHash len a.
    destruct 1; sepLemma.
  Qed.

  Lemma htableOk_weaken : forall m m' hmax len curHash a,
    (forall k, curHash <= k < curHash + len -> only m' hmax k = only m hmax k)
    -> htableOk m hmax curHash len a ===> !{htableOk m' hmax curHash len a}.
    induction len; sepLemma.
  Qed.

  Lemma htableOk_mid_fwd' : forall m m' hmax n curHash len a, n < len
    -> (forall k, k <> curHash + n -> only m' hmax k = only m hmax k)
    -> htableOk m hmax curHash len a
    ===> Ex a', !{htableOk m' hmax curHash n a} * (a+n) ==> a' * !{alist (only m hmax (curHash+n)) a'}
    * !{htableOk m' hmax (curHash+n+1) (len-n-1) (a+n+1)}.
    intros m m'; use (htableOk_weaken m m'); induction n; destruct len; simpl; intros; try (elimtype False; omega); sepLemma; auto.
  Qed.

  Lemma htableOk_mid_fwd_change : forall n m m' hmax curHash len a, n < len
    -> (forall k, k <> curHash + n -> only m' hmax k = only m hmax k)
    -> htableOk m hmax curHash len a
    ===> Ex a', !{htableOk m' hmax curHash n a} * (a+n) ==> a' * !{alist (only m hmax (curHash+n)) a'}
    * !{htableOk m' hmax (curHash+n+1) (len-n-1) (a+n+1)}.
    intros; apply htableOk_mid_fwd'; auto.
  Qed.

  Lemma htableOk_mid_fwd : forall n m hmax curHash len a, n < len
    -> htableOk m hmax curHash len a
    ===> Ex a', !{htableOk m hmax curHash n a} * (a+n) ==> a' * !{alist (only m hmax (curHash+n)) a'}
    * !{htableOk m hmax (curHash+n+1) (len-n-1) (a+n+1)}.
    intros; apply htableOk_mid_fwd'; auto.
  Qed.

  Theorem htableOk_mid_bwd : forall n m hmax curHash len a, n < len
    -> Ex a', !{htableOk m hmax curHash n a} * (a+n) ==> a' * !{alist (only m hmax (curHash+n)) a'} * !{htableOk m hmax (curHash+n+1) (len-n-1) (a+n+1)}
    ===> htableOk m hmax curHash len a.
    induction n; destruct len; simpl; intros; try (elimtype False; omega); sepLemma.
  Qed.
End HTable.

Import HTable.
Export HTable.

Local Hint Immediate htable_fwd : Forward.
Local Hint Immediate htable_bwd : Backward.

Definition hashS : state -> PropX pc state := st ~> Ex fr,
  ![ ![fr] ] st
  /\ st#Rret @@ (st' ~> [< st'#Rsp = st#Rsp /\ st'#R0 = hash st#R0 st#R1 >]
    /\ ![ ![fr] ] st').

Definition constructorS : state -> PropX pc state := st ~> Ex fr, Ex ss, [< ss >= 5 /\ st#R0 > 0 >]
  /\ ![ !{mallocHeap 0} * !{allocated st#Rsp ss} * ![fr] ] st
  /\ st#Rret @@ (st' ~> [< st'#Rsp = st#Rsp >]
    /\ ![ !{mallocHeap 0} * !{allocated st#Rsp ss} * !{htable empty st'#R0} * ![fr] ] st').

Definition notStacky (a : nat) := True.

Hint Extern 1 (notStacky ?a) => match a with
                                  | context[Rsp] => fail 1
                                  | _ => constructor
                                end.

Theorem allocated_expose_fwd_notStacky : forall n base len, n <= len
  -> notStacky base
  -> allocated base len ===> !{allocated base (n + (len - n))}.
  use allocated_expose_fwd; sepLemma.
Qed.

Theorem allocated_expose_bwd_notStacky : forall n base len, n <= len
  -> notStacky base
  -> !{allocated base (n + (len - n))} ===> allocated base len.
  use allocated_expose_bwd; sepLemma.
Qed.

Definition change_add (h k v : nat) (m : map) := htableOk_mid_fwd_change h m (add m k v).
Definition change_del (h k : nat) (m : map) := htableOk_mid_fwd_change h m (del m k).

Definition htab := bimport [[ "malloc" @ [mallocS], "hash" @ [hashS],
                              "AssociationList" @ [AssociationList.constructorS],
                              "containsKey" @ [containsKeyS alist 0], "get" @ [getS alist 0],
                              "put" @ [putS alist 4], "remove" @ [removeS alist 4], "isEmpty" @ [isEmptyS alist 0] ]] bmodule {{
  bfunction "Hashtable" [constructorS] {
    $[Rsp] <- Rret;;
    $[Rsp+1] <- R0;;

    R1 <- R0-1;;
    R0 <- 0;;

    Use [allocated_expose_fwd 4];;
    Use [allocated_expose_fwd_notStacky 1];;

    Call "malloc"
    [st ~> Ex fr, Ex ss, Ex ret, Ex sz, Ex junk1, Ex junk2, [< ss >= 5 /\ sz > 0 >]
      /\ ![ !{mallocHeap 0} * st#Rsp ==> ret * (st#Rsp+1) ==> sz * (st#Rsp+2) ==> junk1 * (st#Rsp+3) ==> junk2 * !{allocated (st#Rsp+4) (ss-4)}
        * !{allocated st#R0 (1+sz)} * ![fr] ] st
      /\ ret @@ (st' ~> [< st'#Rsp = st#Rsp /\ st'#R0 = st#R0 >]
        /\ ![ !{mallocHeap 0} * !{allocated st#Rsp ss} * st#R0 ==> sz * !{htableOk empty sz 0 sz (st#R0+1)} * ![fr] ] st')];;

    $[R0] <- $[Rsp+1];;
    $[Rsp+2] <- R0;;
    $[Rsp+3] <- 0;;

    [st ~> Ex fr, Ex ss, Ex ret, Ex sz, Ex base, Ex i, [< ss >= 5 /\ sz > 0 /\ i <= sz >]
      /\ ![ !{mallocHeap 0} * st#Rsp ==> ret * (st#Rsp+1) ==> sz * (st#Rsp+2) ==> base * (st#Rsp+3) ==> i * !{allocated (st#Rsp+4) (ss-4)}
        * !{allocated (base+1+i) (sz-i)} * ![fr] ] st
      /\ ret @@ (st' ~> [< st'#Rsp = st#Rsp /\ st'#R0 = base >]
        /\ ![ !{mallocHeap 0} * !{allocated st#Rsp ss} * !{htableOk empty sz i (sz - i) (base+1+i)} * ![fr] ] st')]
    While ($[Rsp+3] < $[Rsp+1]) {
      Rsp <- Rsp+4;;

      Use [allocated_expose_fwd_notStacky 1];;
      Use [allocated_expose_bwd_notStacky 1];;

      Call "AssociationList"
      [st ~> Ex fr, Ex ss, Ex ret, Ex sz, Ex base, Ex i, [< ss >= 5 /\ sz > 0 /\ i < sz /\ st#Rsp >= 4 >]
        /\ ![ !{mallocHeap 0} * (st#Rsp-4) ==> ret * (st#Rsp-3) ==> sz * (st#Rsp-2) ==> base * (st#Rsp-1) ==> i * !{allocated st#Rsp (ss-4)}
          * !{allocated (base+1+i) (sz-i)} * !{alist empty st#R0} * ![fr] ] st
        /\ ret @@ (st' ~> [< st'#Rsp = st#Rsp-4 /\ st'#R0 = base >]
          /\ ![ !{mallocHeap 0} * !{allocated st'#Rsp ss} * !{htableOk empty sz i (sz - i) (base+1+i)} * ![fr] ] st')];;

      Rsp <- Rsp-4;;
      R2 <- $[Rsp+2] + $[Rsp+3];;
      $[R2+1] <- R0;;
      $[Rsp+3] <- $[Rsp+3] + 1;;

      Use [htableOk_nonempty_bwd];;
      Use [allocated_expose_fwd_notStacky 1]
    };;

    Use [allocated_expose_bwd 4];;
    Use [allocated0_fwd];;
    Use [htableOk_empty_bwd];;

    R0 <- $[Rsp+2];;
    Goto $[Rsp]
  }

  with bfunction "hcontainsKey" [containsKeyS htable 3] {
    $[Rsp] <- Rret;;
    $[Rsp+1] <- R0;;
    $[Rsp+2] <- R1;;

    R0 <- $[R0];;

    Use [allocated_expose_fwd 3];;

    Call "hash"
    [st ~> Ex fr, Ex ss, Ex m, Ex ret, Ex base, Ex hmax, Ex v, [< ss >= 3 /\ st#R0 = hash hmax v /\ hmax > 0 >]
      /\ ![ st#Rsp ==> ret * (st#Rsp+1) ==> base * (st#Rsp+2) ==> v * !{allocated (st#Rsp+3) (ss-3)}
        * base ==> hmax * !{htableOk m hmax 0 hmax (base+1)} * ![fr] ] st
      /\ ret @@ (st' ~> [< st'#R0 = (match m v with None => 0 | Some _ => 1 end) /\ st'#Rsp = st#Rsp >]
        /\ ![ !{allocated st#Rsp ss} * base ==> hmax * !{htableOk m hmax 0 hmax (base+1)} * ![fr] ] st')];;

    Use [allocated_expose_fwd 3];;
    Use [allocated_expose_bwd 3];;
    Use st [htableOk_mid_fwd st#R0];;
    Use st [htableOk_mid_bwd st#R0];;

    R0 <- $[Rsp+1] + R0;;
    R0 <- $[R0+1];;
    R1 <- $[Rsp+2];;
    Rret <- $[Rsp];;

    Goto "containsKey"
  }

  with bfunction "hget" [getS htable 3] {
    $[Rsp] <- Rret;;
    $[Rsp+1] <- R0;;
    $[Rsp+2] <- R1;;

    R0 <- $[R0];;

    Use [allocated_expose_fwd 3];;

    Call "hash"
    [st ~> Ex fr, Ex ss, Ex m, Ex ret, Ex base, Ex hmax, Ex v, [< ss >= 3 /\ st#R0 = hash hmax v /\ hmax > 0 >]
      /\ ![ st#Rsp ==> ret * (st#Rsp+1) ==> base * (st#Rsp+2) ==> v * !{allocated (st#Rsp+3) (ss-3)}
        * base ==> hmax * !{htableOk m hmax 0 hmax (base+1)} * ![fr] ] st
      /\ ret @@ (st' ~> [< st'#R0 = (match m v with None => 0 | Some v => v end) /\ st'#Rsp = st#Rsp >]
        /\ ![ !{allocated st#Rsp ss} * base ==> hmax * !{htableOk m hmax 0 hmax (base+1)} * ![fr] ] st')];;

    Use [allocated_expose_fwd 3];;
    Use [allocated_expose_bwd 3];;
    Use st [htableOk_mid_fwd st#R0];;
    Use st [htableOk_mid_bwd st#R0];;

    R0 <- $[Rsp+1] + R0;;
    R0 <- $[R0+1];;
    R1 <- $[Rsp+2];;
    Rret <- $[Rsp];;

    Goto "get"
  }

  with bfunction "hput" [putS htable 4] {
    $[Rsp] <- Rret;;
    $[Rsp+1] <- R0;;
    $[Rsp+2] <- R1;;
    $[Rsp+3] <- R2;;

    R0 <- $[R0];;

    Use [allocated_expose_fwd 4];;

    Call "hash"
    [st ~> Ex fr, Ex ss, Ex m, Ex ret, Ex base, Ex hmax, Ex k, Ex v, [< ss >= 4 /\ st#R0 = hash hmax k /\ hmax > 0 >]
      /\ ![ !{mallocHeap 0} * st#Rsp ==> ret * (st#Rsp+1) ==> base * (st#Rsp+2) ==> k * (st#Rsp+3) ==> v * !{allocated (st#Rsp+4) (ss-4)}
        * base ==> hmax * !{htableOk m hmax 0 hmax (base+1)} * ![fr] ] st
      /\ ret @@ (st' ~> [< st'#Rsp = st#Rsp >]
        /\ ![ !{mallocHeap 0} * !{allocated st#Rsp ss} * base ==> hmax * !{htableOk (add m k v) hmax 0 hmax (base+1)} * ![fr] ] st')];;

    Use [allocated_expose_fwd 4];;
    Use [allocated_expose_bwd 4];;
    Use st [change_add st#R0 st.[st#Rsp+2] st.[st#Rsp+3] ];;
    Use st [htableOk_mid_bwd st#R0];;

    R0 <- $[Rsp+1] + R0;;
    R0 <- $[R0+1];;
    R1 <- $[Rsp+2];;
    R2 <- $[Rsp+3];;
    Rret <- $[Rsp];;

    Goto "put"
  }

  with bfunction "hremove" [removeS htable 4] {
    $[Rsp] <- Rret;;
    $[Rsp+1] <- R0;;
    $[Rsp+2] <- R1;;

    R0 <- $[R0];;

    Use [allocated_expose_fwd 4];;

    Call "hash"
    [st ~> Ex fr, Ex ss, Ex m, Ex ret, Ex base, Ex hmax, Ex k, Ex junk, [< ss >= 4 /\ st#R0 = hash hmax k /\ hmax > 0 >]
      /\ ![ !{mallocHeap 0} * st#Rsp ==> ret * (st#Rsp+1) ==> base * (st#Rsp+2) ==> k * (st#Rsp+3) ==> junk * !{allocated (st#Rsp+4) (ss-4)}
        * base ==> hmax * !{htableOk m hmax 0 hmax (base+1)} * ![fr] ] st
      /\ ret @@ (st' ~> [< st'#Rsp = st#Rsp >]
        /\ ![ !{mallocHeap 0} * !{allocated st#Rsp ss} * base ==> hmax * !{htableOk (del m k) hmax 0 hmax (base+1)} * ![fr] ] st')];;

    Use [allocated_expose_fwd 4];;
    Use [allocated_expose_bwd 4];;
    Use st [change_del st#R0 st.[st#Rsp+2] ];;
    Use st [htableOk_mid_bwd st#R0];;

    R0 <- $[Rsp+1] + R0;;
    R0 <- $[R0+1];;
    R1 <- $[Rsp+2];;
    Rret <- $[Rsp];;

    Goto "remove"
  }

  with bfunction "hisEmpty" [isEmptyS htable 3] {
    $[Rsp] <- Rret;;
    $[Rsp+1] <- $[R0];;
    $[Rsp+2] <- R0+1;;

    Use [allocated_expose_fwd 3];;

    [st ~> Ex fr, Ex ss, Ex m, Ex ret, Ex sz, Ex arr, Ex hmax, Ex curHash, [< ss >= 3 >]
      /\ ![ st#Rsp ==> ret * (st#Rsp+1) ==> sz * (st#Rsp+2) ==> arr * !{allocated (st#Rsp+3) (ss-3)}
        * !{htableOk m hmax curHash sz arr} * ![fr] ] st
      /\ ret @@ (st' ~> [< match st'#R0 with O => m <> empty | _ => forall h, curHash <= h < curHash + sz -> only m hmax h = empty end
        /\ st'#Rsp = st#Rsp >]
        /\ ![ !{allocated st#Rsp ss} * !{htableOk m hmax curHash sz arr} * ![fr] ] st')]
    While (0 < $[Rsp+1]) {
      Use [htableOk_nonempty_fwd];;
      Use [htableOk_nonempty_fwd];;
      Use [htableOk_nonempty_bwd];;
      Use [allocated_expose_fwd 3];;
      Use st [allocated_expose_bwd 3 st#Rsp];;

      R0 <- $[Rsp+2];;
      R0 <- $[R0];;
      Rsp <- Rsp+3;;

      Call "isEmpty"
      [st ~> Ex fr, Ex ss, Ex m, Ex ret, Ex sz, Ex arr, Ex hmax, Ex curHash, [< ss >= 3 /\ sz > 0 /\ st#Rsp >= 3
        /\ match st#R0 with O => only m hmax curHash <> empty | _ => only m hmax curHash = empty end>]
      /\ ![ (st#Rsp-3) ==> ret * (st#Rsp-2) ==> sz * (st#Rsp-1) ==> arr * !{allocated st#Rsp (ss-3)}
        * !{htableOk m hmax curHash sz arr} * ![fr] ] st
      /\ ret @@ (st' ~> [< match st'#R0 with O => m <> empty | _ => forall h, curHash <= h < curHash + sz -> only m hmax h = empty end
        /\ st'#Rsp = st#Rsp-3 >]
        /\ ![ !{allocated st'#Rsp ss} * !{htableOk m hmax curHash sz arr} * ![fr] ] st')];;
      Rsp <- Rsp-3;;

      If (R0 == 0) {
        Use [allocated_expose_bwd 3];;
        Goto $[Rsp]
      } else {
        $[Rsp+1] <- $[Rsp+1] - 1;;
        $[Rsp+2] <- $[Rsp+2] + 1;;
        Use [htableOk_nonempty_fwd];;
        Use [htableOk_nonempty_bwd]
      }
    };;

    R0 <- 1;;
    Use [allocated_expose_bwd 3];;
    Goto $[Rsp]
  }
}}.

Ltac maps := unfold only; OMaps.maps.

Theorem only_empty : forall hmax n, n = n -> only empty hmax n = empty.
  maps.
Qed.

Hint Rewrite only_empty using match goal with
                                | [ |- ?U = _ ] => ensureNotUnif U; reflexivity
                              end : InSep.

Theorem only_noloss : forall h hmax n m,
  h = hash hmax n
  -> only m hmax h n = m n.
  maps.
Qed.

Theorem add_only : forall m k v hmax h, h = hash hmax k -> add (only m hmax h) k v = only (add m k v) hmax h.
  maps.
Qed.

Theorem del_only : forall m k hmax h, h = hash hmax k -> del (only m hmax h) k = only (del m k) hmax h.
  maps.
Qed.

Hint Rewrite only_noloss add_only del_only using assumption : InSep.

Hint Extern 1 (?X < _) => match goal with
                            | [ H : X = _ |- _ ] => rewrite H; apply hash_bound; omega
                          end.

Hint Extern 1 (only _ _ _ = _) => maps.

Theorem isEmpty_view : forall m hmax n, hmax > 0
  -> match n with
       | 0 => m = empty -> False
       | S _ => forall h : nat, 0 <= h < hmax -> only m hmax h = empty
     end
  -> match n with
       | 0 => m = empty -> False
       | S _ => m = empty
     end.
  destruct n; intuition; let k := fresh "k" in extensionality k;
    match goal with
      | [ H : _ |- _ ] => rewrite <- (H (hash hmax k)) by auto; maps
    end.
Qed.

Theorem isEmpty_coalesce : forall n1 P m hmax curHash n2 sz,
  n1 <> 0
  -> match n1 with
       | 0 => P
       | S _ => only m hmax curHash = empty
     end
  -> match n2 with
       | 0 => m = empty -> False
       | S _ => forall h, S curHash <= h < S (curHash + (sz - 1)) -> only m hmax h = empty
     end
  -> match n2 with
       | 0 => m = empty -> False
       | S _ => forall h, curHash <= h < curHash + sz -> only m hmax h = empty
     end.
  destruct n1; intuition; destruct n2; intuition; destruct (eq_nat_dec h curHash); subst; auto.
Qed.

Theorem isEmpty_foundOne : forall m hmax h v P,
  only m hmax h <> empty
  -> v = 0
  -> match v with
       | 0 => m <> empty
       | S _ => P
     end.
  intros ? ? ? ? ? ? H; rewrite H; unfold not; intuition; match goal with
                                                            | [ H : _ |- _ ] => apply H; maps
                                                          end.
Qed.

Hint Extern 1 => solve [ eapply isEmpty_view; eauto ].
Hint Extern 1 => solve [ eapply isEmpty_coalesce; eauto ].
Hint Extern 1 => solve [ eapply isEmpty_foundOne; eauto ].

Theorem htabOk : moduleOk htab.
  structured; abstract (sep; auto).
Qed.
