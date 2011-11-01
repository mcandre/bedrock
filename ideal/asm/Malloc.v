Require Import Arith.

Require Import Ideal.

Lemma S_le : forall n m,
  S n <= m
  -> exists m', m = S m' /\ n <= m'.
  destruct m; eauto.
Qed.

Theorem allocated_split : forall len' len base,
  len' <= len
  -> allocated base len
  ===> !{allocated base len'} * !{allocated (base + len') (len - len')}.
  induction len'; [ | intros ? ? H; apply S_le in H ]; sepLemma.
Qed.

Module Type FREE_LIST.
  Parameter freeList : list nat -> nat -> nat -> sprop.

  Axiom freeList_create : forall p,
    (Ex sz, [< p <> 0 >] * p ==> 0 * (p+1) ==> sz * !{allocated (p+2) sz})
    ===> freeList (p :: nil) p 0.

  Axiom freeList_cons_bwd : forall fl flh flt,
    ([< flh <> 0 >] * Ex p, Ex sz, flh ==> p * (flh+1) ==> sz
      * !{allocated (flh+2) sz} * !{freeList fl p flt})
    ===> freeList (flh :: fl) flh flt.

  Axiom freeList_nonempty_fwd : forall fl flh flt,
    flh <> flt
    -> freeList fl flh flt
    ===> Ex p, Ex sz, Ex fl', [< fl = flh :: fl' >] * flh ==> p * (flh+1) ==> sz
    * !{allocated (flh+2) sz} * !{freeList fl' p flt}.

  Axiom freeList_nonempty_bwd : forall fl p,
    (Ex flh, Ex sz, [< p <> 0 >] * p ==> flh * (p+1) ==> sz
    * !{allocated (p+2) sz} * !{freeList fl flh 0})
    ===> freeList (p :: fl) p 0.

  Axiom freeList_split : forall fl flh flt,
    freeList fl flh flt
    ===> !{freeList nil flh flh} * !{freeList fl flh flt}.

  Axiom freeList_nil_bwd : forall flh,
    emp
    ===> freeList nil flh flh.

  Axiom freeList_neq : forall fl flh flt,
    flt <> 0
    -> freeList fl flh flt
    ===> [< flh <> 0 >] * !{freeList fl flh flt}.

  Axiom freeList_middle : forall flt fl1 fl2 p sz flh,
    flt <> 0
    -> !{freeList fl1 flh flt} * flt ==> p * (flt+1) ==> sz
    * !{allocated (flt+2) sz} * !{freeList fl2 p 0}
    ===> freeList (fl1 ++ flt :: fl2) flh 0.

  Axiom freeList_end : forall flt fl flh p sz,
    flt <> 0
    -> !{freeList fl flh flt} * flt ==> p * (flt+1) ==> sz * !{allocated (flt+2) sz}
    ===> freeList (fl ++ flt :: nil) flh p.
End FREE_LIST.

Module FreeList : FREE_LIST.
  Open Scope Sep_scope.

  Fixpoint freeList (fl : list nat) (flh flt : nat) : sprop :=
    match fl with
      | nil => [< flh = flt >]
      | p :: fl => [< flh <> 0 /\ flh = p >] * Ex p', Ex sz, flh ==> p' * (flh+1) ==> sz
        * !{allocated (flh+2) sz} * !{freeList fl p' flt}
    end.

  Theorem freeList_create : forall p,
    (Ex sz, [< p <> 0 >] * p ==> 0 * (p+1) ==> sz * !{allocated (p+2) sz})
    ===> freeList (p :: nil) p 0.
    sepLemma; auto.
  Qed.

  Theorem freeList_cons_bwd : forall fl flh flt,
    ([< flh <> 0 >] * Ex p, Ex sz, flh ==> p * (flh+1) ==> sz
    * !{allocated (flh+2) sz} * !{freeList fl p flt})
    ===> freeList (flh :: fl) flh flt.
    sepLemma.
  Qed.

  Theorem freeList_nonempty_fwd : forall fl flh flt,
    flh <> flt
    -> freeList fl flh flt
    ===> Ex p', Ex sz, Ex fl', [< fl = flh :: fl' >] * flh ==> p' * (flh+1) ==> sz
    * !{allocated (flh+2) sz} * !{freeList fl' p' flt}.
    destruct fl; sepLemma.
  Qed.

  Theorem freeList_nonempty_bwd : forall fl p,
    (Ex flh, Ex sz, [< p <> 0 >] * p ==> flh * (p+1) ==> sz
    * !{allocated (p+2) sz} * !{freeList fl flh 0})
    ===> freeList (p :: fl) p 0.
    sepLemma.
  Qed.

  Theorem freeList_split : forall fl flh flt,
    freeList fl flh flt
    ===> !{freeList nil flh flh} * !{freeList fl flh flt}.
    sepLemma.
  Qed.

  Lemma freeList_nil_bwd : forall flh,
    emp
    ===> freeList nil flh flh.
    sepLemma.
  Qed.

  Lemma freeList_neq : forall fl flh flt,
    flt <> 0
    -> freeList fl flh flt
    ===> [< flh <> 0 >] * !{freeList fl flh flt}.
    destruct fl; sepLemma.
  Qed.

  Lemma freeList_middle' : forall fl2 flt p sz fl1 flh,
    flt <> 0
    -> !{freeList fl1 flh flt} * flt ==> p * (flt+1) ==> sz
    * !{allocated (flt+2) sz} * !{freeList fl2 p 0}
    ===> freeList (fl1 ++ flt :: fl2) flh 0.
    induction fl1; sepLemma.
  Qed.

  Theorem freeList_middle : forall flt fl1 fl2 p sz flh,
    flt <> 0
    -> !{freeList fl1 flh flt} * flt ==> p * (flt+1) ==> sz
    * !{allocated (flt+2) sz} * !{freeList fl2 p 0}
    ===> freeList (fl1 ++ flt :: fl2) flh 0.
    intros; apply freeList_middle'; auto.
  Qed.

  Lemma freeList_end' : forall flt p sz fl flh,
    flt <> 0
    -> !{freeList fl flh flt} * flt ==> p * (flt+1) ==> sz * !{allocated (flt+2) sz}
    ===> freeList (fl ++ flt :: nil) flh p.
    induction fl; sepLemma.
  Qed.

  Theorem freeList_end : forall flt fl flh p sz,
    flt <> 0
    -> !{freeList fl flh flt} * flt ==> p * (flt+1) ==> sz * !{allocated (flt+2) sz}
    ===> freeList (fl ++ flt :: nil) flh p.
    intros; apply freeList_end'; auto.
  Qed.
End FreeList.

Import FreeList.
Export FreeList.

Module Type MALLOC_HEAP.
  Parameter mallocHeap : nat -> sprop.

  Axiom mallocHeap_fwd : forall p, mallocHeap p ===> Ex fl, Ex flh, p ==> flh * !{freeList fl flh 0}.
  Axiom mallocHeap_bwd : forall p, (Ex fl, Ex flh, p ==> flh * !{freeList fl flh 0}) ===> mallocHeap p.
End MALLOC_HEAP.

Module MallocHeap : MALLOC_HEAP.
  Open Scope Sep_scope.

  Definition mallocHeap p : sprop :=
    Ex fl, Ex flh, p ==> flh * !{freeList fl flh 0}.

  Theorem mallocHeap_fwd : forall p, mallocHeap p ===> Ex fl, Ex flh, p ==> flh * !{freeList fl flh 0}.
    sepLemma.
  Qed.

  Theorem mallocHeap_bwd : forall p, (Ex fl, Ex flh, p ==> flh * !{freeList fl flh 0}) ===> mallocHeap p.
    sepLemma.
  Qed.
End MallocHeap.

Import MallocHeap.
Export MallocHeap.

Definition initHeapS : state -> PropX pc state := st ~> Ex fr, ![ !{allocated st#R0 (st#R1+3)} * ![fr] ] st
  /\ st#Rret @@ (st' ~> [< st'#Rsp = st#Rsp >] /\ ![ !{mallocHeap st#R0} * ![fr] ] st').

Definition mallocS : state -> PropX pc state := st ~> Ex fr, ![ !{mallocHeap st#R0} * ![fr] ] st
  /\ st#Rret @@ (st' ~> [< st'#R0 <> 0 /\ st'#Rsp = st#Rsp >]
    /\ ![ !{allocated st'#R0 (st#R1+2)} * !{mallocHeap st#R0} * ![fr] ] st').

Definition freeS : state -> PropX pc state := st ~>
  Ex fr, ![ !{mallocHeap st#R0} * !{allocated st#R1 (st#R2+2)} * ![fr] ] st
  /\ [< st#R1 <> 0 >]
  /\ st#Rret @@ (st' ~> [< st'#Rsp = st#Rsp >] /\ ![ !{mallocHeap st#R0} * ![fr] ] st').

Definition malloc := bmodule {{
  bfunction "initHeap" [initHeapS] {
    Use [allocated_expose_fwd 3];;
    Use [freeList_create];;
    $[R0] <- R0 + 1;;
    $[R0+1] <- 0;;
    $[R0+2] <- R1;;
    Goto Rret
  }
  with bfunction "free" [freeS] {
    Use [allocated_expose_fwd 2];;
    Use [freeList_cons_bwd];;
    $[R1] <- $[R0];;
    $[R1+1] <- R2;;
    $[R0] <- R1;;
    Goto Rret
  }
  with bfunction "malloc" [mallocS] {
    R2 <- $[R0];;
    If (R2 == 0) {
      Halt (* Out of memory! *)
    } else {
      If ($[R2+1] < R1) {
        (* The first free list block isn't big enough. *)
        Skip
      } else {
        If ($[R2+1] == R1) {
          (* The current free list block is an exact size match for this
             request. *)
          Use [freeList_nonempty_fwd];;
          Use [allocated_expose_bwd 2];;

          $[R0] <- $[R2];;
          R0 <- R2;;
          Goto Rret
        } else {
          R3 <- R1 + 2;;
          If ($[R2+1] < R3) {
            (* Not an exact match, but not enough memory left over to split out a
               smaller free list block after this one. *)
            Skip
          } else {
            (* Split this free block into two.  The caller gets the first part,
               and the free list keeps the second part. *)
            Use [freeList_nonempty_fwd];;
            Use st [allocated_split st#R1];;
            Use st [allocated_expose_fwd_plus 2 st#R1];;
            Use [freeList_nonempty_bwd];;
            Use st [allocated_expose_bwd_len 2 (st#R1 + 2)];;

            R3 <- R2 + R1;;
            R3 <- R3 + 2;;
            $[R3] <- $[R2];;
            R4 <- $[R2+1] - R1;;
            $[R3+1] <- R4 - 2;;
            $[R0] <- R3;;
            R0 <- R2;;
            Goto Rret
          }
        }
      };;

      (* The first free list block isn't big enough.  Move on to the next one.
         In this loop, R1 stores the current list position, and R2 stores its
         predecessor. *)
      Use [freeList_nonempty_fwd];;
      Use [freeList_nil_bwd];;

      R3 <- R2;;
      R2 <- $[R2];;
      [ st ~> Ex fr, Ex flh, Ex Lpre, Ex Lpost,
        ![ st#R0 ==> flh * !{freeList Lpre flh st#R3}
          * (Ex sz, st#R3 ==> st#R2 * (st#R3+1) ==> sz * !{allocated (st#R3+2) sz})
          * !{freeList Lpost st#R2 0} * ![fr] ] st
        /\ [< st#R3 <> 0 >]
        /\ st#Rret @@ (st' ~> [< st'#R0 <> 0 /\ st'#Rsp = st#Rsp >]
          /\ ![ !{allocated st'#R0 (st#R1+2)} * !{mallocHeap st#R0} * ![fr] ] st') ]
      While (R2 != 0) {
        If ($[R2+1] < R1) {
          (* This free list block isn't big enough.  Move on to the next one. *)
          Skip
        } else {
          If ($[R2+1] == R1) {
            (* The current free list block is an exact size match for this
               request. *)
            Use [freeList_nonempty_fwd];;
            Use [allocated_expose_bwd 2];;
            Use st [freeList_middle st#R3];;

            $[R3] <- $[R2];;
            R0 <- R2;;
            Goto Rret
          } else {
            R4 <- R1 + 2;;
            If ($[R2+1] < R4) {
              (* Not an exact match, but not enough memory left over to split out a
                 smaller free list block after this one. *)
              Skip
            } else {
              (* Split this free block into two.  The caller gets the first part,
                 and the free list keeps the second part. *)
              Use st [allocated_split st#R1];;
              Use [freeList_nonempty_fwd];;
              Use st [allocated_expose_fwd 2 (st#R2 + 2 + st#R1)]%nat;;
              Use [allocated_expose_bwd 2];;
              Use st [freeList_middle st#R3];;
              Use [freeList_nonempty_bwd];;

              R4 <- R2 + R1;;
              R4 <- R4 + 2;;
              $[R3] <- R4;;
              $[R4] <- $[R2];;
              R5 <- $[R2+1] - R1;;
              $[R4+1] <- R5 - 2;;
              R0 <- R2;;
              Goto Rret
            }
          }
        };;

        Use [freeList_nonempty_fwd];;
        Use st [freeList_end st#R3];;
      
        R3 <- R2;;
        R2 <- $[R2]
      };;

      Halt (* Out of memory! *)      
    }
  }
}}.

Section mallocOk.
  Hint Immediate mallocHeap_fwd : Forward.
  Hint Immediate mallocHeap_bwd : Backward.

  Theorem mallocOk : moduleOk malloc.
    structured; abstract (sep; auto).
  Qed.
End mallocOk.
