Require Import Arith.
Require Import x86.examples.Allocated.
Require Import x86.
Require Import x86.WordView.
Require Import x86.examples.Null.
Require Import x86.examples.MallocI.

Set Implicit Arguments.
Set Strict Implicit.

Module Type FREE_LIST.
  Parameter freeList : list SepArg.addr -> SepArg.addr -> SepArg.addr -> sprop.

  Axiom freeList_create : forall (p : SepArg.addr),
    (Ex sz, [< p <> NULL >] * p ==> ##0 * (p^+##8) ==> sz * !{allocated (p^+##16) (wordToNat sz)})
    ===> freeList (p :: nil) p (##0).

  Axiom freeList_cons_bwd : forall fl flh flt,
    ([< flh <> NULL >] * Ex p, Ex sz, flh ==> p * (flh^+##8) ==> sz
      * !{allocated (flh^+##16) (wordToNat sz)} * !{freeList fl p flt})
    ===> freeList (flh :: fl) flh flt.

  Axiom freeList_nonempty_fwd : forall fl flh flt,
    flh <> flt
    -> freeList fl flh flt
    ===> Ex p, Ex sz, Ex fl', [< fl = flh :: fl' >] * flh ==> p * (flh^+##8) ==> sz
    * !{allocated (flh^+##16) (wordToNat sz)} * !{freeList fl' p flt}.

  Axiom freeList_nonempty_bwd : forall fl p,
    (Ex flh, Ex sz, [< p <> NULL >] * p ==> flh * (p^+##8) ==> sz
    * !{allocated (p^+##16) (wordToNat sz)} * !{freeList fl flh (##0)})
    ===> freeList (p :: fl) p (##0).

  Axiom freeList_split : forall fl flh flt,
    freeList fl flh flt
    ===> !{freeList nil flh flh} * !{freeList fl flh flt}.

  Axiom freeList_nil_bwd : forall flh,
    emp
    ===> freeList nil flh flh.

  Axiom freeList_neq : forall fl flh flt,
    flt <> NULL
    -> freeList fl flh flt
    ===> [< flh <> NULL >] * !{freeList fl flh flt}.

  Axiom freeList_middle : forall flt fl1 fl2 p sz flh,
    flt <> NULL
    -> !{freeList fl1 flh flt} * flt ==> p * (flt^+##8) ==> sz
    * !{allocated (flt^+##16) (wordToNat sz)} * !{freeList fl2 p (##0)}
    ===> freeList (fl1 ++ flt :: fl2) flh (##0).

  Axiom freeList_end : forall flt fl flh p sz,
    flt <> NULL
    -> !{freeList fl flh flt} * flt ==> p * (flt^+##8) ==> sz * !{allocated (flt^+##16) (wordToNat sz)}
    ===> freeList (fl ++ flt :: nil) flh p.
End FREE_LIST.

Module FreeList : FREE_LIST.
  Open Scope Sep_scope.

  Fixpoint freeList (fl : list SepArg.addr) (flh flt : SepArg.addr) : sprop :=
    match fl with
      | nil => [< flh = flt >]
      | p :: fl => [< flh <> NULL /\ flh = p >] * Ex p', Ex sz, flh ==> p' * (flh^+##8) ==> sz
        * !{allocated (flh^+##16) (wordToNat sz)} * !{freeList fl p' flt}
    end.

  Opaque natToWord.
  Theorem freeList_create : forall p,
    (Ex sz, [< p <> NULL >] * p ==> NULL * (p^+##8) ==> sz * !{allocated (p^+##16) (wordToNat sz)})
    ===> freeList (p :: nil) p (##0).
    sepLemma; auto. 
  Qed.

  Theorem freeList_cons_bwd : forall fl flh flt,
    ([< flh <> NULL >] * Ex p, Ex sz, flh ==> p * (flh^+##8) ==> sz
    * !{allocated (flh^+##16) (wordToNat sz)} * !{freeList fl p flt})
    ===> freeList (flh :: fl) flh flt.
    sepLemma.
  Qed.

  Theorem freeList_nonempty_fwd : forall fl flh flt,
    flh <> flt
    -> freeList fl flh flt
    ===> Ex p', Ex sz, Ex fl', [< fl = flh :: fl' >] * flh ==> p' * (flh^+##8) ==> sz
    * !{allocated (flh^+##16) (wordToNat sz)} * !{freeList fl' p' flt}.
    destruct fl; sepLemma.
  Qed.

  Theorem freeList_nonempty_bwd : forall fl p,
    (Ex flh, Ex sz, [< p <> NULL >] * p ==> flh * (p^+##8) ==> sz
    * !{allocated (p^+##16) (wordToNat sz)} * !{freeList fl flh (##0)})
    ===> freeList (p :: fl) p (##0).
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
    flt <> NULL
    -> freeList fl flh flt
    ===> [< flh <> NULL >] * !{freeList fl flh flt}.
    destruct fl; sepLemma.
  Qed.

  Lemma freeList_middle' : forall fl2 flt p sz fl1 flh,
    flt <> NULL
    -> !{freeList fl1 flh flt} * flt ==> p * (flt^+##8) ==> sz
    * !{allocated (flt^+##16) (wordToNat sz)} * !{freeList fl2 p (##0)}
    ===> freeList (fl1 ++ flt :: fl2) flh (##0).
    induction fl1; sepLemma.
  Qed.

  Theorem freeList_middle : forall flt fl1 fl2 p sz flh,
    flt <> NULL
    -> !{freeList fl1 flh flt} * flt ==> p * (flt^+##8) ==> sz
    * !{allocated (flt^+##16) (wordToNat sz)} * !{freeList fl2 p (##0)}
    ===> freeList (fl1 ++ flt :: fl2) flh (##0).
    intros; apply freeList_middle'; auto.
  Qed.

  Lemma freeList_end' : forall flt p sz fl flh,
    flt <> NULL
    -> !{freeList fl flh flt} * flt ==> p * (flt^+##8) ==> sz * !{allocated (flt^+##16) (wordToNat sz)}
    ===> freeList (fl ++ flt :: nil) flh p.
    induction fl; sepLemma.
  Qed.

  Theorem freeList_end : forall flt fl flh p sz,
    flt <> NULL
    -> !{freeList fl flh flt} * flt ==> p * (flt^+##8) ==> sz * !{allocated (flt^+##16) (wordToNat sz)}
    ===> freeList (fl ++ flt :: nil) flh p.
    intros; apply freeList_end'; auto.
  Qed.
End FreeList.

Import FreeList.
Export FreeList.

Module Type MALLOC_HEAP.
  Parameter mallocHeap : SepArg.addr -> sprop.

  Axiom mallocHeap_fwd : forall p, mallocHeap p ===> Ex fl, Ex flh, p ==> flh * !{freeList fl flh (##0)}.
  Axiom mallocHeap_bwd : forall p, (Ex fl, Ex flh, p ==> flh * !{freeList fl flh (##0)}) ===> mallocHeap p.
End MALLOC_HEAP.

Module MallocHeap : MALLOC_HEAP.
  Open Scope Sep_scope.

  Definition mallocHeap p : sprop :=
    Ex fl, Ex flh, p ==> flh * !{freeList fl flh (##0)}.

  Theorem mallocHeap_fwd : forall p, mallocHeap p ===> Ex fl, Ex flh, p ==> flh * !{freeList fl flh (##0)}.
    sepLemma.
  Qed.

  Theorem mallocHeap_bwd : forall p, (Ex fl, Ex flh, p ==> flh * !{freeList fl flh (##0)}) ===> mallocHeap p.
    sepLemma.
  Qed.
End MallocHeap.

Import MallocHeap.
Export MallocHeap.

(*
Definition mallocCell (p : SepArg.addr) (sz : nat) : PropX pc state :=
  (Ex pt, ![ !{allocated p sz} * (p^-##8) ==> sz * (p^-##16) ==> pt ])%PropX.
*)

Require Import NArith.

Definition initHeapS : state -> PropX pc state := st ~> Ex fr, 
  ![ !{allocated st#RAX (wordToNat st#RBX + 24)} * [< noneNull st#RAX (wordToNat st#RBX + 24) >] * ![fr] ] st
  /\ st#RBP @@ (st' ~> [< st'#RSP = st#RSP >] /\ ![ !{mallocHeap st#RAX} * ![fr] ] st').

Definition mallocS : state -> PropX pc state := st ~> Ex fr, ![ !{mallocHeap st#RAX} * ![fr] ] st
  /\ st#RBP @@ (st' ~> [< st'#RSP = st#RSP >]
    /\ ![ !{if weq st'#RAX NULL then emp else allocated st'#RAX (wordToNat st#RBX + 16)} * !{mallocHeap st#RAX} * ![fr] ] st').

Definition freeS : state -> PropX pc state := st ~>
  Ex fr, ![ !{mallocHeap st#RAX} * !{allocated st#RBX (wordToNat st#RCX + 16)} * ![fr] ] st (** TODO: Why do we need the size? **)
  /\ [< st#RBX <> NULL >]
  /\ st#RBP @@ (st' ~> [< st'#RSP = st#RSP >] /\ ![ !{mallocHeap st#RAX} * ![fr] ] st').

Definition malloc := bmodule {{
  bfunction "initHeap" [initHeapS] {
    Use [ tallocated_fwd (W64 :: W64 :: W64 :: nil) ];;
    Use [ freeList_create ];;
    $[!RAX] = rImm32 ##8;;
    $[!RAX] += RAX ;;
    $[!RAX++8] = rImm32 ##0 ;;
    $[!RAX++16] = RBX;;
    Goto RBP
  }
  with bfunction "free" [freeS] {
    Use [ tallocated_fwd (W64 :: W64 :: nil) ] ;;
    Use [ freeList_cons_bwd ];;

    RDX = $[!RAX] ;;
    $[!RBX] = RDX ;;
    $[!RBX++8] = RCX;;
    $[!RAX] = RBX;;
    Goto RBP
  }
  with bfunction "malloc" [mallocS] {
    RCX = $[!RAX];;
    If (RCX == rImm32 ##0) {
      RAX = rImm32 ##0 ;;
      Goto RBP (* Out of memory! *)
    } else {
      If ($[!RCX++1] < RBX) {
        (* The first free list block isn't big enough. *)
        Skip
      } else {
        If ($[!RCX++1] == RBX) {
          (* The current free list block is an exact size match for this
             request. *)
          Use [freeList_nonempty_fwd];;
          Use [allocated_expose_bwd 2];;

          RDX = $[!RCX] ;;
          $[!RAX] = RDX ;;
          RAX = RCX;;
          Goto RBP
        } else {
          RDX = RBX ;;
          RDX += rImm32 ##16 ;;
          If ($[!RCX++8] < RDX) {
            (* Not an exact match, but not enough memory left over to split out a
               smaller free list block after this one. *)
            Skip
          } else {
            (* Split this free block into two.  The caller gets the first part,
               and the free list keeps the second part. *)
            Use [freeList_nonempty_fwd];;
(*            Use st [allocated_split st#RBX];; *)
(*            Use st [allocated_expose_fwd_plus 2 st#RBX];; *)
            Use [freeList_nonempty_bwd];;
(*            Use st [allocated_expose_bwd_len 2 (st#RBX + 2)];; *)

            RDX = RCX ;;
            RDX += RBX ;;
            RDX += rImm32 ##16 ;;
            R9 = $[!RCX] ;;
            $[!RDX] = R9 ;;
            RDX = $[!RCX++8] ;;
            RDX -= RBX ;;
            R10 = R8 ;;
            R10 -= rImm32 ##2 ;;
            $[!RDX++8] = R10 ;;
            $[!RAX] = RDX ;;
            RAX = RCX;;
            Goto RBP
          }
        }
      };;

      (* The first free list block isn't big enough.  Move on to the next one.
         In this loop, R1 stores the current list position, and R2 stores its
         predecessor. *)
      Use [freeList_nonempty_fwd];;
      Use [freeList_nil_bwd];;

      RDX = RCX;;
      RCX = $[!RCX];;
      [ st ~> Ex fr, Ex flh, Ex Lpre, Ex Lpost,
        ![ st#RAX ==> flh * !{freeList Lpre flh st#RDX}
          * (Ex sz, st#RDX ==> st#RCX * (st#RDX ^+ ##8) ==> sz * !{allocated (st#RDX ^+ ##16) (wordToNat sz)})
          * !{freeList Lpost st#RCX NULL} * ![fr] ] st
        /\ [< st#RDX <> NULL >]
        /\ st#RBP @@ (st' ~> [< st'#RAX <> NULL /\ st'#RSP = st#RSP >]
          /\ ![ !{allocated st'#RAX (wordToNat st#RBX + 16)} * !{mallocHeap st#RAX} * ![fr] ] st') ]
      While (RCX != rImm32 ##0) {
        If ($[!RCX++8] < RBX) {
          (* This free list block isn't big enough.  Move on to the next one. *)
          Skip
        } else {
          If ($[!RCX++8] == RBX) {
            (* The current free list block is an exact size match for this
               request. *)
            Use [freeList_nonempty_fwd];;
            Use [allocated_expose_bwd 2];;
(*            Use st [freeList_middle st#RDX];; *)

            R9 = $[!RCX] ;;
            $[!RDX] = R9 ;;
            RAX = RCX ;;
            Goto RBP
          } else {
            R9 = RBX ;;
            R9 += rImm32 ##16 ;;
            If ($[!RCX++8] < R9) {
              (* Not an exact match, but not enough memory left over to split out a
                 smaller free list block after this one. *)
              Skip
            } else {
              (* Split this free block into two.  The caller gets the first part,
                 and the free list keeps the second part. *)
(*              Use st [allocated_split st#RBX];; *)
              Use [freeList_nonempty_fwd];;
(*              Use st [allocated_expose_fwd 2 (st#RCX + 2 + st#RBX)]%nat;; *)
              Use [allocated_expose_bwd 2];;
(*              Use st [freeList_middle st#RDX];; *)
              Use [freeList_nonempty_bwd];;

              R9 = RCX ;;
              R9 += RBX ;;
              R8 += rImm32 ##16;;
              $[!RDX] = R8;;
              R11 = $[!RCX] ;;
              $[!RCX] = R11 ;;
              R12 = $[!RCX++8] ;;
              R12 -= RBX ;;
              R12 -= rImm32 ##16 ;;
              $[!R8++8] = R12 ;;
              RAX = RCX;;
              Goto RBP
            }
          }
        };;

        Use [freeList_nonempty_fwd];;
(*        Use st [freeList_end st#RDX];; *)
      
        RDX = RCX ;;
        RCX = $[!RCX]
      };;

      RAX = rImm32 ##0 ;;
      Goto RBP   (* Out of memory! *)      
    }
  }
}}.

Section mallocOk.
  Hint Immediate mallocHeap_fwd : Forward.
  Hint Immediate mallocHeap_bwd : Backward.
  Hint Rewrite mupd_eq : InSep. (** TODO : move to tactics **)

  Lemma t_le_b_plus_t : forall t b, (t <= b + t)%nat. 
  Proof. intros; omega. Qed.
  Hint Resolve t_le_b_plus_t.

  Lemma noneNull_side : forall (a b : SepArg.word W64),
    noneNull a (wordToNat b + 24) ->
    natToWord 64 8 ^+ a = NULL -> False.
  Admitted.
  Hint Resolve noneNull_side.

  Lemma sext32_lt_32 : forall n, 
    (n <= 32)%nat ->
    @sext 32 (@inj _ WordView_nat _ n) 32 = ##n.
  Proof.
    intros. cut (wmsb (@inj _ WordView_nat 32 n) false = false). unfold sext.
    intros. rewrite H0. clear H0.
  Admitted.
  Hint Rewrite sext32_lt_32 using omega : word_canon.


  Opaque natToWord wordToNat inj.
  Theorem mallocOk : moduleOk malloc.
    structured.
    solve [ sep; eauto ].
    solve [ sep; eauto ].
    solve [ sep; eauto ].
    solve [ sep; eauto ].
    solve [ sep; eauto ].
    solve [ sep; eauto ].
    solve [ sep; eauto ].
    solve [ sep; eauto ].
    solve [ sep; eauto ].
    solve [ sep; eauto ].
    solve [ sep; eauto ].
    solve [ sep; eauto ].
    solve [ sep; eauto ].
    solve [ sep; eauto ].
    solve [ sep; eauto ].
    solve [ sep; eauto ].
(* initHeap
    sep.
    sep; eauto. 
   free
    sep.
    sep.
*)


  Admitted.
End mallocOk.