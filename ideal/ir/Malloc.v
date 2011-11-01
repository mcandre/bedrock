Require Import Arith.

Require Import Mir.

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
  Parameter freeList : list nat -> nat -> sprop.

  Axiom freeList_nonempty_fwd : forall fl flh,
    flh <> 0
    -> freeList fl flh
    ===> Ex p', Ex sz, Ex fl', [< fl = flh :: fl' >] * flh ==> p' * (flh+1) ==> sz
    * !{allocated (flh+2) sz} * !{freeList fl' p'}.

  Axiom freeList_nonempty_bwd : forall fl flh,
    flh <> 0
    -> (Ex p', Ex sz, Ex fl', [< fl = flh :: fl' >] * flh ==> p' * (flh+1) ==> sz
    * !{allocated (flh+2) sz} * !{freeList fl' p'})
    ===> freeList fl flh.

  Axiom freeList_nil_bwd : emp ===> freeList nil O.
End FREE_LIST.

Module FreeList : FREE_LIST.
  Open Scope Sep_scope.

  Fixpoint freeList (fl : list nat) (flh : nat) : sprop :=
    match fl with
      | nil => [< flh = 0 >]
      | p :: fl => [< flh <> 0 /\ flh = p >] * Ex p', Ex sz, flh ==> p' * (flh+1) ==> sz
        * !{allocated (flh+2) sz} * !{freeList fl p'}
    end.

  Theorem freeList_nonempty_fwd : forall fl flh,
    flh <> 0
    -> freeList fl flh
    ===> Ex p', Ex sz, Ex fl', [< fl = flh :: fl' >] * flh ==> p' * (flh+1) ==> sz
    * !{allocated (flh+2) sz} * !{freeList fl' p'}.
    destruct fl; sepLemma.
  Qed.

  Theorem freeList_nonempty_bwd : forall fl flh,
    flh <> 0
    -> (Ex p', Ex sz, Ex fl', [< fl = flh :: fl' >] * flh ==> p' * (flh+1) ==> sz
    * !{allocated (flh+2) sz} * !{freeList fl' p'})
    ===> freeList fl flh.
    sepLemma.
  Qed.

  Lemma freeList_nil_bwd : emp ===> freeList nil 0.
    sepLemma.
  Qed.
End FreeList.

Import FreeList.
Export FreeList.

Module Type MALLOC_HEAP.
  Parameter mallocHeap : nat -> sprop.

  Axiom mallocHeap_fwd : forall p, mallocHeap p ===> Ex fl, Ex flh, p ==> flh * !{freeList fl flh}.
  Axiom mallocHeap_bwd : forall p, (Ex fl, Ex flh, p ==> flh * !{freeList fl flh}) ===> mallocHeap p.
End MALLOC_HEAP.

Module MallocHeap : MALLOC_HEAP.
  Open Scope Sep_scope.

  Definition mallocHeap p : sprop :=
    Ex fl, Ex flh, p ==> flh * !{freeList fl flh}.

  Theorem mallocHeap_fwd : forall p, mallocHeap p ===> Ex fl, Ex flh, p ==> flh * !{freeList fl flh}.
    sepLemma.
  Qed.

  Theorem mallocHeap_bwd : forall p, (Ex fl, Ex flh, p ==> flh * !{freeList fl flh}) ===> mallocHeap p.
    sepLemma.
  Qed.
End MallocHeap.

Import MallocHeap.
Export MallocHeap.

Definition initHeapS : spec := st ~> Ex fr, FUNC st
  PRE [m0, arg] ![ !{allocated (arg 0) (arg 1 + 3)} * ![fr] ] m0
  POST [m1, _] ![ !{mallocHeap (arg 0)} * ![fr] ] m1.

Definition mallocS : spec := st ~> Ex fr, FUNC st
  PRE [m0, arg] ![ !{mallocHeap (arg 0)} * ![fr] ] m0
  POST [m1, ret] [< ret <> 0 >]
    /\ ![ !{allocated ret (arg 1 + 2)} * !{mallocHeap (arg 0)} * ![fr] ] m1.

Definition freeS : spec := st ~> Ex fr, FUNC st
  PRE [m0, arg] [< arg 1 <> 0 >]
    /\ ![ !{mallocHeap (arg 0)} * !{allocated (arg 1) (arg 2 + 2)} * ![fr] ] m0
  POST [m1, _] ![ !{mallocHeap (arg 0)} * ![fr] ] m1.

Definition malloc := bmodule {{
  bfunction "initHeap" Args [["base", "len"]] [initHeapS] {
    $"base" <$- $"base" + 1;;
    $"base"+1 <$- 0;;
    $"base"+2 <$- $"len";;
    Return 0
  } with bfunction "free" Args [["base", "ptr", "len"]] [freeS] {
    $"ptr" <$- $[$"base"];;
    $"ptr"+1 <$- $"len";;
    $"base" <$- $"ptr";;
    Return 0
  } with bfunction "malloc" Args [["heap", "size"]] [mallocS] {
    [st ~> Ex fr, FUNCi st
      PRE [m0, x] ![ !{mallocHeap (x "heap")} * ![fr] ] m0
      POST [m1, rv] [< rv <> 0 >]
        /\ ![ !{allocated rv (x "size" + 2)} * !{mallocHeap (x "heap")} * ![fr] ] m1]
    While ($[$"heap"] != 0) {
      "cur" <- $[$"heap"];;

      If ($[$"cur"+1] < $"size") {
        (* This free list block isn't big enough.  Move on to the next one. *)
        Skip
      } else {
        If ($[$"cur"+1] == $"size") {
          (* The current free list block is an exact size match for this
             request. *)
          $"heap" <$- $[$"cur"];;
          Return $"cur"
        } else {
          If ($[$"cur"+1] < $"size"+2) {
            (* Not an exact match, but not enough memory left over to split out a
               smaller free list block after this one. *)
            Skip
          } else {
            (* Split this free block into two.  The caller gets the first part,
               and the free list keeps the second part. *)
            Use x [allocated_split (x "size")];;
            Use [allocated_expose_fwd 2];;

            "newNode" <- $"cur" + $"size" + 2;;
            $"heap" <$- $"newNode";;
            $"newNode" <$- $[$"cur"];;
            $"newNode" + 1 <$- $[$"cur"+1] - $"size" - 2;;
            Return $"cur"
          }
        }
      };;

      "heap" <- $"cur"
    };;

    Halt (* Out of memory! *)
  }
}}.

Section mallocOk.
  Hint Immediate mallocHeap_fwd : Forward.
  Hint Immediate mallocHeap_bwd : Backward.

  Ltac isNum n :=
    match eval hnf in n with
      | O => idtac
      | S ?n' => isNum n'
    end.

  Hint Extern 1 (allocated _ (_ + ?n) ===> _) => isNum n; apply (allocated_expose_fwd n); womega : Forward.
  Hint Extern 1 (_ ===> allocated _ (_ + ?n)) => isNum n; apply (allocated_expose_bwd n); womega : Backward.

  Ltac makeDarnSure lemma := apply lemma; womega.

  Hint Extern 1 (freeList _ _ ===> _) => makeDarnSure freeList_nonempty_fwd : SafeAddress Forward.
  Hint Extern 1 (_ ===> freeList _ _) => makeDarnSure freeList_nonempty_bwd : Backward.
  Hint Extern 1 (_ ===> freeList _ (natToWord O)) => apply freeList_nil_bwd : Backward.

  Theorem mallocOk : moduleOk malloc.
    structured; abstract (sep; auto).
  Qed.
End mallocOk.
