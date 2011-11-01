Require Import Arith.
Require Import x86.examples.Allocated.
Require Import x86.
Require Import x86.WordView.
Require Import x86.examples.Null.

Set Implicit Arguments.
Set Strict Implicit.

Module Type FREE_LIST.
  Parameter freeList : list SepArg.addr -> SepArg.addr -> SepArg.addr -> sprop.

  Axiom freeList_create : forall (p : SepArg.addr),
    (Ex sz, [< p <> NULL >] * p ==> ##0 * (p^-##8) ==> (sz ^+ ##8) * !{allocated (p^+##8) (ext sz)})
    ===> freeList (p :: nil) p (##0).

  Axiom freeList_cons_bwd : forall fl flh flt,
    ([< flh <> NULL >] * Ex p, Ex sz, flh ==> p * (flh^-##8) ==> (sz ^+ ##8)
      * !{allocated (flh^+##8) (ext sz)} * !{freeList fl p flt})
    ===> freeList (flh :: fl) flh flt.

  Axiom freeList_nonempty_fwd : forall fl flh flt,
    flh <> flt
    -> freeList fl flh flt
    ===> Ex p, Ex sz, Ex fl', [< fl = flh :: fl' >] * flh ==> p * (flh^-##8) ==> (sz ^+ ##8)
    * !{allocated (flh^+##8) (ext sz)} * !{freeList fl' p flt}.

  Axiom freeList_nonempty_bwd : forall fl p,
    (Ex flh, Ex sz, [< p <> NULL >] * p ==> flh * (p^-##8) ==> (sz ^+ ##8)
    * !{allocated (p^+##8) (ext sz)} * !{freeList fl flh (##0)})
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
    -> !{freeList fl1 flh flt} * flt ==> p * (flt^-##8) ==> (sz ^+ ##8)
    * !{allocated (flt^+##8) (ext sz)} * !{freeList fl2 p (##0)}
    ===> freeList (fl1 ++ flt :: fl2) flh (##0).

  Axiom freeList_end : forall flt fl flh p sz,
    flt <> NULL
    -> !{freeList fl flh flt} * flt ==> p * (flt^-##8) ==> (sz ^+ ##8) * !{allocated (flt^+##8) (ext sz)}
    ===> freeList (fl ++ flt :: nil) flh p.
End FREE_LIST.

Module FreeList : FREE_LIST.
  Open Scope Sep_scope.

  Fixpoint freeList (fl : list SepArg.addr) (flh flt : SepArg.addr) : sprop :=
    match fl with
      | nil => [< flh = flt >]
      | p :: fl => [< flh <> NULL /\ flh = p >] * Ex p', Ex sz, flh ==> p' * (flh^-##8) ==> (sz ^+ ##8)
        * !{allocated (flh^+##8) (ext sz)} * !{freeList fl p' flt}
    end.

  Opaque natToWord.
  Theorem freeList_create : forall p,
    (Ex sz, [< p <> NULL >] * p ==> NULL * (p^-##8) ==> (sz ^+ ##8) * !{allocated (p^+##8) (ext sz)})
    ===> freeList (p :: nil) p (##0).
    sepLemma; auto. 
  Qed.

  Theorem freeList_cons_bwd : forall fl flh flt,
    ([< flh <> NULL >] * Ex p, Ex sz, flh ==> p * (flh^-##8) ==> (sz ^+ ##8)
    * !{allocated (flh^+##8) (ext sz)} * !{freeList fl p flt})
    ===> freeList (flh :: fl) flh flt.
    sepLemma.
  Qed.

  Theorem freeList_nonempty_fwd : forall fl flh flt,
    flh <> flt
    -> freeList fl flh flt
    ===> Ex p', Ex sz, Ex fl', [< fl = flh :: fl' >] * flh ==> p' * (flh^-##8) ==> (sz ^+ ##8)
    * !{allocated (flh^+##8) (ext sz)} * !{freeList fl' p' flt}.
    destruct fl; sepLemma.
  Qed.

  Theorem freeList_nonempty_bwd : forall fl p,
    (Ex flh, Ex sz, [< p <> NULL >] * p ==> flh * (p^-##8) ==> (sz ^+ ##8)
    * !{allocated (p^+##8) (ext sz)} * !{freeList fl flh (##0)})
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
    -> !{freeList fl1 flh flt} * flt ==> p * (flt^-##8) ==> (sz ^+ ##8)
    * !{allocated (flt^+##8) (ext sz)} * !{freeList fl2 p (##0)}
    ===> freeList (fl1 ++ flt :: fl2) flh (##0).
    induction fl1; sepLemma.
  Qed.

  Theorem freeList_middle : forall flt fl1 fl2 p sz flh,
    flt <> NULL
    -> !{freeList fl1 flh flt} * flt ==> p * (flt^-##8) ==> (sz ^+ ##8)
    * !{allocated (flt^+##8) (ext sz)} * !{freeList fl2 p (##0)}
    ===> freeList (fl1 ++ flt :: fl2) flh (##0).
    intros; apply freeList_middle'; auto.
  Qed.

  Lemma freeList_end' : forall flt p sz fl flh,
    flt <> NULL
    -> !{freeList fl flh flt} * flt ==> p * (flt^-##8) ==> (sz ^+ ##8) * !{allocated (flt^+##8) (ext sz)}
    ===> freeList (fl ++ flt :: nil) flh p.
    induction fl; sepLemma.
  Qed.

  Theorem freeList_end : forall flt fl flh p sz,
    flt <> NULL
    -> !{freeList fl flh flt} * flt ==> p * (flt^-##8) ==> (sz ^+ ##8) * !{allocated (flt^+##8) (ext sz)}
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
