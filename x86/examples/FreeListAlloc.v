Require Import NArith.
Require Import Allocated.
Require Import x86.

Module SlabAlloc.

  Open Scope Sep_scope.

  Section Sized.
    Variable n : nat.

    Fixpoint freeList (ls : list SepArg.addr) (f : SepArg.addr) : sprop :=
      match ls with
        | nil => [< f = NULL >]
        | p :: r => [< f <> NULL >] *
          f ==> p * !{allocated (f ^+ ##8) (n - 8)} * !{freeList r p}
      end.      
    
    Definition heap (hd : SepArg.addr) (n' : nat) : sprop :=
      [< (n >= 8)%nat >] *
      Ex fl , !{freeList fl hd} * [< length fl = n' >].

  End Sized.

  Fixpoint preserved (st st' : state) (ls : list (reg W64)) : Prop :=
    match ls with
      | nil => True
      | r :: rs => rrd r (Regs st) = rrd r (Regs st') /\ preserved st st' rs 
    end.

  Theorem heap_null_bwd : forall n p s, (n >= 8)%nat -> s = 0 -> p = NULL -> emp ===> heap n p s.
  Proof.
    unfold heap. sepLemma. instantiate (1 := nil). reflexivity. sepLemma.
  Qed.

  Theorem heap_unfold_fwd : forall sz p n, 
    heap sz p n ===> [< (8 <= sz)%nat >] * Ex fl , !{freeList sz fl p} * [< length fl = n >].
  Proof. sepLemma. Qed.

  Theorem heap_unfold_bwd : forall sz p n, 
    Ex fl, [< (8 <= sz)%nat >] * !{freeList sz fl p} * [< length fl = n >] ===> heap sz p n.
  Proof. sepLemma. Qed.

  Lemma freeList_cons_bwd : forall sz ls ls' hd hd',
    ls = hd' :: ls' ->
    [< ls = hd' :: ls' /\ hd <> NULL >] * !{freeList sz ls' hd'} * hd ==> hd' * !{allocated (hd ^+ ##8) (sz - 8)}
    ===> freeList sz ls hd.
  Proof. sepLemma. Qed.

  Lemma freeList_nil_bwd : forall sz ls hd,
    ls = nil ->
    [< hd = NULL >] ===> freeList sz ls hd.
  Proof. sepLemma. Qed.

  Lemma freeList_notnull_fwd : forall sz ls hd,
    hd <> NULL -> 
    freeList sz ls hd ===> Ex ls', Ex hd',
    [< ls = hd' :: ls' >] * !{freeList sz ls' hd'} * hd ==> hd' * !{allocated (hd ^+ ##8) (sz - 8)}.
  Proof. destruct ls; sepLemma. Qed.

  Theorem freeList_null_fwd : forall sz hd ls,
    hd = NULL ->
    freeList sz ls hd ===> [< ls = nil >].
  Proof. destruct ls; sepLemma. Qed.

  Definition noneNull (base : word 64) (len : N) : Prop :=
    base <> NULL /\ (wordToN base + len < Npow2 64)%N.

  Lemma noneNull_not_null : forall b l, 
    noneNull b l -> b = NULL -> False.
  Proof. unfold noneNull; intuition. Qed.
  Lemma noneNull_next_noneNull : forall b l o p,
    noneNull b l -> (p <= l - wordToN o)%N -> noneNull (b ^+ o) p.
  Proof.
    unfold noneNull. intros. destruct H.
  Admitted.

  Definition specExtendHeap : state -> PropX pc state :=
    st ~> Ex fr , Ex n , 
    ![ !{allocated st#RBX (wordToNat st#RCX * wordToNat st#RDX)} * !{heap (wordToNat st#RDX) st#RAX n} * ![fr] *
       [< noneNull st#RBX (wordToN st#RCX * wordToN st#RDX) >] *
       [< st#RBX <> NULL >] ] st
    /\ st#RBP @@ (st' ~> [< preserved st st' (RSP :: nil) >] /\
        ![ !{heap (wordToNat st#RDX) st'#RAX (n + wordToNat st#RCX)} * ![fr] ] st').

  Definition specAlloc : state -> PropX pc state :=
    st ~> Ex fr , Ex n , Ex sz ,
    ![ !{heap sz st#RAX n} * ![fr] ] st
    /\ st#RBP @@ (st' ~> [< preserved st st' (RAX :: RSP :: nil) >] /\
        ![ !{heap sz st'#RBX (n-1)} * !{if weq st'#RAX NULL then emp else allocated st#RAX sz} * ![fr] ] st').

  Definition specFree : state -> PropX pc state :=
    st ~> Ex fr , Ex n , Ex sz ,
    ![ !{heap sz st#RAX n} * !{allocated st#RBX sz} * [< st#RBX <> NULL >] * ![fr] ] st
    /\ st#RBP @@ (st' ~> [< preserved st st' (RSP :: nil) >] /\ ![ !{heap sz st'#RAX (n+1)} * ![fr] ] st').

  Theorem allocated_split_fwd : forall n' p n n'',
    n = n' + n'' ->
    allocated p n ===> !{allocated p n'} * !{allocated (p ^+ natToWord _ n') n''}.
  Proof.
    induction n'. intros. simpl plus in H. subst. 
    use allocated0_bwd. sepLemma.
    intros. destruct n. exfalso. omega. rewrite allocated_def. unfold allocated'. fold allocated'.
    rewrite <- allocated_def. inversion H. rewrite <- H1.  eapply (IHn' (p ^+ wone W64)) in H1. clear IHn' H.
    generalize (Ex v : SepArg.word W8, p =8> v). generalize dependent H1. generalize (allocated (p ^+ wone W64) n).
    generalize (!{allocated (p ^+ wone W64) n'}). cutrewrite (p ^+ wone W64 ^+ ##n' = p ^+ ##(S n')).
    generalize (!{allocated (p ^+ ##(S n')) n''}). clear. intros.
    eapply Himp_trans. instantiate (1 := !{s2} * (!{s0} * !{s})). eapply Himp_split. sepLemma. remove_guard.
    eapply Himp_trans. eapply H1. clear. eapply Himp_split; remove_guard; sepLemma. clear.
    eapply Himp_trans. 2: instantiate (1 := !{s2} * !{s0} * !{s}). sepLemma. eapply Himp_split.
    remove_guard. eapply Himp_split; remove_guard; sepLemma. sepLemma.

    cutrewrite (S n' = 1 + n'); auto. rewrite <- natToWord_plus. ring.
  Qed.

  Lemma minus1_times_n_eq_minus_n : forall sz (a : word sz) c,
    (wordToN (a ^- ##1) * c = wordToN a * c - c)%N.
  Admitted.

  Lemma extendHeap_separate : forall p (c d : word W64),
    c <> wzero _ -> (wordToNat d >= 8)%nat ->
    allocated (p ^+ ##8) (wordToNat c * wordToNat d - 8) ===> 
    !{allocated (p ^+ ##8) (wordToNat d - 8)} * !{allocated (p ^+ d) (wordToNat (c ^- ##1) * wordToNat d)}.
  Proof.
    intros. eapply Himp_trans. eapply allocated_split_fwd.
    instantiate (2 := wordToNat d - 8). instantiate (1 := (wordToNat (c ^- wone _) * wordToNat d)%nat).
    2: unfold wone; cutrewrite (p ^+ ##(8) ^+ ##(wordToNat d - 8) = p ^+ d)%nat. 2: sepLemma.
  Admitted.

  Definition slab_alloc := bmodule {{
    bfunction "extendHeap" [specExtendHeap] {
      let _width := RDX in
      let _buf   := RBX in
      let _heap  := RAX in
      let _count := RCX in
      Use [ heap_unfold_fwd ] ;;

      [st ~> Ex fr, Ex fl,
        ![ [< (8 <= wordToNat st#_width)%nat >] * 
           [< noneNull st#_buf (wordToN st#_count * wordToN st#_width) >] *
           !{freeList (wordToNat st#_width) fl st#_heap} *
           !{allocated st#_buf (wordToNat st#_count * wordToNat st#_width)} * ![fr] ] st 
        /\ st#RBP @@ (st' ~> [< preserved st st' (RSP :: nil) >] /\ 
          ![ !{heap (wordToNat st#RDX) st'#RAX (List.length fl + wordToNat st#_count)} * ![fr] ] st')
      ]
      While (RCX != rImm32 ##0) {
        Use [ allocated_split_fwd ] ;;
        Use [ allocated0_fwd ] ;;
        Use [ extendHeap_separate ] ;;
        Use [ Allocated.tallocated_fwd (W64 :: nil) ] ;;
        Use [ freeList_cons_bwd ] ;;
        $[!_buf] = _heap ;;
        _heap    = _buf ;;
        _buf    += _width ;;
        _count  -= rImm32 ##1 
      } ;;

      Use [ heap_unfold_bwd ] ;;
      Use [ allocated0_fwd ] ;;
      Goto RBP
    }
    with bfunction "alloc" [specAlloc] {
      let _heap := RAX in
      
      If (_heap == rImm32 ##0) {
        Use [ heap_unfold_fwd ] ;;
        Use [ heap_unfold_bwd ] ;;
        Use [ freeList_null_fwd ] ;;
        Use [ freeList_nil_bwd ] ;;
        RBX = _heap
      } else {
        Use [ Allocated.tallocated_fwd (W64 :: nil) ] ;;
        Use [ Allocated.tallocated_bwd (W64 :: nil) ] ;;
        Use [ heap_unfold_fwd ] ;;
        Use [ heap_unfold_bwd ] ;;
        Use [ freeList_notnull_fwd ] ;;

        RBX = $[!_heap]
      } ;;

      Goto RBP
    }
    with bfunction "free" [specFree] {
      let _heap := RAX in
      let _buf  := RBX in

      Use [ heap_unfold_fwd ] ;;
      Use [ heap_unfold_bwd ] ;;
      Use [ Allocated.tallocated_fwd (W64 :: nil) ] ;;
      Use [ freeList_cons_bwd ] ;;

      $[!_buf] = _heap ;;
      _heap    = _buf ;;

      Goto RBP
    }
  }}.



Section SlabAllocOk.
  Lemma times0_eq_0 : forall a b,
    a = wzero 64 ->
    (wordToNat a * b = 0)%nat.
  Proof.
    intros; subst. simpl. auto.
  Qed.

  Lemma plus0_eq_b : forall a b,
    a = wzero 64 ->
    (b + wordToNat a = b)%nat.
  Proof.
    intros; subst. simpl. auto.
  Qed.

  Lemma not_zero_wordToNat : forall (c : word 64),
    c <> wzero _ -> wordToNat c <> 0.
  Proof.
    intros. intro. apply H. assert (##(@wordToNat _ c) = natToWord 64 0). rewrite H0. auto.
    rewrite natToWord_wordToNat in H1.  auto.
  Qed.
  Lemma eight_lt_prod : forall c (d : word 64),
    c <> wzero 64 ->
    (8 <= wordToNat d)%nat ->
    (8 <= (wordToNat c * wordToNat d))%nat.
  Proof.
    intros. apply not_zero_wordToNat in H. 
    generalize dependent (wordToNat d). generalize dependent (wordToNat c). clear.
    intros. destruct n. congruence. simpl. generalize (n * n0)%nat. intros. omega.
  Qed.
  Lemma Neq_Nle : forall (a b : N), 
    a = b -> (a <= b)%N.
  Proof.
    simpl. intros. subst. unfold Nle. rewrite Ncompare_refl. congruence.
  Qed.
  Lemma unify_heap_minus_1 : forall d a x5 (c : word 64), 
    c <> wzero _ ->
    sep (heap d a (S (x5 + wordToNat (c ^- ##(1))))) :: nil --->
    sep (heap d a (x5 + wordToNat c)) :: nil.
  Proof.
    intros. eapply not_zero_wordToNat in H.
    cutrewrite (S (x5 + wordToNat (c ^- ##(1))) = x5 + wordToNat c). sepLemma.
    cutrewrite (wordToNat (c ^- ##1) = wordToNat c - 1). omega.
(*    
    unfold wminus, wplus, wordBin. rewrite NToWord_nat.
    edestruct (wordToNat_natToWord 64 (nat_of_N (wordToN c + wordToN (^~ ##(1))))).
    unfold wneg in *. rewrite NToWord_nat in *.
    destruct H0. rewrite H0. rewrite nat_of_Nplus in *. repeat rewrite wordToN_nat in *.
    repeat rewrite nat_of_N_of_nat in *. 
*)
  Admitted. (** I have no idea how to solve goals like this **)
  Hint Immediate unify_heap_minus_1. 
  Hint Extern 1 (noneNull _ _) => eapply noneNull_next_noneNull; [ match goal with 
                                                                     | [ H : _ |- _ ] => eapply H
                                                                   end | eauto ].
  Hint Resolve times0_eq_0 plus0_eq_b.
  Hint Resolve Neq_Nle minus1_times_n_eq_minus_n. 
  Hint Resolve eight_lt_prod.
  Hint Resolve noneNull_not_null noneNull_next_noneNull.
  
  Opaque wordToNat natToWord.
  Theorem slab_allocOk : moduleOk slab_alloc.
    structured; try abstract (sep; eauto; simpl; auto; symmetry; eauto).
  Qed.

End SlabAllocOk.

End SlabAlloc.

