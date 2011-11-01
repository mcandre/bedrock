Require Import Arith.
Require Import x86.examples.Allocated.
Require Import x86.
Require Import x86.WordView.
Require Import x86.examples.Null.
Require Import x86.examples.FreeList.
Require Import x86.examples.MallocI.

Set Implicit Arguments.
Set Strict Implicit.

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

Definition initHeapS : state -> PropX pc state := st ~> Ex fr, 
  ![ !{allocated st#RAX (ext st#RBX + 24)} * [< noneNull st#RAX (ext st#RBX + 24) >] * ![fr] ] st
  /\ st#RBP @@ (st' ~> [< st'#RSP = st#RSP >] /\ ![ !{mallocHeap st#RAX} * ![fr] ] st').

Definition mallocCell (p : SepArg.addr) (n : nat) : sprop :=
  (Ex n', [< (n' + n >= 8)%nat /\ Vbound W64 (n' + n) >] * 
    (p ^- ## 8) ==> inj _ (n + n') *
    !{allocated (p ^+ inj _ n) n'})%Sep.

Definition mallocS : state -> PropX pc state := 
  spec_malloc mallocCell mallocHeap.

Definition freeS : state -> PropX pc state :=
  spec_free mallocCell mallocHeap.

Opaque inj ext.

Lemma mallocCell_unfold_fwd : forall p n, 
  mallocCell p n ===> 
  (Ex n', [< (n' + n >= 8)%nat /\ Vbound W64 (n' + n) >] * 
    (p ^- ## 8) ==> inj _ (n + n') *
    !{allocated (p ^+ inj _ n) n'})%Sep.
Proof. unfold mallocCell; sepLemma. Qed.
Lemma mallocCell_unfold_bwd : forall p n, 
  (Ex n', [< (n' + n >= 8)%nat /\ Vbound W64 (n' + n) >] * 
    (p ^- ## 8) ==> inj _ (n + n') *
    !{allocated (p ^+ inj _ n) n'})%Sep ===>  mallocCell p n.
Proof. unfold mallocCell; sepLemma. Qed.

Definition spec_free' : state -> PropX pc state := st ~> Ex fr : hprop , 
  let p := st#RBX in
  Ex n ,
  ![ !{allocated p n} * ((p ^- inj _ 8) ==> inj W64 n) * !{mallocHeap st#RAX} * ![fr] ] st
  /\ [< (n >= 8)%nat >]
  /\ [< Vbound W64 n >]
  /\ [< p <> NULL >]
  /\ st#RBP @@ (st' ~> [< st'#RSP = st#RSP >] /\ ![ !{mallocHeap st#RAX} * ![fr] ] st').

Lemma allocated_join_bwd : forall p n n',
  !{allocated p n} * !{allocated (p ^+ inj _ n) n'} ===> allocated p (n + n').
Proof.
  intros p n. generalize dependent p.
  rewrite allocated_def.
  induction n. simpl. intros; word_simpl; sepLemma.
  intros; word_simpl; sepLemma.
  word_simpl. sepLemma.
Qed.


Definition malloc := bmodule {{
(*
  bfunction "initHeap" [initHeapS] {
    Use [ tallocated_fwd (W64 :: W64 :: W64 :: nil) ];;
    Use [ freeList_create ];;
    R9         = rImm32 ##16 ;;
    R9        += RAX ;;
    $[!RAX]    = R9 ;;
    $[!RAX++8] = RBX ;;
    $[!RAX++8] += rImm32 ##8 ;;
    $[!RAX++16] = rImm32 ##0 ;;
    Goto RBP
  }
  with
  bfunction "free" [freeS] {
    let _freePtr := RAX in
    let _buf     := RBX in
    Use [ mallocCell_unfold_fwd ] ;;
    Use st [ @allocated_join_bwd (st#_buf) (ext st#RCX) ] ;;
    

    Goto "free'"
  }
  with bfunction "free'" [spec_free'] {
    let _freePtr := RAX in
    let _buf     := RBX in
    Use [ tallocated_fwd (W64 ::  nil) ] ;;
    Use [ freeList_cons_bwd ];;

    RDX = $[!_freePtr] ;;

    $[!_buf] = RDX ;;

    $[!_freePtr] = _buf;;
    Goto RBP
  }
  with *)
  bfunction "malloc" [mallocS] {
    let _heap := RAX in
    let _size := RBX in
    RCX = $[!RAX];;
    If (RCX == rImm32 ##0) {
      RAX = rImm32 ##0 ;;
      Goto RBP (* Out of memory! *)
    } else {
      R9 = $[!RCX -- 8] ;;
      If (R9 < _size) {
        (* The first free list block isn't big enough. *)
        Skip
      } else {
        If (R9 < _size) {
          Skip
        } else {
          (* Split this free block into two.  The caller gets the first part,
             and the free list keeps the second part. *)
          Use [ freeList_nonempty_fwd ] ;;
          Use [ mallocCell_unfold_bwd ] ;;
(*          Use st [allocated_split st#RBX];; *)
(*          Use st [allocated_expose_fwd_plus 2 st#RBX];; *)
          Use [ freeList_nonempty_bwd ] ;;
(*          Use st [allocated_expose_bwd_len 2 (st#RBX + 2)];; *)

          (* compute the "remaining" *)
          R9 -= _size ;;
          If (R9 >= rImm32 ##16) {
            R10 = RCX ;;
            R10 += _size ;;
            R11 = $[!RCX] ;;
            $[!R10 ++ 8] = R11 ;; (** writes the "next" pointer **)
            
            R9 -= rImm32 ##8 ;;
            $[!R10] = R9 ;; (** writes the broken block size **)
            
            R9 = _size ;;
            R9 += rImm32 ##8 ;;
            $[!RAX] = R9 ;; (** update the head pointer **)
            
            RAX = RCX ;; (** return value **)

            Goto RBP
          } else {
            
            R9 = $[!RCX] ;;
            $[!RAX] = R9 ;;
            
            RAX = RCX ;; (** return value **)

            Goto RBP
          }

        }
(*
        If (R9 == _size) {
          (* The current free list block is an exact size match for this
             request. *)
          Use [ freeList_nonempty_fwd ];;


          RDX = $[!RCX] ;;
          $[!RAX] = RDX ;;
          RAX = RCX;;
          Goto RBP
        } else {
          RDX = RBX ;;
          RDX += rImm32 ##16 ;;
          If (R9 < RDX) {
            (* Not an exact match, but not enough memory left over to split out a
               smaller free list block after this one. *)
            Skip
          } else {
            (* Split this free block into two.  The caller gets the first part,
               and the free list keeps the second part. *)
            Use [ freeList_nonempty_fwd ] ;;
            Use [ mallocCell_unfold_bwd ] ;;
(*            Use st [allocated_split st#RBX];; *)
(*            Use st [allocated_expose_fwd_plus 2 st#RBX];; *)
            Use [ freeList_nonempty_bwd ] ;;
(*            Use st [allocated_expose_bwd_len 2 (st#RBX + 2)];; *)

            (** TODO: This code is wrong **)
            R10 = RCX ;;
            R10 += _size ;;
            R11 = $[!RCX] ;;
            $[!R10 ++ 8] = R11 ;; (** writes the "next" pointer **)
            
            R9 -= _size ;;
            R9 -= rImm32 ##8 ;;
            $[!R10] = R9 ;; (** writes the broken block size **)
            
            $[!RAX] += _size ;;
            $[!RAX] += rImm32 ##8 ;;
            
(*            
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
*)
            Goto RBP
          }
        }
*)
      };;

(*

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
*)

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
    noneNull a (ext b + 24) ->
    inj W64 16 ^+ a = NULL -> False.
  Proof.
    intros. eapply noneNull_not_null_start. 3: eassumption.
    2: rewrite wplus_comm; eapply noneNull_move_noneNull. 2: eassumption.
    instantiate (1 := 1). omega.
    word_simpl. omega. reflexivity.
  Qed.
  Hint Resolve noneNull_side.

  Lemma sext32_lt_32 : forall n, 
    (n <= 32)%nat ->
    @sext W32 (@inj _ WordView_nat _ n) W64 = ##n.
  Proof.
    intros. rewrite sbound_ext; auto.
    2: compute; omega.
    Opaque BinNat.Ncompare. simpl.
    eapply nat_compare_le in H. rewrite Nnat.N_of_nat_compare in H.
    Require Import NArith.
    assert (Nnat.N_of_nat n <= Nnat.N_of_nat 32)%N. intuition.
    clear H.
    cut (2147483648 > N_of_nat n)%N; auto. Require Import Omega. zify. omega.
  Qed.
  Hint Rewrite sext32_lt_32 using omega : word_canon.
  Transparent BinNat.Ncompare.

  Hint Extern 1 (_ >= _)%nat => omega.
  Hint Extern 1 (_ <= _)%nat => omega.
  
  Hint Extern 1 (?X ^+ _ = _) => is_evar X; eapply word_solve_plus; reflexivity.
  Lemma fequiv_himp : forall T U f (a : T) (b : U) a' b',
    a = a' -> b = b' ->
    sep (f a b) :: nil ---> sep (f a' b') :: nil.
  Proof. intros; subst; eapply himp_refl. Qed.
  Hint Resolve fequiv_himp.
  Lemma eq_nat_lem : forall sz (a b : nat),
    (a >= b)%nat ->
    Vbound sz a -> 
    Vbound sz b ->
    a - b = ext (inj sz a ^- inj sz b).
  Proof. intros; word_simpl; eauto. Qed.
  Hint Resolve eq_nat_lem.

  Axiom cheat : forall T, T.

  Opaque natToWord wordToNat inj Vbound.
  Theorem mallocOk : moduleOk malloc.
    structured.
(*
    abstract sep.
    abstract sep.
    abstract sep.
    abstract sep.
    abstract sep.
    abstract sep.
    abstract sep.
    abstract sep.
    abstract sep.
    abstract sep.
    abstract sep.
*)
    Focus 12.
    Print Ltac pre.
    Print Ltac SP.postStructured.
    propxFo.
   intuition
    auto. 
     intuition auto. try subst; simpl in *; try autorewrite with Mac in *.
     Print Ltac refl_eval_subst.
     Print Ltac refl_eval.
     Ltac test := let H := fresh "XXX" in
  sym_getInitialState H;
  apply symEval_sound in H. 
     test.
     repeat match goal with
              | [ H : SPArg.exec _ _ _ |- _ ] => clear H
            end.
     simpl map in XXX. 
     Ltac simpl_steps H' :=
       match goal with
         | [ H : context [ symEval _ _ _ _ (_ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: ?X) _ ] |- _ ] =>
           match H with 
             | H' => let k := fresh in remember X as k in H'; simpl in H'; 
               match goal with 
                 | [ H'' : k = _ |- _ ] => rewrite H'' in H'; clear H'' k; simpl_steps H'
               end
           end
         | _ => simpl in H'
       end.

     Lemma symEval_cons : forall r f m x st sts P,
       symEval r f m x (st :: sts) P
       = match st with
           | Instr i =>
             let '(r0, f0, m0, x0) := symStep r f m x i in symEval r0 f0 m0 x0 sts P
           | Decide c b =>
             let '(r0, f0, m0, x0, P') := symDecide (r, f, m, x) c b in
               symEval r0 f0 m0 x0 sts (P /\ P')
         end.
       reflexivity.
     Qed.

     Ltac run :=
       match goal with
         | [ H : context [symEval] |- _ ] =>
           repeat (rewrite symEval_cons in H; simpl symStep in H; simpl symDecide in H; cbv beta iota zeta in H);
             simpl in H
       end.

     Time run.

     (*Time simpl_steps XXX.*) word_simpl_in XXX.

     intros. 
     Opaque symUpd.
     simpl symEval in XXX.
     rewrite H in XXX.

  repeat match goal with 
           | [ H : SPArg.eval _ _ _ |- _ ] => apply symRval_sound in H; subst
           | [ H : SPArg.exec _ _ _ |- _ ] => clear H
           | [ H : SPArg.state |- _ ] => clear H
           | [ H : context [ ?ST # ?R ] |- _ ] => change (ST # R) with (rrd R (Regs ST)) in H
           | [ H : SPArg.decide ?CC ?ST ?RES ?ST' |- _ ] =>
             (simple eapply symDecide_sound in H; [ | solve [ apply denoteState_reflectState ] ]); simpl in H;
               let Heq := fresh in
               destruct H as [ Heq ? ]; try rewrite Heq in *; rm Heq; simpl_State
           | [ H : _ /\ _ |- _ ] => destruct H
         end.

     refl_eval ltac:(fun H => idtac).
     reflect.
     Print Ltac pre.
    propxFo.
    pre.
    Focus.
    sep.
    pre.
    unfold evalAddr, rupd8, rupd64, rrd8, rrd64 in *. simpl. normalizer.
    sepSimp; try autorewrite with InSep in *; sepFwd; (instantiate; word_simpl_in_star). 
    sepSimpFull. sep_next.
    sep_next.
    unfold evalAddr, rupd8, rupd64, rrd8, rrd64 in *. simpl. normalizer.
    sepSimp; try autorewrite with InSep in *; sepFwd; (instantiate; word_simpl_in_star). 
    sepSimpFull. sepUpdate.
    use mallocCell_unfold_bwd.
    sepBwd.
    (instantiate; word_simpl_in_star). sepCancel.


    sep.
    sep.
    sep.
    sep.
    sep.
    sep.
    sep.
    sep.

    (* initHeap *)
    solve [ sep; eauto ].
    solve [ sep; eauto ].
    (* free *)
    solve [ sep; eauto ].
    solve [ sep; eauto ].
    solve [ sep; eauto ].
    solve [ sep; eauto ].

(*
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
*)


  Admitted.
End mallocOk.