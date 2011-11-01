Require Import Allocated.
Require Import x86 Malloc BSets.
Require Import WordView.
Require Import Null.

Set Implicit Arguments.
Set Strict Implicit.

Module Type LLIST.
  Parameter llist : set -> SepArg.addr -> sprop.
  Parameter llistOk : set -> list (word W64) -> SepArg.addr -> sprop.

  Axiom unfold_llist_fwd : forall s a, llist s a ===> Ex a', Ex ls, Ex junk, a ==> a' * (a^+##8) ==> junk * !{llistOk s ls a'}.
  Axiom unfold_llist_bwd : forall s a, (Ex a', Ex ls, Ex junk, a ==> a' * (a^+##8) ==> junk * !{llistOk s ls a'}) ===> llist s a.

  Axiom llist_empty_fwd : forall s ls a,
    a = NULL
    -> llistOk s ls a ===> [< ls = nil /\ s = empty >].

  Axiom llist_empty_bwd : forall s ls a,
    a = NULL
    -> [< ls = nil /\ s = empty >] ===> llistOk s ls a.

  Axiom llist_nonempty_fwd : forall a s ls,
    a <> NULL
    -> llistOk s ls a ===> Ex x, Ex ls', Ex a', [< ls = x :: ls' /\ s x = true >] * a ==> x * (a^+##8) ==> a' * !{llistOk (del s x) ls' a'}.

  Axiom llist_nonempty_bwd : forall a s ls,
    a <> NULL
    -> (Ex x, Ex ls', Ex a', [< ls = x :: ls' /\ s x = true >] * a ==> x * (a^+##8) ==> a' * !{llistOk (del s x) ls' a'}) ===> llistOk s ls a.
End LLIST.

Module LList : LLIST.
  Open Scope Sep_scope.

  Fixpoint llistOk (s : set) (ls : list (word W64)) (a : SepArg.addr) : sprop :=
    match ls with
      | nil => [< a = NULL /\ s = empty >]
      | x :: ls' => Ex a', [< a <> NULL /\ s x = true >] * a ==> x * (a^+##8) ==> a' * !{llistOk (del s x) ls' a'}
    end.

  Definition llist (s : set) (a : SepArg.addr) : sprop := Ex a', Ex ls, Ex junk, a ==> a' * (a^+##8) ==> junk * !{llistOk s ls a'}.

  Theorem unfold_llist_fwd : forall s a, llist s a ===> Ex a', Ex ls, Ex junk, a ==> a' * (a^+##8) ==> junk * !{llistOk s ls a'}.
    sepLemma.
  Qed.

  Theorem unfold_llist_bwd : forall s a, (Ex a', Ex ls, Ex junk, a ==> a' * (a^+##8) ==> junk * !{llistOk s ls a'}) ===> llist s a.
    sepLemma.
  Qed.

  Theorem llist_empty_fwd : forall s ls a,
    a = NULL
    -> llistOk s ls a ===> [< ls = nil /\ s = empty >].
    destruct ls; sepLemma.
  Qed.

  Theorem llist_empty_bwd : forall s ls a,
    a = NULL
    -> [< ls = nil /\ s = empty >] ===> llistOk s ls a.
    sepLemma.
  Qed.

  Theorem llist_nonempty_fwd : forall a s ls,
    a <> NULL
    -> llistOk s ls a ===> Ex x, Ex ls', Ex a', [< ls = x :: ls' /\ s x = true >] * a ==> x * (a^+##8) ==> a' * !{llistOk (del s x) ls' a'}.
    destruct ls; sepLemma.
  Qed.

  Theorem llist_nonempty_bwd : forall a s ls,
    a <> NULL
    -> (Ex x, Ex ls', Ex a', [< ls = x :: ls' /\ s x = true >] * a ==> x * (a^+##8) ==> a' * !{llistOk (del s x) ls' a'}) ===> llistOk s ls a.
    sepLemma.
  Qed.
End LList.

Import LList.

Local Hint Immediate unfold_llist_fwd : Forward.
Local Hint Immediate unfold_llist_bwd : Backward.

Hint Extern 0 (_ <= _)%nat => omega.

Lemma sext_zero : forall sz sz',
  sext (wzero sz) sz' = wzero (sz + sz').
Proof.
  intros. assert (wmsb (wzero sz) false = false). clear. induction sz; auto.
  unfold sext. rewrite H. clear. induction sz; simpl; auto.
  unfold wzero in *. unfold natToWord. simpl. f_equal. eauto.
Qed.

Lemma sext_null : sext (wzero 32) 32 = NULL.
Proof.
  rewrite sext_zero. reflexivity.
Qed.

Definition sll := bimport [[ "malloc" @ [mallocS], "free" @ [freeS] ]] bmodule {{
  bfunction "SinglyLinkedList" [constructorS llist] {
    (*$[!RSP] = RBP;;*)
    push RBP ;;

    RAX ::= 0;; (** malloc pointer **)
    RBX ::= 0;; (** size? **)

    Use [rallocated_64val_fwd];;

    Call "malloc"
    [st ~> Ex n, Ex ret, Ex fr, [< n >= 8 >]
      /\ ![ !{mallocHeap NULL} * st#RSP ==> ret * !{rallocated st#RSP (n-8)} * 
            !{if weq st#RAX NULL then emp else allocated st#RAX 16} * ![fr] ] st
      /\ ret @@ (st' ~> [< st'#RSP = st#RSP ^+ ##8 >]
        /\ ![ !{mallocHeap NULL} * 
              !{if weq st'#RAX NULL then emp else llist empty st'#RAX} * !{rallocated st'#RSP n} * ![fr] ] st')];;

    If (RAX == rImm32 (##0)) {
      Use [rallocated_64val_bwd] ;;
      (* RBP = $[!RSP] ;; *)
      pop RBP ;;
      Goto RBP

    } else {
      Use [rallocated_64val_bwd] ;;
      Use [allocated0_fwd] ;;
      Use [allocated_64val_fwd] ;;
      Use [allocated_64val_fwd] ;;
      Use [llist_empty_bwd] ;;

      RBX ::= 0 ;;
      $[!RAX] = RBX ;;
      pop RBP ;;
      Goto RBP
    }
  }
  with bfunction "contains" [containsS llist] {
    RAX = $[!RAX];;

    [st ~> Ex fr, Ex s, Ex ls, ![ !{llistOk s ls st#RAX} * ![fr] ] st
      /\ st#RBP @@ (st' ~> [< st'#RSP = st#RSP /\ st'#RAX = if s st#RBX then ##1 else ##0 >]
        /\ ![ !{llistOk s ls st#RAX} * ![fr] ] st')]
    While (RAX != rImm32 (natToWord _ 0)) {
      Use [llist_nonempty_fwd];;
      Use [llist_nonempty_bwd];;

      RDX = $[!RDX] ;;

      If ($[!RAX] == RBX) {
        RAX ::= 1;;
        Goto RBP
      } else {
        RAX = $[!RAX ++ 8]
      }
    };;

    Use [llist_empty_fwd];;
    Use [llist_empty_bwd];;

    RAX ::= 0;;
    Goto RBP
  }
  with bfunction "add" [addS llist] {
    push RBP ;; (* $[Rsp] <- Rret;; *)
    push RAX ;; (* $[Rsp+1] <- R0;; *)
    push RBX ;; (* $[Rsp+2] <- R1;; *)

    Use [trallocated_fwd (W64 :: W64 :: W64 :: nil)] ;;
    Use [ unfold_llist_bwd ] ;;
    Call "contains"
    [st ~> Ex fr, Ex n, Ex s : set, Ex ls, Ex ret, Ex base, Ex new, Ex a, [< n >= 24 /\ st#RAX = (if s new then ##1 else ##0) /\ n >= 0 >]%nat
      /\ ![ !{mallocHeap ##0} * (st#RSP^+##16) ==> ret * (st#RSP^+##8) ==> base * st#RSP ==> new * !{rallocated st#RSP (n-24)}
        * base ==> a * !{llistOk s ls a} * ![fr] ] st
      /\ ret @@ (st' ~> [< st'#RSP = st#RSP^+##24 >]
        /\ ![ !{mallocHeap ##0} * !{rallocated st'#RSP n} * Ex ls', Ex a', base ==> a' * 
              !{if weq st'#RAX NULL then llistOk s ls' a' else llistOk (add s new) ls' a'} * ![fr] ] st')];;

    If (RAX == rImm32 (##0)) {
      RBX ::= 0;;
      Call "malloc"
      [st ~> Ex fr, Ex n, Ex s, Ex ls, Ex ret, Ex base, Ex new, Ex a, [< n >= 24 /\ s new = false >]
        /\ ![ !{mallocHeap ##0} * (st#RSP^+##16) ==> ret * (st#RSP^+##8) ==> base * st#RSP ==> new * !{rallocated st#RSP (n-24)}
          * base ==> a * !{llistOk s ls a} * !{if weq st#RAX NULL then emp else allocated st#RAX 16} * ![fr] ] st
        /\ ret @@ (st' ~> [< st'#RSP = st#RSP^+##24 >]
          /\ ![ !{mallocHeap ##0} * !{rallocated st'#RSP n} * Ex ls', Ex a', base ==> a' * 
                !{if weq st'#RAX NULL then llistOk s ls' a' else llistOk (add s new) ls' a'} * ![fr] ] st')];;
      
      If (RAX == rImm32 (##0)) {
        Skip
      } else {
        RCX = $[!RSP] ;;
        $[!RAX] = RCX ;; 
        RBX = $[!RSP ++ 8] ;;
        RCX = $[!RBX] ;;
        $[!RAX++ 8] = RCX ;;
        $[!RBX] = RAX ;;

        Use [ llist_nonempty_bwd ] ;;
        Use [ tallocated_fwd (W64 :: W64 :: nil) ] ;;
        Use [ allocated0_fwd ]
      }
    } else {
      Skip
    };;

    Use [ trallocated_bwd (W64 :: W64 :: W64 :: nil) ] ;;
    Use [ unfold_llist_bwd ] ;;

    RSP += rImm32 (##24);;
    Goto $[!RSP -- 8]
  }
  with bfunction "remove" [removeS llist] {
    RCX = RAX ;;
    RAX = $[!RAX];;

    [st ~> Ex fr, Ex s, Ex ls, ![ !{mallocHeap (##0)} * st#RCX ==> st#RAX * !{llistOk s ls st#RAX} * ![fr] ] st
      /\ st#RBP @@ (st' ~> [< st'#RSP = st#RSP >]
        /\ ![ !{mallocHeap (##0)} * Ex a, st#RCX ==> a * Ex ls', !{llistOk (del s st#RBX) ls' a} * ![fr] ] st')]
    While (RAX != rImm32 (natToWord _ 0)) {
      Use [llist_nonempty_fwd];;

      If ($[!RAX] == RBX) {
        Use [ allocated_64val_bwd ] ;;
        Use [ allocated_64val_bwd ] ;;
        Use [ allocated0_bwd ] ;;
        RDX = $[!RAX ++ 8] ;;
        $[!RCX] = RDX ;;

        RBX = RAX;;
        RAX ::= 0;;
        RCX ::= 0;;
        Goto "free"
      } else {
        Use [llist_nonempty_bwd];;

        RCX = RAX ;;
        RCX += rImm32 (natToWord 32 8);;
        RAX = $[!RCX]
      }
    };;

    Use [llist_empty_fwd];;
    Use [llist_empty_bwd];;

    Goto RBP
  }
}}.

Require Import NArith.
Require Import FunctionalExtensionality.

Lemma not_zero_not_zero : forall sz (a : word sz) n (P : Prop),
  a = natToWord sz n ->
  a = wzero _ ->
  n <> 0 ->
  (N_of_nat n < Npow2 sz)%N ->
  P.
Proof.
  intros. subst. unfold wzero in *. admit.
Qed.

Lemma expand_idem : forall T sz (y : word sz) a (t : T),
  a y = t ->
  a = (fun x => if weq x y then t else a x).
Proof.
  intros. 
  apply functional_extensionality. intros. destruct (weq x y); subst; auto.
Qed.

Ltac finisher := instantiate; 
  auto;
  do 2 match goal with
         | [ |- _ ---> _ ] => rewrite del_del; apply himp_refl
         | [ H : ?X = natToWord _ _ , 
           H' : ?X = wzero _ |- _ ] =>
         eapply not_zero_not_zero; [ eapply H | eapply H' | omega | simpl; repeat constructor ]
         | [ |- context [ fun x => if weq x _ then _ else _ x ] ] => rewrite <- expand_idem by assumption
         | _ => sets
       end; eauto.

Opaque split1 split2.

Hint Extern 0 (_ >= _)%nat => eassumption.
  
Lemma trans_equal : forall sz (a b c d : word sz), 
  a = b ^+ d ->
  b = c ^- d -> 
  a = c.
Proof.
  intros; subst. unfold wminus. rewrite <- wplus_assoc. rewrite (wplus_comm _ d). rewrite wminus_inv. 
  rewrite wplus_comm. rewrite wplus_unit. reflexivity.
Qed.
Hint Extern 0 (@eq (word _) _ _) => eapply trans_equal; eassumption.

Ltac combine_as_necessary := idtac;
  repeat match goal with
           | [ H : ?X # ?R = ?Y |- ?G ] =>
             match G with 
               | context [ X#R ] => 
                 match Y with 
                   | context [ ?S#?Z ] => 
                   rewrite H; word_simpl
                 end
             end
         end.
Hint Extern 0 (@eq hprop _ _) => combine_as_necessary. (** I need to figure out how to hint this correctly **)
(*
Hint Extern 1 (@eq (word _) _ _) => combine_as_necessary.
Hint Extern 1 (@eq SepArg.addr _ _) => combine_as_necessary.
Hint Extern 1 (@eq SepArg.addr _ _) => combine_as_necessary.
*)
Lemma minus_assoc : forall a b c,
  a - b - c = a - (b + c).
  intros; omega.
Qed.
Ltac eomega :=
  repeat match goal with
           | [ |- context [ ?X - ?Y - ?Z ] ] => 
             rewrite (minus_assoc X Y Z); simpl plus
         end; reflexivity.
Hint Extern 0 (sep (rallocated _ _) = sep (rallocated _ _)) => f_equal; f_equal; [ combine_as_necessary; ring | eomega ].

Opaque natToWord inj.

Lemma if_bool_equation : forall T (b : bool) (x y z : T),
  (x = if b then y else z) ->
  x = z ->
  y <> z ->
  b = false.
Proof.
  intuition; destruct b; subst; auto. exfalso; auto.
Qed.
Hint Extern 1 (_ = false) => eapply if_bool_equation; [ eassumption | eassumption | let H := fresh in intro H; discriminate H ].

Theorem sllOk : moduleOk sll.
  structured; abstract ((sep; finisher); finisher; eauto).
Qed.
