Require Import Arith.

Require Import Ideal Malloc OMaps Hashtable.


Definition pureSpec := nat -> nat -> Prop.
Definition localInv := hprop.

Module Type MEMO.
  Parameter funcOk : pureSpec -> localInv -> pc -> PropX pc state.

  Axiom funcOk_fwd : forall specs sp li i,
    interp specs (funcOk sp li i)
    -> interp specs (ExX, Cptr i (Var VO)
      /\ Al st, AlX, Al fr, (![ ![li] * ![fr] ] st
        /\ Cptr st#Rret (Var VO)
        /\ (Al st', [< st'#Rsp = st#Rsp /\ sp st#R0 st'#R0 >] --> ![ ![li] * ![fr] ] st' --> VO @ st'))
      --> VS VO @ st)%PropX.

  Parameter memo : pureSpec -> localInv -> pc -> nat -> sprop.

  Axiom memo_fwd : forall sp li i a, memo sp li i a
    ===> Ex m, Ex ht, a ==> i * (a+1) ==> ht * !{htable m ht} * [< forall k v, m k = Some v -> sp k v >] * ![li].
  Axiom memo_bwd : forall (sp : pureSpec) li i a,
    (Ex m, Ex ht, a ==> i * (a+1) ==> ht * !{htable m ht} * [< forall k v, m k = Some v -> sp k v >] * ![li])
    ===> memo sp li i a.
End MEMO.

Module Memo : MEMO.
  Definition funcOk (sp : pureSpec) (li: localInv) (i : pc) : PropX pc state := (ExX, Cptr i (Var VO)
    /\ Al st, AlX, Al fr, (![ ![li] * ![fr] ] st
      /\ Cptr st#Rret (Var VO)
      /\ Al st', [< st'#Rsp = st#Rsp /\ sp st#R0 st'#R0 >] --> ![ ![li] * ![fr] ] st' --> VO @ st')
    --> VS VO @ st)%PropX.

  Theorem funcOk_fwd : forall specs sp li i,
    interp specs (funcOk sp li i)
    -> interp specs (ExX, Cptr i (Var VO)
      /\ Al st, AlX, Al fr, (![ ![li] * ![fr] ] st
      /\ Cptr st#Rret (Var VO)
      /\ (Al st', [< st'#Rsp = st#Rsp /\ sp st#R0 st'#R0 >] --> ![ ![li] * ![fr] ] st' --> VO @ st'))
      --> VS VO @ st)%PropX.
    auto.
  Qed.

  Open Scope Sep_scope.

  Definition memo (sp : pureSpec) (li : localInv) (i : pc) (a : nat) : sprop :=
    Ex m, Ex ht, a ==> i * (a+1) ==> ht * !{htable m ht} * [< forall k v, m k = Some v -> sp k v >] * ![li].

  Theorem memo_fwd : forall sp li i a, memo sp li i a
    ===> Ex m, Ex ht, a ==> i * (a+1) ==> ht * !{htable m ht} * [< forall k v, m k = Some v -> sp k v >] * ![li].
    sepLemma.
  Qed.

  Theorem memo_bwd : forall (sp : pureSpec) li i a,
    (Ex m, Ex ht, a ==> i * (a+1) ==> ht * !{htable m ht} * [< forall k v, m k = Some v -> sp k v >] * ![li])
    ===> memo sp li i a.
    sepLemma.
  Qed.
End Memo.

Import Memo.
Export Memo.

Local Hint Immediate memo_fwd : Forward.
Local Hint Immediate memo_bwd : Backward.


Definition constructorS : state -> PropX pc state := st ~> Ex fr, Ex ss, Ex sp, Ex li, [< ss >= 8 /\ st#R1 > 0 >]
  /\ ![ !{mallocHeap 0} * !{allocated st#Rsp ss} * ![li] * ![fr] ] st
  /\ st#Rret @@ (st' ~> [< st'#Rsp = st#Rsp >]
    /\ ![ !{mallocHeap 0} * !{allocated st#Rsp ss} * !{memo sp li st#R0 st'#R0} * ![fr] ] st').

Definition callS : state -> PropX pc state := st ~> Ex fr, Ex ss, Ex sp, Ex li, Ex f, [< ss >= 7 >]
  /\ ![ !{mallocHeap 0} * !{allocated st#Rsp ss} * !{memo sp li f st#R0} * ![fr] ] st
  /\ funcOk sp li f
  /\ st#Rret @@ (st' ~> [< st'#Rsp = st#Rsp /\ sp st#R1 st'#R0 >]
    /\ ![ !{mallocHeap 0} * !{allocated st#Rsp ss} * !{memo sp li f st#R0} * ![fr] ] st').

Theorem allocated_expose_bwd_delay : forall n base len, [< n <= len >] * !{allocated base (n + (len - n))} ===> allocated base len.
  sepLemma.
Qed.

Definition memmod := bimport [[ "malloc" @ [mallocS], "Hashtable" @ [Hashtable.constructorS],
                                "hcontainsKey" @ [containsKeyS htable 3],
                                "hget" @ [getS htable 3], "hput" @ [putS htable 4] ]] bmodule {{
  bfunction "Memo" [constructorS] {
    $[Rsp] <- Rret;;
    $[Rsp+1] <- R0;;

    R0 <- R1;;
    Rsp <- Rsp+3;;

    Use [allocated_expose_fwd 3];;

    Call "Hashtable"
    [st ~> Ex fr, Ex ss, Ex sp, Ex li, Ex ret, Ex i, Ex junk, [< ss >= 8 /\ st#Rsp >= 3 >]
      /\ ![ !{mallocHeap 0} * (st#Rsp-3) ==> ret * (st#Rsp-2) ==> i * (st#Rsp-1) ==> junk * !{allocated st#Rsp (ss-3)}
        * !{htable empty st#R0} * ![li] * ![fr] ] st
      /\ ret @@ (st' ~> [< st'#Rsp = st#Rsp-3 >]
        /\ ![ !{mallocHeap 0} * !{allocated st'#Rsp ss} * !{memo sp li i st'#R0} * ![fr] ] st')];;

    Rsp <- Rsp-3;;
    $[Rsp+2] <- R0;;

    R0 <- 0;;
    R1 <- 0;;
    Call "malloc"
    [st ~> Ex fr, Ex ss, Ex sp, Ex li, Ex ret, Ex i, Ex ht, [< ss >= 8 >]
      /\ ![ !{mallocHeap 0} * st#Rsp ==> ret * (st#Rsp+1) ==> i * (st#Rsp+2) ==> ht * !{allocated (st#Rsp+3) (ss-3)}
        * !{htable empty ht} * !{allocated st#R0 2} * ![li] * ![fr] ] st
      /\ ret @@ (st' ~> [< st'#Rsp = st#Rsp >]
        /\ ![ !{mallocHeap 0} * !{allocated st#Rsp ss} * !{memo sp li i st'#R0} * ![fr] ] st')];;
    
    $[R0] <- $[Rsp+1];;
    $[R0+1] <- $[Rsp+2];;
    Use [allocated_expose_bwd 3];;
    Goto $[Rsp]
  } with bfunction "call" [callS] {
    $[Rsp] <- Rret;;
    $[Rsp+1] <- R0;;
    $[Rsp+2] <- R1;;

    Use [allocated_expose_fwd 3];;

    R0 <- $[R0+1];;
    Rsp <- Rsp+3;;
    Call "hcontainsKey" 
    [st ~> Ex fr, Ex ss, Ex sp : pureSpec, Ex li, Ex f, Ex ret, Ex mt, Ex k, Ex m, Ex ht, [< ss >= 7 /\ st#Rsp >= 3
      /\ st#R0 = (match m k with None => 0 | Some _ => 1 end) /\ forall k v, m k = Some v -> sp k v >]
      /\ funcOk sp li f
      /\ ![ !{mallocHeap 0} * (st#Rsp-3) ==> ret * (st#Rsp-2) ==> mt * (st#Rsp-1) ==> k * !{allocated st#Rsp (ss-3)}
        * mt ==> f * (mt+1) ==> ht * !{htable m ht} * ![li] * ![fr] ] st
      /\ ret @@ (st' ~> [< st'#Rsp = st#Rsp-3 /\ sp k st'#R0 >]
        /\ ![ !{mallocHeap 0} * !{allocated st'#Rsp ss} * mt ==> f * (mt+1) ==> ht * !{htable (add m k st'#R0) ht} * ![li] * ![fr] ] st')];;

    Rsp <- Rsp-3;;

    If (R0 == 1) {
      R0 <- $[Rsp+1];;
      R0 <- $[R0+1];;
      R1 <- $[Rsp+2];;
      Rret <- $[Rsp];;
      Use st [allocated_expose_bwd_delay 3 st#Rsp];;
      Goto "hget"
    } else {
      R1 <- $[Rsp+1];;
      R1 <- $[R1];;
      R0 <- $[Rsp+2];;
      Call R1
      [st ~> Ex fr, Ex ss, Ex sp : pureSpec, Ex li, Ex f, Ex ret, Ex mt, Ex k, Ex m, Ex ht, [< ss >= 7 /\ sp k st#R0
        /\ forall k v, m k = Some v -> sp k v >]
        /\ ![ !{mallocHeap 0} * st#Rsp ==> ret * (st#Rsp+1) ==> mt * (st#Rsp+2) ==> k * !{allocated (st#Rsp+3) (ss-3)}
          * mt ==> f * (mt+1) ==> ht * !{htable m ht} * ![li] * ![fr] ] st
        /\ ret @@ (st' ~> [< st'#Rsp = st#Rsp /\ st'#R0 = st#R0 >]
          /\ ![ !{mallocHeap 0} * !{allocated st'#Rsp ss} * mt ==> f * (mt+1) ==> ht * !{htable (add m k st'#R0) ht} * ![li] * ![fr] ] st')];;

      R2 <- R0;;
      R1 <- $[Rsp+2];;
      R0 <- $[Rsp+1];;
      R0 <- $[R0+1];;
      $[Rsp+1] <- R2;;
      Rsp <- Rsp+3;;
      Call "hput"
      [st ~> Ex fr, Ex ss, Ex ret, Ex r, Ex junk, [< ss >= 7 /\ st#Rsp >= 3 >]
        /\ ![ (st#Rsp-3) ==> ret * (st#Rsp-2) ==> r * (st#Rsp-1) ==> junk * !{allocated st#Rsp (ss-3)} * ![fr] ] st
        /\ ret @@ (st' ~> [< st'#Rsp = st#Rsp-3 /\ st'#R0 = r >]
          /\ ![ !{allocated st'#Rsp ss} * ![fr] ] st')];;

      Rsp <- Rsp-3;;
      R0 <- $[Rsp+1];;
      Use [allocated_expose_bwd 3];;
      Goto $[Rsp]
    }
  }
}}.

Theorem table_add : forall (sp : pureSpec) m k v,
  sp k v
  -> (forall k' v', m k' = Some v' -> sp k' v')
  -> (forall k' v', add m k v k' = Some v' -> sp k' v').
  intros ? ? ? ? ? H k' v'; specialize (H k' v').
  unfold add; destruct (eq_nat_dec k' k); auto; congruence.
Qed.

Theorem oldStillGood : forall (sp : pureSpec) k v m,
  (forall k' v', m k' = Some v' -> sp k' v')
  -> 1 = match m k with Some _ => 1 | None => 0 end
  -> v = match m k with Some v => v | _ => 0 end
  -> sp k v.
  intros ? ? ? ? H; specialize (H k v); destruct (m k); auto; congruence.
Qed.

Theorem add_idem : forall m k v, m k = Some v -> add m k v = m.
  maps.
Qed.

Theorem add_idem' : forall m k v,
  1 = match m k with Some _ => 1 | None => 0 end
  -> v = match m k with Some v => v | _ => 0 end
  -> add m k v = m.
  intros; rewrite add_idem; auto; destruct (m k); congruence.
Qed.

Local Hint Extern 1 => match goal with
                         | [ _ : forall k' v', _ -> ?sp _ _ |- _ ] => eapply (@table_add sp); eassumption
                       end.
Local Hint Extern 1 => match goal with
                         | [ _ : forall k' v', _ -> ?sp _ _ |- _ ] => eapply (@oldStillGood sp); eassumption
                       end.

Hint Rewrite add_idem' using assumption : InSep.

Theorem memmodOk : moduleOk memmod.
  structured; abstract (pre;
    try match goal with
          | [ _ : _ <> 1, H : _ |- _ ] => apply funcOk_fwd in H; propxFo
        end; sep; eauto; maps
    || match goal with
         | [ H : forall x0 a x1, interp _ (_ --> subst (lift (?x x0) _) a) |- interp _ (?x ?st) ] =>
           let ret := eval hnf in st#Rret in
             match goal with
               | [ _ : _ ret = Some ?p |- _ ] =>
                 let fr' := fresh "fr" in evar (fr' : hprop); let fr := eval unfold fr' in fr' in clear fr';
                   generalize (Imply_sound (H st p fr)); clear H; intro H; simpl in H;
                     match type of H with
                       | ?P -> _ => assert P; [ unfold rupd; propxFo; [ Sep.sep memOut idtac | rewrite lift_nadaF; assumption |
                         doTrans; sep1; eauto; doTrans; congruence ]
                         | propxFo ]
                     end
             end
       end).
Qed.
