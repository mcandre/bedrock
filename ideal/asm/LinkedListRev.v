Require Import Ideal.


Module Type LSEG.
  Parameter lseg : list nat -> nat -> nat -> sprop.

  Axiom lseg_empty_fwd : forall ls hd, hd = 0
    -> lseg ls hd 0 ===> [< ls = nil >].
  Axiom lseg_empty_bwd : forall hd tl,
    [< hd = tl >] ===> lseg nil hd tl.

  Axiom lseg_nonempty_fwd : forall ls hd tl, hd <> tl
    -> lseg ls hd tl ===> Ex x, Ex ls', Ex p, [< ls = x :: ls' >] * hd ==> x * (hd+1) ==> p * !{lseg ls' p tl}.

  Axiom lseg_last : forall x tl ls hd,
    (Ex tl', [< tl' <> 0 >] * !{lseg ls hd tl'} * tl' ==> x * (tl'+1) ==> tl) ===> lseg (ls ++ x :: nil) hd tl.
End LSEG.

Module Lseg : LSEG.
  Open Scope Sep_scope.

  Fixpoint lseg (ls : list nat) (hd tl : nat) : sprop :=
    match ls with
      | nil => [< hd = tl >]
      | x :: ls' => Ex p, [< (*hd <> tl /\*) hd <> 0 >] * hd ==> x * (hd+1) ==> p * !{lseg ls' p tl}
    end.

  Theorem lseg_empty_fwd : forall ls hd, hd = 0
    -> lseg ls hd 0 ===> [< ls = nil >].
    destruct ls; sepLemma.
  Qed.

  Theorem lseg_empty_bwd : forall hd tl,
    [< hd = tl >] ===> lseg nil hd tl.
    sepLemma.
  Qed.

  Theorem lseg_nonempty_fwd : forall ls hd tl, hd <> tl
    -> lseg ls hd tl ===> Ex x, Ex ls', Ex p, [< ls = x :: ls' >] * hd ==> x * (hd+1) ==> p * !{lseg ls' p tl}.
    destruct ls; sepLemma.
  Qed.

  Theorem lseg_last : forall x tl ls hd,
    (Ex tl', [< tl' <> 0 >] * !{lseg ls hd tl'} * tl' ==> x * (tl'+1) ==> tl) ===> lseg (ls ++ x :: nil) hd tl.
    induction ls; sepLemma; auto.
  Qed.
End Lseg.

Import Lseg.

Definition linkedList := bmodule {{
  bfunction "linc" [st ~> Ex fr, Ex ls, ![ !{lseg ls st#R0 0} * ![fr] ] st
    /\ st#Rret @@ (st' ~> ![ !{lseg (rev ls) st'#R0 0} * ![fr] ] st')] {
    R1 <- 0;;
      
    [st ~> Ex fr, Ex ls, ![ !{lseg ls st#R0 0} * ![fr] ] st
      /\ st#Rret @@ (st' ~> ![ !{lseg (rev ls) st'#R0 st#R1} * ![fr] ] st')]
    While (R0 != 0) {
      Use [lseg_nonempty_fwd];;
      Use st [lseg_last st.[st#R0] st#R1];;

      R2 <- $[R0+1];;
      $[R0+1] <- R1;;
      R1 <- R0;;
      R0 <- R2
    };;

    Use [lseg_empty_fwd];;
    Use [lseg_empty_bwd];;

    R0 <- R1;;
    Goto Rret
  }
}}.

Theorem linkedListOk : moduleOk linkedList.
  structured; sep; auto.
Qed.
