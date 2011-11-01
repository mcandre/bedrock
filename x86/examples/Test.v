Require Import x86.

(** Addition **)
Definition plus := bmodule {{
  bfunction "plus" [st ~> 
    st#RAX @@ (st' ~> [< st'#RBX = st#RBX ^+ st#RCX >]) ] {
    RBX += RCX ;;
    Goto RAX
  }
}}.

Theorem plusOk : moduleOk plus.
  structured; sep.
Qed.

(** Swap **)

Definition swap := bmodule {{
  bfunction "swap" [st ~> Ex fr, Ex a, Ex b, ![ st#RAX ==> a * st#RBX ==> b * ![fr] ] st
    /\ st#RBP @@ (st' ~> ![ st#RBX ==> a * st#RAX ==> b * ![fr] ] st') ] {
    RCX = $[!RAX] ;;
    RDX = $[!RBX] ;;
    $[!RAX] = RDX;;
    $[!RBX] = RCX;;
    Goto RBP
  }
}}.

Theorem swapOk : moduleOk swap.
  structured; sep. 
Qed.

Definition cond := bmodule {{
  bfunction "ifthen" [st ~> Ex fr, ![ ![fr] ] st
    /\ st#RBP @@ (st' ~> [< if weq st#RAX (wzero _) then st'#RBX = wzero _ else st'#RBX = wone _ >] /\ ![ ![fr] ] st') ] {
    If (RAX == (rImm32 (wzero _))) {
      RBX ::= 0
    } else {
      RBX ::= 1
    } ;;
    Goto RBP
  }
}}.

(** TODO: These are pretty general **)
Lemma red_if_weq : forall sz (a b : word sz) (P Q : Prop),
  a = b ->
  ((if weq a b then P else Q) <-> P). 
Proof.
  intros. destruct (weq a b); tauto.
Qed.
Lemma red_if_weq_not : forall sz (a b : word sz) (P Q : Prop),
  a <> b ->
  ((if weq a b then P else Q) <-> Q).
Proof.
  intros. destruct (weq a b); tauto.
Qed.

Ltac finisher := 
  repeat ((rewrite red_if_weq by auto) || (rewrite red_if_weq_not by auto)); auto.

Theorem condOk : moduleOk cond.
  structured; sep; finisher.
Qed.