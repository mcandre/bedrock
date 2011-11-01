Require Import x86.
Require Import x86.examples.Allocated.
Require Import x86.examples.Null.
Require Import x86.WordView.

Section Malloc.

  Variable Cell : SepArg.addr -> nat -> sprop.

  Variable mallocHeap : SepArg.addr -> sprop.
  
  (** 
   ** - Note that passing the size isn't really transparent at this interface.
   **)

  Definition spec_malloc : state -> PropX pc state := st ~> 
    Ex fr, ![ !{mallocHeap st#RAX} * ![fr] ] st
    /\ st#RBP @@ (st' ~> [< st'#RSP = st#RSP >]
    /\ ![ !{if weq st'#RAX NULL then emp 
            else (!{Cell st'#RAX (ext st#RBX)} * !{allocated st'#RAX (ext st#RBX)})} *
          !{mallocHeap st#RAX} * ![fr] ] st').

  Definition spec_free : state -> PropX pc state := st ~>
    Ex fr,
         ![ !{mallocHeap st#RAX} *
            !{allocated st#RBX (ext st#RCX)} * !{Cell st#RBX (ext st#RCX)} * ![fr] ] st
      /\ [< st#RBX <> NULL >]
      /\ st#RBP @@ (st' ~> [< st'#RSP = st#RSP >] /\ ![ !{mallocHeap st#RAX} * ![fr] ] st').

End Malloc.

