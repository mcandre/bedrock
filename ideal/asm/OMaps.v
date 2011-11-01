Require Import Arith FunctionalExtensionality.

Require Import Ideal Malloc.


Definition map := nat -> option nat.
Definition empty : map := fun _ => None.
Definition add (m : map) (k v : nat) : map := fun k' => if eq_nat_dec k' k then Some v else m k'.
Definition del (m : map) (k : nat) : map := fun k' => if eq_nat_dec k' k then None else m k'.

Ltac mapsIf E := match E with
                   | context[if _ then _ else _] => fail 1
                   | _ =>
                     match type of E with
                       | {_} + {_} => destruct E
                       | _ => let Heq := fresh "Heq" in
                         case_eq E; ((intros ? Heq; try rewrite Heq in *) || (intro Heq; try rewrite Heq in *))
                     end
                 end.

Require Import FunctionalExtensionality.

Ltac maps := unfold empty, add, del in *; intros; try subst;
  repeat match goal with
           | [ |- _ = _ ] => let x := fresh "x" in extensionality x
           | [ H : _ = _ |- _ ] => rewrite H
           | [ |- context[if ?E then _ else _] ] => mapsIf E
           | [ _ : context[if ?E then _ else _] |- _ ] => mapsIf E
         end; try subst; congruence || (elimtype False; omega) || omega.

Theorem add_eq : forall m k v, add m k v k = Some v.
  maps.
Qed.

Theorem add_other : forall m k v k', k <> k' -> add m k v k' = m k'.
  maps.
Qed.

Theorem del_other : forall m k k', k <> k' -> del m k k' = m k'.
  maps.
Qed.

Theorem add_del : forall m k v k', k <> k' -> del (add m k v) k' = add (del m k') k v.
  maps.
Qed.

Theorem add_del' : forall m k v, del (add m k v) k = del m k.
  maps.
Qed.

Theorem del_empty : forall k, del empty k = empty.
  maps.
Qed.

Theorem del_del : forall m k k', del (del m k) k' = del (del m k') k.
  maps.
Qed.

Hint Rewrite add_eq add_other del_other add_del add_del' del_empty using omega : OMaps.

Section specs.
  Variable adt : map -> nat -> sprop.
  Variable smin : nat.

  Definition isEmptyS : state -> PropX pc state := st ~> Ex fr, Ex ss, Ex m, [< ss >= smin >]
    /\ ![ !{allocated st#Rsp ss} * !{adt m st#R0} * ![fr] ] st
    /\ st#Rret @@ (st' ~> [< match st'#R0 with O => m <> empty | _ => m = empty end /\ st'#Rsp = st#Rsp >]
      /\ ![ !{allocated st#Rsp ss} * !{adt m st#R0} * ![fr] ] st').

  Definition containsKeyS : state -> PropX pc state := st ~> Ex fr, Ex ss, Ex m, [< ss >= smin >]
    /\ ![ !{allocated st#Rsp ss} * !{adt m st#R0} * ![fr] ] st
    /\ st#Rret @@ (st' ~> [< st'#R0 = (match m st#R1 with None => 0 | Some _ => 1 end) /\ st'#Rsp = st#Rsp >]
      /\ ![ !{allocated st#Rsp ss} * !{adt m st#R0} * ![fr] ] st').

  Definition getS : state -> PropX pc state := st ~> Ex fr, Ex ss, Ex m, [< ss >= smin >]
    /\ ![ !{allocated st#Rsp ss} * !{adt m st#R0} * ![fr] ] st
    /\ st#Rret @@ (st' ~> [< st'#R0 = (match m st#R1 with None => 0 | Some v => v end) /\ st'#Rsp = st#Rsp >]
      /\ ![ !{allocated st#Rsp ss} * !{adt m st#R0} * ![fr] ] st').

  Definition putS : state -> PropX pc state := st ~> Ex fr, Ex ss, Ex m, [< ss >= smin >]
    /\ ![ !{mallocHeap 0} * !{allocated st#Rsp ss} * !{adt m st#R0} * ![fr] ] st
    /\ st#Rret @@ (st' ~> [< st'#Rsp = st#Rsp >]
      /\ ![ !{mallocHeap 0} * !{allocated st#Rsp ss} * !{adt (add m st#R1 st#R2) st#R0} * ![fr] ] st').

  Definition removeS : state -> PropX pc state := st ~> Ex fr, Ex ss, Ex m, [< ss >= smin >]
    /\ ![ !{mallocHeap 0} * !{allocated st#Rsp ss} * !{adt m st#R0} * ![fr] ] st
    /\ st#Rret @@ (st' ~> [< st'#Rsp = st#Rsp >]
      /\ ![ !{mallocHeap 0} * !{allocated st#Rsp ss} * !{adt (del m st#R1) st#R0} * ![fr] ] st').
End specs.
