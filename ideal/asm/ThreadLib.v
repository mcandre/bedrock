Require Import Arith.

Require Import Ideal Malloc.


Definition globalInv := hprop.
Definition localInv := nat -> hprop.

Module Type THREADS.
  Parameter threads : list (localInv * nat) -> nat -> sprop.
  Parameter threadsOk : list (localInv * nat) -> nat -> nat -> sprop.

  Axiom threads_fwd : forall invs root,
    threads invs root ===> Ex start, Ex finish, [< finish <> 0 >]
    * root ==> start * (root+1) ==> finish * !{allocated finish 3} * !{threadsOk invs start finish}.

  Axiom threads_bwd : forall invs root,
    (Ex start, Ex finish, [< finish <> 0 >]
      * root ==> start * (root+1) ==> finish * !{allocated finish 3} * !{threadsOk invs start finish}) ===> threads invs root.

  Axiom threadsOk_empty_bwd : forall start finish,
    [< start = finish >] ===> threadsOk nil start finish.

  Axiom threadsOk_nonempty_fwd : forall invs start finish,
    start <> finish
    -> threadsOk invs start finish
    ===> Ex inv, Ex i, Ex invs', Ex sp, Ex next, [< invs = (inv, i) :: invs' /\ start <> 0 >]
    * start ==> i * (start+1) ==> sp * (start+2) ==> next
    * (Ex v, sp ==> v) * ![inv sp] * !{threadsOk invs' next finish}.

  Axiom threadsOk_end : forall p inv i invs start finish,
    (Ex sp, [< p <> 0 >] * !{threadsOk invs start p} * p ==> i * (p+1) ==> sp * (p+2) ==> finish
      * (Ex v, sp ==> v) * ![inv sp])
    ===> threadsOk (invs ++ (inv, i) :: nil) start finish.
End THREADS.

Module Threads : THREADS.
  Open Scope Sep_scope.

  Fixpoint threadsOk (invs : list (localInv * nat)) (start finish : nat) : sprop :=
    match invs with
      | nil => [< start = finish >]
      | (inv, i) :: invs' => Ex sp, Ex next, [< start <> 0 >] * start ==> i * (start+1) ==> sp * (start+2) ==> next
        * (Ex v, sp ==> v) * ![inv sp] * !{threadsOk invs' next finish}
    end.

  Definition threads (invs : list (localInv * nat)) (root : nat) :=
    Ex start, Ex finish, [< finish <> 0 >]
    * root ==> start * (root+1) ==> finish * !{allocated finish 3} * !{threadsOk invs start finish}.

  Theorem threads_fwd : forall invs root,
    threads invs root ===> Ex start, Ex finish, [< finish <> 0 >]
    * root ==> start * (root+1) ==> finish * !{allocated finish 3} * !{threadsOk invs start finish}.
    sepLemma.
  Qed.

  Theorem threads_bwd : forall invs root,
    (Ex start, Ex finish, [< finish <> 0 >]
      * root ==> start * (root+1) ==> finish * !{allocated finish 3} * !{threadsOk invs start finish}) ===> threads invs root.
    sepLemma.
  Qed.

  Theorem threadsOk_empty_bwd : forall start finish,
    [< start = finish >] ===> threadsOk nil start finish.
    sepLemma.
  Qed.

  Theorem threadsOk_nonempty_fwd : forall invs start finish,
    start <> finish
    -> threadsOk invs start finish
    ===> Ex inv, Ex i, Ex invs', Ex sp, Ex next, [< invs = (inv, i) :: invs' /\ start <> 0 >]
    * start ==> i * (start+1) ==> sp * (start+2) ==> next
    * (Ex v, sp ==> v) * ![inv sp] * !{threadsOk invs' next finish}.
    destruct invs; sepLemma.
  Qed.

  Theorem threadsOk_end : forall p inv i invs start finish,
    (Ex sp, [< p <> 0 >] * !{threadsOk invs start p} * p ==> i * (p+1) ==> sp * (p+2) ==> finish
    * (Ex v, sp ==> v) * ![inv sp])
    ===> threadsOk (invs ++ (inv, i) :: nil) start finish.
    induction invs; sepLemma; auto.
  Qed.
End Threads.

Import Threads.
Export Threads.

Definition susp (ginv : globalInv) (inv : localInv) (i : pc) : PropX pc state :=
  (i @@ (st ~> Ex invs'', Ex root, Ex fr, ![ !{mallocHeap 0} * st#Rsp ==> root * !{threads invs'' root} * ![ginv] * ![inv st#Rsp] * ![fr] ] st))%PropX.

Fixpoint codesOk ginv (invs : list (localInv * nat)) : PropX pc state :=
  match invs with
    | nil => [< True >]
    | (inv, i) :: invs' => susp ginv inv i /\ codesOk ginv invs'
  end%PropX.

Theorem codesOk_end : forall specs ginv inv i invs,
  interp specs (susp ginv inv i)
  -> interp specs (codesOk ginv invs)
  -> interp specs (codesOk ginv (invs ++ (inv, i) :: nil)).
  induction invs as [ | [] ]; propxFo.
Qed.

Definition newSchedulerS : state -> PropX pc state := st ~> Ex fr, Ex ss, Ex ginv, [< ss >= 1 >]
  /\ ![ !{mallocHeap 0} * !{allocated st#Rsp ss} * ![fr] ] st
  /\ st#Rret @@ (st' ~> Ex invs, [< st'#Rsp = st#Rsp >]
    /\ ^[codesOk ginv invs]
    /\ ![ !{mallocHeap 0} * !{allocated st#Rsp ss} * !{threads invs st'#R0} * ![fr] ] st').

Definition spawnS : state -> PropX pc state := st ~> Ex fr, Ex ss, Ex ginv, Ex invs, [< ss >= 3 >]
  /\ susp ginv (fun sp => sep ([< sp <> 0 >] * !{allocated (sp+1) st#R2})%Sep) st#R1
  /\ codesOk ginv invs
  /\ ![ !{mallocHeap 0} * !{allocated st#Rsp ss} * !{threads invs st#R0} * ![fr] ] st
  /\ st#Rret @@ (st' ~> Ex invs', [< st'#Rsp = st#Rsp >]
    /\ ^[codesOk ginv invs']
    /\ ![ !{mallocHeap 0} * !{allocated st#Rsp ss} * !{threads invs' st#R0} * ![fr] ] st').

Definition yieldS : state -> PropX pc state := st ~> Ex fr, Ex ginv, Ex invs, Ex root,
  susp ginv (fun sp => sep ([< sp = st#Rsp >] * ![fr])%Sep) st#Rret
  /\ codesOk ginv invs
  /\ ![ !{mallocHeap 0} * st#Rsp ==> root * !{threads invs root} * ![ginv] * ![fr] ] st.

Definition exitS : state -> PropX pc state := st ~> Ex fr, Ex ginv, Ex invs, Ex root, [< st#Rsp <> 0 /\ st#R0 >= 4 >]
  /\ codesOk ginv invs
  /\ ![ !{mallocHeap 0} * st#Rsp ==> root * !{allocated (st#Rsp+1) (st#R0-1)} * !{threads invs root} * ![ginv] * ![fr] ] st.

Definition sched := bimport [[ "malloc" @ [mallocS], "free" @ [freeS] ]] bmodule {{
  bfunction "newScheduler" [newSchedulerS] {
    $[Rsp] <- Rret;;

    R0 <- 0;;
    R1 <- 3;;

    Use [allocated_expose_fwd 1];;

    Call "malloc"
    [st ~> Ex fr, Ex ss, Ex ret, [< st#R0 <> 0 /\ ss >= 1 >]
      /\ ![ !{mallocHeap 0} * st#Rsp ==> ret * !{allocated (st#Rsp+1) (ss-1)} * !{allocated st#R0 5} * ![fr] ] st
      /\ ret @@ (st' ~> [< st'#Rsp = st#Rsp >]
        /\ ![ !{mallocHeap 0} * !{allocated st#Rsp ss} * !{threads nil st'#R0} * ![fr] ] st')];;

    $[R0] <- R0+2;;
    $[R0+1] <- R0+2;;

    Use [allocated_expose_bwd 1];;
    Use [threads_bwd];;
    Use [threadsOk_empty_bwd];;

    Goto $[Rsp]
  }

  with bfunction "spawn" [spawnS] {
    $[Rsp] <- Rret;;
    $[Rsp+1] <- R0;;
    $[Rsp+2] <- R1;;

    R0 <- 0;;
    R1 <- R2+2;;

    Use [allocated_expose_fwd 4];;
    Use st [allocated_expose_fwd 3 st#Rsp];;

    Call "malloc"
    [st ~> Ex fr, Ex ss, Ex ginv, Ex invs, Ex ret, Ex root, Ex f, Ex ss', [< st#R0 <> 0 /\ ss >= 3 >]
      /\ let inv := fun sp => sep ([< sp <> 0 >] * !{allocated (sp+1) ss'})%Sep in
        ![ !{mallocHeap 0} * st#Rsp ==> ret * (st#Rsp+1) ==> root * (st#Rsp+2) ==> f * !{allocated (st#Rsp+3) (ss-3)}
          * !{threads invs root} * !{allocated st#R0 (4+ss')} * ![fr] ] st
        /\ susp ginv inv f /\ codesOk ginv invs
        /\ ret @@ (st' ~> [< st'#Rsp = st#Rsp >]
          /\ ![ !{mallocHeap 0} * !{allocated st#Rsp ss} * !{threads (invs ++ (inv, f) :: nil) root} * ![fr] ] st')];;

    Use [threads_fwd];;
    Use [threads_bwd];;
    Use [allocated_expose_bwd 3];;
    Use st [threadsOk_end st.[st.[st#Rsp+1]+1] ];;

    R1 <- $[Rsp+1];;
    R2 <- $[R1+1];;
    $[R2] <- $[Rsp+2];;
    $[R2+1] <- R0+3;;
    $[R2+2] <- R0;;
    $[R1+1] <- R0;;

    Goto $[Rsp]
  }

  with bfunction "yield" [yieldS] {
    R0 <- $[Rsp];;

    If ($[R0] == $[R0+1]) {
      (* No threads are queued, so return to the calling thread. *)
      Goto Rret
    } else {
      (* Pick a thread off the queue, using some slightly obscure rotation of the roles of queue nodes. *)

      (* Get current queue start and finish. *)
      R1 <- $[R0];;
      R2 <- $[R0+1];;

      (* Use the old finish to store the activation for the yielding thread. *)
      $[R2] <- Rret;;
      $[R2+1] <- Rsp;;
      $[R2+2] <- R1;;

      (* Change start to the old start's "next" and finish to the old start. *)
      $[R0] <- $[R1+2];;
      $[R0+1] <- R1;;

      (* Reactivate dequeued thread. *)
      Rsp <- $[R1+1];;
      $[Rsp] <- R0;;

      Use [threads_fwd];;
      Use [threads_bwd];;
      Use [threadsOk_nonempty_fwd];;
      Use st [threadsOk_end st#R2 ];;

      Goto $[R1]
    }
  }

  with bfunction "exit" [exitS] {
    R1 <- $[Rsp];;
    If ($[R1] == $[R1+1]) {
      (* No more threads in the queue.  The program is finished. *)
      Halt
    } else {
      (* At least one thread is ready to run.  Remove it from the queue and execute it. *)
      R2 <- $[R1];;
      $[R1] <- $[R2+2];;

      $[Rsp] <- $[R2];;
      $[Rsp+1] <- $[R2+1];;
      $[Rsp+2] <- R1;;
      $[Rsp+3] <- R0;;

      R0 <- 0;;
      R1 <- R2;;
      R2 <- 1;;

      Use [threads_fwd];;
      Use [threads_fwd];;
      Use [threads_bwd];;
      Use [allocated_expose_fwd 3];;
      Use [threadsOk_nonempty_fwd];;

      Call "free"
      [st ~> Ex fr, Ex ss, Ex inv, Ex ginv, Ex invs, Ex ret, Ex sp, Ex root, [< st#Rsp <> 0 /\ ss >= 4 >]
        /\ susp ginv inv ret /\ codesOk ginv invs
        /\ ![ !{mallocHeap 0} * st#Rsp ==> ret * (st#Rsp+1) ==> sp * (st#Rsp+2) ==> root * (st#Rsp+3) ==> ss * !{allocated (st#Rsp+4) (ss-4)}
          * !{threads invs root} * (Ex v, sp ==> v) * ![ginv] * ![inv sp] * ![fr] ] st];;

      Rret <- $[Rsp];;
      R0 <- 0;;
      R3 <- $[Rsp+1];;
      $[R3] <- $[Rsp+2];;
      R2 <- $[Rsp+3];;
      R2 <- R2-2;;
      R1 <- Rsp;;
      Rsp <- R3;;

      Use [allocated_expose_bwd 4];;

      Goto "free"
    }
  }
}}.

Lemma cancelFour : forall n, n + 2 + 2 - 4 = n.
  auto.
Qed.

Lemma extra_emp : forall inv,
  inv :: nil ---> inv :: sep emp :: nil.
  sepLemma.
Qed.

Lemma swappedy_dooda : forall inv1 inv2 inv3,
  inv1 :: inv2 :: inv3 :: nil ---> inv2 :: inv1 :: inv3 :: nil.
  sepLemma.
Qed.

Local Hint Immediate swappedy_dooda.

Theorem schedOk : moduleOk sched.
  structured; abstract (sep; simpl; auto;
    match goal with
      | [ |- ?inv :: nil ---> ?f _ :: ?g :: nil ] =>
        equate f (fun _ : nat => inv); equate g (sep emp); apply extra_emp
      | [ |- simplify _ _ _ ] => autorewrite with PropX; apply simplify_fwd; apply codesOk_end; auto; propxFo; try rewrite cancelFour; eauto
      | _ => canceler
    end).
Qed.
