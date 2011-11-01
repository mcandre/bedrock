Require Import Arith.

Require Import Ideal Malloc BSets.


(** Functional trees, to model heap pieces that represent trees *)
Inductive ftree : Type :=
| Leaf : ftree
| Node : ftree -> nat -> ftree -> ftree.

Module Type TREE.
  Parameter tree : set -> nat -> sprop.
  Parameter ftreeOk : set -> ftree -> nat -> sprop.

  Axiom unfold_tree_fwd : forall s a, tree s a ===> Ex a', Ex t, Ex junk, a ==> a' * (a+1) ==> junk * !{ftreeOk s t a'}.
  Axiom unfold_tree_bwd : forall s a, (Ex a', Ex t, Ex junk, a ==> a' * (a+1) ==> junk * !{ftreeOk s t a'}) ===> tree s a.

  Axiom ftree_empty_fwd : forall s t a,
    a = 0
    -> ftreeOk s t a ===> [< s = empty >].

  Axiom ftree_empty_bwd : forall s t a,
    a = 0
    -> [< s = empty /\ t = Leaf >] ===> ftreeOk s t a.

  Axiom ftree_nonempty_fwd : forall a s t,
    a <> 0
    -> ftreeOk s t a
    ===> Ex t1, Ex n, Ex t2, Ex s1, Ex a1, Ex s2, Ex a2,
    [< s n = true /\ s1 = s -<- n /\ s2 = s ->- n >]
    * !{ftreeOk s1 t1 a1}
    * a ==> a1 * (a+1) ==> n * (a+2) ==> a2
    * !{ftreeOk s2 t2 a2}.

  Axiom ftree_nonempty_bwd : forall a s t,
    a <> 0
    -> (Ex t1, Ex n, Ex t2, Ex s1, Ex a1, Ex s2, Ex a2,
    [< t = Node t1 n t2 /\ s n = true /\ s1 = s -<- n /\ s2 = s ->- n >]
    * !{ftreeOk s1 t1 a1}
    * a ==> a1 * (a+1) ==> n * (a+2) ==> a2
    * !{ftreeOk s2 t2 a2})
    ===> ftreeOk s t a.

  Axiom ftree_nonempty_fwd' : forall a s t,
    s <> empty
    -> ftreeOk s t a
    ===> Ex t1, Ex n, Ex t2, Ex s1, Ex a1, Ex s2, Ex a2,
    [< a <> 0 /\ s n = true /\ s1 = s -<- n /\ s2 = s ->- n >]
    * !{ftreeOk s1 t1 a1}
    * a ==> a1 * (a+1) ==> n * (a+2) ==> a2
    * !{ftreeOk s2 t2 a2}.
End TREE.

Module Tree : TREE.
  Open Scope Sep_scope.

  Fixpoint ftreeOk (s : set) (t : ftree) (a : nat) : sprop :=
    match t with
      | Leaf => [< a = 0 /\ s = empty >]
      | Node t1 n t2 => Ex s1, Ex a1, Ex s2, Ex a2,
        [< a <> 0 /\ s n = true /\ s1 = s -<- n /\ s2 = s ->- n >]
         * !{ftreeOk s1 t1 a1}
         * a ==> a1 * (a+1) ==> n * (a+2) ==> a2
         * !{ftreeOk s2 t2 a2}
    end.

  Definition tree (s : set) (a : nat) : sprop := Ex a', Ex t, Ex junk, a ==> a' * (a+1) ==> junk * !{ftreeOk s t a'}.

  Theorem unfold_tree_fwd : forall s a, tree s a ===> Ex a', Ex t, Ex junk, a ==> a' * (a+1) ==> junk * !{ftreeOk s t a'}.
    sepLemma.
  Qed.

  Theorem unfold_tree_bwd : forall s a, (Ex a', Ex t, Ex junk, a ==> a' * (a+1) ==> junk * !{ftreeOk s t a'}) ===> tree s a.
    sepLemma.
  Qed.

  Theorem ftree_empty_fwd : forall s t a,
    a = 0
    -> ftreeOk s t a ===> [< s = empty >].
    destruct t; sepLemma.
  Qed.

  Theorem ftree_empty_bwd : forall s t a,
    a = 0
    -> [< s = empty /\ t = Leaf >] ===> ftreeOk s t a.
    sepLemma.
  Qed.

  Theorem ftree_nonempty_fwd : forall a s t,
    a <> 0
    -> ftreeOk s t a
    ===> Ex t1, Ex n, Ex t2, Ex s1, Ex a1, Ex s2, Ex a2,
    [< s n = true /\ s1 = s -<- n /\ s2 = s ->- n >]
    * !{ftreeOk s1 t1 a1}
    * a ==> a1 * (a+1) ==> n * (a+2) ==> a2
    * !{ftreeOk s2 t2 a2}.
    destruct t; sepLemma; auto.
  Qed.

  Theorem ftree_nonempty_bwd : forall a s t,
    a <> 0
    -> (Ex t1, Ex n, Ex t2, Ex s1, Ex a1, Ex s2, Ex a2,
      [< t = Node t1 n t2 /\ s n = true /\ s1 = s -<- n /\ s2 = s ->- n >]
      * !{ftreeOk s1 t1 a1}
      * a ==> a1 * (a+1) ==> n * (a+2) ==> a2
      * !{ftreeOk s2 t2 a2})
    ===> ftreeOk s t a.
    sepLemma.
  Qed.

  Theorem ftree_nonempty_fwd' : forall a s t,
    s <> empty
    -> ftreeOk s t a
    ===> Ex t1, Ex n, Ex t2, Ex s1, Ex a1, Ex s2, Ex a2,
    [< a <> 0 /\ s n = true /\ s1 = s -<- n /\ s2 = s ->- n >]
    * !{ftreeOk s1 t1 a1}
    * a ==> a1 * (a+1) ==> n * (a+2) ==> a2
    * !{ftreeOk s2 t2 a2}.
    destruct t; sepLemma; auto.
  Qed.
End Tree.

Import Tree.

Local Hint Immediate unfold_tree_fwd : Forward.
Local Hint Immediate unfold_tree_bwd : Backward.

Definition extractMinS : state -> PropX pc state := st ~> Ex fr, Ex n, Ex s, [< n >= 2 /\ s <> empty >]
  /\ ![ !{mallocHeap 0} * !{allocated st#Rsp n} * !{tree s st#R0} * ![fr] ] st
  /\ st#Rret @@ (st' ~> [< st'#Rsp = st#Rsp /\ s st'#R0 = true /\ all s (fun x => st'#R0 <= x) >]
    /\ ![ !{mallocHeap 0} * !{allocated st#Rsp n} * !{tree (del s st'#R0) st#R0} * ![fr] ] st').

Definition extractMaxS : state -> PropX pc state := st ~> Ex fr, Ex n, Ex s, [< n >= 2 /\ s <> empty >]
  /\ ![ !{mallocHeap 0} * !{allocated st#Rsp n} * !{tree s st#R0} * ![fr] ] st
  /\ st#Rret @@ (st' ~> [< st'#Rsp = st#Rsp /\ s st'#R0 = true /\ all s (fun x => st'#R0 >= x) >]
    /\ ![ !{mallocHeap 0} * !{allocated st#Rsp n} * !{tree (del s st'#R0) st#R0} * ![fr] ] st').

Definition bst := bimport [[ "malloc" @ [mallocS], "free" @ [freeS] ]] bmodule {{
  bfunction "BinarySearchTree" [constructorS tree] {
    $[Rsp] <- Rret;;

    R0 <- 0;;
    R1 <- 0;;

    Use [allocated_expose_fwd 1];;

    Call "malloc"
    [st ~> Ex n, Ex ret, Ex fr, [< n >= 1 >]
      /\ ![ !{mallocHeap 0} * st#Rsp ==> ret * !{allocated (st#Rsp+1) (n-1)} * !{allocated st#R0 2} * ![fr] ] st
      /\ ret @@ (st' ~> [< st'#Rsp = st#Rsp >]
        /\ ![ !{mallocHeap 0} * !{allocated st#Rsp n} * !{tree empty st'#R0} * ![fr] ] st')];;

    Use [allocated_expose_bwd 1];;
    Use [ftree_empty_bwd];;

    $[R0] <- 0;;
    Goto $[Rsp]
  }

  with bfunction "contains" [containsS tree] {
    R0 <- $[R0];;
    [st ~> Ex fr, Ex s, Ex t, ![ !{ftreeOk s t st#R0} * ![fr] ] st
      /\ st#Rret @@ (st' ~> [< st'#Rsp = st#Rsp /\ st'#R0 = if s st#R1 then 1 else 0 >]
        /\ ![ Ex t', !{ftreeOk s t' st#R0} * ![fr] ] st')]
    While (R0 != 0) {
      Use [ftree_nonempty_fwd];;
      Use [ftree_nonempty_bwd];;

      If ($[R0+1] == R1) {
        R0 <- 1;;
        Goto Rret
      } else {
        If (R1 < $[R0+1]) {
          R0 <- $[R0]
        } else {
          R0 <- $[R0+2]
        }
      }
    };;

    Use [ftree_empty_fwd];;
    Use [ftree_empty_bwd];;

    R0 <- 0;;
    Goto Rret
  }

  with bfunction "add" [addS tree] {
    R2 <- R0;;
    R0 <- $[R0];;

    [st ~> Ex fr, Ex n, Ex s, Ex t, [< n >= 3 >]
      /\ ![ !{mallocHeap 0} * !{allocated st#Rsp n} * st#R2 ==> st#R0 * !{ftreeOk s t st#R0} * ![fr] ] st
      /\ st#Rret @@ (st' ~> [< st'#Rsp = st#Rsp >]
        /\ ![ !{mallocHeap 0} * !{allocated st#Rsp n} * Ex rt, st#R2 ==> rt
          * Ex t', !{ftreeOk (add s st#R1) t' rt} * ![fr] ] st')]
    While (R0 != 0) {
      Use [ftree_nonempty_fwd];;
      Use [ftree_nonempty_bwd];;

      If (R1 == $[R0+1]) {
        Goto Rret
      } else {
        If (R1 < $[R0+1]) {
          R2 <- R0
        } else {
          R2 <- R0+2
        };;
        R0 <- $[R2]
      }
    };;

    $[Rsp] <- Rret;;
    $[Rsp+1] <- R1;;
    $[Rsp+2] <- R2;;
    R0 <- 0;;
    R1 <- 1;;

    Use [allocated_expose_fwd 3];;
    Use [ftree_empty_fwd];;

    Call "malloc"
    [st ~> Ex fr, Ex n, Ex oldRet, Ex old1, Ex old2, [< n >= 3 /\ st#R0 <> 0 >]
      /\ ![ !{mallocHeap 0} * st#Rsp ==> oldRet * (st#Rsp+1) ==> old1 * (st#Rsp+2) ==> old2 * !{allocated (st#Rsp+3) (n-3)}
        * old2 ==> 0 * !{allocated st#R0 3} * ![fr] ] st
      /\ oldRet @@ (st' ~> [< st'#Rsp = st#Rsp >]
        /\ ![ !{mallocHeap 0} * !{allocated st#Rsp n} * old2 ==> st#R0
          * !{ftreeOk (add empty old1) (Node Leaf old1 Leaf) st#R0} * ![fr] ] st')];;

    R2 <- $[Rsp+2];;
    $[R2] <- R0;;
    $[R0] <- 0;;
    $[R0+1] <- $[Rsp+1];;
    $[R0+2] <- 0;;

    Use [allocated_expose_bwd 3];;
    Use [ftree_nonempty_bwd];;
    Use [ftree_empty_bwd];;
    Use [ftree_empty_bwd];;

    Goto $[Rsp]
  }

  with bfunction "extractMin" [extractMinS] {
    R1 <- R0;;
    R0 <- $[R0];;

    Use [ftree_nonempty_fwd'];;
    Use [ftree_nonempty_bwd];;

    [st ~> Ex fr, Ex n, Ex s, Ex t, [< n >= 2 /\ s <> empty /\ st#R0 <> 0 >]
      /\ ![ !{mallocHeap 0} * !{allocated st#Rsp n} * st#R1 ==> st#R0 * !{ftreeOk s t st#R0} * ![fr] ] st
      /\ st#Rret @@ (st' ~> [< st'#Rsp = st#Rsp /\ s st'#R0 = true /\ all s (fun x => st'#R0 <= x) >]
        /\ ![ !{mallocHeap 0} * !{allocated st#Rsp n} * Ex rt, st#R1 ==> rt
          * Ex t', !{ftreeOk (del s st'#R0) t' rt} * ![fr] ] st')]
    While ($[R0] != 0) {
      Use [ftree_nonempty_fwd];;
      Use st [ftree_nonempty_bwd st#R0];;

      R1 <- R0;;
      R0 <- $[R0]
    };;

    $[Rsp] <- Rret;;
    $[Rsp+1] <- $[R0+1];;
    $[R1] <- $[R0+2];;
    R1 <- R0;;
    R0 <- 0;;
    R2 <- 1;;

    Use [allocated_expose_fwd 2];;
    Use [ftree_empty_fwd];;
    Use [ftree_nonempty_fwd];;

    Call "free"
    [st ~> Ex fr, Ex n, Ex ret, Ex rv, [< n >= 2 >]
      /\ ![ !{mallocHeap 0} * st#Rsp ==> ret * (st#Rsp+1) ==> rv * !{allocated (st#Rsp+2) (n-2)} * ![fr] ] st
      /\ ret @@ (st' ~> [< st'#Rsp = st#Rsp /\ st'#R0 = rv >]
        /\ ![ !{mallocHeap 0} * !{allocated st#Rsp n} * ![fr] ] st')];;

    Use [allocated_expose_bwd 2];;

    R0 <- $[Rsp+1];;
    Goto $[Rsp]
  }

  with bfunction "extractMax" [extractMaxS] {
    R1 <- R0;;
    R0 <- $[R0];;

    Use [ftree_nonempty_fwd'];;
    Use [ftree_nonempty_bwd];;

    [st ~> Ex fr, Ex n, Ex s, Ex t, [< n >= 2 /\ s <> empty /\ st#R0 <> 0 >]
      /\ ![ !{mallocHeap 0} * !{allocated st#Rsp n} * st#R1 ==> st#R0 * !{ftreeOk s t st#R0} * ![fr] ] st
      /\ st#Rret @@ (st' ~> [< st'#Rsp = st#Rsp /\ s st'#R0 = true /\ all s (fun x => st'#R0 >= x) >]
        /\ ![ !{mallocHeap 0} * !{allocated st#Rsp n} * Ex rt, st#R1 ==> rt
          * Ex t', !{ftreeOk (del s st'#R0) t' rt} * ![fr] ] st')]
    While ($[R0+2] != 0) {
      Use [ftree_nonempty_fwd];;
      Use st [ftree_nonempty_bwd st#R0];;

      R1 <- R0+2;;
      R0 <- $[R1]
    };;

    $[Rsp] <- Rret;;
    $[Rsp+1] <- $[R0+1];;
    $[R1] <- $[R0];;
    R1 <- R0;;
    R0 <- 0;;
    R2 <- 1;;

    Use [allocated_expose_fwd 2];;
    Use [ftree_empty_fwd];;
    Use [ftree_nonempty_fwd];;

    Call "free"
    [st ~> Ex fr, Ex n, Ex ret, Ex rv, [< n >= 2 >]
      /\ ![ !{mallocHeap 0} * st#Rsp ==> ret * (st#Rsp+1) ==> rv * !{allocated (st#Rsp+2) (n-2)} * ![fr] ] st
      /\ ret @@ (st' ~> [< st'#Rsp = st#Rsp /\ st'#R0 = rv >]
        /\ ![ !{mallocHeap 0} * !{allocated st#Rsp n} * ![fr] ] st')];;

    Use [allocated_expose_bwd 2];;

    R0 <- $[Rsp+1];;
    Goto $[Rsp]
  }

  with bfunction "remove" [removeS tree] {
    R2 <- R0;;
    R0 <- $[R0];;

    [st ~> Ex fr, Ex n, Ex s, Ex t, [< n >= 4 >]
      /\ ![ !{mallocHeap 0} * !{allocated st#Rsp n} * st#R2 ==> st#R0 * !{ftreeOk s t st#R0} * ![fr] ] st
      /\ st#Rret @@ (st' ~> [< st'#Rsp = st#Rsp >]
        /\ ![ !{mallocHeap 0} * !{allocated st#Rsp n} * Ex rt, st#R2 ==> rt
          * Ex t', !{ftreeOk (del s st#R1) t' rt} * ![fr] ] st')]
    While (R0 != 0) {
      Use [ftree_nonempty_fwd];;

      If (R1 == $[R0+1]) {
        If ($[R0] == 0) {
          Use [ftree_empty_fwd];;

          $[R2] <- $[R0+2];;

          R1 <- R0;;
          R0 <- 0;;
          R2 <- 1;;
          Goto "free"
        } else {
          If ($[R0+2] == 0) {
            Use [ftree_empty_fwd];;

            $[R2] <- $[R0];;

            R1 <- R0;;
            R0 <- 0;;
            R2 <- 1;;
            Goto "free"
          } else {
            $[Rsp] <- Rret;;
            $[Rsp+1] <- R0;;
            Rsp <- Rsp+2;;

            Use [allocated_expose_fwd 2];;
            Use st [ftree_nonempty_bwd st#R0];;

            Call "extractMax"
            [st ~> Ex fr, Ex n, Ex ret, Ex oldNode, Ex oldData, [< n >= 4 /\ st#Rsp >= 2 >]
              /\ ![ !{mallocHeap 0} * (st#Rsp-2) ==> ret * (st#Rsp-1) ==> oldNode * !{allocated st#Rsp (n-2)} * (oldNode+1) ==> oldData * ![fr] ] st
            /\ ret @@ (st' ~> [< st'#Rsp = st#Rsp-2 >]
                /\ ![ !{mallocHeap 0} * !{allocated st'#Rsp n} * (oldNode+1) ==> st#R0 * ![fr] ] st')];;

            Use [allocated_expose_bwd 2];;

            Rsp <- Rsp-2;;
            R1 <- $[Rsp+1];;
            $[R1+1] <- R0;;
            Goto $[Rsp]
          }
        }
      } else {
        Use [ftree_nonempty_bwd];;

        If (R1 < $[R0+1]) {
          R2 <- R0
        } else {
          R2 <- R0+2
        };;
        R0 <- $[R2]
      }
    };;

    Use [ftree_empty_fwd];;
    Use [ftree_empty_bwd];;
    
    Goto Rret
  }
}}.

Ltac useAll :=
  match goal with
    | [ H1 : all _ _ |- _ ] =>
      use ftree_nonempty_fwd; sepFwd;
      match goal with
        | [ H2 : _ |- _ ] => specialize (H1 _ H2); simpl in H1; sets
      end
  end.

Ltac useAllSplit n := apply all_split with n; (assumption || useAll).
Ltac useAllSplitE H n := apply all_split with n; try rewrite H; sets.

Ltac finisher := intros; auto;
  match goal with
    | [ _ : _ = empty |- False ] =>
      use ftree_nonempty_fwd; sepFwd;
      match goal with
        | [ n : nat |- _ ] => eapply (empty_contra n); eassumption
      end
    | [ _ : all (?s -<- ?n) _ |- all ?s _ ] => useAllSplit n
    | [ _ : all (?s ->- ?n) _ |- all ?s _ ] => useAllSplit n
    | [ H : _ -<- ?n = empty |- all _ _ ] => useAllSplitE H n
    | [ H : _ ->- ?n = empty |- all _ _ ] => useAllSplitE H n
    | [ |- _ ---> _ ] => rewrite drop_del_lt by useAll; apply himp_refl
    | [ |- _ ---> _ ] => rewrite drop_del_gt by useAll; apply himp_refl
    | [ |- _ ---> _ ] => rewrite del_left by eauto 2; rewrite del_left' by eauto 2; apply himp_refl
    | [ |- del _ _ _ = true ] => useAll
    | _ => sets
  end.

Theorem bstOk : moduleOk bst.
  structured; abstract (sep; finisher).
Qed.
