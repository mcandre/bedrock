Require Import Malloc Typed Pure Impure.


Notation "^next1 p" := p (at level 38, only parsing) : Sep_scope.
Notation "^next2 p" := (p + 1) (at level 38, only parsing) : Sep_scope.
Notation "^data p" := (p + 2) (at level 38, only parsing) : Sep_scope.

Notation "^next1 p" := p (only parsing) : Mir_scope.
Notation "^next2 p" := (p + #1)%Mir (only parsing) : Mir_scope.
Notation "^data p" := (p + #2)%Mir (only parsing) : Mir_scope.


Inductive skeleton : Type :=
| Leaf : skeleton
| Node : skeleton -> skeleton -> skeleton.

Module Type PRIVATE.
  Parameter rep : nat -> skeleton -> word -> sprop.

  Axiom rep_empty_fwd : forall sz sk p, p = 0
    -> rep sz sk p ===> emp.

  Axiom rep_empty_bwd : forall sz sk p, p = 0
    -> [< sk = Leaf >] ===> rep sz sk p.

  Axiom rep_nonempty_fwd : forall sz sk p, p <> 0
    -> rep sz sk p ===> Ex v, Ex sk1, Ex sk2, Ex p1, Ex p2, [< sk = Node sk1 sk2 >] * ^data p ==> v * [< v <> 0 >] * !{allocated v sz}
    * ^next1 p ==> p1 * ^next2 p ==> p2 * !{rep sz sk1 p1} * !{rep sz sk2 p2}.

  Axiom rep_nonempty_bwd : forall sz sk p, p <> 0
    -> (Ex v, Ex sk1, Ex sk2, Ex p1, Ex p2, [< sk = Node sk1 sk2 >] * ^data p ==> v * [< v <> 0 >] * !{allocated v sz}
    * ^next1 p ==> p1 * ^next2 p ==> p2 * !{rep sz sk1 p1} * !{rep sz sk2 p2}) ===> rep sz sk p.
End PRIVATE.

Module Private : PRIVATE.
  Open Scope Sep_scope.

  Fixpoint rep (sz : nat) (sk : skeleton) (p : word) : sprop :=
    match sk with
      | Leaf => [< p = 0 >]
      | Node sk1 sk2 => Ex v, Ex p1, Ex p2, [< p <> 0 >] * ^data p ==> v * [< v <> 0 >] * !{allocated v sz}
        * ^next1 p ==> p1 * ^next2 p ==> p2 * !{rep sz sk1 p1} * !{rep sz sk2 p2}
    end.

  Theorem rep_empty_fwd : forall sz sk p, p = 0
    -> rep sz sk p ===> emp.
    destruct sk; sepLemma.
  Qed.

  Theorem rep_empty_bwd : forall sz sk p, p = 0
    -> [< sk = Leaf >] ===> rep sz sk p.
    sepLemma.
  Qed.

  Theorem rep_nonempty_fwd : forall sz sk p, p <> 0
    -> rep sz sk p ===> Ex v, Ex sk1, Ex sk2, Ex p1, Ex p2, [< sk = Node sk1 sk2 >] * ^data p ==> v * [< v <> 0 >] * !{allocated v sz}
    * ^next1 p ==> p1 * ^next2 p ==> p2 * !{rep sz sk1 p1} * !{rep sz sk2 p2}.
    destruct sk; sepLemma; auto.
  Qed.

  Theorem rep_nonempty_bwd : forall sz sk p, p <> 0
    -> (Ex v, Ex sk1, Ex sk2, Ex p1, Ex p2, [< sk = Node sk1 sk2 >] * ^data p ==> v * [< v <> 0 >] * !{allocated v sz}
    * ^next1 p ==> p1 * ^next2 p ==> p2 * !{rep sz sk1 p1} * !{rep sz sk2 p2}) ===> rep sz sk p.
    sepLemma; auto.
  Qed.
End Private.

Import Private.
Export Private.

Hint Extern 1 (rep _ _ _ ===> _) => makeDarnSure rep_empty_fwd : Forward.
Hint Extern 1 (_ ===> rep _ _ _) => makeDarnSure rep_empty_bwd : Backward.

Hint Extern 1 (rep _ _ _ ===> _) => makeDarnSure rep_nonempty_fwd : SafeAddress Forward.
Hint Extern 1 (_ ===> rep _ _ _) => makeDarnSure rep_nonempty_bwd : Backward.

Local Open Scope PropX_scope.

Definition sqlTree (sz : nat) : type1 word :=
  {| Model1 := (skeleton : Type) :: nil;
    Typing1 := fun p ms => {| Pure := [< True >];
      Impure := Ex rt, p ==> rt * !{rep sz (fst ms) rt} * Ex garbage, (p+1) ==> garbage |}
    |}.

Definition sqlTree' (sz : nat) : type1 word :=
  {| Model1 := (skeleton : Type) :: nil;
    Typing1 := fun p ms => {| Pure := [< True >];
      Impure := Ex rt, p ==> rt * !{rep sz (fst ms) rt} |}
    |}.

Definition sqlTreeN (sz : nat) : type1 word :=
  {| Model1 := (skeleton : Type) :: nil;
    Typing1 := fun p ms => {| Pure := [< True >];
      Impure := !{rep sz (fst ms) p} |}
    |}.

Definition sqlTreeS : spec := TYPED
  PRE[arg]
    heap
  POST[rv]
    heap,,
    rv :: sqlTree (arg 0).

Definition insertS : spec := TYPED
  PRE[arg]
    heap,,
    arg 1 :: sqlTree (arg 0 + 2),,
    arg 2 :: chunk (arg 0 + 2)
  POST[_]
    heap,,
    arg 1 :: sqlTree (arg 0 + 2).

Definition iterS : spec := Exi inv, TYPED
  PRE[arg]
    arg 1 :: sqlTree (arg 0 + 2),,
    arg 2 :: (function
      PRE[arg']
        arg' 0 :: chunk (arg 0 + 2),,
        invariant (inv (arg' 1))
      POST[_]
        arg' 0 :: chunk (arg 0 + 2),,
        invariant (inv (arg' 1))),,
    invariant (inv (arg 3))
  POST[_]
    arg 1 :: sqlTree (arg 0 + 2),,
    invariant (inv (arg 3)).

Definition iter'S : spec := Exi inv, TYPED
  PRE[arg]
    arg 1 :: sqlTreeN (arg 0 + 2),,
    arg 2 :: (function
      PRE[arg']
        arg' 0 :: chunk (arg 0 + 2),,
        invariant (inv (arg' 1))
      POST[_]
        arg' 0 :: chunk (arg 0 + 2),,
        invariant (inv (arg' 1))),,
    invariant (inv (arg 3))
  POST[_]
    arg 1 :: sqlTreeN (arg 0 + 2),,
    invariant (inv (arg 3)).

Definition treeOps := bimport [[ "malloc" @ [mallocS], "free" @ [freeS] ]]
  bmodule {{
    bfunction "sqlTree" Args [["size"]] [sqlTreeS] {
      Call "malloc" Args #0, #0
      [TYPEDc
        PRE[x, rv']
          heap,,
          rv' :: chunk 2
        POST[rv]
          heap,,
          rv :: sqlTree (x "size")];;
        
      Retv <$- 0;;
      Return Retv
    } with bfunction "insert" Args [["size", "tree", "tuple"]] [insertS] {
      "newKey" <- $[$"tuple"];;

      [TYPEDi
        PRE[x]
          heap,,
          x "tree" :: sqlTree' (x "size" + 2),,
          x "tuple" :: chunk (x "size" + 2)
        POST[_]
          heap,,
          x "tree" :: sqlTree' (x "size" + 2)]
      While ($[$"tree"] != 0) {
        "this" <- $[$"tree"];;
        "thisData" <- $[^data $"this"];;
        "thisKey" <- $[$"thisData"];;

        If ($"newKey" == $"thisKey") {
          ^data $"this" <$- $"tuple";;
          TailCall "free" Args #0, $"thisData", $"size"
        } else {
          If ($"newKey" < $"thisKey") {
            "tree" <- ^next1 $"this"
          } else {
            "tree" <- ^next2 $"this"
          }
        }
      };;

      Call "malloc" Args #0, #1
      [TYPEDc
        PRE[x, rv]
          heap,,
          x "tree" :: ptr,,
          x "tuple" :: chunk (x "size" + 2),,
          rv :: chunk 3
        POST[_]
          heap,,
          x "tree" :: sqlTree' (x "size" + 2)];;

      ^data Retv <$- $"tuple";;
      ^next1 Retv <$- 0;;
      ^next2 Retv <$- 0;;
      $"tree" <$- Retv;;
      Return 0
    } with bfunction "pointQuery" Args [["size", "tree", "f", "env", "key"]] [iterS] {
      "tree" <- $[$"tree"];;

      [Exi inv, TYPEDi
        PRE[x]
          x "tree" :: sqlTreeN (x "size" + 2),,
          x "f" :: (function
            PRE[arg']
              arg' 0 :: chunk (x "size" + 2),,
              invariant (inv (arg' 1))
            POST[_]
              arg' 0 :: chunk (x "size" + 2),,
              invariant (inv (arg' 1))),,
          invariant (inv (x "env"))
        POST[rv]
          x "tree" :: sqlTreeN (x "size" + 2),,
          invariant (inv (x "env"))]
      While ($"tree" != 0) {
        "thisData" <- $[^data $"tree"];;
        "thisKey" <- $[$"thisData"];;

        If ($"key" == $"thisKey") {
          TailCall $"f" Args $"thisData", $"env"
        } else {
          If ($"key" < $"thisKey") {
            "tree" <- $[^next1 $"tree"]
          } else {
            "tree" <- $[^next2 $"tree"]
          }
        }
      };;

      Return 0
    } with bfunction "iter" Args [["size", "tree", "f", "env"]] [iterS] {
      TailCall "iter'" Args $"size", $[$"tree"], $"f", $"env"
    } with bfunction "iter'" Args [["size", "tree", "f", "env"]] [iter'S] {
      If ($"tree" == 0) {
        Return 0
      } else {
        "data" <- $[^data $"tree"];;
        "left" <- $[^next1 $"tree"];;
        "right" <- $[^next2 $"tree"];;

        Call $"f" Args $"data", $"env"
        [Exi inv, TYPEDi
          PRE[x]
            x "left" :: sqlTreeN (x "size" + 2),,
            x "right" :: sqlTreeN (x "size" + 2),,
            x "f" :: (function
              PRE[arg']
                arg' 0 :: chunk (x "size" + 2),,
                invariant (inv (arg' 1))
              POST[_]
                arg' 0 :: chunk (x "size" + 2),,
                invariant (inv (arg' 1))),,
            invariant (inv (x "env"))
          POST[_]
            x "left" :: sqlTreeN (x "size" + 2),,
            x "right" :: sqlTreeN (x "size" + 2),,
            invariant (inv (x "env"))];;

        Call "iter'" Args $"size", $"left", $"f", $"env"
        [Exi inv, TYPEDi
          PRE[x]
            x "right" :: sqlTreeN (x "size" + 2),,
            x "f" :: (function
              PRE[arg']
                arg' 0 :: chunk (x "size" + 2),,
                invariant (inv (arg' 1))
              POST[_]
                arg' 0 :: chunk (x "size" + 2),,
                invariant (inv (arg' 1))),,
            invariant (inv (x "env"))
          POST[_]
            x "right" :: sqlTreeN (x "size" + 2),,
            invariant (inv (x "env"))];;

        TailCall "iter'" Args $"size", $"right", $"f", $"env"
      }
    }
  }}.

(* This heuristic figures out which part of a state is an instance of a parameterized invariant and which part the frame condition. *)
Local Hint Extern 1 (?ls ---> ?inv ?env :: ?fr :: nil) => is_evar inv; is_evar fr;
  let rec finder ls :=
    match eval hnf in ls with
      | ?x env :: _ :: _ =>
        match goal with
          | [ y : _ -> hprop |- _ ] =>
            match x with
              | y => solve [ equate inv y; sepLemma ]
            end
        end
      | _ :: ?ls => finder ls
    end in
    finder ls : sep0.

Hint Extern 0 (SPArg.exec _ _ _) => unfold SPArg.exec; simpl; reflexivity : sep0.

Theorem treeOpsOk : moduleOk treeOps.
  structured; abstract sep.
Qed.
