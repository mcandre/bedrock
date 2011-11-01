Require Import Mir.


(** Function to add two numbers *)

Definition addS : spec := st ~> FUNC st
  PRE[m0, arg] [< True >]
  POST[m1, rv] [< rv = arg 0 + arg 1 >].

Definition add := bmodule {{
  bfunction "add" Args [["x", "y"]] [addS] {
    Return $"x" + $"y"
  }
}}.

Theorem addOk : moduleOk add.
  structured; sep.
Qed.


(** Swapping memory values *)

Definition swap := bmodule {{
  bfunction "swap" Args [["a", "b"]] [st ~> Ex fr, Ex a, Ex b, FUNC st
    PRE [m, arg] ![ arg 0 ==> a * arg 1 ==> b * ![fr] ] m
    POST [m', r] ![ arg 1 ==> a * arg 0 ==> b * ![fr] ] m' ] {
    "tmp" <- $[$"a"];;
    $"a" <$- $[$"b"];;
    $"b" <$- $"tmp";;
    Return 0
  }
}}.

Theorem swapOk : moduleOk swap.
  structured; sep.
Qed.


(** A test program for addition *)

Definition testAdd := bimport [[ "add" @ [addS] ]]
  bmodule {{
    bfunction "main" [st ~> FUNC st
      PRE[_, _] [< True >]
      POST[_, rv] [< rv = 42 >] ] {

      Call "add" Args #10, #30
      [st ~> CALLi st
        PRE[_, _, rv'] [< rv' = 40 >]
        POST[_, rv] [< rv = 42 >] ];;
      
      Return Retv + 2
    }
  }}.

Theorem testAddOk : moduleOk testAdd.
  structured; abstract sep.
Qed.

Definition testAddFull := link add testAdd.

Theorem testAddFullOk : moduleOk testAddFull.
  linkOk addOk testAddOk.
Qed.

Definition lo : sizedLayout testAddFull.
  buildLayout.
Defined.

Eval compute in assemble testAddFull lo.
