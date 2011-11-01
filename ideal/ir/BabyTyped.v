Require Import Malloc Typed Pure Impure SlList.


(** The increment function *)

Definition incS : spec := TYPED
  PRE [arg]
    arg 0 :: any
  POST [ret]
    ret :: any.

Definition inc := bmodule {{
  bfunction "inc" [incS] {
    Return $#0 + 1
  }
}}.

Theorem incOk : moduleOk inc.
  structured; sep.
Qed.


(** Lists of numbers *)

Definition lengthS : spec := TYPED
  PRE [arg]
    arg 0 :: slList any
  POST [ret]
    arg 0 :: slList any,,
    ret :: any.

Definition reverseS : spec := TYPED
  PRE [arg]
    arg 0 :: slList any
  POST [ret]
    ret :: slList any.

Definition appendS : spec := TYPED
  PRE [arg]
    arg 0 :: slList any,,
    arg 1 :: slList any
  POST [ret]
    ret :: slList any.

Definition lists := bmodule {{
  bfunction "length" Args [["ls"]] [lengthS] {
    "count" <- 0;;

    [TYPEDi
      PRE [x]
        x "ls" :: slList any
      POST [ret]
        x "ls" :: slList any]
    While ($"ls" != 0) {
      "count" <- $"count" + 1;;
      "ls" <- $[^next $"ls"]
    };;

    Return $"count"
  } with bfunction "reverse" Args [["in"]] [reverseS] {
    "out" <- 0;;

    [TYPEDi
      PRE [x]
        x "in" :: slList any,,
        x "out" :: slList any
      POST [ret]
        ret :: slList any]
    While ($"in" != 0) {
      "tmp" <- $[^next $"in"];;
      ^next $"in" <$- $"out";;
      "out" <- $"in";;
      "in" <- $"tmp"
    };;

    Return $"out"
  } with bfunction "append" Args [["first", "second"]] [appendS] {
    If ($"first" == 0) {
      Return $"second"
    } else {
      "head" <- $"first";;

      [TYPEDi
        PRE [x]
          x "first" :: slListNonempty any,,
          x "second" :: slList any
        POST [ret]
          x "first" :: slList any,,
          ret :: equals (x "head")]
      While ($[^next $"first"] != 0) {
        "first" <- $[^next $"first"]
      };;

      ^next $"first" <$- $"second";;
      Return $"head"
    }
  }
}}.

Theorem listsOk : moduleOk lists.
  structured; abstract sep.
Qed.


(** Lists of lists *)

Definition length2S : spec := TYPED
  PRE [arg]
    arg 0 :: slList (slList any)
  POST [ret]
    arg 0 :: slList (slList any).

Definition concatS : spec := TYPED
  PRE [arg]
    heap,,
    arg 0 :: slList (slList any)
  POST [ret]
    heap,,
    ret :: slList any.

Definition lists2 := bimport [[ "free" @ [freeS], "append" @ [appendS] ]]
  bmodule {{
    bfunction "length2" Args [["ls"]] [length2S] {
      "count" <- 0;;

      [TYPEDi
        PRE [x]
          x "ls" :: slList (slList any)
        POST [ret]
          x "ls" :: slList (slList any)]
      While ($"ls" != 0) {
        "count" <- $"count" + 1;;
        "ls" <- $[^next $"ls"]
      };;

      Return $"count"
    } with bfunction "concat" Args [["lists"]] [concatS] {
      "result" <- 0;;

      [TYPEDi
        PRE [x]
          heap,,
          x "result" :: slList any,,
          x "lists" :: slList (slList any)
        POST [ret]
          heap,,
          ret :: slList any]
      While ($"lists" != 0) {
        "current" <- $[^data $"lists"];;
        "next" <- $[^next $"lists"];;

        Call "free" Args #0, $"lists", #0
        [TYPEDi
          PRE [x]
            heap,,
            x "result" :: slList any,,
            x "current" :: slList any,,
            x "next" :: slList (slList any)
          POST [ret]
            heap,,
            ret :: slList any];;

        Call "append" Args $"result", $"current"
        [TYPEDc
          PRE [x, ret]
            heap,,
            ret :: slList any,,
            x "next" :: slList (slList any)
          POST [ret]
            heap,,
            ret :: slList any];;

        "result" <- Retv;;
        "lists" <- $"next"
      };;

      Return $"result"
    }
  }}.

Theorem lists2Ok : moduleOk lists2.
  structured; abstract sep.
Qed.
