Require Import Malloc Typed Pure Impure SlList BabyTyped.


(** A function applier *)

Definition appS : spec := TYPED
  PRE[arg]
    arg 0 :: (function
      PRE[arg]
        arg 0 :: slList any
      POST[rv]
        rv :: slList any),,
    arg 1 :: slList any
  POST[ret]
    ret :: slList any.

Definition app := bmodule {{
  bfunction "app" Args [["f", "x"]] [appS] {
    TailCall $"f" Args $"x"
  }
}}.

Theorem appOk : moduleOk app.
  structured; abstract slList.
Qed.

Definition testApp := bimport [[ "reverse" @ [reverseS], "app" @ [appS] ]] bmodule {{
  bfunction "sillyReverse" Args [["ls"]] [reverseS] {
    "f" <-- "reverse";;
    TailCall "app" Args $"f", $"ls"
  }
}}.

Theorem testAppOk : moduleOk testApp.
  structured; abstract slList.
Qed.


(** List iteration *)

Definition iterS : spec := TYPED
  PRE[arg]
    arg 0 :: (function
      PRE[arg]
        arg 0 :: slList any
      POST[_]
        arg 0 :: slList any),,
    arg 1 :: slList (slList any)
  POST[_]
    arg 1 :: slList (slList any).

Definition iter := bmodule {{
  bfunction "iter" Args [["f", "ls"]] [iterS] {
    [TYPEDi
      PRE[x]
        x "f" :: (function
          PRE[arg]
            arg 0 :: slList any
          POST[_]
            arg 0 :: slList any),,
        x "ls" :: slList (slList any)
      POST[_]
        x "ls" :: slList (slList any)]
    While ($"ls" != 0) {
      "data" <- $[^data $"ls"];;
      "ls" <- $[^next $"ls"];;
      Call $"f" Args $"data"
      [TYPEDi
        PRE[x]
          x "f" :: (function
            PRE[arg]
              arg 0 :: slList any
            POST[_]
              arg 0 :: slList any),,
          x "ls" :: slList (slList any)
        POST[_]
          x "ls" :: slList (slList any)]
    };;

    Return 0
  }
}}.

Theorem iterOk : moduleOk iter.
  structured; abstract slList.
Qed.


(** List mapping *)

Definition mapS : spec := Exi inv, TYPED
  PRE[arg]
    arg 0 :: (function
      PRE[arg]
        arg 0 :: slList any,,
        invariant inv
      POST[rv]
        rv :: slList any,,
        invariant inv),,
    arg 1 :: slList (slList any),,
    invariant inv
  POST[_]
    arg 1 :: slList (slList any),,
    invariant inv.

Definition map := bmodule {{
  bfunction "map" Args [["f", "ls"]] [mapS] {
    [Exi inv, TYPEDi
      PRE[x]
        x "f" :: (function
          PRE[arg]
            arg 0 :: slList any,,
            invariant inv
          POST[rv]
            rv :: slList any,,
            invariant inv),,
        x "ls" :: slList (slList any),,
        invariant inv
      POST[_]
        x "ls" :: slList (slList any),,
        invariant inv]
    While ($"ls" != 0) {
      "data" <- $[^data $"ls"];;
      Call $"f" Args $"data"
      [Exi inv, Exi next, TYPEDc
        PRE[x, rv]
          x "f" :: (function
            PRE[arg]
              arg 0 :: slList any,,
              invariant inv
            POST[rv]
              rv :: slList any,,
              invariant inv),,
          x "ls" :: slListNode next,,
          next :: slList (slList any),,
          rv :: slList any,,
          invariant inv
        POST[_]
          x "ls" :: slList (slList any),,
          invariant inv];;

      ^data $"ls" <$- Retv;;
      "ls" <- $[^next $"ls"]
    };;

    Return 0
  }
}}.

Theorem mapOk : moduleOk map.
  structured; abstract slList.
Qed.


(** Lists of functions *)

Definition applyAllS : spec := TYPED
  PRE[arg]
    arg 0 :: slList (function
      PRE[arg]
        arg 0 :: slList any
      POST[_]
        arg 0 :: slList any),,
    arg 1 :: slList any
  POST[_]
    arg 0 :: slList (function
      PRE[arg]
        arg 0 :: slList any
      POST[_]
        arg 0 :: slList any),,
    arg 1 :: slList any.

Definition applyAll := bmodule {{
  bfunction "applyAll" Args [["fs", "x"]] [applyAllS] {
    [TYPEDi
      PRE[x]
        x "fs" :: slList (function
          PRE[arg]
            arg 0 :: slList any
          POST[_]
            arg 0 :: slList any),,
        x "x" :: slList any
      POST[_]
        x "fs" :: slList (function
          PRE[arg]
            arg 0 :: slList any
          POST[_]
            arg 0 :: slList any),,
        x "x" :: slList any]
    While ($"fs" != 0) {
      "f" <- $[^data $"fs"];;
      "fs" <- $[^next $"fs"];;
      Call $"f" Args $"x"
      [TYPEDi
        PRE[x]
          x "fs" :: slList (function
            PRE[arg]
              arg 0 :: slList any
            POST[_]
              arg 0 :: slList any),,
          x "x" :: slList any
        POST[_]
          x "fs" :: slList (function
            PRE[arg]
              arg 0 :: slList any
            POST[_]
              arg 0 :: slList any),,
          x "x" :: slList any]
    };;

    Return 0
  }
}}.

Theorem applyAllOk : moduleOk applyAll.
  structured; abstract slList.
Qed.
