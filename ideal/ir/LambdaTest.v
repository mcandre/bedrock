Require Import Mir Lambda.


Definition test := bmodule {{
  bfunction "test" [st ~> FUNC st
    PRE[_, _] [< True >]
    POST[_, rv] [< rv = 3 >] ] {
    "f" <-- blambda [["n"]] [st ~> FUNC st
      PRE[_, arg] [< True >]
      POST[_, rv] [< rv = arg 0 + 1 >] ] {
        Return $"n" + 1
      };;

    Call $"f" Args #1
    [st ~> CALLi st
      PRE[_, _, rv'] [< True >]
      POST[_, rv] [< rv = rv' + 1 >] ];;

    Return Retv + 1
  }
}}.

Theorem testOk : moduleOk test.
  structured; abstract sep.
Qed.
