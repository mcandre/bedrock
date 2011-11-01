Require Import Mir IfStar.


Definition test := bmodule {{
  bfunction "test" Args [["n"]] [st ~> FUNC st
    PRE[_, _] [< True >]
    POST[_, rv] [< rv = 3 >] ] {
    If* ((($"n" >= 3) && ($"n" < 4)) || !(($"n" < 3) || ($"n" > 3))) {
      Return $"n"
    } else {
      Return 3
    }
  }
}}.

Theorem testOk : moduleOk test.
  structured; abstract ifStar.
Qed.
