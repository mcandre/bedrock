Require Import Typed.


Definition any {dom} : type1 dom := {|
  Model1 := nil;
  Typing1 := fun _ _ => {| Pure := [< True >];
    Impure := emp |}
  |}.

Definition equals {dom} (v : dom) : type1 dom := {|
  Model1 := nil;
  Typing1 := fun v' _ => {| Pure := [< v' = v >];
    Impure := emp |}
  |}.

Import PropX.
Local Open Scope PropX_scope.

Definition function_ (pre : args -> type0) (post : args -> word -> type0) : type1 word := {|
  Model1 := nil;
  Typing1 := fun w _ => {| Pure := ExX, Cptr w (Var VO)
    /\ Al st, [< Frames st <> nil >]
    --> AlX, Al fr, ^[typingHolds (pre (Argl st)) (Mem st) fr]
    /\ Cptr (Retptr st) (Var VO)
    /\ (Al st', [< Frames st' = Frames st >]
      /\ ^[typingHolds (post (Argl st) (Retval st')) (Mem st') fr] --> VO @ st')
    --> VS VO @ st;
    Impure := emp |}
|}.

Notation "'function' 'PRE' [ args ] P 'POST' [ rv ] Q" :=
  (function_ (fun args => P) (fun args rv => Q))
  (at level 62) : Typed_scope.

Definition function1 T (pre : T -> args -> type0) (post : T -> args -> word -> type0) : type1 word := {|
  Model1 := T :: nil;
  Typing1 := fun w ms => {| Pure := ExX, Cptr w (Var VO)
    /\ Al st, [< Frames st <> nil >]
    --> AlX, Al fr, ^[typingHolds (pre (fst ms) (Argl st)) (Mem st) fr]
    /\ Cptr (Retptr st) (Var VO)
    /\ (Al st', [< Frames st' = Frames st >]
      /\ ^[typingHolds (post (fst ms) (Argl st) (Retval st')) (Mem st') fr] --> VO @ st')
    --> VS VO @ st;
    Impure := emp |}
|}.

Notation "'function' [ x ] 'PRE' [ args ] P 'POST' [ rv ] Q" :=
  (function1 _ (fun x args => P) (fun x args rv => Q))
  (at level 62) : Typed_scope.
