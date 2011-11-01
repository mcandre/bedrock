Require Import Mir.
Export Mir.

Set Implicit Arguments.

Fixpoint models (ls : list Type) : Type :=
  match ls with
    | nil => unit
    | t :: ls => t * models ls
  end%type.

Fixpoint models1 {ls1 ls2 : list Type} : models (ls1 ++ ls2) -> models ls1 :=
  match ls1 with
    | nil => fun _ => tt
    | _ :: _ => fun ms => (fst ms, models1 (snd ms))
  end.

Fixpoint models2 {ls1 ls2 : list Type} : models (ls1 ++ ls2) -> models ls2 :=
  match ls1 with
    | nil => fun ms => ms
    | _ :: _ => fun ms => models2 (snd ms)
  end.

Record typing := {
  Pure : PropX pc state;
  Impure : sprop
}.
Record type0 := {
  Model0 : list Type;
  Typing0 : models Model0 -> typing
}.
Record type1 (dom : Type) := {
  Model1 : list Type;
  Typing1 : dom -> models Model1 -> typing
}.

Definition top : type0 := {|
  Model0 := nil;
  Typing0 := fun _ => {| Pure := Inj True;
    Impure := emp |}
  |}.
Definition hasType dom (v : dom) (t : type1 dom) : type0 := {|
  Model0 := Model1 t;
  Typing0 := Typing1 t v
|}.
Definition merge (tp1 tp2 : type0) : type0 := {|
  Model0 := Model0 tp1 ++ Model0 tp2;
  Typing0 := fun ms => {| Pure := And (Pure (Typing0 tp1 (models1 ms))) (Pure (Typing0 tp2 (models2 ms)));
    Impure := Star (Impure (Typing0 tp1 (models1 ms))) (Impure (Typing0 tp2 (models2 ms))) |}
|}.

Notation "?" := top : Typed_scope.
Infix "::" := hasType : Typed_scope.
Infix ",," := merge (right associativity, at level 61) : Typed_scope.

Delimit Scope Typed_scope with Typed.

Fixpoint typingHolds' (m : mem) fr (ms : list Type) : (models ms -> typing) -> PropX pc state :=
  match ms with
    | nil => fun tp => ![ Impure (tp tt) * ![fr] ] m /\ Pure (tp tt)
    | _ :: ms' => fun tp => Ex x, typingHolds' m fr ms' (fun ms => tp (x, ms))
  end%PropX.

Definition typingHolds (tp : type0) (m : mem) fr : PropX pc state :=
  typingHolds' m fr (Model0 tp) (Typing0 tp).

Notation "'TYPED' 'PRE' [ args ] P 'POST' [ rv ] Q" :=
  (st ~> Ex fr, FUNC st
    PRE [m0, args] typingHolds P%Typed m0 fr
    POST [m1, rv] ^[typingHolds Q%Typed m1 fr])%Mir%PropX
  (at level 100, args at level 0, rv at level 0, only parsing).

Notation "'TYPEDi' 'PRE' [ xs ] P 'POST' [ rv ] Q" :=
  (st ~> Ex fr, FUNCi st
    PRE [m0, xs] typingHolds P%Typed m0 fr
    POST [m1, rv] ^[typingHolds Q%Typed m1 fr])%Mir%PropX
  (at level 100, xs at level 0, rv at level 0, only parsing).

Notation "'TYPEDc' 'PRE' [ xs , rv' ] P 'POST' [ rv ] Q" :=
  (st ~> Ex fr, CALLi st
    PRE [m0, xs, rv'] typingHolds P%Typed m0 fr
    POST [m1, rv] ^[typingHolds Q%Typed m1 fr])%Mir%PropX
  (at level 100, xs at level 0, rv' at level 0, rv at level 0, only parsing).

Notation "'Exi' v , p" := (fun st => PropX.Exists (fun v => p st)) (at level 100).
