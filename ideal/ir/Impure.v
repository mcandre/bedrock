Require Import Malloc Typed.


Module Type OPT.
  Parameter opt : forall model, (model -> word -> sprop) -> option model -> nat -> sprop.

  Axiom opt_O_fwd : forall model rep m p, p = 0
    -> opt model rep m p ===> [< m = None >].

  Axiom opt_O_bwd : forall model rep m p, p = 0
    -> [< m = None >] ===> opt model rep m p.

  Axiom opt_S_fwd : forall model rep m p, p <> 0
    -> opt model rep m p ===> Ex m', [< m = Some m' >] * !{rep m' p}.

  Axiom opt_S_bwd : forall model m' rep m p, p <> 0
    -> [< m = Some m' >] * !{rep m' p} ===> opt model rep m p.
End OPT.

Module Opt : OPT.
  Open Scope Sep_scope.

  Definition opt model (rep : model -> word -> sprop) (m : option model) (p : nat) :=
    match m with
      | None => [< p = 0 >]
      | Some m' => [< p <> 0 >] * !{rep m' p}
    end.

  Theorem opt_O_fwd : forall model rep m p, p = 0
    -> opt model rep m p ===> [< m = None >].
    destruct m; sepLemma.
  Qed.

  Theorem opt_O_bwd : forall model rep m p, p = 0
    -> [< m = None >] ===> opt model rep m p.
    sepLemma.
  Qed.

  Theorem opt_S_fwd : forall model rep m p, p <> 0
    -> opt model rep m p ===> Ex m', [< m = Some m' >] * !{rep m' p}.
    destruct m; sepLemma.
  Qed.

  Theorem opt_S_bwd : forall model m' rep m p, p <> 0
    -> [< m = Some m' >] * !{rep m' p} ===> opt model rep m p.
    sepLemma.
  Qed.
End Opt.

Import Opt.
Export Opt.

Implicit Arguments opt [model].


Definition ptr : type1 word := {|
  Model1 := nil;
  Typing1 := fun p _ => {| Pure := [< True >];
    Impure := Ex v, p ==> v |}
  |}.

Definition pointer (t : type1 word) : type1 word := {|
  Model1 := (word : Type) :: Model1 t;
  Typing1 := fun w ms => {| Pure := Pure (Typing1 t (fst ms) (snd ms));
    Impure := (w ==> fst ms * Impure (Typing1 t (fst ms) (snd ms)))%Sep |}
  |}.

Definition chunk (sz : nat) : type1 word := {|
  Model1 := nil;
  Typing1 := fun w _ => {| Pure := [< w <> 0 >];
    Impure := !{allocated w sz} |}
  |}.

Definition optional (t : type1 word) : type1 word := {|
  Model1 := option (models (Model1 t)) :: nil;
  Typing1 := fun w ms => {| Pure := (Al m', [< fst ms = Some m' >] --> Pure (Typing1 t w m'))%PropX;
    Impure := !{opt (fun m' w' => Impure (Typing1 t w' m')) (fst ms) w} |}
  |}.

Definition heap : type0 := {|
  Model0 := nil;
  Typing0 := fun _ => {| Pure := [< True >];
    Impure := !{mallocHeap 0} |}
  |}.

Definition invariant (p : hprop) := {|
  Model0 := nil;
  Typing0 := fun _ => {| Pure := [< True >];
    Impure := ![p] |}
  |}.


(* This heuristic figures out which part of a state is an invariant and which part the frame condition. *)
Hint Extern 1 (?ls ---> ?inv :: ?fr :: nil) => is_evar inv; is_evar fr;
  let rec finder ls :=
    match eval hnf in ls with
      | ?x :: _ :: _ =>
        match goal with
          | [ y : hprop |- _ ] =>
            match x with
              | y => solve [ equate inv y; sepLemma ]
            end
        end
      | _ :: ?ls => finder ls
    end in
    finder ls : sep0.

Ltac makeDarnSure lemma := apply lemma; womega.

Ltac witness T k :=
  match T with
    | unit => k tt
    | prod ?T1 ?T2 =>
      witness T1 ltac:(fun m1 =>
        witness T2 ltac:(fun m2 =>
          k (m1, m2)))
    | _ => let x := fresh "x" in evar (x : T); let y := eval unfold x in x in clear x; k y
  end.

Hint Extern 1 (opt _ _ _ ===> _) => makeDarnSure opt_O_fwd : Forward.
Hint Extern 1 (_ ===> opt _ _ _) => makeDarnSure opt_O_bwd : Backward.

Hint Extern 1 (opt _ _ _ ===> _) => makeDarnSure opt_S_fwd : SafeAddress Forward.
Hint Extern 1 (_ ===> opt (model := ?T) _ _ _) =>
  witness T ltac:(fun v =>
    makeDarnSure (opt_S_bwd T v)) : Backward.

Ltac isNum n :=
  match eval hnf in n with
    | O => idtac
    | S ?n' => isNum n'
  end.

Hint Extern 1 (allocated _ (_ + ?n) ===> _) => isNum n; apply (allocated_expose_fwd n); womega : Forward.
Hint Extern 1 (_ ===> allocated _ (_ + ?n)) => isNum n; apply (allocated_expose_bwd n); womega : Backward.
