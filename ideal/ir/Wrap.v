Require Import Mir.
Import SP.


Section Wrap.
  Variable c : scode.
  Variable conds : forall GT, compileIn (ScLabT (toStructured c)) GT -> instrsOut -> list (layout pc GT -> prop * prop).

  Definition Wrap :=
    let c' := toStructured c in
      SStructured (Scode (ScEntry c') (fun _ is cin =>
        let cout := ScCompile c' is cin in
          CompOut (CoutPostcondition cout) (CoutCode cout)
            (conds _ cin (is (CinPrecondition cin))))).

  Hypothesis Hconds : forall GT is cin,
    AllS (fun p => forall specs lo st, interp specs (fst (p lo) st) -> interp specs (snd (p lo) st))
    (conds GT cin (is (CinPrecondition cin)))
    -> AllS (fun p => forall specs lo st, interp specs (fst (p lo) st) -> interp specs (snd (p lo) st))
    (CoutConditions (ScCompile (GT := GT) (toStructured c) is cin)).

  Variables imports exports : list (string * prop).

  Hypothesis Hstructured : match c with
                             | SStructured _ => True
                             | _ => False
                           end.

  Hypothesis Hok : scodeOk imports exports c.

  Theorem WrapOk : scodeOk imports exports Wrap.
    unfold Wrap; destruct c; simpl in *; try tauto; destruct Hok; split; simpl; intuition.
  Qed.
End Wrap.
