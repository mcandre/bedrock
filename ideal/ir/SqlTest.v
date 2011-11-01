Require Import Malloc Typed Pure Impure SqlTree Sql SlList.


(** Test INSERT *)

Definition testInsert := bimport [[ "malloc" @ [mallocS], "insert" @ [insertS] ]]
  bmodule {{
    bfunction "testInsert" Args [[ "table", "key" ]] [TYPED
      PRE[arg]
        heap,,
        arg 0 :: sqlTree 3
      POST[_]
        heap,,
        arg 0 :: sqlTree 3] {
     (INSERT INTO "table"
       VALUES ($"key", #1, #2)
       INVARIANT[x] ?
       POST[_] heap,, x "table" :: sqlTree 3);;

      Return 0
    }
  }}.

Theorem testInsertOk : moduleOk testInsert.
  structured; abstract sep.
Qed.


(** Test SELECT *)

Definition testSelect := bimport [[ "malloc" @ [mallocS], "free" @ [freeS],
                                    "iter" @ [iterS], "pointQuery" @ [iterS] ]]
  bmodule {{
    bfunction "getList" Args [[ "table", "acc" ]] [TYPED
      PRE[arg]
        heap,,
        arg 0 :: sqlTree 3,,
        arg 1 :: pointer (slList any)
      POST[_]
        heap,,
        arg 0 :: sqlTree 3,,
        arg 1 :: pointer (slList any)] {
     (SELECT *
      FROM "table"
      COLUMNS 3
      WHERE (3.#0 == #1) && (3.#1 + 3.#2 < #6)
      CAPTURING ("acc")
      INVARIANT[x] (x "acc" :: pointer (slList any))
      POST[_] (heap,,
               x "table" :: sqlTree 3,,
               x "acc" :: pointer (slList any))
      FOREACH
        Call "malloc" Args #0, #0
        [TYPEDc
          PRE[x, rv]
            heap,,
            x "acc" :: pointer (slList any),,
            x "tuple" :: chunk 3,,
            rv :: chunk 2
          POST[_]
            heap,,
            x "acc" :: pointer (slList any),,
            x "tuple" :: chunk 3];;

        ^data Retv <$- $[$"tuple"];;
        ^next Retv <$- $[$"acc"];;
        $"acc" <$- Retv);;

      Return 0
    }
  }}.

(* Have to define a custom version of [structured] because of horrible performance of reduction.... *)

Import SP.

Ltac structuredSql := apply bmoduleOk; [
  reflexivity
  | unfold getArgs, setArgs, fold_right; simpl exports;
    repeat match goal with
             | |- Forall _ _ => constructor
           end; unfold SCode; auto 999999 with Structured
  | unfold vcPasses; simpl exports;
    cbv beta iota zeta
      delta [IoutPostcondition IoutCode CinPrecondition CinExit CinInject
        CoutPostcondition CoutCode CoutConditions ScLabT ScEntry
        ScCompile Skip Halt StraightLine GotoI WithCode SP.Goto Assert_
        Call_ CallI Use_ SeqI Seq toStructured If_ While_ exports SName
        SSpec SCode Locs Exps nullInstrs makeIin labelT
        IfStar.IfStar Lambda.Lambda Wrap.Wrap Select Select0 Pack' Pack Unpack' Unpack
        setArgs getArgs fold_right];
      simpl;
        repeat match goal with
                 | |- Forall _ _ => constructor; intros
               end; simpl in *
].

Theorem testSelectOk : moduleOk testSelect.
  structuredSql; abstract sep.
Qed.
