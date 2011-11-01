Require Export Semantics.

Definition XenExt := unit.
Definition XenExtOwns (x : XenExt) (addr : Word.word 64) : Prop := False.

Module SPArg.
  Definition pc := pc.
  Definition state := state XenExt.
  Definition instr := instr.
  Definition jmp := control.

  Definition exec : instr -> state -> state -> Prop := @exec _ XenExtOwns.
  Definition resolve : jmp -> state -> pc -> Prop := @resolve _ XenExtOwns.
  Definition pc_eq := @weq W64.

  Definition directJump (p : pc) := JMPd p.
  Theorem resolve_directJump : forall i s, resolve (directJump i) s i.
    intros; constructor.
  Qed.
  Theorem resolve_directJump_unique : forall i s i', resolve (directJump i) s i' -> i' = i.
    intros. inversion H. auto.
  Qed.

  Definition exp := rval W64.
  Definition eval (e : exp) (s : state) (n : pc) : Prop := evalR XenExtOwns s e n.

  Record cond' : Type := 
  { csize : wsize
  ; Code : cc
  ; valL : lval csize
  ; valR : rval csize 
  ; notMems : notBothMem valL valR }.
  Definition cond := cond'.
  Definition decide c s b s' := 
    exists l : word (csize c), exists r, evalL XenExtOwns s (valL c) l /\ 
      evalR XenExtOwns s (valR c) r /\ 
      cmpFlagVals l r s s' /\
      b =  checkCC (Code c) (Flags s').

  Definition conditionalJump c i1 i2 := (BOP CMP (valL c) (valR c) (notMems c) :: nil, JCC (Code c) i1 i2).
  Theorem resolve_conditionalJump : forall b s s' i1 i2 b', decide b s b' s'
    -> execs exec (fst (conditionalJump b i1 i2)) s s'
    /\ resolve (snd (conditionalJump b i1 i2)) s' (if b' then i1 else i2).
    unfold decide, resolve. simpl. intros. destruct H as [ ? [ ? [ ] ]]. intuition.
    eexists; split; eauto. econstructor; eauto; reflexivity.
    destruct b'; econstructor; eauto.
  Qed.    
  Theorem resolve_conditionalJump_unique : forall b s s' i1 i2 i, 
       execs exec (fst (conditionalJump b i1 i2)) s s'
    -> resolve (snd (conditionalJump b i1 i2)) s' i
    -> exists b', decide b s b' s' /\ i = if b' then i1 else i2.
    unfold decide, resolve. simpl. intros. destruct H; intuition. subst.
    inversion H1; clear H1; subst.
    Require Import Eqdep.
    apply inj_pair2 in H2. apply inj_pair2 in H3. subst.
    inversion H0; subst; eauto 10.
  Qed.

  Definition indirectJump := JMP.
  Theorem resolve_indirectJump : forall e s i, eval e s i
    -> resolve (indirectJump e) s i.
    unfold resolve; econstructor; eauto.
  Qed.
  Theorem resolve_indirectJump_unique : forall e s i, resolve (indirectJump e) s i
    -> eval e s i.
    inversion 1; eauto.
  Qed.
 
End SPArg.

Module SP := Structured.Make ( SPArg ).

(** Notations **)

Coercion lReg : reg >-> lval.

(** Instruction Notations **)

Definition AddrPlus (a b : Addr) : Addr :=
  {| base := match base a, base b with 
               | Some _, _ => base a
               | _, _ => base b
             end
  ; width := match width a, width b with
               | AI0, x => x
               | x, _ => x 
             end
  ; disp  := match disp a, disp b with
               | None, x => x
               | x,None => x
               | Some x, Some y => Some (x ^+ y)
             end
  |}.

Definition AddrNeg (a : Addr) : Addr :=
  {| base := base a
  ; width := width a
  ; disp  := match disp a with
               | None => None
               | Some x => Some (^~ x)
             end
  |}.

Definition nat_to_addr (a : nat) : Addr :=
  {| base := None
  ; width := AI0
  ; disp  := Some (inj _ a)
  |}.
Coercion nat_to_addr : nat >-> Addr.

Delimit Scope addr_scope with addr.
Bind Scope addr_scope with Addr.

Definition index (n : nat) (r : reg W64) : notRsp r -> AddrIdx :=
  match n with
    | 1 => AI1 r
    | 2 => AI2 r
    | 4 => AI4 r
    | 8 => AI8 r
    | _ => fun _ => AI0 
  end.

Delimit Scope SP_scope with SP.

Notation "! r" := {| base := @Some (reg W64) r ; width := AI0 ; disp := None |} (at level 20) : addr_scope.
Notation "r ** w" := {| base := None ; width := (@index (w%nat) r I) ; disp := None |} (at level 20) : addr_scope.

Notation "x ++ y" := (AddrPlus x%addr y%addr) (at level 60, right associativity) : addr_scope.
Notation "x -- y" := (AddrPlus x%addr (AddrNeg y%addr)) (at level 60, right associativity) : addr_scope.

Notation "$[ r ]" := (@lMem r%addr W64).
Notation "$B[ r ]" := (@lMem r%addr W8).

Coercion lval_to_rval : lval >-> rval.

Notation "rv1 == rv2" := (@SPArg.Build_cond' _ ccZ rv1 rv2 I) (no associativity, at level 70) : SP_scope.
Notation "rv1 != rv2" := (@SPArg.Build_cond' _ (ccN ccZ) rv1 rv2 I) (no associativity, at level 70) : SP_scope.
Notation "rv1 < rv2" := (@SPArg.Build_cond' _ ccB rv1 rv2 I) : SP_scope.
Notation "rv1 <= rv2" := (@SPArg.Build_cond' _ ccBE rv1 rv2 I) : SP_scope.
Notation "rv1 > rv2" := (@SPArg.Build_cond' _ (ccN ccBE) rv1 rv2 I) : SP_scope.
Notation "rv1 >= rv2" := (@SPArg.Build_cond' _ (ccN ccB) rv1 rv2 I) : SP_scope.

Notation "lhs = rhs" :=  (fun _ _ => SP.StraightLine (BOP MOV lhs rhs I)) (no associativity, at level 70) : SP_scope.
Notation "lhs += rhs" := (fun _ _ => SP.StraightLine (BOP ADD lhs rhs I)) (no associativity, at level 70) : SP_scope.
Notation "lhs -= rhs" := (fun _ _ => SP.StraightLine (BOP SUB lhs rhs I)) (no associativity, at level 70) : SP_scope.
(*
Notation "lhs *= rhs" := (fun _ _ => SP.StraightLine (BOP MUL lhs rhs I)) (no associativity, at level 70) : SP_scope.
*)
Require Import NArith.
Notation "lhs ::= rhs" := (fun _ _ => SP.StraightLine (MOVi lhs (@inj _ WordView_N W64 rhs%N))) (no associativity, at level 70) : SP_scope.

Notation "'push' r" := (fun _ _ => SP.StraightLine (PUSH r)) (no associativity, at level 70) : SP_scope.
Notation "'pop' r" := (fun _ _ => SP.StraightLine (POP r)) (no associativity, at level 70) : SP_scope.

Notation "c1 ;; c2" := (fun imp exp => SP.Seq (c1 imp exp) (c2 imp exp))
  (right associativity, at level 95) : SP_scope.

Class Gotoable (T : Type) : Type :=
{ Goto  : T -> list (string * SP.prop) -> list (string * SP.prop) -> SP.scode
; Call_ : T -> SP.prop -> list (string * SP.prop) -> list (string * SP.prop) -> SP.scode
}.

(** TODO: This is a "bad" calling convention **)
Global Instance Gotoable_string : Gotoable string :=
{ Goto := fun s im ex => SP.Goto (imports := im) (exports := ex) s
; Call_ := fun s post im ex => SP.Call_ (imports := im) (exports := ex) (fun pc => MOVi RBP pc :: nil) s post 
}.

Global Instance Gotoable_reg64 : Gotoable (reg W64) :=
{ Goto := fun s im ex => SP.GotoI s
; Call_ := fun s post im ex => SP.CallI (fun pc => MOVi RBP pc :: nil) s post 
}.

Global Instance Gotoable_rval64 : Gotoable (rval W64) :=
{ Goto := fun s im ex => SP.GotoI s
; Call_ := fun s post im ex => SP.CallI (fun pc => MOVi RBP pc :: nil) s post 
}.

Global Instance Gotoable_lval64 : Gotoable (lval W64) :=
{ Goto := fun s im ex => SP.GotoI s
; Call_ := fun s post im ex => SP.CallI (fun pc => MOVi RBP pc :: nil) s post 
}.


Notation "'Use' [ pf ]" := (fun imp exp => SP.Use_ _ (fun _ => pf%nat)) (no associativity, at level 95) : SP_scope.
Notation "'Use' st [ pf ]" := (fun imp exp => SP.Use_ _ (fun st => pf%nat)) (no associativity, at level 95, st at level 0) : SP_scope.

Notation "'If' c { b1 } 'else' { b2 }" := (fun imp exp => SP.If_ c (b1 imp exp) (b2 imp exp))
  (no associativity, at level 95, c at level 0) : SP_scope.

Notation "[ p ] 'While' c { b }" := (fun imp exp => SP.While_ p c (b imp exp))
  (no associativity, at level 95, c at level 0) : SP_scope.

Definition Skip := fun (_ _ : list (string * SP.prop)) => SP.Skip.
Definition Halt := fun (_ _ : list (string * SP.prop)) => SP.Halt.

Notation "name @ [ p ]" := (name, p) (at level 0, only parsing) : SPimps_scope.
Delimit Scope SPimps_scope with SPimps.

Notation "[[ x , .. , y ]]" := (cons x .. (cons y nil) ..) (only parsing) : SPimps_scope.

Notation "'bfunction' name [ p ] { b }" := (SP.Sfunc name p b%SP)
  (no associativity, at level 95, only parsing) : SPfuncs_scope.
Delimit Scope SPfuncs_scope with SPfuncs.

Notation "'bmodule' fs" := (SP.bmodule_ nil fs%SPfuncs) (no associativity, at level 95, only parsing).
Notation "'bimport' ls 'bmodule' fs" := (SP.bmodule_ ls%SPimps fs%SPfuncs)
  (no associativity, at level 95, only parsing).

Notation "{{ x 'with' .. 'with' y }}" := (cons x .. (cons y nil) ..) (only parsing) : SPfuncs_scope.

Notation "c1 ;; c2" := (fun imp exp => SP.Seq (c1 imp exp) (c2 imp exp))
  (right associativity, at level 95) : SP_scope.

Infix "#" := Regs (no associativity, at level 0).
Notation "st .[ a ]" := (Mem st a) (no associativity, at level 0).

Notation "'Call' rv [ p ]" := (Call_ rv p) (no associativity, at level 95) : SP_scope.

Definition state := state XenExt.

Definition module : Type := module pc state (list instr * control).
Definition step (c : list instr * control) (s1 : state) (i : pc) (s2 : state) : Prop :=
  execs (@exec _ XenExtOwns) (fst c) s1 s2
  /\ resolve XenExtOwns (snd c) s2 i.

Definition moduleOk (m : module) : Prop := moduleOk step (@weq W64) m.

(** Tactics **)
Ltac structured := SP.structured ltac:(unfold Goto, Gotoable_reg64, Gotoable_lval64, Gotoable_rval64, Gotoable_string, Call_, Skip, Halt).

Hint Constructors evalL evalR exec updL MemVal MemUpd.
Hint Unfold SPArg.eval.

Require Import Eqdep Program.
Ltac reduceAll :=
  unfold setFlags in *;
  repeat (unfold setFlags, setFlag, execFlags in *;
          match goal with
           | [ H : evalL _ _ _ _ |- _ ] => generalize dependent H; let F := fresh in intro F; dependent destruction F; [ ]
           | [ H : evalR _ _ _ _ |- _ ] => generalize dependent H; let F := fresh in intro F; dependent destruction F; [ ]
           | [ H : SPArg.exec _ _ _ |- _ ] => inversion H; [ clear H ]
           | [ H : updL _ _ _ _ _ |- _ ] => inversion H; [ clear H ]
           | [ H : rReg _ = rReg _ |- _ ] => injection H; clear H; intros
           | [ H : lReg _ = lReg _ |- _ ] => injection H; clear H; intros
           | [ H : existT _ _ _ = existT _ _ _ |- _ ] => apply inj_pair2 in H
           | [ H : Then _ _ _ _ |- _ ] => destruct H; intuition
         end; try subst; try discriminate); try subst.