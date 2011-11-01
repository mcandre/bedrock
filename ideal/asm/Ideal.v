Require Import Arith String.

Require Import Bedrock.

Export Bedrock.

Set Implicit Arguments.


Definition pc := nat.

Inductive reg := Rret | Rsp | R0 | R1 | R2 | R3 | R4 | R5.

Definition regs := reg -> nat.
Definition mem := nat -> nat.

Record state := State {
  Regs : regs;
  Mem : mem
}.

Definition state0 := State (fun _ => 0) (fun _ => 0).

Definition req : forall x y : reg, {x = y} + {x <> y}.
  decide equality.
Defined.

Definition rupd (rs : regs) (r : reg) (v : nat) : regs := fun r' =>
  if req r' r then v else rs r'.
Definition mupd (m : mem) (a : nat) (v : nat) : mem := fun a' =>
  if eq_nat_dec a' a then v else m a'.

Definition Rupd (st : state) (r : reg) (v : nat) := State (rupd (Regs st) r v) (Mem st).
Definition Mupd (st : state) (a : nat) (v : nat) := State (Regs st) (mupd (Mem st) a v).

Inductive rval :=
| Const : nat -> rval
| RReg : reg -> rval
| RMem : nat -> rval
| RMemI : reg -> nat -> rval.

Inductive lval :=
| LReg : reg -> lval
| LMem : nat -> lval
| LMemI : reg -> nat -> lval.

Inductive binop := Plus | Minus | Times.

Inductive instr :=
| Asgn : lval -> rval -> instr
| Binop : lval -> binop -> rval -> rval -> instr.

Inductive cc := Eq | Ne | Lt | Le.

Inductive jmp :=
| Jmp : pc -> jmp
| JmpI : rval -> jmp
| Jc : cc -> rval -> rval -> pc -> pc -> jmp.

Definition code := (list instr * jmp)%type.

Definition eval (rv : rval) (st : state) : nat :=
  match rv with
    | Const n => n
    | RReg r => Regs st r
    | RMem a => Mem st a
    | RMemI r n => Mem st (Regs st r + n)
  end.

Definition assign (lv : lval) (st : state) (v : nat) : state :=
  match lv with
    | LReg r => Rupd st r v
    | LMem a => Mupd st a v
    | LMemI r n => Mupd st (Regs st r + n) v
  end.

Definition cond (c : cc) (n1 n2 : nat) : bool :=
  match c with
    | Eq => if eq_nat_dec n1 n2 then true else false
    | Ne => if eq_nat_dec n1 n2 then false else true
    | Lt => if le_lt_dec n2 n1 then false else true
    | Le => if le_lt_dec n1 n2 then true else false
  end.

Definition evalBinop (b : binop) : nat -> nat -> nat :=
  match b with
    | Plus => plus
    | Minus => minus
    | Times => mult
  end.

Definition exec (i : instr) (st : state) : state :=
  match i with
    | Asgn lv rv => assign lv st (eval rv st)
    | Binop lv bo rv1 rv2 => assign lv st (evalBinop bo (eval rv1 st) (eval rv2 st))
  end.

Definition resolve (j : jmp) (st : state) : pc :=
  match j with
    | Jmp i => i
    | JmpI rv => eval rv st
    | Jc c rv1 rv2 i1 i2 => if cond c (eval rv1 st) (eval rv2 st) then i1 else i2
  end.

Definition execR i s s' := exec i s = s'.

Definition step (c : code) (s1 : state) (i : pc) (s2 : state) : Prop :=
  execs execR (fst c) s1 s2
  /\ i = resolve (snd c) s2.

Definition module : Type := module pc state code.

Definition moduleOk (m : module) : Prop := moduleOk step eq_nat_dec m.

Hint Unfold step.

Theorem rupd_eq : forall rs r1 v r2,
  r2 = r1
  -> rupd rs r1 v r2 = v.
  unfold rupd; intros; destruct (req r2 r1); intuition.
Qed.

Theorem rupd_ne : forall rs r1 v r2,
  r2 <> r1
  -> rupd rs r1 v r2 = rs r2.
  unfold rupd; intros; destruct (req r2 r1); intuition.
Qed.

Theorem mupd_eq : forall m r1 v r2,
  r2 = r1
  -> mupd m r1 v r2 = v.
  unfold mupd; intros; destruct (eq_nat_dec r2 r1); intuition.
Qed.

Theorem mupd_ne : forall m r1 v r2,
  r2 <> r1
  -> mupd m r1 v r2 = m r2.
  unfold mupd; intros; destruct (eq_nat_dec r2 r1); intuition.
Qed.

Hint Rewrite rupd_eq rupd_ne mupd_eq mupd_ne using auto; congruence : Mac.

Infix "#" := Regs (no associativity, at level 0).
Notation "st .[ a ]" := (Mem st a) (no associativity, at level 0).

Coercion Const : nat >-> rval.

Coercion LReg : reg >-> lval.

Record condition := Condition {
  Code : cc;
  Rval1 : rval;
  Rval2 : rval
}.

Notation "rv1 == rv2" := (Condition Eq rv1 rv2) (no associativity, at level 70) : SP_scope.
Notation "rv1 != rv2" := (Condition Ne rv1 rv2) (no associativity, at level 70) : SP_scope.
Notation "rv1 < rv2" := (Condition Lt rv1 rv2) : SP_scope.
Notation "rv1 <= rv2" := (Condition Le rv1 rv2) : SP_scope.

Delimit Scope SP_scope with SP.

Inductive rhs :=
| Assign : rval -> rhs
| Bop : binop -> rval -> rval -> rhs.

Definition Asgn' (lv : lval) (rs : rhs) :=
  match rs with
    | Assign rv => Asgn lv rv
    | Bop o rv1 rv2 => Binop lv o rv1 rv2
  end.

Coercion Assign : rval >-> rhs.

Notation "x + y" := (Bop Plus x y) : SP_scope.
Notation "x - y" := (Bop Minus x y) : SP_scope.
Notation "x * y" := (Bop Times x y) : SP_scope.

Definition deref (rh : rhs) :=
  match rh with
    | Assign (Const n) => LMem n
    | Assign (RReg r) => LMemI r 0
    | Bop Plus (RReg r) (Const n) => LMemI r n
    | _ => LMem 0
  end.

Notation "$[ a ]" := (deref a) : SP_scope.

Definition lvalToRval (lv : lval) :=
  match lv with
    | LReg r => RReg r
    | LMem n => RMem n
    | LMemI r n => RMemI r n
  end.

Coercion lvalToRval : lval >-> rval.


Module SPArg.
  Definition pc := pc.
  Definition state := state.
  Definition instr := instr.
  Definition jmp := jmp.

  Definition exec := execR.
  Definition resolve j s i := i = resolve j s.
  Definition pc_eq := eq_nat_dec.

  Definition directJump := Jmp.
  Theorem resolve_directJump : forall i s, resolve (directJump i) s i.
    reflexivity.
  Qed.
  Theorem resolve_directJump_unique : forall i s i', resolve (directJump i) s i' -> i' = i.
    tauto.
  Qed.

  Definition exp := rval.
  Definition decide c s b s' := b = cond (Code c) (eval (Rval1 c) s) (eval (Rval2 c) s) /\ s' = s.
  Definition eval e s n := n = eval e s.

  Definition indirectJump := JmpI.
  Theorem resolve_indirectJump : forall e s i, eval e s i
    -> resolve (indirectJump e) s i.
    tauto.
  Qed.
  Theorem resolve_indirectJump_unique : forall e s i, resolve (indirectJump e) s i
    -> eval e s i.
    tauto.
  Qed.

  Definition cond := condition.

  Definition conditionalJump c i1 i2 := (@nil instr, Jc (Code c) (Rval1 c) (Rval2 c) i1 i2).
  Theorem resolve_conditionalJump : forall b s s' i1 i2 b', decide b s b' s'
    -> execs exec (fst (conditionalJump b i1 i2)) s s'
    /\ resolve (snd (conditionalJump b i1 i2)) s' (if b' then i1 else i2).
    unfold decide, resolve; simpl; intuition; subst; reflexivity.
  Qed.
  Theorem resolve_conditionalJump_unique : forall b s s' i1 i2 i, 
       execs exec (fst (conditionalJump b i1 i2)) s s'
    -> resolve (snd (conditionalJump b i1 i2)) s' i
    -> exists b', decide b s b' s' /\ i = if b' then i1 else i2.
    unfold decide, resolve; simpl; intuition eauto. eexists; repeat esplit; subst; auto.
  Qed.
End SPArg.

Module SP := Structured.Make(SPArg).

Notation "lhs <- rhs" := (fun _ _ => SP.StraightLine (Asgn' lhs rhs)) (no associativity, at level 90) : SP_scope.
Notation "c1 ;; c2" := (fun imp exp => SP.Seq (c1 imp exp) (c2 imp exp))
  (right associativity, at level 95) : SP_scope.

Inductive rvalS : Type :=
| Rval : rval -> rvalS
| Direct : string -> rvalS.

Coercion Rval : rval >-> rvalS.
Coercion Direct : string >-> rvalS.

Definition Goto (rv : rvalS) imports exports : SP.scode :=
  match rv with
    | Rval rv => SP.GotoI rv
    | Direct s => SP.Goto (imports := imports) (exports := exports) s
  end.

Notation "r <-- s" := (fun imp exp => SP.WithCode (imports := imp) (exports := exp) s (fun n : pc => Asgn r (Const n)))
  (no associativity, at level 90) : SP_scope.

Notation "'Assert' [ p ]" := (fun _ _ => SP.Assert_ p)
  (no associativity, at level 95) : SP_scope.

Notation "'Call' rv [ p ]" := (fun imp exp =>
  match (rv : rvalS) with
    | Rval rv' => SP.CallI (fun pc => Asgn (LReg Rret) (Const pc) :: nil) rv' p
    | Direct s => SP.Call_ (imports := imp) (exports := exp) (fun pc => Asgn (LReg Rret) (Const pc) :: nil) s p
  end)
  (no associativity, at level 95) : SP_scope.

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

Module SepArg.
  Definition addr := nat.
  Definition byte := nat.
  Definition size := unit.
  Definition word (_ : size) := nat.
  Definition addresses (a : addr) (_ : size) := a :: nil.
  Definition explode (a : addr) (sz : size) (w : word sz) := (a, w) :: nil.
  Definition implode (ls : list byte) (_ : size) :=
    match ls with
      | b :: nil => b
      | _ => O
    end.
  
  Theorem explode_addresses : forall a sz (w : word sz),
    map (@fst _ _) (explode a w) = addresses a sz.
    unfold explode, addresses; simpl; eauto.
  Qed.

  Theorem explode_functional : forall a sz (w : word sz) a' b b',
    In (a', b) (explode a w)
    -> In (a', b') (explode a w)
    -> b = b'.
    unfold explode; simpl; intuition congruence.
  Qed.

  Theorem implode_explode : forall a sz (w : word sz),
    implode (map (@snd _ _) (explode a w)) sz = w.
    reflexivity.
  Qed.

  Definition addr_eq := eq_nat_dec.

  Definition state := state.
  Definition Mem := Mem.
End SepArg.

Module Sep := Separation.Make(SepArg).

Theorem msel_sep : forall m a, m a = Sep.msel m a tt.
  rewrite Sep.msel_def; reflexivity.
Qed.

Theorem mupd_sep : forall m a v, mupd m a v = Sep.mupd m a (sz := tt) v.
  rewrite Sep.mupd_def; reflexivity.
Qed.

Theorem mkSel : forall s a,
  SepArg.Mem s a = Sep.msel (SepArg.Mem s) a tt.
  rewrite Sep.msel_def; reflexivity.
Qed.

Theorem mupd_read : forall m a v a',
  Sep.mupd m a (sz := tt) v a' = Sep.msel (Sep.mupd m a (sz := tt) v) a' tt.
  rewrite Sep.msel_def; rewrite Sep.mupd_def; reflexivity.
Qed.

Ltac normalizer := (replace Mem with SepArg.Mem in *; [ | reflexivity ]);
  repeat match goal with
           | [ _ : context[?m _] |- _ ] =>
             let Heq := fresh "Heq" in let t := type of m in
               assert (Heq : t = Sep.mem) by reflexivity; clear Heq; rewrite (msel_sep m) in *
           | [ |- context[?m _] ] =>
             let Heq := fresh "Heq" in let t := type of m in
               assert (Heq : t = Sep.mem) by reflexivity; clear Heq; rewrite (msel_sep m)
           | _ => rewrite mupd_sep in *
           | _ => rewrite mkSel in *
           | _ => rewrite mupd_read in *
         end.

Ltac memOut E :=
  match E with
    | (fun a' => Some (?f ?m ?a ?v a')) => constr:(f m a v)
    | (fun a' => ?f ?m ?a ?v a') => constr:(f m a v)
  end.

Ltac sep1 := unfold rupd; simpl; normalizer;
  Sep.sep memOut idtac; try autorewrite with PostSep in *; try solve [ autorewrite with InSep; Sep.canceler ].

Ltac pre := 
  unfold SPArg.eval, SPArg.exec, SPArg.resolve, SPArg.decide in *;
  SP.postStructured ltac:(unfold execR in * );
  normalizer;
  unfold SepArg.addr in *;
    repeat match goal with
             | [ H : _ = (if ?E then _ else _) |- _ ] =>
               match type of E with
                 | {_} + {_} => let pf := fresh "pf" in destruct E as [pf | pf];
                   try discriminate; clear H; try rewrite pf in *; simpl in *
               end
             | [ |- ex _ ] =>
               repeat match goal with
                        | [ |- ex _ ] => esplit
                        | [ |- _ /\ _ ] => split
                      end; reflexivity
           end.

Import Sep.
Export Sep.

Notation "[< p >]" := (Pure p%nat) : Sep_scope.
Notation "![ p ]" := (fun st => Inj (sep p%Sep (fun a => Some (Mem st a)))) : PropX_scope.

Ltac structured := SP.structured ltac:(unfold Goto, Skip, Halt).

Ltac sep := pre; sep1; (cbv beta;
  repeat (match goal with
            | [ specs : codeSpec _ _ |- _ ] =>
              match goal with
                | [ |- specs ?x = Some _ ] => ensureNotUnif x; solve [ eauto | rewrite lift_nadaF; eauto ]
              end
            | [ |- forall x, interp _ (_ --> _) ] =>
              intro; try (eapply Imply_trans; [ | match goal with
                                                    | [ H : _ |- _ ] => apply H
                                                  end ]); propxFo; sep1
            | [ |- interp _ (?f _) ] =>
              rewrite <- (lift_nadaF f); match goal with
                                           | [ H : _ |- _ ] => apply (Imply_sound (H _)); propxFo; sep1
                                         end
          end; cbv beta)).

Ltac doTrans := ((intro; eapply Imply_trans; [ |
    match goal with
      | [ H : _ |- _ ] => apply H
    end ])
  || ((rewrite <- lift_nada || rewrite <- lift_nadaF);
    match goal with
      | [ H : _ |- _ ] => apply (Imply_sound (H _))
    end)); propxFo.

Ltac structuredSep := structured; sep.

Hint Extern 2 (@eq nat _ _) => omega.
Hint Extern 2 (not (@eq nat _ _)) => omega.
Hint Extern 2 (_ < _) => omega.
Hint Extern 2 (_ <= _) => omega.
Hint Extern 2 (_ > _) => omega.
Hint Extern 2 (_ >= _) => omega.
Hint Extern 2 False => omega.

Hint Extern 1 (@eq _ ?n ?m) => progress change (@eq nat n m).

Open Scope string_scope.
Open Scope list_scope.

Local Open Scope Sep_scope.

Notation "a ==> v" := (Impure (ptsTo a (sz := tt) v)) (no associativity, at level 39) : Sep_scope.

Fixpoint allocated (base len : nat) : sprop :=
  match len with
    | O => emp
    | S len' => (Ex v, base ==> v) * !{allocated (S base) len'}
  end.

Theorem allocated0_bwd : forall a n, n = 0 -> emp ===> allocated a n.
  sepLemma.
Qed.

Theorem allocated0_fwd : forall a n, n = 0 -> allocated a n ===> emp.
  sepLemma.
Qed.

Theorem allocated_expose_fwd : forall n base len, n <= len -> allocated base len ===> !{allocated base (n + (len - n))}.
  sepLemma.
Qed.

Theorem allocated_expose_fwd_plus : forall n n' base len, n <= len -> allocated (base + n') len ===> !{allocated (base + n') (n + (len - n))}.
  sepLemma.
Qed.

Theorem allocated_expose_bwd : forall n base len, n <= len -> !{allocated base (n + (len - n))} ===> allocated base len.
  sepLemma.
Qed.

Theorem allocated_expose_bwd_len : forall n len base, n <= len -> !{allocated base (n + (len - n))} ===> allocated base len.
  sepLemma.
Qed.

Implicit Arguments allocated_expose_fwd [].
Implicit Arguments allocated_expose_fwd_plus [].
Implicit Arguments allocated_expose_bwd [].
Implicit Arguments allocated_expose_bwd_len [].

Hint Extern 1 (simplify _ _ _) => autorewrite with PropX PropXF; apply simplify_fwd.

Hint Rewrite mkSel : SimplifyMem.

Theorem noOverlap_tt : forall a a' : nat,
  a <> a'
  -> noOverlap (SepArg.addresses a tt) (SepArg.addresses a' tt).
  simpl; intros; destruct (SepArg.addr_eq a' a); intuition.
Qed.

Hint Resolve noOverlap_tt.

Ltac memsEqer := repeat match goal with
                          | [ |- context[if ?E then _ else _] ] => destruct E; try reflexivity
                        end; reflexivity || elimtype False; solve [ auto ].

Hint Extern 1 => memsEqer : memsEq.
