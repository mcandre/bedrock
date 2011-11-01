(** A language in the style of mid-level compiler IRs, suitable for programming in directly *)

Require Import Arith Bool Compare_dec List String.

Require Import Bedrock.

Export Bedrock.


Definition word := nat.

Definition natToWord (n : nat) : word := n.
Coercion natToWord : nat >-> word.

Definition var := string.
Definition pc := word.

Definition mem : Type := word -> word.
Definition mempty : mem := fun _ => O.
Definition mupd (m : mem) (a v : word) : mem :=
  fun a' => if eq_nat_dec a' a then v else m a'.

Definition frame := var -> word.
Definition fempty : frame := fun _ => O.
Definition fupd (fr : frame) (x : var) (v : word) : frame :=
  fun x' => if string_dec x' x then v else fr x'.

Theorem fupd_eq : forall rs r1 v r2,
  r2 = r1
  -> fupd rs r1 v r2 = v.
  unfold fupd; intros; destruct (string_dec r2 r1); intuition.
Qed.

Theorem fupd_ne : forall rs r1 v r2,
  r2 <> r1
  -> fupd rs r1 v r2 = rs r2.
  unfold fupd; intros; destruct (string_dec r2 r1); intuition.
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

Hint Rewrite fupd_eq fupd_ne mupd_eq mupd_ne using auto; congruence : Mac.

Definition frames := list frame.

Parameter MemHigh : word.

Definition args := nat -> word.

Record state : Type := {
  Mem : mem;
  Frames : frames;
  Retval : word;
  Retptr : word;
  Argl : args
}.

Inductive binop : Type :=
| Plus
| Minus
| Mult.

Definition evalBinop (b : binop) : word -> word -> word :=
  match b with
    | Plus => plus
    | Minus => minus
    | Mult => mult
  end.

Inductive exp : Type :=
| Const : word -> exp
| Var : var -> exp
| Retv : exp
| Retp : exp
| Arg : nat -> exp
| Binop : exp -> binop -> exp -> exp
| Read : exp -> exp.

Coercion Const : word >-> exp.
Notation "#" := Const : Mir_scope.
Notation "$" := Var : Mir_scope.
Notation "$#" := Arg : Mir_scope.
Notation "$[ e ]" := (Read e) : Mir_scope.

Notation "e1 + e2" := (Binop e1 Plus e2) : Mir_scope.
Notation "e1 - e2" := (Binop e1 Minus e2) : Mir_scope.
Notation "e1 * e2" := (Binop e1 Mult e2) : Mir_scope.

Fixpoint evalExp (e : exp) (st : state) : option word :=
  match e with
    | Const w => Some w
    | Var v => match Frames st with
                 | fr :: _ => Some (fr v)
                 | nil => None
               end
    | Retv => Some (Retval st)
    | Retp => Some (Retptr st)
    | Arg n => Some (Argl st n)
    | Binop e1 b e2 => match evalExp e1 st, evalExp e2 st with
                         | Some v1, Some v2 => Some (evalBinop b v1 v2)
                         | _, _ => None
                       end
    | Read e => match evalExp e st with
                  | None => None
                  | Some v => if le_lt_dec MemHigh v
                    then None
                    else Some (Mem st v)
                end
  end.

Inductive cmd : Type :=
| Assign : var -> exp -> cmd
| SetRetv : exp -> cmd
| SetRetp : exp -> cmd
| SetArg : nat -> exp -> cmd
| Write : exp -> exp -> cmd
| Push : cmd
| Pop : cmd.

Definition evalCmd (c : cmd) (st : state) : option state :=
  match c with
    | Assign x e => match Frames st, evalExp e st with
                      | fr :: frs, Some v => Some {| Mem := Mem st;
                        Frames := fupd fr x v :: frs;
                        Retval := Retval st;
                        Retptr := Retptr st;
                        Argl := Argl st |}
                      | _, _ => None
                    end
    | SetRetv e => match evalExp e st with
                     | Some v => Some {| Mem := Mem st;
                       Frames := Frames st;
                       Retval := v;
                       Retptr := Retptr st;
                       Argl := Argl st |}
                     | _ => None
                   end
    | SetRetp e => match evalExp e st with
                     | Some v => Some {| Mem := Mem st;
                       Frames := Frames st;
                       Retval := Retval st;
                       Retptr := v;
                       Argl := Argl st |}
                     | _ => None
                   end
    | SetArg n e => match evalExp e st with
                      | Some v => Some {| Mem := Mem st;
                        Frames := Frames st;
                        Retval := Retval st;
                        Retptr := Retptr st;
                        Argl := mupd (Argl st) n v |}
                     | _ => None
                    end
    | Write e1 e2 => match evalExp e1 st, evalExp e2 st with
                       | Some v1, Some v2 => if le_lt_dec MemHigh v1
                         then None
                         else Some {| Mem := mupd (Mem st) v1 v2;
                           Frames := Frames st;
                           Retval := Retval st;
                           Retptr := Retptr st;
                           Argl := Argl st|}
                       | _, _ => None
                     end
    | Push => Some {| Mem := Mem st;
      Frames := fempty :: Frames st;
      Retval := Retval st;
      Retptr := Retptr st;
      Argl := Argl st|}
    | Pop => match Frames st with
               | _ :: fr :: frs => Some {| Mem := Mem st;
                 Frames := fr :: frs;
                 Retval := Retval st;
                 Retptr := Retptr st;
                 Argl := Argl st|}
               | _ => None
             end
  end.

Inductive rel : Type :=
| Eq
| Ne
| Lt
| Le
| Gt
| Ge.

Definition evalRel (r : rel) : word -> word -> bool :=
  match r with
    | Eq => beq_nat
    | Ne => fun x y => negb (beq_nat x y)
    | Lt => fun x y => leb x y && negb (beq_nat x y)
    | Le => fun x y => leb x y
    | Gt => fun x y => leb y x && negb (beq_nat x y)
    | Ge => fun x y => leb y x
  end.

Inductive jmp : Type :=
| Jmp : exp -> jmp
| JmpC : exp -> rel -> exp -> word -> word -> jmp.

Definition evalJmp (j : jmp) (st : state) : option pc :=
  match j with
    | Jmp e => evalExp e st
    | JmpC e1 r e2 w1 w2 => match evalExp e1 st, evalExp e2 st with
                              | Some v1, Some v2 => Some (if evalRel r v1 v2 then w1 else w2)
                              | _, _ => None
                            end
  end.

Module SPArg.
  Definition pc := word.

  Definition state := state.

  Definition instr := cmd.
  Definition jmp := jmp.

  Definition exec (i : instr) (st st' : state) := evalCmd i st = Some st'.
  Definition resolve (j : jmp) (st : state) (p : pc) := evalJmp j st = Some p.
  Definition pc_eq := eq_nat_dec.

  Definition directJump (p : pc) := Jmp (Const p).
  Theorem resolve_directJump : forall i s, resolve (directJump i) s i.
    reflexivity.
  Qed.
  Theorem resolve_directJump_unique : forall i s i', resolve (directJump i) s i' -> i' = i.
    unfold resolve; simpl; congruence.
  Qed.

  Definition exp := exp.
  Definition eval (e : exp) (st : state) (p : pc) := evalExp e st = Some p.

  Definition indirectJump := Jmp.
  Theorem resolve_indirectJump : forall e s i, eval e s i
    -> resolve (indirectJump e) s i.
    auto.
  Qed.
  Theorem resolve_indirectJump_unique : forall e s i, resolve (indirectJump e) s i
    -> eval e s i.
    auto.
  Qed.

  Record cond' : Type := {
    CondRel : rel;
    CondOp1 : exp;
    CondOp2 : exp
  }.
  Definition cond := cond'.
  Definition decide (c : cond) (st : state) (b : bool) (st' : state) :=
    match evalExp (CondOp1 c) st, evalExp (CondOp2 c) st with
      | Some v1, Some v2 => evalRel (CondRel c) v1 v2 = b
      | _, _ => False
    end /\ st' = st.

  Definition conditionalJump (c : cond) (p1 p2 : pc) :=
    (@nil cmd, JmpC (CondOp1 c) (CondRel c) (CondOp2 c) p1 p2).
  Theorem resolve_conditionalJump : forall b s s' i1 i2 b', decide b s b' s'
    -> execs exec (fst (conditionalJump b i1 i2)) s s'
    /\ resolve (snd (conditionalJump b i1 i2)) s' (if b' then i1 else i2).
    unfold decide, conditionalJump, resolve; simpl; intuition (subst; auto);
      repeat match goal with
               | [ |- context[match ?E with Some _ => _ | None => _ end] ] => destruct E; intuition
               | [ |- context[if ?E then _ else _] ] => destruct E; intuition
             end; discriminate.
  Qed.

  Theorem resolve_conditionalJump_unique : forall b s s' i1 i2 i, 
    execs exec (fst (conditionalJump b i1 i2)) s s'
    -> resolve (snd (conditionalJump b i1 i2)) s' i
    -> exists b', decide b s b' s' /\ i = if b' then i1 else i2.
    unfold decide, resolve; simpl; intuition (subst; eauto);
      repeat match goal with
               | [ |- context[match ?E with Some _ => _ | None => _ end] ] => destruct E; intuition
               | [ |- context[if ?E then _ else _] ] => destruct E; intuition
               | [ H : Some _ = Some _ |- _ ] => injection H; eauto
             end; discriminate.
  Qed.
End SPArg.

Module SP := Structured.Make(SPArg).

Notation "e1 == e2" := (SPArg.Build_cond' Eq e1 e2) (no associativity, at level 70) : Mir_scope.
Notation "e1 != e2" := (SPArg.Build_cond' Ne e1 e2) (no associativity, at level 70) : Mir_scope.
Notation "e1 < e2" := (SPArg.Build_cond' Lt e1 e2) : Mir_scope.
Notation "e1 <= e2" := (SPArg.Build_cond' Le e1 e2) : Mir_scope.
Notation "e1 > e2" := (SPArg.Build_cond' Gt e1 e2) : Mir_scope.
Notation "e1 >= e2" := (SPArg.Build_cond' Ge e1 e2) : Mir_scope.

Notation "st .[ a ]" := (Mem st a) (no associativity, at level 0).

Open Scope string_scope.

Notation "'Preamble'" := (fun _ _ => SP.Seq (SP.StraightLine Push)
  (SP.StraightLine (Assign "rp" Retp))) : Mir_scope.
Notation "lhs <- rhs" := (fun _ _ => SP.StraightLine (Assign lhs rhs)) (no associativity, at level 90) : Mir_scope.
Notation "'Return' rhs" := (fun _ _ => SP.Seq (SP.StraightLine (SetRetv rhs))
  (SP.Seq (SP.StraightLine (SetRetp (Var "rp")))
    (SP.Seq (SP.StraightLine Pop) (SP.GotoI Retp))))
  (no associativity, at level 90) : Mir_scope.
Notation "lhs <$- rhs" := (fun _ _ => SP.StraightLine (Write lhs rhs)) (no associativity, at level 90) : Mir_scope.
Notation "c1 ;; c2" := (fun imp exp => SP.Seq (c1 imp exp) (c2 imp exp))
  (right associativity, at level 95) : Mir_scope.

Inductive expS : Type :=
| Exp : exp -> expS
| Direct : string -> expS.

Coercion Exp : exp >-> expS.
Coercion Direct : string >-> expS.

Definition Goto_ (eS : expS) imports exports : SP.scode :=
  match eS with
    | Exp e => SP.GotoI e
    | Direct s => SP.Goto (imports := imports) (exports := exports) s
  end.

Notation "'Goto' v" := (Goto_ v) (no associativity, at level 90) : Mir_scope.

Notation "r <-- s" := (fun imp exp => SP.WithCode (imports := imp) (exports := exp) s (fun n : pc => Assign r (Const n)))
  (no associativity, at level 90) : Mir_scope.

Notation "'Assert' [ p ]" := (fun _ _ => SP.Assert_ p)
  (no associativity, at level 95) : Mir_scope.

Definition TailGoto (eS : expS) imports exports : SP.scode :=
  match eS with
    | Exp e => SP.Seq (SP.StraightLine (SetRetv e))
      (SP.Seq (SP.StraightLine Pop) (SP.GotoI Retv))
    | Direct s => SP.Seq (SP.StraightLine Pop) (SP.Goto (imports := imports) (exports := exports) s)
  end.

Notation "'Call' eS [ p ]" := (fun imp exp =>
  match (eS : expS) with
    | Exp e => SP.CallI (fun pc => SetRetp (Const pc) :: nil) e p
    | Direct s => SP.Call_ (imports := imp) (exports := exp) (fun pc => SetRetp (Const pc) :: nil) s p
  end)
  (no associativity, at level 95) : Mir_scope.

Notation "'TailCall' eS" := (fun imp exp =>
  SP.Seq (SP.StraightLine (SetRetp (Var "rp")))
  (TailGoto eS imp exp))
  (no associativity, at level 95) : Mir_scope.

Fixpoint setArgs (n : nat) (es : list exp) : list cmd :=
  match es with
    | nil => nil
    | e :: es => SetArg n e :: setArgs (S n) es
  end.

Local Open Scope list_scope.

Notation "'Call' eS 'Args' arg1 , .. , argN [ p ]" := (fun imp exp =>
  match (eS : expS) with
    | Exp e => SP.CallI (fun pc => setArgs O (cons arg1 .. (cons argN nil) ..) ++ SetRetp (Const pc) :: nil) e p
    | Direct s => SP.Call_ (imports := imp) (exports := exp)
      (fun pc => setArgs O (cons arg1 .. (cons argN nil) ..) ++ SetRetp (Const pc) :: nil) s p
  end)
  (no associativity, at level 95) : Mir_scope.

Notation "'TailCall' eS 'Args' arg1 , .. , argN" := (fun imp exp =>
  SP.Seq (fold_right (fun i p => SP.Seq (SP.StraightLine i) p)
    (SP.StraightLine (SetRetp (Var "rp")))
    (setArgs O (cons arg1 .. (cons argN nil) ..)))
  (TailGoto eS imp exp))
  (no associativity, at level 95) : Mir_scope.

Notation "'Use' [ pf ]" := (fun imp exp => SP.Use_ _ (fun _ => pf%nat)) (no associativity, at level 95) : Mir_scope.

Definition UseVar (lemma : frame -> Prop) (pf : forall fr, lemma fr) : SP.scode :=
  SP.Use_ (fun st => match Frames st return Prop with
                       | f :: _ => lemma f
                       | nil => True
                     end)
  (fun st => match Frames st as fs return match fs return Prop with
                                            | f :: _ => lemma f
                                            | nil => True
                                          end with
               | f :: _ => pf f
               | nil => I
             end).

Notation "'Use' v [ pf ]" := (fun imp exp => UseVar _ (fun v => pf%nat))
  (no associativity, at level 95, v at level 0) : Mir_scope.

Notation "'If' c { b1 } 'else' { b2 }" := (fun imp exp => SP.If_ c (b1 imp exp) (b2 imp exp))
  (no associativity, at level 95, c at level 0) : Mir_scope.

Notation "[ p ] 'While' c { b }" := (fun imp exp => SP.While_ p c (b imp exp))
  (no associativity, at level 95, c at level 0) : Mir_scope.

Definition Skip := fun (_ _ : list (string * SP.prop)) => SP.Skip.
Definition Halt := fun (_ _ : list (string * SP.prop)) => SP.Halt.

Notation "name @ [ p ]" := (name, p) (at level 0, only parsing) : MirImps_scope.
Delimit Scope MirImps_scope with MirImps.

Notation "[[ x , .. , y ]]" := (cons x .. (cons y nil) ..) (only parsing) : MirImps_scope.

Delimit Scope Mir_scope with Mir.

Fixpoint getArgs (n : nat) (xs : list var) : list cmd :=
  match xs with
    | nil => nil
    | x :: xs => Assign x (Arg n) :: getArgs (S n) xs
  end.

Notation "'bfunction' name [ p ] { b }" :=
  (SP.Sfunc name p (Preamble;; b)%Mir)
  (no associativity, at level 95, only parsing) : MirFuncs_scope.
Notation "'bfunction' name 'Args' args [ p ] { b }" :=
  (SP.Sfunc name p (Preamble;;
    (fun imp exp => fold_right (fun i p' => SP.Seq (SP.StraightLine i) p')
      (b imp exp)
      (getArgs O args%MirImps)))%Mir)
  (no associativity, at level 95, only parsing) : MirFuncs_scope.
Delimit Scope MirFuncs_scope with MirFuncs.

Notation "'bmodule' fs" := (SP.bmodule_ nil fs%MirFuncs) (no associativity, at level 95, only parsing).
Notation "'bimport' ls 'bmodule' fs" := (SP.bmodule_ ls%MirImps fs%MirFuncs)
  (no associativity, at level 95, only parsing).

Notation "{{ x 'with' .. 'with' y }}" := (cons x .. (cons y nil) ..) (only parsing) : MirFuncs_scope.


Module SepArg.
  Definition addr := word.
  Definition byte := word.
  Definition size := unit.
  Definition word (_ : size) := word.
  Definition addresses (a : addr) (_ : size) := a :: nil.
  Definition explode (a : addr) (sz : size) (w : word sz) := (a, w) :: nil.
  Definition implode (ls : list byte) (_ : size) :=
    match ls with
      | b :: nil => b
      | _ => O
    end.
  
  Theorem explode_addresses : forall a sz (w : word sz),
    map (@fst _ _) (explode a sz w) = addresses a sz.
    unfold explode, addresses; simpl; eauto.
  Qed.

  Theorem explode_functional : forall a sz (w : word sz) a' b b',
    In (a', b) (explode a sz w)
    -> In (a', b') (explode a sz w)
    -> b = b'.
    unfold explode; simpl; intuition congruence.
  Qed.

  Theorem implode_explode : forall a sz (w : word sz),
    implode (map (@snd _ _) (explode a sz w)) sz = w.
    reflexivity.
  Qed.

  Definition addr_eq := eq_nat_dec.

  Definition state := state.
  Definition Mem := Mem.
End SepArg.

Module Sep := Separation.Make(SepArg).

Theorem msel_mupd_eq : forall m r1 v r2,
  r2 = r1
  -> Sep.msel (Sep.mupd m r1 v) r2 tt = v.
  intros.
  rewrite Sep.msel_def; rewrite Sep.mupd_def; unfold Sep.mupd', Sep.msel'; simpl.
  apply mupd_eq; auto.
Qed.

Theorem msel_mupd_ne : forall m r1 v r2,
  r2 <> r1
  -> Sep.msel (Sep.mupd m r1 (sz := tt) v) r2 tt = Sep.msel m r2 tt.
  intros.
  rewrite Sep.msel_def; rewrite Sep.mupd_def; unfold Sep.mupd', Sep.msel'; simpl.
  apply mupd_ne; auto.
Qed.

Hint Rewrite msel_mupd_eq msel_mupd_ne using congruence : InSep.

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
               match t with
                 | args => fail 1
                 | _ => assert (Heq : t = Sep.mem) by reflexivity; clear Heq; rewrite (msel_sep m) in *
               end
           | [ |- context[?m _] ] =>
             let Heq := fresh "Heq" in let t := type of m in
               match t with
                 | args => fail 1
                 | _ => assert (Heq : t = Sep.mem) by reflexivity; clear Heq; rewrite (msel_sep m)
               end
           | _ => rewrite mupd_sep in *
           | _ => rewrite mkSel in *
           | _ => rewrite mupd_read in *
         end.

Ltac memOut E :=
  match E with
    | (fun a' => if _ then None else Some (?f ?m ?a ?v a')) => constr:(f m a v)
  end.

Ltac sep1 := unfold fupd; simpl; normalizer;
  Sep.sep memOut idtac; try autorewrite with PostSep in *; try solve [ autorewrite with InSep; Sep.canceler ].

Import Sep.
Export Sep.

Theorem readWord_eq : forall m a,
  readWord m a tt = m a.
  unfold readWord, SepArg.addresses; simpl; intros; destruct (m a); simpl in *; auto.
Qed.

Theorem readWord_eq_msel : forall m a,
  (exists v, readWord (fun a' => if Compare_dec.le_lt_dec MemHigh a' then None else Some (m a')) a tt = Some v)
  -> readWord (fun a' => if Compare_dec.le_lt_dec MemHigh a' then None else Some (m a')) a tt = Some (msel m a tt).
  unfold readWord, SepArg.addresses; simpl; intros.
  destruct (Compare_dec.le_lt_dec MemHigh a); simpl.
  destruct H; discriminate.
  rewrite msel_def; reflexivity.
Qed.

Hint Rewrite readWord_eq_msel using (eexists; eassumption) : SimplifyMem.

Theorem ne_false : forall x y,
  negb (beq_nat x y) = false
  -> x = y.
  intros.
  generalize (proj1 (Bool.negb_false_iff _) H); intro.
  apply beq_nat_true in H0; omega.
Qed.

Theorem ne_true : forall x y,
  negb (beq_nat x y) = true
  -> x <> y.
  intros.
  generalize (proj1 (Bool.negb_true_iff _) H); intro.
  apply beq_nat_false in H0; omega.
Qed.

Theorem lt_false : forall x y,
  (leb x y && negb (beq_nat x y))%bool = false
  -> x >= y.
  intros.
  generalize (proj1 (Bool.andb_false_iff _ _) H); intuition.
  apply leb_complete_conv in H1; omega.
  generalize (proj1 (Bool.negb_false_iff _) H1); intro.
  apply beq_nat_true in H0; omega.
Qed.

Theorem lt_true : forall x y,
  (leb x y && negb (beq_nat x y))%bool = true
  -> x < y.
  intros.
  generalize (proj1 (Bool.andb_true_iff _ _) H); intuition.
  apply leb_complete in H1; auto.
  generalize (proj1 (Bool.negb_true_iff _) H2); intro.
  apply beq_nat_false in H0; omega.
Qed.

Ltac pre := 
  unfold SPArg.eval, SPArg.exec, SPArg.resolve, SPArg.decide in *;
    propxFo;

    repeat (match goal with
              | [ x : _ |- _ ] =>
                match goal with
                  | [ H : _ = x |- _ ] => subst x; simpl in *
                end
              | [ H : Some _ = Some _ |- _ ] => injection H; clear H; intros; try subst; simpl in *
              | [ H : _ :: _ = _ :: _ |- _ ] => injection H; clear H; intros; try subst; simpl in *

              | [ _ : context[match Frames ?x with nil => _ | _ :: ls =>
                                match ls with nil => _ | _ :: _ => _ end end] |- _ ] =>
              destruct x as [ ? [ | ? [ | ] ] ]; propxFo; try subst; simpl in *
              | [ _ : context[match Frames ?x with nil => _ | _ :: _ => _ end] |- _ ] =>
               destruct x as [ ? [ | ] ]; propxFo; try subst; simpl in *
            end; try discriminate); propxFo;
    SP.postStructured ltac:idtac;
      normalizer;
      unfold SepArg.addr in *;
        repeat match goal with
                 | [ H : _ = (if ?E then _ else _) |- _ ] =>
                   match type of E with
                     | {_} + {_} => let pf := fresh "pf" in destruct E as [pf | pf];
                       try discriminate; clear H; try rewrite pf in *; simpl in *
                   end
               end;
        try (match goal with
               | [ _ : interp _ ?p |- _ ] =>
                 match eval hnf in p with
                   | match Frames ?st with
                       | nil => _
                       | _ :: ls =>
                         match ls with
                           | nil => _
                           | _ :: _ => _
                         end
                     end => destruct st as [ ? [ | ? [ | ] ] ]
                   | match Frames ?st with
                       | nil => _
                       | _ :: _ => _
                     end => destruct st as [ ? [ | ] ]
                 end
             end; simpl in *); propxFo; try subst;
        repeat match goal with
                 | [ H : context[Compare_dec.le_lt_dec ?a ?v] |- _ ] =>
                   match type of H with
                     | Compare_dec.le_lt_dec a v = _ => fail 1
                     | _ =>
                       let Heq := fresh "Heq" in
                         case_eq (Compare_dec.le_lt_dec a v); [ intros ? Heq; rewrite Heq in *; discriminate
                           | intros ? Heq; rewrite Heq in *; clear Heq ]
                   end
                 | [ H : Some _ = Some _ |- _ ] => injection H; clear H; intros; try subst; simpl in *
                 | [ H : _ :: _ = _ :: _ |- _ ] => injection H; clear H; intros; try subst; simpl in *
               end; autorewrite with Mac in *;
        repeat match goal with
                 | [ H1 : ?x < MemHigh, H2 : ?x < MemHigh |- _ ] => clear H2
                 | [ H : beq_nat _ _ = _ |- _ ] => (apply beq_nat_true in H; try subst) || apply beq_nat_false in H
                 | [ H : leb _ _ = _ |- _ ] => apply leb_complete in H || apply leb_complete_conv in H
                 | [ H : negb (beq_nat _ _) = _ |- _ ] => (apply ne_false in H; try subst) || apply ne_true in H
                 | [ H : match (if ?E then None else Some _) with Some _ => _ | None => False end |- _ ] => destruct E; try tauto
                 | [ H : andb _ _ = _ |- _ ] => apply lt_false in H || apply lt_true in H
               end; propxFo; try congruence.

Notation "[< p >]" := (Pure p%nat) : Sep_scope.
Notation "![ p ]" := (fun m => Inj (sep p%Sep (fun a => if le_lt_dec MemHigh a then None else Some (m a)))) : PropX_scope.

Ltac structured := SP.structured ltac:(unfold Goto_, TailGoto, Skip, Halt, UseVar, fold_right, setArgs, getArgs).
Hint Extern 1 => apply SP.SeqOk : Structured.

Ltac useFrame := repeat match goal with
                       | [ H : Frames _ = _ |- _ ] => rewrite H; propxFo
                       | [ H : Build_state _ _ _ _ = Build_state _ _ _ _ |- _ ] =>
                         discriminate H || (injection H; intros; clear H; subst)
                     end.

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

Theorem allocated_expose_bwd : forall n base len, n <= len -> !{allocated base (n + (len - n))} ===> allocated base len.
  sepLemma.
Qed.

Implicit Arguments allocated_expose_fwd [].
Implicit Arguments allocated_expose_bwd [].

Require Import FunctionalExtensionality.

Lemma touchAllocated'' : forall len base pos, base <= pos < base + len
  -> forall sm, sep (allocated base len) sm
    -> sm pos <> None.
  induction len; simpl; intuition.
  red in H; simpl in H; firstorder. 
  rewrite stars_def in H3; simpl in H3.
  destruct H3 as [? [] ]; intuition.
  destruct (eq_nat_dec pos base); subst.

  red in H3; intuition.
  destruct H5.
  rewrite H5 in H2.
  unfold readWord', SepArg.explode in H6; simpl in H6.
  inversion H6; clear H6; intros; subst; simpl in *.
  rewrite H11 in H2.
  discriminate.

  apply IHlen with (S base) pos x1; intuition.
  destruct H7 as [? [ ] ]; intuition.
  red in H9; intuition.
  replace x1 with x2; auto.
  extensionality a.
  destruct H7.
  rewrite H9.
  destruct (x2 a); auto.

  destruct H5.
  rewrite H6 in H2.
  splitmaster.
Qed.

Lemma touchAllocated' : forall base len pos, base <= pos < base + len
  -> forall ps2 ps1 sm,
    stars (ps1 ++ sep (allocated base len) :: ps2) sm
    -> sm pos <> None.
  rewrite stars_def; induction ps1; simpl; intuition; subst.

  red in H; firstorder.
  specialize (touchAllocated'' _ _ _ (conj H0 H1) _ H3).
  rewrite H4 in H2.
  splitmaster.

  red in H; firstorder.
  specialize (IHps1 _ H5); clear H5.
  rewrite H4 in H2.
  splitmaster.
Qed.

Theorem touchAllocated : forall base len pos ps2 ps1 sm,
  stars (ps1 ++ sep (allocated base len) :: ps2) sm
  -> base <= pos < base + len
  -> sm pos <> None.
  intros; eapply touchAllocated'; eauto.
Qed.

Theorem Imply_easy : forall pc state specs (p1 : Prop) (p2 : PropX pc state),
  (p1 -> interp specs p2)
  -> interp specs (Imply (Inj p1) p2).
  intros; apply Imply_I; eapply Inj_E; eauto.
Qed.

Theorem function_subtype : forall specs T (ls : list T)
  A (hyp1 hyp2 : A -> propX pc state (state :: nil)) hyp3 B (conc1 : B -> propX _ _ nil) conc2 conc3,
  (forall p x, interp specs (subst (hyp1 x) p /\ subst (hyp2 x) p
    --> Ex y, conc1 y /\ subst (conc2 y) p
      /\ Al st, subst (conc3 y st) p --> subst (hyp3 x st) p))%PropX
  -> interp specs ([< ls = nil -> False >]
    --> AlX, Al x : A, hyp1 x /\ hyp2 x /\ (Al st : state, hyp3 x st --> VO @ st)
    --> Ex y : B, ^[match ls with
                      | nil => [< False >]
                      | _ => conc1 y /\ ExX, conc2 y /\ Al st : state, conc3 y st --> VO @ st
                    end])%PropX.
  simpl; intros.
  apply simplify_Imply; simpl; intro.
  destruct ls; try tauto.
  intros p v; specialize (H p v); intuition.
  apply Imply_I.
  eapply Exists_E.
  eapply Imply_E.
  eauto.
  apply And_I.
  eapply And_E1.
  apply Env; simpl; eauto.
  eapply And_E1; eapply And_E2.
  eapply Env; simpl; eauto.

  simpl.
  intro.
  apply Exists_I with B0.
  autorewrite with PropX.
  apply And_I.

  eapply And_E1.
  apply Env; simpl; eauto.

  apply ExistsX_I with p; unfold Subst; simpl.
  rewrite lift_cons2.
  apply And_I.

  eapply And_E1; eapply And_E2; apply Env; simpl; eauto.

  apply Forall_I; intro.
  rewrite lift_cons2.
  apply Imply_I.
  eapply Imply_E.
  apply (Forall_E (P := fun x => subst (hyp3 v x) p --> ^[p x])%PropX).
  eapply And_E2; eapply And_E2.
  apply Env; simpl; eauto.

  eapply Imply_E.
  eapply Forall_E with (P := (fun st => subst (conc3 B0 st) p --> subst (hyp3 v st) p)%PropX).
  eapply And_E2; eapply And_E2; apply Env; simpl; eauto.
  apply Env; simpl; auto.
Qed.

Ltac sep0 := 
  match goal with
    | _ => reflexivity || solve [ auto with sep0 ]
    | [ H : stars _ _ |- context[if Compare_dec.le_lt_dec MemHigh ?E then _ else _] ] =>
      normalizer; simplifyMem
    | [ H : stars _ _ |- context[if Compare_dec.le_lt_dec MemHigh _ then _ else _] ] =>
      (* Proving memory access safety using a points-to fact *)
      repeat unfolderF ltac:(eauto with SafeAddress);
        match goal with
          | [ H : stars ?ls _ |- context[if Compare_dec.le_lt_dec MemHigh ?a then _ else _] ] =>
            let H' := fresh "H'" in generalize H; intro H';
              let rec finder pre post :=
                match eval hnf in post with
                  | ptsTo ?a' (sz := ?sz) ?w :: ?post =>
                    apply (read (a := a') (a' := a) (sz := sz) w post (rev pre)) in H'; [ | solve [ auto ] ]
                  | ?p :: ?post => finder (p :: pre) post
                end in
                finder (@nil hprop) ls;
                rewrite readWord_eq in H';
                  destruct (Compare_dec.le_lt_dec MemHigh a); [ discriminate | eauto ]
        end
    | [ H : stars ?ls _ |- context[if Compare_dec.le_lt_dec MemHigh ?pos then _ else _] ] =>
      (* Proving memory access safety using an allocated fact *)
      let H' := fresh "H'" in generalize H; intro H';
        let rec finder pre post :=
          match eval hnf in post with
            | sep (allocated ?base ?len) :: ?post =>
              apply (touchAllocated base len pos post (rev pre)) in H'; [ | solve [ auto ] ]
            | ?p :: ?post => finder (p :: pre) post
          end in
          finder (@nil hprop) ls;
          match goal with
            | [ |- (if ?E then None else Some _) = Some _ ] =>
              destruct E; tauto
          end
    | [ specs : codeSpec _ _ |- _ ] =>
      (* Finding the spec of a PC *)
      match goal with
        | [ |- specs ?x = Some _ ] => ensureNotUnif x; solve [ eauto | rewrite lift_nadaF; eauto ]
      end
    | [ |- forall x, interp _ (_ --> _) ] =>
      (* Proving that a first-class code pointer meets its spec *)
      intro; try ((* First-class functions *)
        (simpl; apply function_subtype)
        || (* First-class continuations *)
          (eapply Imply_trans; [ | match goal with
                                     | [ H : forall x, interp _ (Imply _ (lift (_ x) _)) |- _ ] => apply H
                                   end ])); propxFo; useFrame; sep1
    | [ |- interp _ (?f _) ] =>
      (* Using a first-class continuation hypothesis *)
      rewrite <- (lift_nadaF f); match goal with
                                   | [ H : forall x, interp _ (Imply _ (lift (_ x) _)) |- _ ] =>
                                     apply (Imply_sound (H _)); propxFo; useFrame; sep1
                                 end
    | [ H : forall x, interp _ ([< _ >] --> AlX, Al x0, _ --> ^[?p x])%PropX |- interp _ (?p ?st) ] =>
      (* Using a first-class function hypothesis *)
      let H' := fresh "H'" in
        specialize (Imply_sound (H st)); intro H'; simpl in H';
          match type of H' with
            | ?P -> _ => assert P by (propxFo; congruence); propxFo
          end;
          match goal with
            | [ H : forall (a : ?T1) (x : ?T2), interp _ (_ --> subst ^[?p] a)%PropX |- interp _ ?p ] =>
              let sp := fresh "sp" in let hp := fresh "hp" in
                evar (sp : T1); evar (hp : T2);
                specialize (Imply_sound (H sp hp)); unfold sp, hp in *; clear sp hp H; intro H;
                  autorewrite with PropX in H; apply H; clear H; propxFo; useFrame; sep1
          end
  end; cbv beta.

Ltac sep := pre; sep1; (cbv beta; unfold SPArg.exec; simpl; repeat sep0).

Ltac doTrans := ((intro; eapply Imply_trans; [ |
    match goal with
      | [ H : _ |- _ ] => apply H
    end ])
  || ((rewrite <- lift_nada || rewrite <- lift_nadaF);
    match goal with
      | [ H : _ |- _ ] => apply (Imply_sound (H _))
    end)); propxFo; useFrame; repeat (apply Imply_easy; propxFo).

Ltac structuredSep := structured; sep.

Ltac womega := unfold SepArg.byte, word, natToWord in *; omega.

Hint Extern 2 (@eq nat _ _) => womega.
Hint Extern 2 (not (@eq nat _ _)) => womega.
Hint Extern 2 (_ < _) => womega.
Hint Extern 2 (_ <= _) => womega.
Hint Extern 2 (_ > _) => womega.
Hint Extern 2 (_ >= _) => womega.
Hint Extern 2 False => womega.

Hint Extern 1 (@eq _ ?n ?m) => progress change (@eq nat n m).

Open Scope list_scope.

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


Definition code := (list cmd * jmp)%type.

Definition step (c : code) (s1 : state) (p : pc) (s2 : state) : Prop :=
  execs SPArg.exec (fst c) s1 s2
  /\ SPArg.resolve (snd c) s2 p.

Definition module : Type := module pc state code.

Definition moduleOk (m : module) : Prop := moduleOk step eq_nat_dec m.

Notation "'FUNC' st 'PRE' [ m0 , args ] P 'POST' [ m1 , rv ] Q" :=
  (let st0 := st in
    let m0 := Mem st0 in
      let args := Argl st0 in
        match Frames st0 with
          | nil => [< False >]
          | _ => P /\ Retptr st0 @@ (st' ~> let m1 := Mem st' in
            let rv := Retval st' in
              [< Frames st' = Frames st0 >] /\ Q)
        end)%PropX%nat
  (at level 100, st at level 0, m0 at level 0, xs at level 0, m1 at level 0, rv at level 0, only parsing).

Notation "'CALLi' st 'PRE' [ m0 , xs , rv' ] P 'POST' [ m1 , rv ] Q" :=
  (let st0 := st in
    let m0 := Mem st0 in
      let rv' := Retval st0 in
        match Frames st0 with
          | xs0 :: xs' :: xss => let xs := xs0 in
            P /\ xs0 "rp" @@ (st' ~> let m1 := Mem st' in
              let rv := Retval st' in
                [< Frames st' = xs' :: xss >] /\ Q)
          | _ => [< False >]
        end)%PropX%nat
  (at level 100, st at level 0, m0 at level 0, xs at level 0, rv' at level 0, m1 at level 0, rv at level 0, only parsing).

Notation "'FUNCi' st 'PRE' [ m0 , xs ] P 'POST' [ m1 , rv ] Q" :=
  (CALLi st PRE [m0, xs, _] P POST [m1, rv] Q)
  (at level 100, st at level 0, m0 at level 0, xs at level 0, m1 at level 0, rv at level 0, only parsing).

Definition spec := state -> PropX pc state.

Require Import Arith.

Ltac makeLayout T n :=
  match eval hnf in T with
    | Empty_set => constr:(n, fun x : Empty_set => match x return nat with end)
    | unit => constr:(S n, fun _ : unit => n)
    | (?T1 + ?T2)%type =>
      let p1 := makeLayout T1 n in
        let n1 := eval simpl in (fst p1) in
          let f1 := eval simpl in (snd p1) in
            let p2 := makeLayout T2 n1 in
              let n2 := eval simpl in (fst p2) in
                let f2 := eval simpl in (snd p2) in
                  constr:(n2, fun x : T1 + T2 => match x with
                                                   | inl y => f1 y
                                                   | inr y => f2 y
                                                 end)
  end.

Fixpoint globalIndex (s : string) T (gs : list (export pc state code T)) : nat :=
  match gs with
    | nil => O
    | g :: gs => if string_dec (ELabel g) s then O else S (globalIndex s _ gs)
  end.

Definition addExports (m : module) (n : nat) (f : LabelT m -> pc) : layout pc (LabelT m) :=
  fun l => match l with
             | Local l => f l
             | Global g => n + globalIndex g _ (Exports m)
           end.

Definition sizedLayout (m : module) := (nat * layout pc (LabelT m))%type.

Ltac buildLayout := match goal with
                      | [ |- sizedLayout ?m ] => let p := makeLayout (LabelT m) O in
                        let n := eval simpl in (fst p) in
                          let f := eval simpl in (snd p) in
                            exact (n, addExports m n f)
                    end.

Fixpoint getBlocks B (n : nat) (m : mapping nat B) : list (nat * B) :=
  match n with
    | O => nil
    | S n' =>
      match m n' with
        | None => nil
        | Some v => (n', v) :: getBlocks B n' m
      end
  end.

Definition assemble m (sl : sizedLayout m) :=
  getBlocks _ (fst sl + List.length (Exports m)) (Blocks (assemble SPArg.pc_eq m (snd sl))).

Ltac linkOk m1 m2 := apply linkOk; simpl; intuition; subst; simpl in *;
  apply m1 || apply m2 || intuition congruence.
