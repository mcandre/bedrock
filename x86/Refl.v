Set Implicit Arguments.
Set Strict Implicit.

Require Import Struct Sep.
Require Import BinNat.
Require Import Eqdep.
Require Import Program.
Require Import WordView.

(*
Section Vector.
  Variable T : Type.
  Inductive idx : nat -> Type :=
  | Vhere : forall n, idx (S n)
  | Vnext : forall n, idx n -> idx (S n).
  Fixpoint vector (n : nat) : Type :=
    match n with
      | 0 => unit
      | S n => T * vector n
    end%type.
  
  Fixpoint vget n (v : vector n) (i : idx n) : T :=
    match i in idx n return vector n -> T with 
      | Vhere _ => fun x => fst x
      | Vnext _ i => fun x => vget (snd x) i
    end v.

  Fixpoint vset n (v : vector n) (i : idx n) (t : T) : vector n :=
    match i in idx n return vector n -> vector n with 
      | Vhere _ => fun x => (t, snd x)
      | Vnext _ i => fun x => (fst x, vset (snd x) i t)
    end v.
End Vector.
*)

(** Reflected State **)
Definition SymReg := word W64.

Inductive SymRegs : Type := 
| RBase : regs -> SymRegs
| RUpd  : reg W64 -> word W64 -> SymRegs -> SymRegs.

Definition reflectRegs (r : regs) : SymRegs :=
  RBase r.
(*
Definition WrUpd (v64 : word W64) (sz : wsize) (w : word sz) : word W64 :=
  splice v64 w.

Definition WrRd (v64 : word W64) (sz : wsize) : word sz :=
  extract v64 sz.
*)
Fixpoint SrUpd (st : SymRegs) (sz : wsize) (r : reg W64) 
  (w : word sz) : SymRegs :=
  match st with
    | RBase b => 
      RUpd r (splice (b r) w) (RBase b)
    | RUpd r' v' b' =>
      if req r r' then RUpd r (splice v' w) b'
      else RUpd r' v' (SrUpd b' r w)
  end.

Fixpoint SrRd (st : SymRegs) (sz : wsize) (r : reg W64) : word sz :=
  match st with
    | RBase b => extract (b r) sz
    | RUpd r' v' b' =>
      if req r r' then extract v' sz
      else SrRd b' sz r
  end.

Definition symEvalOffset (st : SymRegs) (o : AddrIdx) : word W64 :=
  match o with 
    | AI0 => wzero W64
    | AI1 r _ => SrRd st W64 r
    | AI2 r _ => SrRd st W64 r ^* inj W64 2
    | AI4 r _ => SrRd st W64 r ^* inj W64 4
    | AI8 r _ => SrRd st W64 r ^* inj W64 8
  end.

Definition symEvalAddr (st : SymRegs) (a : Addr) : word W64 :=
  match a with
    | Build_Addr None AI0 (Some d) => sext d W64
    | Build_Addr None w   None =>
      symEvalOffset st w
    | Build_Addr None w (Some d) =>
      symEvalOffset st w ^+ sext d W64
    | Build_Addr (Some r) AI0 None => SrRd st W64 r
    | Build_Addr (Some r) w None => SrRd st W64 r ^+ symEvalOffset st w
    | Build_Addr (Some r) w (Some d)  => SrRd st W64 r ^+ symEvalOffset st w ^+ sext d W64
  end.

Definition symRval sz (rv : rval sz) (mm : mem) (rgs : SymRegs): word sz :=
  match rv in rval sz return word sz with 
    | rImm8 v =>  v
    | rImm32 v => sext v W64
    | rReg sz r => SrRd rgs sz (preg r)
    | rMem a sz => Sep.msel mm (symEvalAddr rgs a) sz
  end.

Definition symUpd (r : SymRegs) (m : mem) (e : XenExt) sz (lv : lval sz) : word sz -> SymRegs * mem * XenExt :=
  match lv in lval sz return word sz -> _ with
    | lReg sz' rg => fun w =>
      (SrUpd r (preg rg) w, m, e)
    | lMem a sz' => fun w => 
      let a := symEvalAddr r a in
      (r, Sep.mupd m a w, e)
  end.

(** TODO: See if flags need to be better **)
Inductive SymFlag :=
| Known   : bool -> SymFlag 
| Unknown : SymFlag.

Inductive SymFlags :=
| FBase : flags -> SymFlags
| FUpd  : flag -> SymFlag -> SymFlags -> SymFlags.

Definition reflectFlags (f : flags) : SymFlags :=
  FBase f.

Definition reflectState (st : state) : SymRegs * SymFlags * mem * XenExt :=
  (reflectRegs (Regs st), reflectFlags (Flags st), Mem st, Ext st).

Definition denoteFlag (s : SymFlag) (b : bool) : Prop :=
  match s with
    | Known b' => b = b'
    | Unknown => True
  end.

Fixpoint lookupFlag (s : SymFlags) (f : flag) : SymFlag := 
  match s with
    | FBase flgs => Known (flgs f)
    | FUpd flg n r => if feq f flg then n else lookupFlag r f
  end.

Fixpoint denoteFlags (fs : flags) (ls : list flag) (s : SymFlags) : Prop :=
  match ls with
    | nil => True
    | f :: r => 
      denoteFlag (lookupFlag s f) (fs f) /\ denoteFlags fs r s
  end.

Definition denoteState (ss : SymRegs * SymFlags * mem * XenExt) st : Prop :=
  let '(a,b,c,d) := ss in
  a = reflectRegs (Regs st) /\ c = Mem st /\ d = Ext st /\
  @denoteFlags (Flags st) (Fcf :: Faf :: Fzf :: Fsf :: Fof :: nil) b.

Theorem denoteState_reflectState : forall st,
  denoteState (reflectState st) st.
Proof.
  destruct st; simpl; intuition.
Qed.  

(** Symbolic Evaluation **)

Fixpoint setFlag (st : SymFlags) (f : flag) (v : SymFlag) : SymFlags :=
  match st with
    | FBase _ => FUpd f v st
    | FUpd f' v' r' => if feq f f' then FUpd f v r' else FUpd f' v' (setFlag r' f v)
  end.

Fixpoint setFlags (ls : list (flag * SymFlag)) (st : SymFlags) : SymFlags :=
  match ls with
    | nil => st
    | (f,b) :: r => setFlags r (setFlag st f b)
  end.

Definition symStep (r : SymRegs) (f : SymFlags) (m : mem) (x : XenExt) (i : instr) : SymRegs * SymFlags * mem * XenExt :=
  match i with 
    | BOP ADD sz lhs rv _ => 
      let lv := symRval lhs m r in
      let rv := symRval rv m r in
      let res := lv ^+ rv in
      let '(r,m,x) := symUpd r m x lhs res in
      let f := setFlags ((Fzf, Known (if weq res (wzero sz) then true else false)) ::
                         (Fsf, Known (wmsb res)) ::
                         (Fcf, Known (if Nle_lt_dec (wordToN lv + wordToN rv)%N (wordToN (wones sz)) then false else true)) ::
                         (Fof, Known (if Nle_lt_dec (wordToN lv + wordToN rv)%N (wordToN (wones sz)) then false else true)) :: nil) f in
      (r,f,m,x)
    | BOP SUB sz lhs rv _ => 
      let lv := symRval lhs m r in
      let rv := symRval rv m r in
      let res := lv ^- rv in
      let '(r,m,x) := symUpd r m x lhs res in
      let f := setFlags ((Fzf, Known (if weq res (wzero sz) then true else false)) ::
                         (Fsf, Known (wmsb res)) ::
                         (Fcf, Known (if wlt_dec lv rv then true else false)) ::
                         (Fof, Known (let sf := wmsb res in
                                      if wslt_dec lv rv then negb sf else
                                      if weq lv rv then false else sf)) :: nil) f in
      (r,f,m,x)
    | BOP CMP sz lhs rv _ => 
      let lv := symRval lhs m r in
      let rv := symRval rv m r in
      let res := lv ^- rv in
      let f := setFlags ((Fzf, Known (if weq res (wzero sz) then true else false)) ::
                         (Fsf, Known (wmsb res)) ::
                         (Fcf, Known (if wlt_dec lv rv then true else false)) ::
                         (Fof, Known (let sf := wmsb res in
                                      if wslt_dec lv rv then negb sf else
                                      if weq lv rv then false else sf)) :: nil) f in
      (r,f,m,x)
    | MUL W64 lhs => 
      let lv := symRval (rReg RAX) m r in
      let rv := symRval lhs m r in
      let '(r,m,x) := symUpd r m x (lReg RAX) (lv ^* rv) in
      let '(r,m,x) := symUpd r m x (lReg RDX) (wmult lv rv) in
      let f := setFlags ((Fzf, Unknown) ::
                         (Fsf, Unknown) ::
                         (Fcf, Known (if weq (wmult lv rv) (wzero _) then false else true)) ::
                         (Fof, Known (if weq (wmult lv rv) (wzero _) then false else true)) :: nil) f in
      (r,f,m,x)
    | MUL W8 lhs => 
      let lv := symRval (rReg AX) m r in
      let rv := symRval lhs m r in
      let '(r,m,x) := symUpd r m x (lReg AL) (Word.combine (wmult lv rv) (wmult lv rv)) in
      let f := setFlags ((Fzf, Unknown) ::
                         (Fsf, Unknown) ::
                         (Fcf, Known (if weq (wmult lv rv) (wzero _) then false else true)) ::
                         (Fof, Known (if weq (wmult lv rv) (wzero _) then false else true)) :: nil) f in
      (r,f,m,x)
    | BOP MOV sz lhs rv _ => 
      let rv := symRval rv m r in
      let '(r,m,x) := symUpd r m x lhs rv in
      (r,f,m,x)
    | MOVi lhs rv => 
      let '(r,m,x) := symUpd r m x (lReg lhs) rv in
      (r,f,m,x)
    | LEA lhs a  =>
      let '(r,m,x) := symUpd r m x (lReg lhs) (symEvalAddr r a) in
      (r,f,m,x)
    | Semantics.PUSH rg =>
      let val := symRval (rReg rg) m r in
      let '(r,m,x) := symUpd r m x (lReg RSP) (symRval (rReg RSP) m r ^- ##8) in
      let '(r,m,x) := symUpd r m x (lMem {| base := Some RSP ; width := AI0 ; disp := None |} W64) val in
      (r,f,m,x)
    | Semantics.POP rg => 
      let val := symRval (lMem {| base := Some RSP ; width := AI0 ; disp := None |} W64) m r in
      let '(r,m,x) := symUpd r m x (lReg rg) val in
      let '(r,m,x) := symUpd r m x (lReg RSP) (symRval (rReg RSP) m r ^+ ##8) in
      (r,f,m,x)
    | MUL _ _ =>  (** Invalid **)
      (r,f,m,x)
  end.

(** Safety **)
Fixpoint All {T : Type} (P : T -> Prop) (ls : list T) {struct ls} : Prop :=
  match ls with
    | nil => True
    | a :: b => P a /\ All P b
  end.

Definition safeRval sz (r : rval sz) (rgs : SymRegs) (ex : XenExt) : Prop :=
  match r with
    | rImm8 _ => True
    | rImm32 _ => True
    | rReg _ _ => True
    | rMem a s =>
      All (fun x : word W64 => ~XenExtOwns ex x) (SepArg.addresses (symEvalAddr rgs a) s)
  end.

Definition safeInstr (i : instr) (r : SymRegs) (e : XenExt) : Prop :=
  match i with
    | BOP o _ L R nm => 
      safeRval L r e /\ safeRval R r e
    | MOVi _ _ => True
    | LEA _ _ => True
    | MUL W8 R => safeRval R r e 
    | MUL W64 R => safeRval R r e
    | Semantics.PUSH _ =>
      safeRval (rMem {| base := Some RSP ; width := AI0 ; disp := Some (^~ (## 8)) |} W64) r e
    | Semantics.POP _ =>
      safeRval (rMem {| base := Some RSP ; width := AI0 ; disp := None |} W64) r e
    | MUL _ _ => False
  end.

Definition safeCond (cc : SPArg.cond') r e : Prop :=
  match cc with
    | SPArg.Build_cond' _ _ lv rv _ => 
     safeRval lv r e /\ safeRval rv r e
  end.

Fixpoint safeFacts (ss : SymRegs * SymFlags * mem * XenExt) (ls : list instr) sz (rv : option (rval sz + SPArg.cond')) : Prop :=
  match ls with
    | nil => 
      let '(r,f,m,e) := ss in
      match rv with 
        | None => True
        | Some (inl rv) => safeRval rv r e
        | Some (inr cc) => safeCond cc r e
      end
    | i :: rr =>
      let '(r,f,m,e) := ss in
         safeInstr i r e 
      /\ safeFacts (symStep r f m e i) rr rv
  end.

Fixpoint safety (ls : list instr) (st st' : state) : Prop :=
  match ls with 
    | nil => st = st'
    | i :: r => exists s, SPArg.exec i st' s /\ safety r st s
  end.

Inductive Stmt :=
| Instr  : instr -> Stmt
| Decide : SPArg.cond' -> bool -> Stmt.

(** Correctness **)
Fixpoint requiredFacts (st : SPArg.state) (ls : list (Stmt * state)) (st' : SPArg.state) : Prop :=
  match ls with
    | nil => st = st'
    | (Instr a, st'') :: r => SPArg.exec a st st'' /\ requiredFacts st'' r st'
    | (Decide c b, st'') :: r => SPArg.decide c st b st'' /\ requiredFacts st'' r st'
  end.

Delimit Scope word_scope with word.
Bind Scope word_scope with word.

Fixpoint denoteCond sz (l r : word sz) (c : cc) (res : bool) : Prop :=
  match c with
    | ccN c => denoteCond l r c (negb res)
    | ccZ  => if res then l = r else l <> r
      (** Unsigned **)
    | ccB  => if res then l < r else l >= r
    | ccA  => if res then l > r else l <= r
    | ccAE => if res then l >= r else l < r
    | ccBE => if res then l <= r else l > r
      (** Signed **)
    | _ => True
  end%word.
  
Definition symDecide (ss : SymRegs * SymFlags * mem * XenExt) cc res 
  : (SymRegs * SymFlags * mem * XenExt) * Prop :=
  match cc with
    | SPArg.Build_cond' sz cc lv rv pf => 
      let '(r,f,m,e) := ss in
      (symStep r f m e (BOP CMP lv rv pf), denoteCond (symRval lv m r) (symRval rv m r) cc res)
  end.

Fixpoint symEval (r : SymRegs) (f : SymFlags) (m : mem) (x : XenExt) (ls : list Stmt) (P : Prop) {struct ls} : 
  (SymRegs * SymFlags * mem * XenExt) * Prop :=
  match ls with 
    | nil => ((r,f,m,x), P)
    | Instr i :: rr => 
      let '(r,f,m,x) := symStep r f m x i in
      symEval r f m x rr P
    | Decide c b :: rr =>
      let '((r,f,m,x),P') := symDecide (r, f, m, x) c b in
      symEval r f m x rr (P /\ P')
  end.

(** Proofs **)
Lemma MemVal_mrd8_sound : forall s addr res,
  MemVal XenExtOwns s addr res ->
  res = mrd8 (Mem s) addr.
Proof.
  intros. dependent destruction H. auto.
Qed.

Lemma symRval_sound : forall sz s (r : rval sz) w,
  evalR XenExtOwns s r w ->
  w = symRval r (Mem s) (reflectRegs (Regs s)). 
Proof.
(*
  intros; dependent destruction H; simpl; auto.
  rewrite H. clear H. rewrite msel_mrd.
  generalize dependent sz. intros; destruct sz;
  repeat match goal with
           | [ H : MemVal _ _ _ _ |- _ ] => apply MemVal_mrd8_sound in H
           | [ H : MemVal _ _ _ _ |- _ ] => generalize H; clear H; let H' := fresh in intro H'; dependent destruction H'
           | _ => progress (repeat (rewrite Sep.Mops.msel_def || unfold Sep.msel,mrd,Sep.mupd,mupd,mrd8,mrd16,mrd32,mrd64))
           | _ => progress subst
           | _ => progress (unfold Sep.msel'; repeat rewrite <- wplus_assoc)
         end; auto.
Qed.
*)
Admitted. (** TOO LONG **)
Lemma symRval_complete : forall sz s (r : rval sz),
  safeRval r (reflectRegs (Regs s)) (Ext s) ->
  evalR XenExtOwns s r (symRval r (Mem s) (reflectRegs (Regs s))).
Proof.
(*
  intros. dependent destruction r; repeat econstructor.
  dependent destruction n; simpl in *; rewrite msel_mrd;
    repeat match goal with 
             | [ H : _ /\ _ |- _ ] => destruct H
           end;
  repeat econstructor; try assumption.
Qed.
*)
Admitted. (** TOO LONG **)
Lemma symRvalL_sound : forall sz s (r : lval sz) w,
  evalL XenExtOwns s r w ->
  w = symRval r (Mem s) (reflectRegs (Regs s)).
Proof.
  inversion 1. subst. eapply symRval_sound in H4. apply inj_pairT2 in H3. subst.
  apply inj_pairT2 in H0. subst. auto.
Qed.

Lemma symRvalL_complete : forall sz s (r : lval sz),
  safeRval r (reflectRegs (Regs s)) (Ext s) ->
  evalL XenExtOwns s r (symRval r (Mem s) (reflectRegs (Regs s))).
Proof.
  intros. constructor. eapply symRval_complete; eauto.
Qed.

Opaque natToWord Word.split1 Word.split2 Word.combine.
Ltac t := repeat match goal with
                   | [ H : existT _ _ _ = existT _ _ _ |- _ ] => apply inj_pairT2 in H; subst
                   | [ H : Then _ _ _ _ |- _ ] => destruct H
                   | [ H : _ /\ _ |- _ ] => destruct H
                   | [ H : MemUpd _ _ _ _ _ |- _ ] => inversion H; clear H; subst
                   | [ |- State _ _ _ _ = State _ _ _ _ ] => reflexivity
                   | _ => progress (repeat unfold Mupd,mupd8,mupd16,mupd32,mupd64)
                   | _ => progress subst
                 end.
(*
Lemma mupd32_sound : forall s s' val ar,
  MemUpd XenExtOwns
         (evalOffset (Regs s) (width ar) ^+ sext (disp ar) W64
          ^+ match base ar with
             | Some r => rrd r (Regs s)
             | None => wzero W64
             end) val s s' ->
         State (Regs s) (Flags s)
    (mupd32 (Mem s) (evalAddr (Regs s) ar) val) (Ext s) = s'.
Proof.
(*
  intros; t.
Qed.
*)
Admitted. (** TOO LONG **)
*)

Lemma symUpd_sound : forall sz (l : lval sz) e st st',
  updL  XenExtOwns l e st st' ->
  symUpd (reflectRegs (Regs st)) (Mem st) (Ext st) l e = (reflectRegs (Regs st'), Mem st', Ext st') /\ Flags st = Flags st'.
Proof.
(**
  intros. dependent destruction H; simpl.
  unfold Rupd. auto. unfold Rupd; auto.

  assert (Regs s = Regs s' /\ Ext s = Ext s' /\ Flags s = Flags s').
  destruct sz; repeat match goal with
                        | [ H : MemUpd _ _ _ _ _ |- _ ] => inversion H; clear H; subst
                        | [ H : Then _ _ _ _ |- _ ] => destruct H
                        | [ H : _ /\ _ |- _ ] => destruct H
                      end; auto.
  intuition. f_equal; eauto. f_equal; eauto.

  rewrite mupd_sep. unfold mupd.
  generalize dependent sz. unfold evalAddr, evalAddr in *. subst.

  intros. clear H1 H2 H4.
  destruct sz; intros; unfold evalAddr. 
  abstract (t; reflexivity).
  abstract (t; reflexivity).
  apply mupd32_sound in H0. subst. simpl. unfold evalAddr. auto.
  inversion H0. clear H0. reduceAll.
  apply mupd32_sound in H0. t. reflexivity.
Qed.
**)
Admitted. (** TOO LONG **)

Lemma MemVal64' : forall (ET : Type) (extMemOwns : ET -> word W64 -> Prop)
         (s : Semantics.state ET) (addr : word W64) (l h : word W32) z,
       @MemVal ET extMemOwns s addr W32 l ->
       @MemVal ET extMemOwns s (addr ^+ ##4) W32 h ->
       z = combine32 l h ->
       @MemVal ET extMemOwns s addr W64 z.
intros. subst; econstructor; eauto.
Qed.
Lemma MemVal32' : forall (ET : Type) (extMemOwns : ET -> word W64 -> Prop)
         (s : Semantics.state ET) (addr : word W64) (l h : word W16) z,
       @MemVal ET extMemOwns s addr _ l ->
       @MemVal ET extMemOwns s (addr ^+ ##2) _ h ->
       z = combine16 l h ->
       @MemVal ET extMemOwns s addr W32 z.
intros. subst; econstructor; eauto.
Qed.
Lemma MemVal16' : forall (ET : Type) (extMemOwns : ET -> word W64 -> Prop)
         (s : Semantics.state ET) (addr : word W64) (l h : word W8) z,
       @MemVal ET extMemOwns s addr _ l ->
       @MemVal ET extMemOwns s (addr ^+ ##1) _  h ->
       z = combine8 l h ->
       @MemVal ET extMemOwns s addr _  z.
intros. subst; econstructor; eauto.
Qed.

Fixpoint safety' (ls : list instr) (st st' : state) : Prop :=
  match ls with 
    | nil => st' = st
    | i :: r => exists s, SPArg.exec i st s /\ safety' r s st'
  end.
(*
Lemma updL_complete : forall sz st (lv : lval sz) v,
  safeRval lv (reflectRegs (Regs st)) (Ext st) ->
  forall r m e, (r,m,e) = symUpd (reflectRegs (Regs st)) (Mem st) (Ext st) lv v ->
  updL XenExtOwns lv v st {| Regs := r ; Flags := Flags st ; Mem := m ; Ext := e |}.
Proof.
  destruct sz; dependent destruction lv;
    simpl; intros; try solve [ exfalso; intuition ];
      repeat match goal with
               | [ H : (_,_,_) = (_,_,_) |- _ ] => inversion H; clear H; subst
               | [ |- context [ State (?F ?R ?V (Regs ?ST)) ?Fl ?M ?E ] ] => 
                 change (State (F R V (Regs ST)) Fl M E) with (Rupd ST (F R V))
               | [ |- _ ] => rewrite mupd_sep
               | [ |- context [ State ?R ?Fl (?F ?M ?V (Regs ?ST)) ?E ] ] => 
                 change (State R Fl (F M V (Regs ST)) E) with (Mupd ST (F M V))
             end;
  try econstructor; try reflexivity; eauto;
  repeat econstructor; intuition auto.
Qed.

Definition denoteFlag (s : SymFlag) (b : bool) : Prop :=
  match s with
    | Known b' => b = b'
    | Unknown => True
  end.

Fixpoint denoteFlags {n} fs : vector SymFlag n -> vector flag n -> Prop :=
  match n as n return vector SymFlag n -> vector flag n -> Prop with
    | 0 => fun _ _ => True 
    | S n => fun s v => 
         denoteFlag (fst s) (fs (fst v))
      /\ denoteFlags fs (snd s) (snd v)
  end.

Definition denoteState (ss : regs * SymFlags * mem * XenExt) st : Prop :=
  let '(a,b,c,d) := ss in
  a = Regs st /\ c = Mem st /\ d = Ext st /\
  @denoteFlags 5 (Flags st) b (Fcf,(Faf,(Fzf,(Fsf,(Fof,tt))))).

Lemma state_Equiv : forall T a c f f' (d : T),
  (forall x, f x = f' x) ->
  State a f c d = State a f' c d.
Proof.
  intros. f_equal. apply functional_extensionality. auto.
Qed.

Lemma symStep_complete : forall R F M E st i,
  safeInstr i R E ->
  denoteState (R,F,M,E) st ->  
  exists st', SPArg.exec i st st'
    /\ denoteState (symStep  R F M E i) st'.
Proof.
(*
  intros; simpl in *; intuition; subst.

  Ltac complete_solver :=

try solve [ simpl in *; intuition;
    try match goal with 
    | [ |- context [ symUpd ?R ?M ?E ?l ?e ] ] =>
      case_eq (symUpd R M E l e); intros;
      match goal with
        | [ H : prod _ _ |- _ ] => destruct H
      end
  end;
  (eexists; split; [ repeat (match goal with 
                               | [ |- exists x, _ ] => exists true
                               | _ => 
                                 solve [ eapply symRvalL_complete; (tauto || auto)
                                       | eapply symRval_complete; (tauto || auto)
                                       | eapply updL_complete; simpl; (tauto || eauto) ]
                               | _ => econstructor
                            end) | ]; 
  instantiate; try (instantiate (1 := true)) ); instantiate; simpl; intuition ].

  destruct i; [ destruct o | destruct sz | | | | ]; complete_solver.
  simpl in *; intuition;
    try match goal with 
    | [ |- context [ symUpd ?R ?M ?E ?l ?e ] ] =>
      case_eq (symUpd R M E l e); intros;
      match goal with
        | [ H : prod _ _ |- _ ] => destruct H
      end
  end;
  (eexists; split; [ 
  repeat (match goal with 
            | [ |- exists x, _ ] => exists true
            | _ => 
              solve [ eapply symRvalL_complete; simpl; (tauto || auto)
                | eapply symRval_complete; simpl; (tauto || auto)
                | eapply updL_complete; simpl; (tauto || eauto) ]
            | _ => econstructor
          end) | ]; simpl; intuition).
Qed.
*)
Admitted.

Lemma symStep_sound : forall i R F M E (st st' : SPArg.state),
  denoteState (R,F,M,E) st ->
  SPArg.exec i st st' ->
  denoteState (symStep R F M E i) st'.
Proof.
(*
  intros. simpl in *. intuition; subst.
  dependent destruction H0;
  try solve [ (try unfold mulFlagVals in * ); repeat (simpl in *;
    match goal with 
      | [ H : evalR _ _ _ _ |- _ ] => rewrite (symRval_sound H) in *
      | [ H : evalL _ _ _ _ |- _ ] => rewrite (symRvalL_sound H) in *
      | [ H : Then _ _ _ _ |- _ ] => destruct H
      | [ H : _ |- _ ] => eapply symUpd_sound in H; destruct H
      | [ H : _ /\ _ |- _ ] => destruct H
      | [ H : _ = _ |- _ ] => progress (rewrite H in * )
    end); unfold Semantics.setFlag, Fupd in *; subst; simpl;
  repeat match goal with
           | [ |- match ?X with 
                    | Known _ => _ 
                    | Unknown => _ 
                  end ] => destruct X; simpl in *; subst
           | [ H : exists x, _ |- _ ] => destruct H
           | [ |- exists x, _ ] => eexists
         end; subst; intuition;
  try (match goal with 
         | _ => apply state_Equiv
         | [ |- ?X = State _ _ _ _ ] => destruct X; simpl in *; subst
       end; let x := fresh in intro x; destruct x; (instantiate; simpl; reflexivity));
  repeat match goal with 
           | [ H : (_,_,_) = (_,_,_) |- _ ] => inversion H; clear H
         end; auto ].
Qed.
*)
Admitted. (** TOO LONG **)

Lemma symDecide_sound' : forall ss cc res st st',
  denoteState ss st ->
  SPArg.decide cc st res st' ->
  let '(ss',sc) := symDecide ss cc res in
    denoteState ss' st' /\ sc.
Proof.
  intros. destruct ss. destruct p. destruct p. destruct cc.
  unfold SPArg.decide in H0. destruct H0. destruct H0. 
  unfold symDecide. split. eapply symStep_sound. eauto. 
  simpl in *; intuition; subst. unfold cmpFlagVals in H4.
  econstructor; eauto.

  simpl in *; intuition; subst.
  rewrite <- (symRval_sound H2).
  rewrite <- (symRvalL_sound H).
  unfold cmpFlagVals in H4. simpl in H4. subst.
  simpl. clear.
  induction Code; simpl;
    try rewrite Bool.negb_involutive; auto;
    repeat match goal with
             | [ |- context [ wlt_dec ?L ?R ] ] => destruct (wlt_dec L R); simpl
             | [ |- context [ weq ?L ?R ] ] => destruct (weq L R); simpl
            end; simpl; eauto with worder.
Qed.
  
Lemma safety_sound_rv' : forall (ls : list instr) st ss (rv : SPArg.exp),
  denoteState ss st ->
  safeFacts ss ls (Some (inl rv)) ->
  exists st', safety' ls st st'
    /\ exists i, SPArg.eval rv st' i. 
Proof.
  induction ls; simpl in *; intros.
    repeat match goal with
             | [ H : prod _ _ |- _ ] => destruct H
           end; simpl in *; intuition; subst;
    repeat match goal with 
             | [ H : exists x, _ |- _ ] => destruct H
           end; subst;
    eexists; (split; [ reflexivity | eexists; eapply symRval_complete; auto ]).

    destruct ss as [ [ [ ? ? ] ? ] ? ]. intuition.
    eapply symStep_complete in H1; eauto. destruct H1. intuition.
    eapply IHls in H3; eauto. destruct H3; intuition. destruct H4.
    repeat esplit; eauto.
Qed.
*)
Lemma safety_sound_decide' : forall (ls : list instr) st ss rv,
  denoteState ss st ->
  @safeFacts ss ls W64 (Some (inr rv)) ->
  exists st', safety' ls st st'
    /\ exists b, exists st'', SPArg.decide rv st' b st''. 
Admitted. (*Proof.
  induction ls; simpl in *; intros. 
    repeat match goal with
             | [ H : prod _ _ |- _ ] => destruct H
           end; simpl in *; intuition; subst.
    repeat match goal with 
             | [ H : exists x, _ |- _ ] => destruct H
           end; subst.
    destruct rv. simpl in H0.  destruct H0.
    apply symRval_complete in H. apply symRval_complete in H0. unfold SPArg.decide. simpl.
    eexists; (split; [ reflexivity | eexists ]).
    eexists. econstructor. eexists. intuition; eauto.
    unfold cmpFlagVals. simpl. reflexivity.

    destruct ss. destruct p. destruct p. intuition.
    eapply symStep_complete in H1. 2: eauto. destruct H1. intuition. eapply IHls in H3; eauto.
    destruct H3. intuition. eexists. split. eexists. split; eauto. eauto.
Qed.
*)
(*
Lemma safety_sound_emp' : forall (ls : list instr) st ss sz,
  denoteState ss st ->
  @safeFacts ss ls sz None ->
  exists st', safety' ls st st'.
Proof.
  induction ls; simpl in *; intros. 
    repeat match goal with
             | [ H : _ * _ |- _ ] => destruct H
           end; simpl in *; intuition; subst;
    repeat match goal with 
             | [ H : exists x, _ |- _ ] => destruct H
           end; subst;
    eexists. reflexivity.

    destruct ss. destruct p. destruct p. intuition.
    eapply symStep_complete in H1. 2: eauto. destruct H1. intuition. eapply IHls in H3; eauto.
    destruct H3. intuition. repeat esplit; eauto.
Qed.

Lemma symEval_sound' : forall (ls : list (Stmt * state)) R F M E (st st' : SPArg.state) (P : Prop),
  denoteState (R,F,M,E) st ->
  requiredFacts st ls st' ->
  P -> 
  let '(ss,P) := symEval R F M E (map (@fst _ state) ls) P in
    denoteState ss st' /\ P.
Proof.
  induction ls; intros; subst.
  simpl symEval; auto. simpl in H0. subst; auto.

  destruct a; simpl in H0; intuition. destruct s.
  intuition. eapply symStep_sound in H; eauto.
  simpl. case_eq (symStep R F M E i). intros. destruct p. destruct p. rewrite H0 in *. 
  eapply IHls; eauto.

  intuition. eapply symDecide_sound' in H2; eauto.
  case_eq (symDecide (R, F, M, E) c b). intros. simpl map. simpl symEval. rewrite H0.
  destruct p. destruct p. destruct p. rewrite H0 in H2. 
  intuition. eapply IHls; eauto.
Qed.
*)
Theorem safety_sound_rv : forall st ls rv,
  safeFacts (reflectState st) ls (Some (inl rv)) ->
  exists st', safety' ls st st'
    /\ exists i, SPArg.eval rv st' i.
Admitted. (* Proof.
  intros. eapply safety_sound_rv'; eauto. simpl; intuition.
Qed.*)

Theorem safety_sound_decide : forall st ls rv,
  @safeFacts (reflectState st) ls W64 (Some (inr rv)) ->
  exists st', safety' ls st st'
    /\ exists b st'', SPArg.decide rv st' b st''.
Proof.
  intros. eapply safety_sound_decide'; eauto. simpl; intuition.
Qed.

Theorem safety_emp_sound_decide : forall (st : state) (rv : SPArg.cond'),
  @safeFacts (reflectState st) nil W64 (Some (inr rv)) ->
  exists b : bool,
    exists st'' : Semantics.state XenExt,
      SPArg.decide rv st b st''.
Admitted. (*Proof.
  intros. generalize (safety_sound_decide st nil rv H). intros.
  destruct H0. intuition. destruct H2. destruct H0. simpl in H1. subst. eauto.
Qed.*)

Theorem safety_emp_sound_rv : forall st rv,
  safeFacts (reflectState st) nil (Some (inl rv)) ->
  exists i, SPArg.eval rv st i.
Admitted. (* Proof.
  intros. generalize (safety_sound_rv _ _ _ H). intros. destruct H0.
  intuition. simpl in H1. subst; auto.
Qed.*)

Theorem safety_sound_emp : forall st ls,
  @safeFacts (reflectState st) ls W64 None ->
  exists st', safety' ls st st'.
Admitted. (*Proof.
  intros. eapply safety_sound_emp'. instantiate (1 := reflectState st).
    destruct st; simpl; intuition. eassumption.
Qed.
*)

Fixpoint computeRegs (sr : SymRegs) (k : regs -> Prop) : Prop :=
  match sr with
    | RBase b => k b
    | RUpd r v sr => 
      computeRegs sr (fun rs => k (fun r' => if req r r' then v else rs r'))
  end.

Fixpoint computeFlags (sf : SymFlags) (k : flags -> Prop) : Prop :=
  match sf with
    | FBase b => k b
    | FUpd r (Known v) sf => 
      computeFlags sf (fun rs => k (fun r' => if feq r r' then v else rs r'))
    | FUpd r Unknown sf =>
      exists v,
      computeFlags sf (fun rs => k (fun r' => if feq r r' then v else rs r'))
  end.

Definition computeState (ss : SymRegs * SymFlags * mem * XenExt) (st : state) : Prop :=
  let '(r,f,m,x) := ss in
    computeFlags f (fun f => computeRegs r 
      (fun r => st = {| Regs := r ; Flags := f ; Mem := m ; Ext := x |})).
(*
Lemma state_eta : forall T (st : Semantics.state T),
  st = State (Regs st) (Flags st) (Mem st) (Ext st).
Proof. destruct st; auto. Qed.

Lemma computeState_denoteState : forall ss st, 
  denoteState ss st -> computeState ss st.
Proof.
(*
  destruct ss. destruct p. destruct p. simpl. intros. intuition; subst.
  repeat match goal with 
           | [ |- match ?X with 
                    | Known _ => _
                    | Unknown => _
                  end ] => destruct X
           | [ |- exists x, _ ] => eexists
         end;
  match goal with
    | [ |- ?X = State _ _ _ _ ] => rewrite (@state_eta _ X) in *; simpl in *; apply state_Equiv
  end;
  let x := fresh in intro x; destruct x; simpl; instantiate;
  try match goal with 
        | _ => solve [ reflexivity | eauto ]
        | [ |- ?X = _ ] => instantiate (1 := X); simpl; reflexivity
      end.
Qed.
*)
Admitted. (** TOO LONG **)
*)
Theorem symEval_sound : forall (ls : list (Stmt * state)) (st st' : SPArg.state),
  requiredFacts st ls st' ->
  let '(ss, P) := symEval (reflectRegs (Regs st)) (reflectFlags (Flags st)) (Mem st) (Ext st) (map (@fst _ state) ls) True in
  computeState ss st' /\ P.
Proof.
(*
  intros. 
  generalize (@symEval_sound' ls (Regs st) (reflectFlags (Flags st)) (Mem st) (Ext st) st st' True).
  intros. apply H0 in H; eauto. 2: simpl; tauto.
  clear H0. destruct (symEval (Regs st) (reflectFlags (Flags st)) (Mem st) (Ext st) (map (@fst _ _) ls) True).
  intuition. eapply computeState_denoteState. eauto.
Qed.
*) Admitted.

Theorem symDecide_sound : forall ss cc res st st',
  denoteState ss st ->
  SPArg.decide cc st res st' ->
  let '(ss',sc) := symDecide ss cc res in
    computeState ss' st' /\ sc.
Proof.
(*
  intros. eapply symDecide_sound' in H0; eauto.
  destruct (symDecide ss cc res). intuition. apply computeState_denoteState; auto.
Qed. 
*)
Admitted.

Lemma decide_exec : forall cc st res st' lv rv pf,
  SPArg.decide cc st res st' ->
  lv = SPArg.valL cc ->
  rv = SPArg.valR cc ->
  SPArg.exec (BOP CMP lv rv pf) st st'.
Proof.
(*
  intros. subst; destruct H. destruct H. intuition.
  econstructor; eauto.
Qed.
*)
Admitted.

(** Tactics **)
Ltac sym_getInstrs st := 
  match goal with
    | [ H : SPArg.exec ?A st ?ST |- _ ] => 
      let r := sym_getInstrs ST in
      let p := constr:((Instr A,ST)) in
      constr:(p :: r)
    | [ H : SPArg.decide ?CC st ?B ?ST |- _ ] => 
      let r := sym_getInstrs ST in
      let p := constr:((Decide CC B,ST)) in
      constr:(p :: r)
    | _ => constr:(@nil (Stmt * SPArg.state))
  end.
Ltac sym_getFinalState st :=
  match goal with
    | [ H : SPArg.exec _ st ?ST |- _ ] => sym_getFinalState ST
    | [ H : SPArg.decide _ st _ ?ST |- _ ] => sym_getFinalState ST
    | _ => st
  end.  
Ltac sym_cleanup st :=
  match goal with
    | [ H : SPArg.exec _ st ?ST |- _ ] => sym_cleanup ST; clear H; try clear ST
    | [ H : SPArg.decide _ st _ ?ST |- _ ] => sym_cleanup ST; clear H; try clear ST
    | _ => idtac
  end.  

Ltac requiredFacts_solver :=
  match goal with
    | [ H : SPArg.decide (SPArg.Build_cond' ?SZ ?C ?VL ?VR ?NM) ?ST ?RES ?ST' |-
      SPArg.exec (BOP CMP ?VL ?VR ?NM) ?ST ?ST' ] =>
    eapply (@decide_exec (SPArg.Build_cond' SZ C VL VR NM) ST RES ST' VL VR NM H); reflexivity
  end.

Ltac sym_getInitialState H' :=
  match goal with
    | [ H : SPArg.exec _ ?X _ |- _ ] =>
      idtac; match goal with
               | [ _ : SPArg.exec _ _ X |- _ ] => fail 1
               | [ _ : SPArg.decide _ _ _ X |- _ ] => fail 1
               | _ => let ins := sym_getInstrs X in
                      let fs := sym_getFinalState X in
                      assert (H' : requiredFacts X ins fs); [ simpl; tauto | ]
             end
    | [ H : SPArg.decide _ ?X _ _ |- _ ] => 
      idtac; match goal with
               | [ _ : SPArg.exec _ _ X |- _ ] => fail 1
               | [ _ : SPArg.decide _ _ _ X |- _ ] => fail 1
               | _ => let ins := sym_getInstrs X in
                      let fs := sym_getFinalState X in
                      assert (H' : requiredFacts X ins fs); [ simpl; intuition requiredFacts_solver | sym_cleanup X ]
             end
  end.

Ltac simpl_State :=   
  repeat ((progress simpl Mem in *)
       || (progress simpl Regs in *)
       || (progress simpl Ext in *)
       || (progress simpl Flags in *)).

Ltac refl_eval rm :=
  let H := fresh in
  sym_getInitialState H;
  apply symEval_sound in H; simpl in H;
  repeat match goal with 
           | [ H : SPArg.eval _ _ _ |- _ ] => apply symRval_sound in H; subst
           | [ H : SPArg.exec _ _ _ |- _ ] => clear H
           | [ H : SPArg.state |- _ ] => clear H
           | [ H : context [ ?ST # ?R ] |- _ ] => change (ST # R) with (rrd R (Regs ST)) in H
           | [ H : SPArg.decide ?CC ?ST ?RES ?ST' |- _ ] =>
             (simple eapply symDecide_sound in H; [ | solve [ apply denoteState_reflectState ] ]); simpl in H;
               let Heq := fresh in
               destruct H as [ Heq ? ]; try rewrite Heq in *; rm Heq; simpl_State
           | [ H : _ /\ _ |- _ ] => destruct H
         end.

Ltac refl_eval_subst :=
  refl_eval ltac:(fun H => idtac);
  repeat match goal with
           | [ H : _ = State _ _ _ _ |- _ ] => 
             rewrite H in *; clear H; simpl in *
         end.

Ltac safe_getInstrs F :=
  match F with 
    | fun y => exists x, SPArg.exec ?I _ _ /\ @?G y x => 
      let k := eval cbv beta in (fun yx => G (fst yx) (snd yx)) in 
      let r := safe_getInstrs k in
      constr:(I :: r)
    | _ => constr:(@nil instr)
  end.


Create HintDb Safety discriminated.

Ltac refl_safety := 
  match goal with 
    | [ |- exists st', @?G st' /\ (exists x, SPArg.eval ?R st' x) ] =>
      (** For computed jumps **)
      let k := safe_getInstrs G in eapply (@safety_sound_rv _ k R)

    | [ |- exists st', @?G st' /\ (exists b st'', SPArg.decide ?R st' b st'') ] =>
      (** For conditional jumps **)
      let k := safe_getInstrs G in eapply (@safety_sound_decide _ k R)

    | [ |- exists st' : _, @?G st' ] =>
      (** For direct jumps **)
      let k := safe_getInstrs G in  eapply (@safety_sound_emp _ k)

    | [ |- exists b st'', SPArg.decide ?R _ b st'' ] =>
      (** For conditional jumps **)
      eapply (@safety_emp_sound_decide _ R)

    | [ |- exists x, SPArg.eval ?R _ x ] =>
      (** For computed jumps **)
      eapply (@safety_emp_sound_rv _ R)
  end; simpl; intuition auto with Safety.

Ltac reflect := 
  refl_safety || refl_eval_subst.
