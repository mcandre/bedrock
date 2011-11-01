Require Import NArith.
Require Import Bedrock.
Require Import WordView.
Require Import Peano_dec.

Export Bedrock.

Set Implicit Arguments.

Inductive wsize : Set :=
| W8 | W16 | W32 | W64.

Definition wsize_size (ws : wsize) : nat :=
  match ws with
    | W8 => 8
    | W16 => 16
    | W32 => 32
    | W64 => 64
  end.

Module x86WordSizes <: WordSizes.
  Definition wsize : Set := wsize.
  Definition wsize_size := wsize_size.
End x86WordSizes.

Module x86Words := Words (x86WordSizes).
Import x86Words.
Export x86Words.

Definition combine8 (a b : word W8) : word W16 :=
  @Word.combine 8 a 8 b.
Definition combine16 (a b : word W16) : word W32 :=
  @Word.combine 16 a 16 b.
Definition combine32 (a b : word W32) : word W64 :=
  @Word.combine 32 a 32 b.

Definition pc := word W64.

(** 64-bit registers **)
Inductive reg : wsize -> Set := 
| RAX : reg W64 | RBX : reg W64 | RCX : reg W64 | RDX : reg W64
| RSI : reg W64 | RDI : reg W64 | RBP : reg W64 | RSP : reg W64
| R8  : reg W64 | R9  : reg W64 | R10 : reg W64 | R11 : reg W64
| R12 : reg W64 | R13 : reg W64 | R14 : reg W64 | R15 : reg W64 

| AX   : reg W8 | BX   : reg W8 | CX   : reg W8 | DX   : reg W8
| SI   : reg W8 | DI   : reg W8 | BP   : reg W8 | SP   : reg W8
| R8B  : reg W8 | R9B  : reg W8 | R10B : reg W8 | R11B : reg W8
| R12B : reg W8 | R13B : reg W8 | R14B : reg W8 | R15B : reg W8

| AL   : reg W16.

(** Condition Flags **)
Inductive flag : Set :=
| Fcf | (* Fpf |*) Faf | Fzf | Fsf | Fof.

Definition regs  := reg W64 -> word W64.
Definition mem   := word W64 -> word W8.
Definition flags := flag -> bool.

Section Extended.
  Variable ET : Type.
  Variable extMemOwns : ET -> word W64 -> Prop.

Record state := State {
  Regs   : regs ;
  Flags  : flags ;
  Mem    : mem   ;
  Ext    : ET
}.

Definition reg_to_nat sz (r : reg sz) : nat :=
  match r with
    | RAX => 0
    | RBX => 1
    | RCX => 2
    | RDX => 3
    | RSI => 4
    | RDI => 5
    | RBP => 6
    | RSP => 7
    | R8  => 8
    | R9  => 9
    | R10 => 10
    | R11 => 11
    | R12 => 12
    | R13 => 13
    | R14 => 14
    | R15 => 15

    | AX => 16
    | BX => 17
    | CX => 18
    | DX => 19
    | SI => 20
    | DI => 21
    | BP => 22
    | SP => 23
    | R8B  => 24
    | R9B  => 25
    | R10B => 26
    | R11B => 27
    | R12B => 28
    | R13B => 29
    | R14B => 30
    | R15B => 31

    | AL => 32
  end.

Definition preg sz (r : reg sz) : reg W64 :=
  match r with 
    | AX | AL => RAX
    | BX => RBX
    | CX => RCX
    | DX => RDX
    | SI => RSI
    | DI => RDI
    | BP => RBP
    | SP => RSP
    | R8B  => R8
    | R9B  => R9
    | R10B => R10
    | R11B => R11
    | R12B => R12
    | R13B => R13
    | R14B => R14
    | R15B => R15
    | x => x
  end.

Require Import Program.

Theorem reg_to_nat_inj : forall sz (a : reg sz) (b : reg sz),
  reg_to_nat a = reg_to_nat b -> a = b.
Proof.
  clear. destruct a; dependent destruction b; simpl; congruence.
Qed.

Definition req : forall sz (x y : reg sz), {x = y} + {x <> y}.
  clear. intros.
  refine (if eq_nat_dec (reg_to_nat x) (reg_to_nat y) then 
            left _
          else right _).
  abstract (apply reg_to_nat_inj; auto).
  abstract (intro; subst; tauto).
Defined.
Definition feq : forall x y : flag, {x = y} + {x <> y}.
  decide equality.
Defined.

(* split1 is the low bits, split2 is the high bits *)
(* combine low high *)

Definition splice (sz : wsize) (w : word sz) (sz' : wsize) (w' : word sz') : word sz :=
  match sz as sz, sz' as sz' return word sz -> word sz' -> word sz with
    | W8,W8   => fun _ w => w
    | W8,W16  => fun _ w => @Word.split1 8 8 w
    | W8,W32  => fun _ w => @Word.split1 8 24 w
    | W8,W64  => fun _ w => @Word.split1 8 56 w
    | W16,W8  => fun w w' => Word.combine w' (Word.split2 8 8 w)
    | W16,W16 => fun _ w => w
    | W16,W32 => fun _ w => @Word.split1 16 16 w
    | W16,W64 => fun _ w => @Word.split1 16 48 w
    | W32,W8  => fun w w' => Word.combine w' (Word.split2 8 24 w)
    | W32,W16 => fun w w' => Word.combine w' (Word.split2 16 16 w)
    | W32,W32 => fun _ w => w
    | W32,W64 => fun _ w => @Word.split1 32 32 w
    | W64,W8  => fun w w' => Word.combine w' (Word.split2 8 56  w)
    | W64,W16 => fun w w' => Word.combine w' (Word.split2 16 48 w)
    | W64,W32 => fun w w' => Word.combine w' (Word.split2 32 32 w)
    | W64,W64 => fun _ w => w
  end w w'.

Definition extract (sz : wsize) (w : word sz) (sz' : wsize) : word sz' :=
  match sz as sz, sz' as sz' return word sz -> word sz' with
    | W8,W8   => fun w => w
    | W8,x    => fun w => @sext _ w x

    | W16,W8  => fun w => Word.split1 8  8  w
    | W16,W16 => fun w => w
    | W16,x   => fun w => @sext _ w x

    | W32,W8  => fun w => Word.split1 8  24 w
    | W32,W16 => fun w => Word.split1 16 16 w
    | W32,W32 => fun w => w
    | W32,x   => fun w => @sext _ w x

    | W64,W8  => fun w => Word.split1 8  56 w
    | W64,W16 => fun w => Word.split1 16 48 w
    | W64,W32 => fun w => Word.split1 32 32 w
    | W64,W64 => fun w => w
  end w.

(** Register Updates **)
(*
Definition rupd64  (r : reg W64) (v : word W64) (rgs : regs) : regs :=
  fun r' => if req r' r then v else rgs r'.
Definition rupd32  (r : reg W32) (v : word W32) (rgs : regs) : regs :=
  rupd64 (preg r) (zext v W64) rgs.
Definition rupd16  (r : reg W16) (v : word W16) (rgs : regs) : regs :=
  let v64 := rgs (preg r) in
  rupd64 (preg r) (splice v64 v) rgs.
Definition rupd8  (r : reg W8) (v : word W8) (rgs : regs) : regs :=
  let v64 := rgs (preg r) in
  rupd64 (preg r) (splice v64 v) rgs.
*)
Definition rupd sz (r : reg sz) (v : word sz) (rgs : regs) : regs :=
  let pr := preg r in
  let v' := splice (rgs pr) v in
  fun r' => if req r' pr then v' else rgs r'.

(** Register Reads **)
(*
Definition rrd8 (r : reg W8) (rgs : regs) : word W8 :=
  split1 8 (64 - 8) (rgs (preg r)).
Definition rrd16 (r : reg W16) (rgs : regs) : word 16 :=
  split1 16 (64 - 16) (rgs (preg r)).
Definition rrd32 (r : reg W32) (rgs : regs) : word W32 :=
  split1 32 32 (rgs (preg r)).
Definition rrd64 (r : reg W64) (rgs : regs) : word W64 :=
  rgs r.
*)
Definition rrd sz (r : reg sz) (rgs : regs) : word sz :=
  extract (rgs (preg r)) sz.
(*
  match sz return reg sz -> word sz with
    | W8 => fun r => rrd8 r rgs
    | W16 => fun r => rrd16 r rgs
    | W32 => fun r => rrd32 r rgs
    | W64 => fun r => rrd64 r rgs
  end r.
*)

(** Memory Updates **)
Definition mupd8 (m : mem) (a : word W64) (v : word W8) : mem :=
  fun a' => 
  if weq a' a then v else m a'.
Definition mupd16 (m : mem) (a : word W64) (v : word W16) : mem :=
  mupd8 (mupd8 m a (Word.split1 8 8 v)) (wplus a (inj W64 1)) (Word.split2 8 8 v).

Definition mupd32 (m : mem) (a : word W64) (v : word W32) : mem :=
  mupd16 (mupd16 m a (Word.split1 16 16 v)) (wplus a (inj W64 2)) (Word.split2 16 16 v).

Definition mupd64 (m : mem) (a : word W64) (v : word W64) : mem :=
  mupd32 (mupd32 m a (Word.split1 32 32 v)) (wplus a (inj W64 4)) (Word.split2 32 32 v).

Definition mupd (sz : wsize) (m : mem) (a : word W64) : word sz -> mem :=
  match sz return word sz -> mem with 
    | W8  => fun w => mupd8 m a w
    | W16 => fun w => mupd16 m a w
    | W32 => fun w => mupd32 m a w
    | W64 => fun w => mupd64 m a w
  end.

(** Memory Reads **)
Definition mrd8 (m : mem) (a : word W64) : word W8 :=
  m a.  
Definition mrd16 (m : mem) (a : word W64) : word W16 :=
  combine8 (mrd8 m a) (mrd8 m (wplus a (inj W64 1))).
Definition mrd32 (m : mem) (a : word W64) : word W32 :=
  combine16 (mrd16 m a) (mrd16 m (wplus a (inj W64 2))).
Definition mrd64 (m : mem) (a : word W64) : word W64 :=
  combine32 (mrd32 m a) (mrd32 m (wplus a (inj W64 4))).

Definition mrd (sz : wsize) (m : mem) (a : word W64) : word sz :=
  match sz return word sz with 
    | W8  => mrd8 m a
    | W16 => mrd16 m a
    | W32 => mrd32 m a
    | W64 => mrd64 m a
  end.

Definition Rupd (st : state) (r : regs -> regs)   := State (r (Regs st)) (Flags st) (Mem st) (Ext st).
Definition Mupd (st : state) (m : mem -> mem)     := State (Regs st) (Flags st) (m (Mem st)) (Ext st).
Definition Fupd (st : state) (f : flags -> flags) := State (Regs st) (f (Flags st)) (Mem st) (Ext st).

(** Instructions **)
Definition notRsp sz (r : reg sz) : Prop :=
  match r with
    | RSP => False
    | SP  => False 
    | _   => True
  end.

Inductive AddrIdx : Type :=
| AI0 : AddrIdx
| AI1 : forall r : reg W64, notRsp r -> AddrIdx
| AI2 : forall r : reg W64, notRsp r -> AddrIdx
| AI4 : forall r : reg W64, notRsp r -> AddrIdx
| AI8 : forall r : reg W64, notRsp r -> AddrIdx.

Record Addr : Type :=
{ base  : option (reg W64)
; width : AddrIdx
; disp  : option (word W32)
}.

Inductive rval : wsize -> Type :=
| rImm8   : word W8  -> rval W8
| rImm32  : word W32 -> rval W64
| rReg    : forall sz, reg sz -> rval sz 
| rMem    : Addr -> forall n, rval n.

Inductive lval : wsize -> Type := 
| lReg    : forall sz, reg sz -> lval sz
| lMem    : Addr -> forall n, lval n.

Definition notBothMem sz (l : lval sz) (r : rval sz) : Prop :=
  match l, r with
    | lMem _ _, rMem _ _ => False
    | _, _ => True
  end.

Inductive opr := ADD | SUB | CMP | MOV.

Inductive instr :=
| BOP : opr -> forall n (l : lval n) (r : rval n), notBothMem l r -> instr
| MUL : forall sz, lval sz -> instr
(* | IMUL  : TODO *)
| MOVi : reg W64 -> word W64 -> instr
| LEA : reg W64 -> Addr -> instr
| PUSH : reg W64 -> instr
| POP : reg W64 -> instr
.

Inductive cc := 
| ccN : cc -> cc (** General negation **)
| ccO | ccC | ccB | ccAE | ccZ | ccBE | ccA | ccS | ccL | ccGE | ccLE | ccG.

Inductive control :=
| JMPd : word W64 -> control
| JMP  : rval W64 -> control
| JCC  : cc -> pc -> pc -> control.

Definition Then (f1 f2 : state -> state -> Prop) (st st' : state) : Prop :=
  exists st'', f1 st st'' /\ f2 st'' st'.
Definition setFlag (f : flag) (b : bool) (st st' : state) : Prop :=
  st' = Fupd st (fun fs => fun f' => if feq f f' then b else fs f').
Definition havocFlag (f : flag) (st st' : state) : Prop :=
  exists b, setFlag f b st st'.
Fixpoint setFlags (ls : list (flag * bool)) (st st' : state) : Prop :=
  match ls with
    | nil => st = st'
    | (f,b) :: r => Then (setFlag f b) (setFlags r) st st'
  end.



Inductive MemVal (s : state) (addr : word W64) : forall n, word n -> Prop :=
| MemVal8 :
  ~extMemOwns (Ext s) addr ->
  MemVal (n := W8) s addr (mrd W8 (Mem s) addr)
(*
| MemVal8_Ext : forall v,
  (wordToN addr < MaxMem s)%N ->
  extMemVal (Ext s) addr v ->
  MemVal s addr v
*)
| MemVal16 : forall l h,
  @MemVal s addr W8 l ->
  @MemVal s (wplus addr (inj W64 1)) W8 h ->
  MemVal (n := W16) s addr (combine8 l h)
| MemVal32 : forall l h,
  @MemVal s addr W16 l ->
  @MemVal s (wplus addr (inj W64 2)) W16 h ->
  MemVal (n := W32) s addr (combine16 l h)
| MemVal64 : forall l h,
  @MemVal s addr W32 l ->
  @MemVal s (wplus addr (inj W64 4)) W32 h ->
  MemVal (n := W64) s addr (combine32 l h).

Inductive MemUpd (addr : word W64) : forall n, word n -> state -> state -> Prop :=
| MemUpd8 : forall s val,
  ~extMemOwns (Ext s) addr ->
  @MemUpd addr W8 val s (Mupd s (fun s => mupd8 s addr val))
| MemUpd16 : forall s s' val,
  Then (MemUpd addr (Word.split1 8 8 val : word W8)) (MemUpd (wplus addr (inj W64 1)) (Word.split2 8 8 val : word W8)) s s' ->
  @MemUpd addr W16 val s s'
| MemUpd32 : forall s s' val,
  Then (MemUpd addr (Word.split1 16 16 val : word W16)) (MemUpd (wplus addr (inj W64 2)) (Word.split2 16 16 val : word W16)) s s' ->
  @MemUpd addr W32 val s s'
| MemUpd64 : forall s s' val,
  Then (MemUpd addr (Word.split1 32 32 val : word W32)) (MemUpd (wplus addr (inj W64 4)) (Word.split2 32 32 val : word W32)) s s' ->
  @MemUpd addr W64 val s s'.

Definition evalOffset (st : regs) (o : AddrIdx) : word W64 :=
  match o with 
    | AI0 => wzero W64
    | AI1 r _ => rrd r st
    | AI2 r _ => rrd r st ^* inj W64 2
    | AI4 r _ => rrd r st ^* inj W64 4
    | AI8 r _ => rrd r st ^* inj W64 8
  end.

Definition evalAddr (st : regs) (a : Addr) : word W64 :=
  evalOffset st (width a) ^+ 
  (match disp a with 
     | None => wzero W64
     | Some a => sext a W64
   end) ^+       
  (match base a with
     | None => wzero W64 
     | Some r => rrd r st
   end).

Inductive evalR : state -> forall sz (r : rval sz), word sz -> Prop :=
| evalR_rImm8   : forall s i, evalR s (rImm8 i) i
| evalR_rImm32  : forall s i, evalR s (rImm32 i) (sext i W64)
| evalR_rReg    : forall sz s (r : reg sz), evalR s (rReg r) (rrd r (Regs s))
| evalR_rMem   : forall s (sz : wsize) ar res addr,
  evalAddr (Regs s) ar = addr ->
  @MemVal s addr sz res ->
  evalR s (@rMem ar sz) res.

Definition lval_to_rval sz (lv : lval sz) : rval sz :=
  match lv with
    | lReg sz r => rReg r
    | lMem r sz => rMem r sz
  end.

Inductive evalL : state -> forall sz (l : lval sz), word sz -> Prop :=
| evalL_evalR : forall s sz l w, @evalR s sz (lval_to_rval l) w -> @evalL s sz l w.

Inductive updL : forall sz (l : lval sz), word sz -> state -> state -> Prop :=
| updL_lReg  : forall sz s (r : reg sz) v, updL (lReg r) v s (Rupd s (rupd r v))
| updL_lMem  : forall s s' (sz : wsize) ar val addr,
  evalAddr (Regs s) ar = addr ->
  @MemUpd addr sz val s s' ->
  updL (@lMem ar sz) val s s'.

Definition Nle_lt_dec (a b : N) : ({a <= b} + {b < a})%N.
  clear; intros. 
  refine (match Ncompare a b as x return x = Ncompare a b -> _ with
            | Gt => fun _ => right _
            | _ => fun _ => left _
          end (refl_equal _)).
  abstract (unfold Nle, Nlt; try congruence).
  abstract (unfold Nle, Nlt; try congruence).
  abstract (unfold Nle, Nlt; rewrite <- Ncompare_antisym; rewrite <- _H; auto).
Defined.

Definition wmsb sz (w : word sz) : bool := Word.wmsb w false.
Definition wones sz : word sz := Word.wones sz.


Definition execFlags (op : opr) (sz : wsize) (lv rv : word sz) (s s' : state) : Prop :=
  match op with
    | ADD => setFlags ((Fzf, if weq (lv ^+ rv) (wzero sz) then true else false) ::
                       (Fsf, wmsb (lv ^+ rv)) ::
                       (Fcf, if Nle_lt_dec (@ext _ WordView_N _ lv + @ext _ WordView_N _ rv)%N (@ext _ WordView_N _ (wones sz)) then false else true) ::
                       (Fof, if Nle_lt_dec (@ext _ WordView_N _ lv + @ext _ WordView_N _ rv)%N (@ext _ WordView_N _ (wones sz)) then false else true) :: nil) s s'
    | SUB 
    | CMP => s' = Fupd s (fun f => fun x => match x with
                                              | Fzf => if weq (lv ^- rv) (wzero sz) then true else false
                                              | Fsf => wmsb (lv ^- rv) 
                                              | Fcf => if wlt_dec lv rv then true else false
                                              | Fof => 
                                                let sf := wmsb (lv ^- rv) in
                                                if wslt_dec lv rv then negb sf else
                                                if weq lv rv then false else sf
                                              | _ => f x
                                            end)
    | MOV => s = s'
  end.

Definition mulFlagVals (sz : wsize) (lv rv : word sz) (s s' : state) : Prop :=
  exists zf, exists sf,
    s' = Fupd s (fun f => fun x => match x with
                                     | Fzf => zf 
                                     | Fsf => sf
                                     | Fcf => if weq (wmult lv rv) (wzero _) then false else true
                                     | Fof => if weq (wmult lv rv) (wzero _) then false else true
                                     | _ => f x
                                   end).

Definition cmpFlagVals (sz : wsize) (lv rv : word sz) : state -> state -> Prop :=
  execFlags CMP lv rv.

(*
Definition rupd16' (r : reg W64) (v : word W16) (rgs : regs) : regs :=
  let v64 := rgs r in
  rupd (preg r) (splice v64 v) rgs.
*)

Inductive exec : instr -> state -> state -> Prop :=
| exec_ADD : forall sz st st' (l : lval sz) (r : rval sz) lv rv pf,
  evalL st l lv ->
  evalR st r rv ->
  Then (updL l (lv ^+ rv)) (execFlags ADD lv rv) st st' ->
  exec (BOP ADD l r pf) st st'
| exec_SUB : forall sz st st' (l : lval sz) (r : rval sz) lv rv pf,
  evalL st l lv ->
  evalR st r rv ->
  Then (updL l (lv ^- rv)) (execFlags SUB lv rv) st st' ->
  exec (BOP SUB l r pf) st st'
| exec_CMP : forall sz st st' (l : lval sz) (r : rval sz) lv rv pf,
  evalL st l lv ->
  evalR st r rv ->
  execFlags CMP lv rv st st' ->
  exec (BOP CMP l r pf) st st'
| exec_MOV : forall sz st st' (l : lval sz) (r : rval sz) rv pf,
  evalR st r rv ->
  updL l rv st st' ->
  exec (BOP MOV l r pf) st st'

| exec_MUL8 : forall st st' (r : lval W8) lv rv,
  evalL st (lReg AX) lv ->
  evalL st r rv ->
  Then (updL (lReg AL) (combine8 (wmult lv rv) (wmult lv rv)))
       (mulFlagVals lv rv) st st' ->
  exec (@MUL W8 r) st st'

| exec_MUL64 : forall st st' (r : lval W64) lv rv,
  evalL st (lReg RAX) lv ->
  evalL st r rv ->
  Then (Then (updL (lReg RAX) (wmult lv  rv)) (updL (lReg RDX) (wmult lv rv)))
       (mulFlagVals lv rv) st  st' ->
  exec (@MUL W64 r) st st'

| exec_MOVi : forall st st' (l : reg W64) (rv : word W64),
  updL (lReg l) rv st st' ->
  exec (MOVi l rv) st st'

| exec_LEA : forall (rg : reg W64) ar addr st st',
  evalAddr (Regs st) ar = addr ->
  updL (lReg rg) addr st st' ->
  exec (LEA rg ar) st st'

| exec_PUSH : forall (rg : reg W64) val spv st st' st'',
  evalR st (rReg RSP) spv ->
  evalR st (rReg rg) val ->
  updL (lReg RSP) (spv ^- inj _ 8) st st' ->
  updL (@lMem {| base := Some RSP ; width := AI0 ; disp := None |} W64) val st' st'' ->
  exec (PUSH rg) st st''

| exec_POP : forall (rg : reg W64) val spv st st' st'',
  evalR st (@rMem {| base := Some RSP ; width := AI0 ; disp := None |} W64) val ->
  updL (lReg rg) val st st' ->
  evalR st' (rReg RSP) spv ->
  updL (lReg RSP) (spv ^+ inj _ 8) st' st'' ->
  exec (POP rg) st st''
.

Require Import Bool.

Fixpoint checkCC (c : cc) (fs : flag -> bool) : bool :=
  match c with
    | ccN x => negb (checkCC x fs)
    | ccO => fs Fof
    | ccB => fs Fcf
    | ccC => fs Fcf
    | ccAE => negb (fs Fcf)
    | ccZ => fs Fzf
    | ccBE => orb (fs Fcf) (fs Fzf)
    | ccA => andb (negb (fs Fcf)) (negb (fs Fzf))
    | ccS => fs Fsf
    | ccL => negb (eqb (fs Fsf) (fs Fof))
    | ccGE => eqb (fs Fsf) (fs Fof)
    | ccLE => orb (fs Fzf) (negb (eqb (fs Fsf) (fs Fof)))
    | ccG => andb (negb (fs Fzf)) (eqb (fs Fsf) (fs Fof))
  end.

Inductive resolve : control -> state -> pc -> Prop :=
| resolve_JMPd : forall st rv,
  resolve (JMPd rv) st rv
| resolve_JMP : forall st r rv,
  evalR st r rv ->
  resolve (JMP r) st rv
| resolve_JCC_true : forall st c t f,
  checkCC c (Flags st) = true ->
  resolve (JCC c t f) st t
| resolve_JCC_false : forall st c t f,
  checkCC c (Flags st) = false ->
  resolve (JCC c t f) st f.

(** Lemmas **)
Theorem preg_idem : forall (r : reg W64),
  preg r = r.
Proof.
  clear. dependent destruction r; reflexivity.
Qed.

Theorem rupd_ne : forall sz rs (r1 : reg sz) v r2,
  r2 <> preg r1
  -> rrd r2 (rupd r1 v rs) = rrd r2 rs.
Proof.
  destruct sz;
  unfold rrd,extract,rupd,splice; intros;
    match goal with 
      | [ |- context [ if ?X then _ else _ ] ] => destruct X
    end; intuition;
  solve [ exfalso; subst; apply H; rewrite <- (preg_idem r2); auto ].
Qed.
Theorem rupd_eq : forall sz (r : reg sz) rs v,
  rrd r (rupd r v rs) = v.
Proof.
  destruct sz;
  unfold rrd,extract,rupd,splice; intros;
    match goal with 
      | [ |- context [ if ?X then _ else _ ] ] => destruct X
    end; intuition; apply Word.split1_combine.
Qed.

End Extended.
