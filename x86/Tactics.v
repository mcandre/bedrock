Require Import Sep Refl.
Require Import WordView.

Lemma rewrite_weq : forall sz (a b : word sz)
  (pf : a = b),  
  weq a b = left pf.
Proof.
  intros; destruct (weq a b); try solve [ elimtype False; auto ].
  f_equal. 
  Require Import Eqdep_dec.
  eapply UIP_dec. eapply weq.
Qed.


Ltac normalizer :=
  (replace (@Mem XenExt) with SepArg.Mem in *; [ | reflexivity ]);
  repeat match goal with
           | [ _ : context[?m _] |- _ ] =>
             let Heq := fresh "Heq" in let t := type of m in
               assert (Heq : t = Sep.mem) by reflexivity; clear Heq; rewrite (msel_sep m) in *
           | [ _ : Sep.sep ?P ?M |- Sep.sep ?Q ?M ] => idtac;
             match P with 
               | context [ if ?C then _ else _ ] => idtac;
                 match Q with
                   | context [ if C then _ else _ ] => destruct C
                 end
             end
           | [ H : ?X <> ?Y , H' : context [ weq ?X ?Z ] |- _ ] =>
             let H'' := fresh in assert (H'' : Y = Z); [ solve [ eauto ] | ]; 
             rewrite <- H'' in H'; destruct (weq X Y); [ exfalso; eapply H; eassumption | ]
           | [ H : ?X = ?Y , H' : context [ weq ?X ?Z ] |- _ ] => 
             let H'' := fresh in assert (H'' : Y = Z); [ solve [ eauto ] | ]; rewrite <- H'' in H';
               rewrite (rewrite_weq H) in H'
           | _ => progress word_simpl_in_star
           | _ => progress autorewrite with normalize in *
         end.

Ltac sep1 := unfold Semantics.evalAddr in *; simpl; normalizer;
  Sep.sep ltac:(instantiate; word_simpl_in_star); try autorewrite with PostSep in *; try solve [ autorewrite with InSep; Sep.canceler ].

Ltac pre := SP.postStructured ltac:(idtac); try reflect;
  word_simpl_in_star;
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

Notation "[< p >]" := (Pure p%word) : Sep_scope.
Notation "![ p ]" := (fun st => Inj (sep p%Sep (fun a => Some (Mem st a)))) : PropX_scope.

Ltac sep_next := 
  match goal with
    | [ specs : codeSpec _ _ |- _ ] =>
      match goal with
        | [ |- specs ?x = Some _ ] => ensureNotUnif x; solve [ eauto | rewrite lift_nadaF; eauto ]
      end
    | [ |- forall x, interp _ (_ --> _) ] =>
      intro; try (eapply Imply_trans; [ | match goal with
                                            | [ H : _ |- _ ] => apply H
                                          end ]); propxFo
    | [ |- interp _ (?f _) ] =>
      rewrite <- (lift_nadaF f); match goal with
                                   | [ H : _ |- _ ] => apply (Imply_sound (H _)); propxFo
                                 end
  end.

Ltac sep := pre; sep1; (instantiate;
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
          end; instantiate)).

Ltac doTrans := ((intro; eapply Imply_trans; [ |
    match goal with
      | [ H : _ |- _ ] => apply H
    end ])
  || ((rewrite <- lift_nada || rewrite <- lift_nadaF);
    match goal with
      | [ H : _ |- _ ] => apply (Imply_sound (H _))
    end)); propxFo.

Ltac structuredSep := structured; sep.

Open Scope string_scope.
Open Scope list_scope.

Local Open Scope Sep_scope.

Notation "a '=8>' v" := (Impure (ptsTo a (sz := W8) v)) (no associativity, at level 39) : Sep_scope.
Notation "a '=16>' v" := (Impure (ptsTo a (sz := W16) v)) (no associativity, at level 39) : Sep_scope.
Notation "a '=32>' v" := (Impure (ptsTo a (sz := W32) v)) (no associativity, at level 39) : Sep_scope.
Notation "a '==>' v" := (Impure (ptsTo a (sz := W64) v)) (no associativity, at level 39) : Sep_scope.


Definition bytes (sz : wsize) : nat :=
  match sz with
    | W8 => 1
    | W16 => 2
    | W32 => 4
    | W64 => 8
  end.

Hint Extern 1 (simplify _ _ _) => autorewrite with PropX PropXF; apply simplify_fwd.

Hint Rewrite mkSel : SimplifyMem.

Ltac addrOut := unfold SepArg.addr in *; simpl plus.

Hint Extern 1 (@eq (word _) _ _) => addrOut; Word.word_eq.
Hint Extern 1 (@eq SepArg.addr _ _) => addrOut; Word.word_eq.

Hint Extern 1 (not (@eq (word _) _ _)) => addrOut; Word.word_neq.
Hint Extern 1 (not (@eq SepArg.addr _ _)) => addrOut; Word.word_neq.

Theorem Some_f_equal : forall A (x y : A),
  x = y
  -> Some x = Some y.
  congruence.
Qed.

Theorem Some_push : forall A B (x : {A} + {B}) C (y z : C),
  Some (if x then y else z) = if x then Some y else Some z.
  destruct x; reflexivity.
Qed.

Theorem if_eq : forall sz (a : word sz) x1 x2 A (y1 : A) z1 y2 z2,
  x1 = x2
  -> y1 = y2
  -> z1 = z2
  -> (if weq a x1 then y1 else z1) = if weq a x2 then y2 else z2.
  intros; subst; reflexivity.
Qed.

Hint Extern 1 => repeat (rewrite Some_push || apply if_eq || apply Some_f_equal) : memsEq.


Hint Rewrite rupd_ne using  discriminate : Mac.

Lemma if_weq_then : forall {T : Type} sz (a b : word sz) (P Q : T),
  a = b ->
  (if weq a b then P else Q) = P.
Proof.
  intros; destruct (weq a b); auto. exfalso; auto.
Qed.
Lemma if_weq_else : forall {T : Type} sz (a b : word sz) (P Q : T),
  a <> b ->
  (if weq a b then P else Q) = Q.
Proof.
  intros; destruct (weq a b); auto. exfalso; auto.
Qed.
Hint Rewrite (@if_weq_then sprop) using solve [ eauto ] : InSep.
Hint Rewrite (@if_weq_else sprop) using solve [ eauto ] : InSep.