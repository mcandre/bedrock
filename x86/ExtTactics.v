Ltac hide_evars_in H :=
 repeat (match goal with
           | [ H' : context[?x] |- _ ] => 
             match H' with
               | H =>
                 is_evar x; 
                 let l := fresh "l" in
                 remember x as l
             end
         end).

Ltac hide_evars :=
 repeat (match goal with
           | [ |- context[?x] ] => 
             is_evar x; 
             let l := fresh "l" in
             remember x as l
         end).

Ltac restore_evars :=
 repeat (match goal with
            | [ H : (?l = ?evar) |- _ ] => is_evar evar; subst l
         end).