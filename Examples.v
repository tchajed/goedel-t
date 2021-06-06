Require Import SystemT.

Set Default Goal Selector "!".

Tactic Notation "take" "step" := eapply Relation_Operators.rt1n_trans.
Ltac iterate := match goal with
                | |- iter _ _ zero |-> _ =>
                  apply step_iter2
                | |- iter _ _ (succ _) |-> _ =>
                  apply step_iter3; [ now auto ]
                | |- iter _ _ _ |-> _ =>
                  apply step_iter1
                end.
Tactic Notation "succ" "steps" := repeat apply step_s.
Ltac finish := match goal with
               | |- ?a |->* ?a =>
                 apply Relation_Operators.rt1n_refl
               end.

Section AddExample.

  Definition add Gamma (n m: expr Gamma natTy) : expr Gamma natTy :=
    iter m (succ (var var_here)) n.

  Example add_2_3 : add (Gamma:=[]) (succ (succ zero)) (succ (succ (succ zero))) |->*
                        (succ (succ (succ (succ (succ zero))))).
  Proof.
    unfold add.
    take step.
    { iterate. }
    cbn.
    take step.
    { succ steps.
      iterate. }
    cbn.
    take step.
    { succ steps.
      iterate. }
    finish.
  Qed.

End AddExample.

(* Local Variables: *)
(* company-coq-local-symbols: (("Gamma" . ?Γ) ("gamma" . ?γ)) *)
(* End: *)
