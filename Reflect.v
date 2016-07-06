Require Import SystemT.

(** * Some unfinished work on reflecting well-typed terms into Gallina terms. *)

Fixpoint type_denote (t: type) : Type :=
  match t with
  | natTy => nat
  | arrow t1 t2 => type_denote t1 -> type_denote t2
  end.

Fixpoint ctx_denote (Gamma: context) : Type :=
  match Gamma with
  | nil => unit
  | t :: Gamma' => type_denote t * ctx_denote Gamma'
  end.

Fixpoint env_get Gamma (env: ctx_denote Gamma)
         t (v: variable Gamma t) : type_denote t.
  destruct v.
  - exact (fst env).
  - exact (env_get _ (snd env) _ v).
Defined.

Fixpoint expr_denote Gamma (t: type) (e: expr Gamma t) :
  ctx_denote Gamma -> type_denote t.
  intro env.
  destruct e; simpl; intros.
  - exact (env_get env v).
  - exact 0.
  - exact (S (expr_denote _ _ e env)).
  - pose proof (expr_denote _ _ e) as f; simpl in *.
    exact (f (X, env)).
  - pose proof (expr_denote _ _ e1) as f; simpl in *.
    pose proof (expr_denote _ _ e2) as x.
    exact (f env (x env)).
  - pose proof (expr_denote _ _ e3 env) as n; simpl in n.
    induction n.
    exact (expr_denote _ _ e1 env).
    pose proof (expr_denote _ _ e2) as iter_f; simpl in *.
    exact (iter_f (IHn, env)).
Defined.

Lemma expr_denote_step : forall t (e e': expr [] t),
    e |-> e' ->
    expr_denote e tt = expr_denote e' tt.
Proof.
  induction 1; simpl; intros; eauto; try congruence.
  - (* TODO: generalize over environments *)
    admit.
  - dependent induction H; simplify.
    (* need general property of expr_denote with for substitutions, not just the
    shift substitution *)
    admit.
    admit.
Admitted.

Lemma expr_denote_step_star : forall t (e e': expr [] t),
    e |->* e' ->
    expr_denote e tt = expr_denote e' tt.
Proof.
  induction 1; crush.
  pose proof (expr_denote_step H); congruence.
Qed.

Theorem expr_denote_ok : forall t (e: expr [] t),
    expr_denote e tt = expr_denote (eval e) tt.
Proof.
  eauto using eval_step, expr_denote_step_star.
Qed.

(* Local Variables: *)
(* company-coq-local-symbols: (("Gamma" . ?Γ) ("gamma" . ?γ)) *)
(* End: *)
