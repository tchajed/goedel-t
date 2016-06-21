Require List.
Import List.ListNotations.
Open Scope list.
Require Import Equality.
Import EqdepTheory.

Set Implicit Arguments.

Inductive type :=
  | natTy
  | arrow : type -> type -> type.

Definition mapping := list type.

Implicit Types (Gamma: mapping) (t: type).

Inductive variable : mapping -> type -> Type :=
| var_here : forall Gamma t, variable (t :: Gamma) t
| var_outer : forall Gamma t t', variable Gamma t -> variable (t' :: Gamma) t.

Theorem variable_to_in : forall Gamma t,
    variable Gamma t -> List.In t Gamma.
Proof.
  induction 1; simpl; intros; eauto.
Qed.

Definition variable_add Gamma t (v: variable Gamma t) t' :
  variable (t' :: Gamma) t :=
  var_outer t' v.

Fixpoint var_index Gamma t (v: variable Gamma t) : nat :=
  match v with
  | var_here _ _ => 0
  | var_outer _ v => S (var_index v)
  end.

Definition var_index_eq Gamma t1 t2 (v1: variable Gamma t1) (v2: variable Gamma t2) :
  {var_index v1 = var_index v2} + {var_index v1 <> var_index v2}.
Proof.
  decide equality.
Qed.

Definition var_indices_eq : forall Gamma t1 t2 (v1: variable Gamma t1) (v2: variable Gamma t2),
    var_index v1 = var_index v2 ->
    { H : t1 = t2 & eq_rect _ (fun t => variable Gamma t) v1 _ H = v2 }.
Proof.
  intros.
  dependent induction Gamma.
  inversion v1.
  dependent induction v1;
    dependent induction v2;
    simpl in *;
    try congruence.
  exists eq_refl; cbn; auto.
  inversion H.
  destruct (IHGamma _ _ _ _ H1); subst.
  exists eq_refl; cbn; auto.
Defined.

Inductive expr (Gamma: mapping) : type -> Type :=
| var : forall t (v: variable Gamma t), expr Gamma t
| zero : expr Gamma natTy
| succ : expr Gamma natTy -> expr Gamma natTy
| abs : forall t1 t2,
    forall (e: expr (t1 :: Gamma) t2),
      expr Gamma (arrow t1 t2)
| app : forall t1 t2,
    forall (e1: expr Gamma (arrow t1 t2))
      (e2: expr Gamma t1),
      expr Gamma t2
| iter : forall t,
    forall (ez: expr Gamma t)
      (e: expr (t :: Gamma) t)
      (n: expr Gamma natTy),
      expr Gamma t.
Arguments zero {Gamma}.

Definition subst_var Gamma t' (e': expr Gamma t') t (v: variable (Gamma ++ [t']) t) : expr Gamma t.
Admitted.

Definition subst Gamma t' (e': expr Gamma t') t (e: expr (Gamma ++ [t']) t) : expr Gamma t.
  intros.
  remember (Gamma ++ [t']).
  induction e; subst.
  + eapply subst_var; eassumption.
Admitted.

Inductive val Gamma : forall t, expr Gamma t -> Prop :=
| val_z : val zero
| val_s : forall (e : expr Gamma natTy), val e -> val (succ e)
| val_abs : forall t1 t2 (e: expr (t1 :: Gamma) t2), val (abs e).

Inductive step : forall t, expr [] t -> expr [] t -> Prop :=
| step_s : forall (e e': expr [] natTy),
             step e e' ->
             step (succ e) (succ e')
| step_ap1 : forall t1 t2 (e1 e1': expr [] (arrow t1 t2)) e2,
               step e1 e1' ->
               step (app e1 e2) (app e1' e2)
| step_ap2 : forall t1 t2 (e1: expr [] (arrow t1 t2)) e2 e2',
               val e1 ->
               step e2 e2' ->
               step (app e1 e2) (app e1 e2')
| step_apE : forall t1 t2 (e2: expr [] t1) (e: expr [t1] t2),
               val e2 ->
               step (app (abs e) e2) (subst e2 e)
| step_iter1 : forall t (ez: expr [] t) e n n',
                 step n n' ->
                 step (iter ez e n) (iter ez e n')
| step_iter2 : forall t (ez: expr [] t) e,
                 step (iter ez e zero) ez
| step_iter3 : forall t (ez: expr [] t) e n,
                 step (iter ez e (succ n)) (subst (iter ez e n) e).
