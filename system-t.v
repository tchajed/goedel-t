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
| var_later : forall Gamma t t', variable Gamma t -> variable (t' :: Gamma) t.

Theorem variable_to_in : forall Gamma t,
    variable Gamma t -> List.In t Gamma.
Proof.
  induction 1; simpl; intros; eauto.
Qed.

Definition variable_add Gamma t (v: variable Gamma t) t' :
  variable (t' :: Gamma) t :=
  var_later t' v.

Fixpoint var_index Gamma t (v: variable Gamma t) : nat :=
  match v with
  | var_here _ _ => 0
  | var_later _ v => S (var_index v)
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

Inductive hasTy (Gamma: mapping) : type -> Type :=
| var : forall t (v: variable Gamma t), hasTy Gamma t
| zero : hasTy Gamma natTy
| succ : hasTy Gamma natTy -> hasTy Gamma natTy
| abs : forall t1 (v: variable Gamma t1) t2,
    forall (e: hasTy (t1 :: Gamma) t2),
      hasTy Gamma (arrow t1 t2)
| app : forall t1 t2,
    forall (e1: hasTy Gamma (arrow t1 t2))
      (e2: hasTy Gamma t1),
      hasTy Gamma t2
| iter : forall t,
    forall (ez: hasTy Gamma t)
      (v: variable Gamma t)
      (e: hasTy (t :: Gamma) t)
      (n: hasTy Gamma natTy),
      hasTy Gamma t.

Definition subst Gamma t (x: variable Gamma t) (e': hasTy Gamma t) t' (e: hasTy Gamma t') : hasTy Gamma t'.
  intros.
  remember e.
  induction e.
  destruct (var_index_eq v x).
  abstract (apply var_indices_eq in e;
    destruct e; subst;
    exact e').
  exact (var v).

  all: exact h.
Defined.
