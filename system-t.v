Require List.
Import List.ListNotations.
Open Scope list.

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
