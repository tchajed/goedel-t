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

Inductive hasTy : mapping -> type -> Type :=
| var : forall Gamma t (v: variable Gamma t), hasTy Gamma t
| zero : forall Gamma, hasTy Gamma natTy
| succ : forall Gamma, hasTy Gamma natTy -> hasTy Gamma natTy
| abs : forall Gamma t1 (v: variable Gamma t1) t2,
    forall (e: hasTy (t1 :: Gamma) t2),
      hasTy Gamma (arrow t1 t2)
| app : forall Gamma t1 t2,
    forall (e1: hasTy Gamma (arrow t1 t2))
      (e2: hasTy Gamma t1),
      hasTy Gamma t2
| iter : forall Gamma t,
    forall (ez: hasTy Gamma t)
      (v: variable Gamma t)
      (e: hasTy Gamma t)
      (n: hasTy Gamma natTy),
      hasTy Gamma t.