Require List.
Require Import Relations.
Import List.ListNotations.
Open Scope list.
Require Import Equality.
Import EqdepTheory.

Set Implicit Arguments.

Inductive type :=
  | boolTy : type
  | arrow : type -> type -> type.

Definition type_dec : forall (t1 t2: type), {t1=t2} + {t1<>t2}.
Proof.
  decide equality.
Defined.

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
| true : expr Gamma boolTy
| false : expr Gamma boolTy
| abs : forall t1 t2,
    forall (e: expr (t1 :: Gamma) t2),
      expr Gamma (arrow t1 t2)
| app : forall t1 t2,
    forall (e1: expr Gamma (arrow t1 t2))
      (e2: expr Gamma t1),
      expr Gamma t2.
Arguments true {Gamma}.
Arguments false {Gamma}.

Definition var_is_last Gamma t' t (v: variable (Gamma ++ [t']) t) : variable Gamma t + {t = t'}.
Proof.
  induction Gamma; simpl in *.
  inversion v; subst.
  right; auto.
  inversion H2.

  inversion v; subst.
  left; apply var_here.

  destruct (IHGamma H2).
  left; apply var_outer; assumption.
  right; auto.
Defined.

Definition subst_var Gamma t' (e': expr Gamma t') t (v: variable (Gamma ++ [t']) t) : expr Gamma t.
Proof.
  destruct (var_is_last _ _ v).
  exact (var v0).
  subst.
  apply e'.
Defined.

Lemma variable_weaken_insertion : forall Gamma Gamma' t a,
    variable (Gamma ++ Gamma') t ->
    variable (Gamma ++ a :: Gamma') t.
Proof.
  intros.
  generalize dependent Gamma'.
  induction Gamma; simpl; intros.
  exact (var_outer _ H).
  inversion H; subst.
  apply var_here.
  apply var_outer.
  apply IHGamma; assumption.
Defined.

Definition expr_weaken Gamma Gamma' t t' (e: expr (Gamma ++ Gamma') t) :
  expr (Gamma ++ t' :: Gamma') t.
Proof.
  remember (Gamma ++ Gamma').
  revert Gamma Heql.
  induction e; intros; subst.
  + apply var; apply variable_weaken_insertion; assumption.
  + apply true.
  + apply false.
  + specialize (IHe (t1 :: Gamma0)).
    rewrite <- List.app_comm_cons in *.
    apply abs.
    now apply IHe.
  + now eapply app; [apply IHe1 | apply IHe2 ].
Defined.

Definition expr_shift Gamma t t' (e: expr Gamma t) : expr (t' :: Gamma) t :=
  expr_weaken nil Gamma t' e.

Definition subst Gamma t' (e': expr Gamma t') t (e: expr (Gamma ++ [t']) t) : expr Gamma t.
  intros.
  remember (Gamma ++ [t']).
  generalize dependent Gamma.
  induction e; intros; subst.
  + eapply subst_var; eassumption.
  + apply true.
  + apply false.
  + eapply abs.
    eapply IHe; trivial.
    now apply expr_shift.
  + now eapply app; [ apply IHe1 | apply IHe2 ].
Defined.

Inductive val Gamma : forall t, expr Gamma t -> Prop :=
| val_t : val true
| val_f : val false
| val_abs : forall t1 t2 (e: expr (t1 :: Gamma) t2), val (abs e).

Inductive step : forall t, expr [] t -> expr [] t -> Prop :=
| step_ap1 : forall t1 t2 (e1 e1': expr [] (arrow t1 t2)) e2,
               step e1 e1' ->
               step (app e1 e2) (app e1' e2)
| step_ap2 : forall t1 t2 (e1: expr [] (arrow t1 t2)) e2 e2',
               val e1 ->
               step e2 e2' ->
               step (app e1 e2) (app e1 e2')
| step_apE : forall t1 t2 (e2: expr [] t1) (e: expr [t1] t2),
               val e2 ->
               step (app (abs e) e2) (subst e2 e).
(* TODO: if? *)

Arguments step {t} e1 e2.

Inductive step' : forall t Gamma, expr Gamma t -> expr Gamma t -> Prop :=
| step'_step : forall t (e e': expr [] t),
                 step e e' ->
                 step' e e'.

Ltac deex :=
  match goal with
  | [ H: exists (varname:_), _ |- _ ] =>
    let name := fresh varname in
    destruct H as [name ?]
  end;
  repeat match goal with
         | [ H: _ /\ _ |- _ ] => destruct H
         end.

Ltac inj_pair2 :=
  match goal with
  | [ H: existT ?P ?p _ = existT ?P ?p _ |- _ ] =>
    apply inj_pair2 in H; subst
  end.

Lemma step_step' : forall t (e e': expr [] t),
                     step' e e' ->
                     step e e'.
  intros.
  inversion H; repeat inj_pair2; auto.
Qed.
Hint Resolve step_step'.

Hint Constructors step step' val.

Notation "R ^*" := (clos_refl_trans_1n _ R) (at level 0).

Theorem type_safety :
  forall t (e e': expr [] t),
    step^* e e' ->
    val e' \/ exists e'', step e' e''.
Proof.
Abort.