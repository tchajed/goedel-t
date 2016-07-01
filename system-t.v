Require List.
Require Import Relations.
Import List.ListNotations.
Open Scope list.
Require Import Equality.
Import EqdepTheory.
Require Import FunctionalExtensionality.

Set Implicit Arguments.

Inductive type :=
  | natTy
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
  + apply zero.
  + apply succ.
    now apply IHe.
  + specialize (IHe (t1 :: Gamma0)).
    rewrite <- List.app_comm_cons in *.
    apply abs.
    now apply IHe.
  + now eapply app; [apply IHe1 | apply IHe2 ].
  + apply iter.
    now apply IHe1.
    now apply (IHe2 (t :: Gamma0)).
    now apply IHe3.
Defined.

Definition expr_shift Gamma t t' (e: expr Gamma t) : expr (t' :: Gamma) t :=
  expr_weaken nil Gamma t' e.

Definition substitution Gamma Gamma' :=
  forall t (v: variable Gamma t), expr Gamma' t.

Definition substitution_shift : forall Gamma Gamma' t
    (gamma: substitution Gamma Gamma'),
    substitution (t :: Gamma) (t :: Gamma').
  unfold substitution; intros.
  inversion v; subst.
  apply var.
  apply var_here.
  pose proof (gamma _ H2).
  now apply expr_shift.
Defined.

Definition substitution_shift_expr : forall Gamma Gamma' t
                                       (e': expr Gamma' t)
                                       (gamma: substitution Gamma Gamma'),
    substitution (t :: Gamma) Gamma'.
  unfold substitution; intros.
  inversion v; subst.
  exact e'.
  exact (gamma _ H2).
Defined.

Definition apply_substitution Gamma Gamma' (gamma: substitution Gamma Gamma')
           t (e: expr Gamma t) : expr Gamma' t.
  intros.
  generalize dependent Gamma'.
  generalize dependent Gamma.
  induction 1; intros; subst.
  + exact (gamma _ v).
  + exact zero.
  + apply succ.
    now apply IHe.
  + eapply abs.
    eapply IHe; trivial.
    now apply substitution_shift.
  + now eapply app; [ apply IHe1 | apply IHe2 ].
  + eapply iter.
    now apply IHe1.
    apply IHe2; trivial.
    now apply substitution_shift.
    now apply IHe3.
Defined.

Definition noop_substitution : forall {Gamma}, substitution Gamma Gamma.
  intros Gamma t v.
  eapply var; eauto.
Defined.

Definition subst t' (e': expr [] t') t (e: expr [t'] t) : expr [] t :=
  apply_substitution (substitution_shift_expr e' noop_substitution) e.

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
                 val n ->
                 step (iter ez e (succ n)) (subst (iter ez e n) e).

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

Theorem progress : forall t (e: expr [] t),
    val e \/
    exists e', step e e'.
Proof.
  intros.
  assert (val e \/ exists e', step' e e'). {
    remember [].
    induction e; subst; eauto.
    inversion v.
    destruct (IHe eq_refl); repeat deex; eauto 10.
    destruct IHe1; repeat deex; eauto 10.
    destruct IHe2; repeat deex; eauto 10.
    inversion H; inj_pair2; eauto 10.
    destruct IHe3; repeat deex; eauto 10.
    inversion H; inj_pair2; eauto 10.
  }
  destruct H; eauto.
  deex. eauto 10.
Qed.

Hint Resolve rt_step rt_refl.

Ltac inv_step :=
  match goal with
  | [ H: step _ _ |- _ ] =>
    inversion H; repeat inj_pair2; clear H
  end.

Arguments step {t} e e'.

Infix "|->*" := (clos_refl_trans _ step) (at level 20).

Lemma step_from_succ : forall e e',
    succ e |->* e' ->
    exists v', e' = succ v'.
Proof.
  intros.
  remember (succ e).
  generalize dependent e.
  induction H; intros; subst; eauto.
  inv_step; eauto.
  edestruct IHclos_refl_trans1; eauto.
Qed.

(* non-strictly positive definition *)
(*
Inductive HT : forall t (e: expr [] t), Prop :=
| HT_natTy : forall e, terminating e -> HT e
| HT_arrow : forall t1 t2 (e: expr [] (arrow t1 t2)), (forall (e1: expr [] t1), HT e1 ->
                                                                      HT (app e e1)) ->
                                                 HT e.
*)

Definition terminating t (e: expr [] t) : Prop := exists e', e |->* e' /\ val e'.

Fixpoint hereditary_termination t : expr [] t -> Prop :=
  match t with
  | natTy => fun e => terminating e
  | arrow t1 t2 => fun e =>
                    exists e0, e |->* abs e0 /\
                    (forall e1: expr [] t1, hereditary_termination e1 ->
                                       hereditary_termination (subst e1 e0))
  end.

Inductive HT : forall Gamma t (e: expr Gamma t), Prop :=
| HT_hereditary_termination : forall t (e: expr [] t), hereditary_termination e -> HT e.

Lemma HT_destruct : forall t (e: expr [] t), HT e ->
                                        hereditary_termination e.
Proof.
  inversion 1; repeat inj_pair2; eauto.
Qed.

Hint Resolve HT_destruct.

Hint Constructors HT.

Hint Constructors clos_refl_trans clos_refl_trans_1n.

Arguments clos_refl_trans {A} R _ _.

Lemma step_respects_succ : forall e e',
    e |->* e' ->
    succ e |->* succ e'.
Proof.
  induction 1; intros; eauto.
Qed.

Hint Resolve step_respects_succ.

Theorem exprs_ht : forall t (e: expr [] t),
    HT e.
Proof.
  remember [].
  induction e; subst.
  - inversion v.
  - constructor; hnf.
    exists zero; eauto.
  - constructor; hnf.
    intuition.
    apply HT_destruct in H.
    hnf in H; deex.

    exists (succ e'); intuition eauto.
  - (* fails due to non-closed term *)
Abort.

Definition HT_context Gamma (gamma: substitution Gamma []) :=
  forall t (v: variable Gamma t), HT (gamma _ v).

Lemma hereditary_termination_zero : hereditary_termination zero.
Proof.
  hnf.
  eauto.
Qed.

Lemma hereditary_termination_succ : forall e,
    hereditary_termination e -> hereditary_termination (succ e).
Proof.
  simpl; unfold terminating; intros.
  deex.
  eauto.
Qed.

Hint Resolve hereditary_termination_zero.
Hint Resolve hereditary_termination_succ.

Lemma hereditary_termination_succ' : forall (e: expr [] natTy),
    hereditary_termination (succ e) ->
    hereditary_termination e.
Proof.
  simpl; unfold terminating; intros.
  deex.

  apply clos_rt_rt1n in H.
  remember (succ e).
  generalize dependent e.
  induction H; intros; subst.
  inversion H0; eauto.

  inv_step.
  intuition.
  specialize (H e'); intuition.
  deex; eauto.
Qed.

Ltac un_step' :=
  match goal with
  | [ H: step' _ _ |- _ ] =>
    inversion H; subst; repeat inj_pair2; clear H;
    repeat match goal with
           | [ H: ?a = ?a |- _ ] => clear H
           end
  end.

Ltac inv_step' := un_step'; inv_step.

Lemma step_to_step' : forall t (e e': expr [] t),
    step e e' ->
    step' e e'.
Proof.
  eauto.
Qed.

Hint Resolve step_to_step'.

Definition deterministic A (R: A -> A -> Prop) :=
  forall a a' a'', R a a' -> R a a'' ->
              a' = a''.

Theorem deterministic_clos_refl_R : forall A (R: A -> A -> Prop),
    deterministic R ->
    forall a a' a'',
      clos_refl_trans R a a'' ->
      (forall a''', ~R a'' a''') ->
      R a a' ->
      clos_refl_trans R a' a''.
Proof.
  intros.
  Search clos_refl_trans.
  apply clos_rt_rt1n in H0.
  apply clos_rt1n_rt.

  induction H0.
  apply H1 in H2; intuition eauto.
  pose proof (H _ _ _ H0 H2); subst.
  eauto.
Qed.

Ltac cleanup :=
  match goal with
  | [ H: ?a = ?a |- _ ] => clear H
  end.

Lemma val_no_step : forall t (e e': expr [] t),
    val e ->
    ~step e e'.
Proof.
  induction 1; intros; subst; repeat inj_pair2;
    inversion 1; subst; repeat inj_pair2;
      intuition eauto.
Qed.

Definition val_dec : forall t (e: expr [] t), {val e} + {~val e}.
Proof.
  induction e; try solve [ right; inversion 1]; intuition eauto.
  right; inversion 1; intuition.
Defined.

Theorem step_deterministic : forall t, deterministic (step (t:=t)).
Proof.
  unfold deterministic; intros.
  induction H; subst; repeat inj_pair2;
    inversion H0; subst; repeat inj_pair2;
      try pose proof (IHstep _ ltac:(eauto));
      repeat (intuition eauto || cleanup || subst);
      try solve [ exfalso; match goal with
                           | [ H: val ?e, H': step ?e ?e' |- _ ] =>
                             apply (val_no_step H H')
                           | [ H: step ?e _ |- _ ] =>
                             let Hval := fresh in
                             assert (val e) as Hval by eauto;
                             apply (val_no_step Hval H)
                           end ].
Qed.

Hint Resolve step_deterministic.
Hint Resolve val_no_step.
Hint Resolve deterministic_clos_refl_R.

Lemma step_clos_refl_R : forall t (e e' e'': expr [] t),
    val e'' ->
    clos_refl_trans step e e'' ->
    step e e' ->
    clos_refl_trans step e' e''.
Proof.
  eauto.
Qed.

Ltac simplify :=
  repeat match goal with
         | [ H: HT _ |- _ ] => inversion H; subst; clear H;
                             repeat inj_pair2
         | [ H: step' _ _ |- _ ] => inversion H; subst; clear H;
                                  repeat inj_pair2
         | [ H: @hereditary_termination natTy _ |- _ ] =>
           simpl in H; unfold terminating in H
         | [ |- HT _ ] => constructor; hnf
         | [ H: exists _, _ |- _ ] => deex
         | [ H: ?a = ?a |- _ ] => clear H
         end.

Lemma HT_respects_step : forall t (e e': expr [] t),
    hereditary_termination e ->
    step e e' ->
    hereditary_termination e'.
Proof.
  intros.
  induction t; intros.
  - simpl in *.
    unfold terminating in *; deex.
    eapply clos_rt_rt1n in H.
    destruct H.
    + eapply val_no_step in H1.
      eapply H1 in H0.
      intuition.
    + assert (y = e') by (eapply step_deterministic; eauto); subst.
      eapply clos_rt1n_rt in H2.
      eauto.
  - simpl in *; deex.
    eauto.
Qed.

Hint Resolve HT_respects_step.

Lemma HT_prepend_step : forall t (e e': expr [] t),
    hereditary_termination e' ->
    step e e' ->
    hereditary_termination e.
Proof.
  intros.
  simplify.
  generalize dependent e.
  generalize dependent e'.
  induction t; simpl; intros.
  - unfold terminating in *; deex.
    eauto.
  - deex. eauto.
Qed.

Definition compose_substitutions Gamma Gamma' Gamma''
           (s1: substitution Gamma Gamma')
           (s2: substitution Gamma' Gamma'') : substitution Gamma Gamma'' :=
  fun t v => apply_substitution s2 (s1 t v).

Theorem apply_compose_substitutions :
  forall Gamma Gamma' Gamma'' (s1: substitution Gamma Gamma') (s2: substitution Gamma' Gamma'') t (e: expr Gamma t),
    apply_substitution (compose_substitutions s1 s2) e = apply_substitution s2 (apply_substitution s1 e).
Proof.
  unfold compose_substitutions.
  intros.
Admitted.

Ltac eq_simpl := simpl; unfold eq_rec_r, eq_rec; rewrite <- ?eq_rect_eq; simpl.

(* TODO: factor properly *)
Lemma subst_shift :
  forall Gamma (gamma: substitution Gamma []) t1 t2 (e: expr (t1 :: Gamma) t2) e2,
    apply_substitution (substitution_shift_expr e2 gamma) e =
    subst e2 (apply_substitution (substitution_shift gamma) e).
Proof.
  unfold subst.
  intros.
  rewrite <- apply_compose_substitutions.
  f_equal.
  unfold compose_substitutions.
  extensionality t.
  extensionality v.
  dependent destruction v; subst; eauto.
  eq_simpl.
  remember (gamma t v).
  clear.
  generalize dependent (@nil type).
  intros.
  remember (expr_shift t1 e0).
  revert Heqe.
  induction e0; intros; subst; eauto; eq_simpl.
  - erewrite <- IHe0; eauto.
  - (* TODO: don't know how to do this case. *)
    admit.
  - erewrite <- IHe0_1; eauto.
    erewrite <- IHe0_2; eauto.
  - erewrite <- IHe0_1; eauto.
    erewrite <- IHe0_3; eauto.
    admit.
Admitted.

Theorem hereditary_termination_terminating :
  forall t (e: expr [] t),
    hereditary_termination e -> terminating e.
Proof.
  intros.
  destruct t; unfold hereditary_termination in *; eauto.
  deex.
  unfold terminating.
  eauto.
Qed.

Lemma HT_abs :
  forall Gamma t1 t2 (e1: expr Gamma (arrow t1 t2)) e2,
    HT e1 ->
    HT e2 ->
    HT (app e1 e2).
Proof.
  intros.
  destruct Gamma; try solve [ inversion H ].
  eapply HT_destruct in H.
  eapply HT_destruct in H0.
  econstructor.
  edestruct H.
  intuition.
  generalize H0; intros Ht2.
  apply hereditary_termination_terminating in H0.
  destruct H0.
  intuition.
  eapply clos_rt_rt1n in H1.
  eapply clos_rt_rt1n in H2.
  remember (abs x).
  induction H2; subst.
  induction H1.
  eapply HT_prepend_step; try eapply step_apE; eauto.
  eapply HT_prepend_step; try eapply step_ap2; eauto.
  eapply HT_prepend_step; try eapply step_ap1; eauto.
Qed.

Theorem HT_context_subst : forall Gamma t (e: expr Gamma t) (gamma: substitution Gamma []),
    HT_context gamma -> HT (apply_substitution gamma e).
Proof.
  intros.
  generalize dependent gamma.
  induction e; simpl; intros.
  - eauto.
  - auto.
  - specialize (IHe _ H).
    apply HT_destruct in IHe.
    eauto.
  - constructor.
    simpl.
    intros.
    eexists.
    split.
    eapply rt_refl.
    intros.
    rewrite <- subst_shift.
    eapply HT_destruct.
    eapply IHe.
    unfold HT_context in *.
    intros.
    econstructor.
    dependent destruction v.
    eq_simpl; eauto.
    eq_simpl; eapply HT_destruct; eauto.
  - eapply HT_abs; eauto.
  - econstructor.
    specialize (IHe3 gamma H).
    remember (apply_substitution gamma e3).
    clear e3 Heqe.
    eapply HT_destruct in IHe3.
    generalize IHe3; intro Ht3.
    eapply hereditary_termination_terminating in Ht3.
    unfold terminating in Ht3; deex.
    eapply clos_rt_rt1n in H0.
    induction H0.
    dependent induction H1.
    eapply HT_prepend_step; try eapply step_iter2; eauto.
    eapply hereditary_termination_succ' in IHe3.
    intuition.
    specialize (H0 _ ltac:(eauto)).
    eapply HT_prepend_step; try eapply step_iter3; eauto.
    rewrite <- subst_shift.
    eapply HT_destruct.
    eapply IHe2.
    unfold HT_context in *; intros.
    econstructor.
    dependent destruction v.
    eq_simpl; eauto.
    eq_simpl; eapply HT_destruct; eauto.
    specialize (IHclos_refl_trans_1n ltac:(eauto) ltac:(eauto)).
    eapply HT_prepend_step; try eapply step_iter1; eauto.
Qed.