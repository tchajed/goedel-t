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

Definition renaming Gamma Gamma' :=
  forall t (v: variable Gamma t), variable Gamma' t.

Definition renaming_shift :
  forall Gamma Gamma' t
    (gamma: renaming Gamma Gamma'),
    renaming (t :: Gamma) (t :: Gamma').
  unfold renaming; intros.
  inversion v; subst.
  apply var_here.
  apply var_outer.
  exact (gamma _ H2).
Defined.

Definition apply_renaming Gamma Gamma' (gamma: renaming Gamma Gamma')
           t (e: expr Gamma t) : expr Gamma' t.
  intros.
  generalize dependent Gamma'.
  generalize dependent Gamma.
  induction 1; intros; subst.
  + exact (var (gamma _ v)).
  + exact zero.
  + apply succ.
    now apply IHe.
  + eapply abs.
    eapply IHe; trivial.
    now apply renaming_shift.
  + now eapply app; [ apply IHe1 | apply IHe2 ].
  + eapply iter.
    now apply IHe1.
    apply IHe2; trivial.
    now apply renaming_shift.
    now apply IHe3.
Defined.

Definition var_shift Gamma t' t (v: variable Gamma t) := var_outer t' v.

Definition expr_shift Gamma t t' (e: expr Gamma t) : expr (t' :: Gamma) t.
  eapply apply_renaming; eauto.
  exact (var_shift _).
Defined.

Definition substitution Gamma Gamma' :=
  forall t (v: variable Gamma t), expr Gamma' t.

Definition substitution_shift :
  forall Gamma Gamma' t
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

Definition compose_ren_ren Gamma Gamma' Gamma''
           (r: renaming Gamma Gamma')
           (r': renaming Gamma' Gamma'') : renaming Gamma Gamma'' :=
  fun t v => r' _ (r t v).

Definition compose_ren_sub Gamma Gamma' Gamma''
           (r: renaming Gamma Gamma')
           (s: substitution Gamma' Gamma'') : substitution Gamma Gamma'' :=
  fun t v => s _ (r t v).

Definition compose_sub_ren Gamma Gamma' Gamma''
           (s: substitution Gamma Gamma')
           (r: renaming Gamma' Gamma'') : substitution Gamma Gamma'' :=
  fun t v => apply_renaming r (s t v).

Definition compose_substitutions Gamma Gamma' Gamma''
           (s: substitution Gamma Gamma')
           (s': substitution Gamma' Gamma'') : substitution Gamma Gamma'' :=
  fun t v => apply_substitution s' (s t v).

Ltac var_extensionality :=
  match goal with
    | [ |- ?X = ?Y ] =>
      let t := fresh "t" in extensionality t;
        let v := fresh "v" in extensionality v;
          dependent destruction v; auto
  end.

Ltac do_rewrites E :=
  intros; simpl; try rewrite E;
  repeat match goal with [H: context[_=_] |- _] => rewrite H end;
  auto.

Definition noop_substitution : forall {Gamma}, substitution Gamma Gamma.
  intros Gamma t v.
  eapply var; eauto.
Defined.

Ltac eq_simpl := simpl; unfold eq_rec_r, eq_rec; rewrite <- ?eq_rect_eq; simpl.

Lemma noop_substitution_shift : forall {Gamma} t, substitution_shift (t := t) (noop_substitution (Gamma := Gamma)) = noop_substitution.
  intros.
  extensionality t0.
  extensionality v.
  dependent destruction v; eq_simpl; reflexivity.
Qed.

Lemma substitute_noop_substitution :
  forall Gamma t (e: expr Gamma t),
    apply_substitution noop_substitution e = e.
Proof.
  induction e; eauto; simpl; try rewrite noop_substitution_shift; congruence.
Qed.

Lemma shift_ren_ren :
  forall Gamma Gamma' Gamma'' t
    (r: renaming Gamma Gamma')
    (r': renaming Gamma' Gamma''),
    renaming_shift (t:=t) (compose_ren_ren r r') =
    compose_ren_ren (renaming_shift r) (renaming_shift r').
Proof.
  intros. var_extensionality.
Qed.

Lemma apply_ren_ren :
  forall Gamma t (e: expr Gamma t) Gamma' Gamma''
    (r: renaming Gamma Gamma')
    (r': renaming Gamma' Gamma'') ,
    apply_renaming (compose_ren_ren r r') e = apply_renaming r' (apply_renaming r e).
Proof.
  induction e; do_rewrites shift_ren_ren.
Qed.

Lemma shift_ren_sub :
  forall Gamma Gamma' Gamma'' t
    (r: renaming Gamma Gamma')
    (s: substitution Gamma' Gamma''),
    substitution_shift (t:=t) (compose_ren_sub r s) =
    compose_ren_sub (renaming_shift r) (substitution_shift s).
Proof.
  intros. var_extensionality.
Qed.

Lemma apply_ren_sub :
  forall Gamma t (e: expr Gamma t) Gamma' Gamma''
    (r: renaming Gamma Gamma')
    (s: substitution Gamma' Gamma'') ,
    apply_substitution (compose_ren_sub r s) e = apply_substitution s (apply_renaming r e).
Proof.
  induction e; do_rewrites shift_ren_sub.
Qed.

Lemma shift_sub_ren :
  forall Gamma Gamma' Gamma'' t
    (s: substitution Gamma Gamma')
    (r: renaming Gamma' Gamma''),
    substitution_shift (t:=t) (compose_sub_ren s r) =
    compose_sub_ren (substitution_shift s) (renaming_shift r).
Proof.
  intros. var_extensionality. unfold compose_sub_ren. eq_simpl.
  unfold expr_shift. rewrite <- ?apply_ren_ren. auto.
Qed.

Lemma apply_sub_ren :
  forall Gamma t (e: expr Gamma t) Gamma' Gamma''
    (s: substitution Gamma Gamma')
    (r: renaming Gamma' Gamma''),
    apply_substitution (compose_sub_ren s r) e = apply_renaming r (apply_substitution s e).
Proof.
  induction e; do_rewrites shift_sub_ren.
Qed.

Lemma shift_sub_sub :
  forall Gamma Gamma' Gamma'' t
    (s: substitution Gamma Gamma')
    (s': substitution Gamma' Gamma''),
    substitution_shift (t:=t) (compose_substitutions s s') =
    compose_substitutions (substitution_shift s) (substitution_shift s').
Proof.
  intros. var_extensionality. eq_simpl. unfold compose_substitutions. eq_simpl.
  unfold expr_shift. rewrite <- apply_sub_ren. rewrite <- apply_ren_sub. auto.
Qed.

Lemma apply_sub_sub :
  forall Gamma t (e: expr Gamma t) Gamma' Gamma''
    (s: substitution Gamma Gamma')
    (s': substitution Gamma' Gamma''),
    apply_substitution (compose_substitutions s s') e =
    apply_substitution s' (apply_substitution s e).
Proof.
  induction e; do_rewrites shift_sub_sub.
Qed.

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

Hint Resolve step'_step step_step'.
Hint Constructors step val.

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

Ltac inv_step :=
  match goal with
  | [ H: step _ _ |- _ ] =>
    inversion H; repeat inj_pair2; clear H
  end.

Arguments step {t} e e'.
Hint Constructors clos_refl_trans_1n.
Arguments clos_refl_trans_1n {A} R _ _.
Infix "|->" := (step) (at level 20).
Infix "|->*" := (clos_refl_trans_1n step) (at level 20).

Lemma step_from_succ : forall e e',
    succ e |->* e' ->
    exists v', e' = succ v'.
Proof.
  intros.
  remember (succ e).
  generalize dependent e.
  induction H; intros; subst; eauto.
  inv_step; eauto.
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

Lemma step_respects_succ : forall e e',
    e |->* e' ->
    succ e |->* succ e'.
Proof.
  induction 1; intros; eauto.
Qed.

Hint Resolve step_respects_succ.

Definition HT_context Gamma (gamma: substitution Gamma []) :=
  forall t (v: variable Gamma t), hereditary_termination (gamma _ v).

Lemma hereditary_termination_succ' : forall (e: expr [] natTy),
    hereditary_termination (succ e) ->
    hereditary_termination e.
Proof.
  simpl; unfold terminating; intros.
  deex.

  remember (succ e).
  generalize dependent e.
  induction H; intros; subst.
  inversion H0; eauto.

  inv_step.
  intuition.
  specialize (H e'); intuition.
  deex; eauto.
Qed.

Ltac simplify :=
  repeat match goal with
         | [ |- forall _, _ ] => intros
         | _ => progress subst
         | [ H: exists _, _ |- _ ] => deex
         | [ H: ?a = ?a |- _ ] => clear H
         | _ => inj_pair2
         | [ H: step' _ _ |- _ ] => inversion H; subst; clear H;
                                  repeat inj_pair2
         | [ H: @hereditary_termination natTy _ |- _ ] =>
           simpl in H
         | [ H: @hereditary_termination (arrow _ _) _ |- _ ] =>
           simpl in H
         | _ => progress eq_simpl
         | _ => progress unfold terminating in *
         end.

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
      clos_refl_trans_1n R a a'' ->
      (forall a''', ~R a'' a''') ->
      R a a' ->
      clos_refl_trans_1n R a' a''.
Proof.
  intros.

  induction H0.
  apply H1 in H2; intuition eauto.
  pose proof (H _ _ _ H0 H2); subst.
  eauto.
Qed.

Lemma val_no_step : forall t (e e': expr [] t),
    val e ->
    ~e |-> e'.
Proof.
  induction 1; simplify;
    inversion 1; simplify; intuition eauto.
Qed.

Definition val_dec : forall t (e: expr [] t), {val e} + {~val e}.
Proof.
  induction e; try solve [ right; inversion 1]; intuition eauto.
  right; inversion 1; intuition.
Defined.

Theorem step_deterministic : forall t, deterministic (step (t:=t)).
Proof.
  unfold deterministic; intros.
  induction H; simplify;
    inversion H0; simplify;
      try pose proof (IHstep _ ltac:(eauto));
      repeat (intuition eauto || simplify);
      try solve [ exfalso; match goal with
                           | [ H: val ?e, H': step ?e ?e' |- _ ] =>
                             apply (val_no_step H H')
                           | [ H: step ?e _ |- _ ] =>
                             let Hval := fresh in
                             assert (val e) as Hval by eauto;
                             apply (val_no_step Hval H)
                           end ].
Qed.

Lemma step_clos_refl_R : forall t (e e' e'': expr [] t),
    val e'' ->
    e |->* e'' ->
    e |-> e' ->
    e' |->* e''.
Proof.
  eauto using step_deterministic, val_no_step, deterministic_clos_refl_R.
Qed.

Hint Resolve step_clos_refl_R.

Lemma HT_respects_step : forall t (e e': expr [] t),
    hereditary_termination e ->
    e |-> e' ->
    hereditary_termination e'.
Proof.
  induction t; simplify; eauto.
Qed.

Hint Resolve HT_respects_step.

Lemma HT_prepend_step : forall t (e e': expr [] t),
    hereditary_termination e' ->
    e |-> e' ->
    hereditary_termination e.
Proof.
  simplify.
  generalize dependent e.
  generalize dependent e'.
  induction t; simplify; eauto.
Qed.

Definition rename_substitution Gamma Gamma' (r: renaming Gamma Gamma') : substitution Gamma Gamma' :=
  fun t e => var (r _ e).

Lemma rename_substitution_shift_commute : forall Gamma Gamma' t (r: renaming Gamma Gamma'),
    rename_substitution (renaming_shift (t:=t) r) =
    substitution_shift (rename_substitution r).
Proof.
  intros; extensionality t'; extensionality e.
  dependent induction e; simplify; eauto.
Qed.

Theorem apply_renaming_as_substitution : forall Gamma Gamma' (r: renaming Gamma Gamma'),
    apply_renaming r = apply_substitution (rename_substitution r).
Proof.
  intros.
  extensionality t; extensionality e.
  generalize dependent Gamma'.
  induction e; simplify; f_equal; eauto.
  erewrite ?IHe,
  ?rename_substitution_shift_commute by eauto;
    auto.
  erewrite ?IHe1, ?IHe2, ?IHe3,
  ?rename_substitution_shift_commute by eauto;
    eauto.
Qed.

Arguments renaming_shift {Gamma Gamma'} t gamma [t0] v.
Arguments substitution_shift {Gamma Gamma'} t gamma [t0] v.

Lemma apply_rename_shift_commute : forall Gamma t1 t2 (e: expr (t1 :: Gamma) t2)
                                     Gamma' (s: substitution Gamma Gamma') t,
    apply_substitution (substitution_shift t1 (rename_substitution (var_shift t)))
                       (apply_substitution (substitution_shift t1 s) e) =
    apply_substitution (substitution_shift t1 (substitution_shift t s))
                       (apply_substitution (substitution_shift t1 (rename_substitution (var_shift t))) e).
Proof.
  unfold rename_substitution.
  intros.
  generalize dependent Gamma'.
  dependent induction e; simplify; f_equal; eauto.
  - admit.
  - specialize (IHe (t1::Gamma) t0 e); intuition.
    admit.
  - specialize (IHe1 Gamma t1 e1);
      specialize (IHe2 (t1::Gamma) t e2);
      specialize (IHe3 Gamma t1 e3);
      intuition.
    admit.
Admitted.

Lemma expr_shift_substitution : forall t Gamma Gamma'
                                  t' (e: expr Gamma t')
                                  (s: substitution Gamma Gamma'),
    expr_shift t (apply_substitution s e) =
    apply_substitution (substitution_shift t s) (expr_shift t e).
Proof.
  unfold expr_shift; intros.

  rewrite ?apply_renaming_as_substitution.

  generalize dependent Gamma'.
  dependent induction e; simplify;
    f_equal; eauto;
      rewrite <- ?apply_renaming_as_substitution,
      ?apply_rename_shift_commute;
      eauto.
Qed.

Lemma substitution_shift_compose_commute : forall Gamma Gamma' Gamma'' t
                                             (s1: substitution Gamma Gamma')
                                             (s2: substitution Gamma' Gamma''),
    substitution_shift t (compose_substitutions s1 s2) =
    compose_substitutions (substitution_shift t s1) (substitution_shift t s2).
Proof.
  unfold compose_substitutions.
  intros; extensionality t'; extensionality v.
  dependent destruction v; simplify; eauto using expr_shift_substitution.
Qed.

Theorem apply_compose_substitutions :
  forall Gamma t (e: expr Gamma t)
    Gamma' Gamma'' (s1: substitution Gamma Gamma') (s2: substitution Gamma' Gamma''),
    apply_substitution (compose_substitutions s1 s2) e =
    apply_substitution s2 (apply_substitution s1 e).
Proof.
  induction e; simplify; eauto;
    rewrite ?substitution_shift_compose_commute;
    now f_equal.
Qed.

Lemma compose_rename_unshift : forall Gamma t t' (e': expr Gamma t'),
    compose_substitutions (rename_substitution
                             (renaming_shift t (var_shift t')))
                          (substitution_shift
                             t (substitution_shift_expr e' noop_substitution)) =
    noop_substitution.
Proof.
  intros.
  extensionality t0; extensionality v.
  dependent destruction v; simplify; eauto.
Qed.

Lemma shift_unshift_noop : forall Gamma t (e: expr Gamma t)
                             t' (e': expr Gamma t'),
    apply_substitution (substitution_shift_expr e' noop_substitution)
                       (expr_shift t' e) = e.
Proof.
  induction e; simplify; f_equal;
    eauto;
    rewrite ?apply_renaming_as_substitution,
    <- ?apply_compose_substitutions,
    ?compose_rename_unshift,
    ?substitute_noop_substitution;
    auto.
Qed.

Lemma subst_shift :
  forall Gamma (gamma: substitution Gamma []) t1 t2 (e: expr (t1 :: Gamma) t2) e2,
    apply_substitution (substitution_shift_expr e2 gamma) e =
    subst e2 (apply_substitution (substitution_shift t1 gamma) e).
Proof.
  unfold subst.
  intros.
  rewrite <- apply_sub_sub.
  f_equal.
  unfold compose_substitutions.
  extensionality t; extensionality v.
  dependent destruction v; simplify;
    rewrite ?shift_unshift_noop;
    eauto.
Qed.

Theorem hereditary_termination_terminating :
  forall t (e: expr [] t),
    hereditary_termination e -> terminating e.
Proof.
  intros.
  destruct t; simplify; eauto.
Qed.

Lemma HT_abs :
  forall t1 t2 (e1: expr [] (arrow t1 t2)) e2,
    hereditary_termination e1 ->
    hereditary_termination e2 ->
    hereditary_termination (app e1 e2).
Proof.
  intros.
  edestruct H.
  intuition.
  generalize H0; intros Ht2.
  apply hereditary_termination_terminating in H0.
  destruct H0.
  intuition.
  remember (abs x).
  induction H2; subst.
  induction H1; eauto using HT_prepend_step.
  eapply HT_prepend_step; [ | eapply step_ap1 ]; eauto.
Qed.

Lemma hereditary_termination_succ : forall e,
    hereditary_termination e ->
    hereditary_termination (succ e).
Proof.
  simplify; eauto.
Qed.

Hint Resolve HT_abs.

Theorem HT_context_subst : forall Gamma t (e: expr Gamma t) (gamma: substitution Gamma []),
    HT_context gamma -> hereditary_termination (apply_substitution gamma e).
Proof.
  intros.
  generalize dependent gamma.
  induction e; simplify; eauto.
  - eapply hereditary_termination_succ; eauto.
  - eexists.
    intuition eauto.
    rewrite <- subst_shift.
    eapply IHe.
    unfold HT_context in *.
    intros.
    dependent destruction v; simplify; eauto.
  - specialize (IHe3 gamma H).
    remember (apply_substitution gamma e3).
    clear e3 Heqe.
    generalize IHe3; intro Ht3.
    eapply hereditary_termination_terminating in Ht3.
    unfold terminating in Ht3; deex.
    induction H0.
    dependent induction H1.
    eapply HT_prepend_step; try eapply step_iter2; eauto.
    eapply hereditary_termination_succ' in IHe3.
    intuition.
    specialize (H0 _ ltac:(eauto)).
    eapply HT_prepend_step; try eapply step_iter3; eauto.
    rewrite <- subst_shift.
    eapply IHe2.
    unfold HT_context in *; intros.
    dependent destruction v; simplify; eauto.
    eapply HT_prepend_step; try eapply step_iter1; eauto.
Qed.

Hint Resolve substitute_noop_substitution.

Theorem exprs_ht :
  forall t (e: expr [] t),
    hereditary_termination e.
Proof.
  intros.
  replace e with (apply_substitution noop_substitution e) by auto.
  eapply HT_context_subst.
  unfold HT_context; intros.
  inversion v.
Qed.

Theorem exprs_terminating :
  forall t (e: expr [] t),
    terminating e.
Proof.
  auto using hereditary_termination_terminating, exprs_ht.
Qed.