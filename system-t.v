Require List.
Require Import Relations.
Import List.ListNotations.
Open Scope list.
Require Import Equality.
Require Import Eqdep_dec.
Require Import Recdef.
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

Program Definition renaming_shift
        Gamma Gamma' t
        (gamma: renaming Gamma Gamma') :
  renaming (t :: Gamma) (t :: Gamma') :=
  fun t' v =>
    match v with
      | var_here _ _ => var_here _ _
      | var_outer _ v' => var_outer _ (gamma _ v')
    end.

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

Definition var_shift Gamma t' : renaming _ _ := fun t (v: variable Gamma t) => var_outer t' v.

Definition expr_shift Gamma t t' (e: expr Gamma t) : expr (t' :: Gamma) t.
  eapply apply_renaming; eauto.
  exact (var_shift _).
Defined.

Definition substitution Gamma Gamma' :=
  forall t (v: variable Gamma t), expr Gamma' t.

Program Definition substitution_shift
        Gamma Gamma' t
        (gamma: substitution Gamma Gamma') :
  substitution (t :: Gamma) (t :: Gamma') := fun t' v =>
  match v with
    | var_here _ _ => var (var_here _ _)
    | var_outer _ v' => expr_shift t (gamma _ v')
  end.

Program Definition substitution_shift_expr
        Gamma Gamma' t
        (e': expr Gamma' t)
        (gamma: substitution Gamma Gamma') :
  substitution (t :: Gamma) Gamma' :=
  fun t' (v: variable (t :: Gamma) t') =>
    match v with
      | var_here _ _ => e'
      | var_outer _ v' => gamma _ v'
    end.

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

Ltac subst_ext :=
  intros;
  let ext := (let t := fresh "t" in
             let v := fresh "v" in
             extensionality t; extensionality v;
             dependent destruction v;
             eauto) in
  match goal with
  | [ |- _ = _ :> (renaming _ _) ] => ext
  | [ |- _ = _ :> (substitution _ _) ] => ext
  end.

Ltac do_rewrites E :=
  intros; simpl; try rewrite E;
  repeat match goal with [H: context[_=_] |- _] => rewrite H end;
  auto.

Definition noop_substitution : forall {Gamma}, substitution Gamma Gamma.
  intros Gamma t v.
  eapply var; eauto.
Defined.

Lemma noop_substitution_shift : forall Gamma t,
    substitution_shift (t := t) (noop_substitution (Gamma := Gamma)) =
    noop_substitution.
Proof.
  subst_ext.
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
  subst_ext.
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
  subst_ext.
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
  subst_ext.
  unfold compose_sub_ren; simpl.
  unfold expr_shift; simpl.
  rewrite <- !apply_ren_ren; auto.
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
  subst_ext; simpl.
  unfold compose_substitutions; simpl.
  unfold expr_shift; simpl.
  rewrite <- apply_sub_ren, <- apply_ren_sub; auto.
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
  | [ H: @existT type ?P ?p _ = existT ?P ?p _ |- _ ] =>
    apply (inj_pair2_eq_dec type type_dec) in H; subst
  end.

Hint Constructors step val.

Theorem progress : forall t (e: expr [] t),
    val e \/
    exists e', step e e'.
Proof.
  intros.
  dependent induction e; subst; eauto.
  - inversion v.
  - edestruct IHe; repeat deex; eauto.
  - edestruct IHe1; repeat deex; eauto.
    edestruct IHe2; repeat deex; eauto.
    inversion H; repeat inj_pair2; eauto.
  - edestruct IHe3; repeat deex; eauto.
    inversion H; repeat inj_pair2; eauto.
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
         | [ H: @hereditary_termination natTy _ |- _ ] =>
           simpl in H
         | [ H: @hereditary_termination (arrow _ _) _ |- _ ] =>
           simpl in H
         | _ => progress simpl
         | _ => progress unfold terminating in *
         end.

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
  - exfalso; intuition eauto.
  - erewrite H; eauto.
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
  induction e; intuition;
    try solve [ right; inversion 1; intuition ].
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
  erewrite !IHe,
  !rename_substitution_shift_commute by eauto;
    auto.
  erewrite ?IHe1, ?IHe2,
  !rename_substitution_shift_commute by eauto;
    eauto.
Qed.

Arguments renaming_shift {Gamma Gamma'} t gamma [t0] v.
Arguments substitution_shift {Gamma Gamma'} t gamma [t0] v.

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
    rewrite !apply_renaming_as_substitution,
    <- !apply_sub_sub,
    !compose_rename_unshift,
    !substitute_noop_substitution;
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

Fixpoint maybe_step t (e: expr [] t) : {e' | step e e'} + {val e}.
  Ltac solve_val := try solve [ right; eauto ].
  destruct e; solve_val.
  - inversion v.
  - destruct (maybe_step _ e) as [[e' ?] | ]; solve_val.
    left.
    (* step_s *)
    exists (succ e'); eauto.
  - left.
    destruct (maybe_step _ e1) as [[e1' ?] |].
    (* step_ap1 *)
    exists (app e1' e2); eauto.
    destruct (maybe_step _ e2) as [[e2' ?] |].
    (* step_ap2 *)
    exists (app e1 e2'); eauto.
    dependent destruction e1;
      try solve [ exfalso; inversion v0 ].
    exists (subst e2 e1); eauto.
    exfalso; inversion v.
    exfalso; inversion v.
  - left.
    destruct (maybe_step _ e3) as [[e3' ?] |].
    (* step_iter1 *)
    exists (iter e1 e2 e3'); eauto.
    dependent destruction e3;
      try solve [ exfalso; inversion v ].
    (* step_iter2 *)
    exists e1; eauto.
    (* step_iter3 *)
    exists (subst (iter e1 e2 e3) e2).
    inversion v; eauto.
Defined.

Definition converse_step t e e' := step (t:=t) e' e.

Theorem converse_step_wf : forall t, well_founded (converse_step (t:=t)).
Proof.
  unfold well_founded, converse_step; intros t e.
  pose proof (exprs_terminating e); simplify.
  induction H.
  constructor; intros.
  exfalso; eapply val_no_step; eauto.
  constructor; intros.
  pose proof (step_deterministic H H2); subst; eauto.
Defined.

Definition eval t : expr [] t -> expr [] t.
Proof.
  refine (Fix (converse_step_wf (t:=t)) (fun _ => expr [] t)
              (fun e => match maybe_step e with
                     | inleft e' => _
                     | inright _ => _
                     end)); intro eval_e.
  - (* recursive subcall via relation proof *)
    exact (eval_e (proj1_sig e') (proj2_sig e')).
  - (* reached a value, terminate *)
    exact e.
Defined.

Theorem eval_val : forall t (e: expr [] t), val (eval e).
Proof.
  unfold eval, Fix; intros.
  induction (converse_step_wf e) using Acc_inv_dep; simpl.
  destruct (maybe_step x); eauto.
Qed.

(* alternate definition using Function *)
Function eval' t (e: expr [] t) {wf (converse_step (t:=t)) e} :=
  match maybe_step e with
  | inleft e' => eval' (proj1_sig e')
  | inright _ => e
  end.
Proof.
  unfold converse_step.
  destruct e'; auto.
  apply converse_step_wf.
Defined.

Theorem eval'_val : forall t (e: expr [] t), val (eval' e).
Proof.
  intros.
  functional induction (eval' e); eauto.
Qed.