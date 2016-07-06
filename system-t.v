(**
 * Formalization of Gödel's System T.
 *
 * We represent the language with well-typed terms, following an approach
 * similar to "Strongly Typed Term Representations in Coq" by Nick Benton,
 * Chung-Kil Hur, Andrew J. Kennedy and Conor Mcbride (2012). A good high-level
 * explanation of the approach is in this presentation:
 * https://www.cis.upenn.edu/~sweirich/wmm/wmm09/Benton-Slides.pdf.
 *
 * From there we define a unary logical relation we call hereditary termination,
 * well-founded due to recursion on (object) types. We prove all terms are
 * hereditarily terminating, which implies termination of every term.
 *
 * As a nice side-effect, we also use the termination proof as the crucial lemma
 * in a well-foundedness proof for an evaluator that steps system T expressions
 * to completion, with the expected correctness proof.
 *)

Require List.
Require Import Relations.
Import List.ListNotations.
Open Scope list.
Require Import Equality.
Require Import Eqdep_dec.
Require Import Recdef.
Require Import FunctionalExtensionality.

Set Implicit Arguments.

(** * Language definitions *)

Inductive type :=
  | natTy
  | arrow : type -> type -> type.

Definition type_dec : forall (t1 t2: type), {t1=t2} + {t1<>t2}.
Proof.
  decide equality.
Defined.

Definition context := list type.

Inductive variable : context -> type -> Type :=
| var_here : forall Gamma t, variable (t :: Gamma) t
| var_outer : forall Gamma t t', variable Gamma t -> variable (t' :: Gamma) t.

Inductive expr (Gamma: context) : type -> Type :=
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

Implicit Types (Gamma: context) (t: type).

(** * Substitution *)

(** Defining substitution is tricky. We build it up gradually , starting with a
more basic notion of renaming. *)

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

Definition var_shift Gamma t' : renaming Gamma (t'::Gamma) :=
  fun _ v => var_outer t' v.

Definition expr_shift Gamma t t' (e: expr Gamma t) : expr (t' :: Gamma) t :=
  apply_renaming (var_shift t') e.

(** General substitution between two contexts. *)
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

(** * Four types of composition, between renamings and substitutions. *)

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

Definition compose_sub_sub Gamma Gamma' Gamma''
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

Ltac inj_pair2 :=
  match goal with
  | [ H: @existT type ?P ?p _ = existT ?P ?p _ |- _ ] =>
    apply (inj_pair2_eq_dec type type_dec) in H; subst
  end.

Ltac deex H :=
  lazymatch type of H with
  | exists (varname:_), _ =>
    let name := fresh varname in
    destruct H as [name ?]
  end.

Ltac simplify_hook := fail.

Ltac simplify :=
  repeat match goal with
         | [ |- forall _, _ ] => intros
         | _ => progress subst
         | [ H: exists _, _ |- _ ] => deex H
         | [ H: _ /\ _ |- _ ] => destruct H
         | [ H: ?a = ?a |- _ ] => clear H
         | _ => inj_pair2
         | _ => progress simpl
         | _ => progress autounfold in *
         | [ H: context[_ = _] |- _ ] => rewrite H by auto
         | _ => progress autorewrite with subst
         | _ => simplify_hook
         end.

Ltac crush :=
  simplify; eauto;
  try solve [ subst_ext ].

Definition noop_substitution : forall {Gamma}, substitution Gamma Gamma.
  intros Gamma t v.
  apply var; auto.
Defined.

Lemma noop_substitution_shift : forall Gamma t,
    substitution_shift (t := t) (noop_substitution (Gamma := Gamma)) =
    noop_substitution.
Proof.
  crush.
Qed.

Hint Rewrite noop_substitution_shift : subst.

Lemma substitute_noop_substitution :
  forall Gamma t (e: expr Gamma t),
    apply_substitution noop_substitution e = e.
Proof.
  induction e; crush.
Qed.

Hint Rewrite substitute_noop_substitution : subst.

Section RenameSubstitutionCompositions.

  Lemma shift_ren_ren :
    forall Gamma Gamma' Gamma'' t
      (r: renaming Gamma Gamma')
      (r': renaming Gamma' Gamma''),
      renaming_shift (t:=t) (compose_ren_ren r r') =
      compose_ren_ren (renaming_shift r) (renaming_shift r').
  Proof.
    crush.
  Qed.

  Hint Rewrite @shift_ren_ren : subst.

  Lemma apply_ren_ren :
    forall Gamma t (e: expr Gamma t) Gamma' Gamma''
      (r: renaming Gamma Gamma')
      (r': renaming Gamma' Gamma'') ,
      apply_renaming (compose_ren_ren r r') e = apply_renaming r' (apply_renaming r e).
  Proof.
    induction e; crush.
  Qed.

  Lemma shift_ren_sub :
    forall Gamma Gamma' Gamma'' t
      (r: renaming Gamma Gamma')
      (s: substitution Gamma' Gamma''),
      substitution_shift (t:=t) (compose_ren_sub r s) =
      compose_ren_sub (renaming_shift r) (substitution_shift s).
  Proof.
    crush.
  Qed.

  Hint Rewrite shift_ren_sub : subst.

  Lemma apply_ren_sub :
    forall Gamma t (e: expr Gamma t) Gamma' Gamma''
      (r: renaming Gamma Gamma')
      (s: substitution Gamma' Gamma'') ,
      apply_substitution (compose_ren_sub r s) e = apply_substitution s (apply_renaming r e).
  Proof.
    induction e; crush.
  Qed.

  Hint Rewrite <- apply_ren_ren : subst.

  Lemma shift_sub_ren :
    forall Gamma Gamma' Gamma'' t
      (s: substitution Gamma Gamma')
      (r: renaming Gamma' Gamma''),
      substitution_shift (t:=t) (compose_sub_ren s r) =
      compose_sub_ren (substitution_shift s) (renaming_shift r).
  Proof.
    subst_ext.
    unfold compose_sub_ren; simplify.
    unfold expr_shift; crush.
  Qed.

  Hint Rewrite shift_sub_ren : subst.

  Lemma apply_sub_ren :
    forall Gamma t (e: expr Gamma t) Gamma' Gamma''
      (s: substitution Gamma Gamma')
      (r: renaming Gamma' Gamma''),
      apply_substitution (compose_sub_ren s r) e = apply_renaming r (apply_substitution s e).
  Proof.
    induction e; crush.
  Qed.

  Hint Rewrite <- apply_sub_ren : subst.
  Hint Rewrite <- apply_ren_sub : subst.

  Lemma shift_sub_sub :
    forall Gamma Gamma' Gamma'' t
      (s: substitution Gamma Gamma')
      (s': substitution Gamma' Gamma''),
      substitution_shift (t:=t) (compose_sub_sub s s') =
      compose_sub_sub (substitution_shift s) (substitution_shift s').
  Proof.
    subst_ext.
    unfold compose_sub_sub; simpl.
    unfold expr_shift; crush.
  Qed.

  Hint Rewrite shift_sub_sub : subst.

  Lemma apply_sub_sub :
    forall Gamma t (e: expr Gamma t) Gamma' Gamma''
      (s: substitution Gamma Gamma')
      (s': substitution Gamma' Gamma''),
      apply_substitution (compose_sub_sub s s') e =
      apply_substitution s' (apply_substitution s e).
  Proof.
    induction e; crush.
  Qed.

End RenameSubstitutionCompositions.

(** * Finally we build subst from a simple substitution.

Note that subst creates closed terms.
 *)

Definition subst t' (e': expr [] t') t (e: expr [t'] t) : expr [] t :=
  apply_substitution (substitution_shift_expr e' noop_substitution) e.

(** * The dynamics of the language. *)

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

Arguments step {t} e e'.

Hint Constructors step val.

(** * We prove progress only as an exercise. *)
Theorem progress : forall t (e: expr [] t),
    val e \/
    exists e', step e e'.
Proof.
  dependent induction e; eauto.
  - inversion v.
  - edestruct IHe; crush.
  - edestruct IHe1; crush.
    edestruct IHe2; crush.
    inversion H; crush.
  - edestruct IHe3; crush.
    inversion H; crush.
Qed.

Ltac inv_step :=
  match goal with
  | [ H: step _ _ |- _ ] =>
    inversion H; repeat inj_pair2; clear H
  end.

(** * General relation properties. *)

Hint Constructors clos_refl_trans_1n.
Arguments clos_refl_trans_1n {A} R _ _.

(** A deterministic relation can also be viewed as a (non-computational) partial
function *)
Definition deterministic A (R: A -> A -> Prop) :=
  forall a a' a'', R a a' ->
              R a a'' ->
              a' = a''.

(** Final values for a relation are those that have no image, interpreting the
relation as a function *)
Definition final A (R: A -> A -> Prop) a := forall a', ~R a a'.

Theorem deterministic_clos_refl_R : forall A (R: A -> A -> Prop),
    deterministic R ->
    forall a a' a'',
      clos_refl_trans_1n R a a'' ->
      final R a'' ->
      R a a' ->
      clos_refl_trans_1n R a' a''.
Proof.
  unfold final; intros.
  induction H0.
  - exfalso; intuition eauto.
  - erewrite H; eauto.
Qed.

(* Repeating a deterministic relation till it yields a final value, viewed as itself a relation, is deterministic. *)
Theorem deterministic_clos_refl_unique : forall A (R: A -> A -> Prop),
    deterministic R ->
    forall a a' a'',
      clos_refl_trans_1n R a a' ->
      clos_refl_trans_1n R a a'' ->
      final R a' ->
      final R a'' ->
      a' = a''.
Proof.
  unfold final; intros.
  generalize dependent a''.
  induction H0; intros.
  - inversion H1; subst; eauto.
    exfalso; intuition eauto.
  - eauto using deterministic_clos_refl_R.
Qed.

(** * Specializing the above tools for step *)

Infix "|->" := (step) (at level 20).
Infix "|->*" := (clos_refl_trans_1n step) (at level 20).

Lemma val_no_step : forall t (e e': expr [] t),
    val e ->
    ~e |-> e'.
Proof.
  induction 1; simplify;
    try match goal with
        | [ H: _ |-> _ |- _ ] =>
          inversion H; crush
        end.
Qed.

Lemma val_final : forall t (e: expr [] t),
    val e ->
    final step e.
Proof.
  unfold final; eauto using val_no_step.
Qed.

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
  eauto using step_deterministic, val_final, deterministic_clos_refl_R.
Qed.

Hint Resolve step_clos_refl_R.

Lemma step_val_unique : forall t (e e' e'': expr [] t),
    e |->* e' ->
    e |->* e'' ->
    val e' ->
    val e'' ->
    e' = e''.
Proof.
  eauto using deterministic_clos_refl_unique, step_deterministic, val_final.
Qed.

(* non-strictly positive definition *)
(*
Inductive HT : forall t (e: expr [] t), Prop :=
| HT_natTy : forall e, terminating e -> HT e
| HT_arrow : forall t1 t2 (e: expr [] (arrow t1 t2)), (forall (e1: expr [] t1), HT e1 ->
                                                                      HT (app e e1)) ->
                                                 HT e.
*)

(** * Logical relation for termination. *)

Definition terminating t (e: expr [] t) : Prop := exists e', e |->* e' /\ val e'.

Hint Unfold terminating.

Fixpoint hereditary_termination t : expr [] t -> Prop :=
  match t with
  | natTy => fun e => terminating e
  | arrow t1 t2 => fun e =>
                    (* not only does e terminate, but we also extract the body
                    of the abstraction it terminates to *)
                    exists e0, e |->* abs e0 /\
                    (forall e1: expr [] t1, hereditary_termination e1 ->
                                       hereditary_termination (subst e1 e0))
  end.

Ltac simplify_hook ::=
     match goal with
     | [ H: @hereditary_termination natTy _ |- _ ] =>
       simpl in H
     | [ H: @hereditary_termination (arrow _ _) _ |- _ ] =>
       simpl in H
     end.

(** Lift hereditary termination to contexts. *)
Definition HT_context Gamma (gamma: substitution Gamma []) :=
  forall t (v: variable Gamma t), hereditary_termination (gamma _ v).

Lemma step_respects_succ : forall e e',
    e |->* e' ->
    succ e |->* succ e'.
Proof.
  induction 1; crush.
Qed.

Hint Resolve step_respects_succ.

(** val turns out to be decidable *)
Definition val_dec : forall t (e: expr [] t), {val e} + {~val e}.
Proof.
  induction e; intuition;
    try solve [ right; inversion 1; intuition ].
Defined.

Lemma hereditary_termination_succ' : forall (e: expr [] natTy),
    hereditary_termination (succ e) ->
    hereditary_termination e.
Proof.
  simplify.

  remember (succ e).
  generalize dependent e.
  induction H; crush.
  inversion H0; eauto.

  inv_step.
  edestruct IHclos_refl_trans_1n; crush.
Qed.

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
  induction t; crush.
Qed.

Definition rename_substitution Gamma Gamma' (r: renaming Gamma Gamma') :
  substitution Gamma Gamma' :=
  fun t e => var (r _ e).

Lemma rename_substitution_shift_commute : forall Gamma Gamma' t (r: renaming Gamma Gamma'),
    rename_substitution (renaming_shift (t:=t) r) =
    substitution_shift (rename_substitution r).
Proof.
  crush.
Qed.

Hint Rewrite rename_substitution_shift_commute using (solve [ eauto ]) : subst.

Theorem apply_renaming_as_substitution : forall Gamma Gamma' (r: renaming Gamma Gamma'),
    apply_renaming r = apply_substitution (rename_substitution r).
Proof.
  intros.
  extensionality t; extensionality e.
  generalize dependent Gamma'.
  induction e; crush.
Qed.

Arguments renaming_shift {Gamma Gamma'} t gamma [t0] v.
Arguments substitution_shift {Gamma Gamma'} t gamma [t0] v.

Lemma compose_rename_unshift : forall Gamma t t' (e': expr Gamma t'),
    compose_sub_sub (rename_substitution
                             (renaming_shift t (var_shift t')))
                          (substitution_shift
                             t (substitution_shift_expr e' noop_substitution)) =
    noop_substitution.
Proof.
  crush.
Qed.

Hint Rewrite compose_rename_unshift : subst.

Hint Rewrite <- apply_sub_sub : subst.
Hint Rewrite apply_renaming_as_substitution : subst.

Lemma shift_unshift_noop : forall Gamma t (e: expr Gamma t)
                             t' (e': expr Gamma t'),
    apply_substitution (substitution_shift_expr e' noop_substitution)
                       (expr_shift t' e) = e.
Proof.
  induction e; crush.
Qed.

Hint Rewrite shift_unshift_noop : subst.

Lemma subst_shift :
  forall Gamma (gamma: substitution Gamma []) t1 t2 (e: expr (t1 :: Gamma) t2) e2,
    apply_substitution (substitution_shift_expr e2 gamma) e =
    subst e2 (apply_substitution (substitution_shift t1 gamma) e).
Proof.
  unfold subst; simplify.
  f_equal.
  unfold compose_sub_sub.
  subst_ext; crush.
Qed.

Hint Rewrite <- subst_shift : subst.

Theorem hereditary_termination_terminating :
  forall t (e: expr [] t),
    hereditary_termination e -> terminating e.
Proof.
  destruct t; crush.
Qed.

Lemma HT_abs :
  forall t1 t2 (e1: expr [] (arrow t1 t2)) e2,
    hereditary_termination e1 ->
    hereditary_termination e2 ->
    hereditary_termination (app e1 e2).
Proof.
  intros.
  edestruct H; crush.
  generalize H0; intros Ht2.
  apply hereditary_termination_terminating in H0.
  destruct H0; crush.
  remember (abs x) as f.
  match goal with
  | [ H: _ |->* f |- _ ] =>
    induction H; crush
  end.
  induction H0; eauto using HT_prepend_step.
  eapply HT_prepend_step; [ | eapply step_ap1 ]; eauto.
Qed.

Lemma hereditary_termination_succ : forall e,
    hereditary_termination e ->
    hereditary_termination (succ e).
Proof.
  crush.
Qed.

Hint Resolve HT_abs.

Lemma succ_step : forall e e',
    succ e |->* e' ->
    exists e'', e' = succ e''.
Proof.
  intros.
  remember (succ e).
  generalize dependent e.
  induction H; crush.
  inv_step; eauto.
Qed.

Hint Resolve HT_prepend_step.

Lemma HT_context_shift : forall Gamma (gamma: substitution Gamma []) t (e: expr [] t),
    HT_context gamma ->
    hereditary_termination e ->
    HT_context (substitution_shift_expr e gamma).
Proof.
  unfold HT_context; intros.
  dependent destruction v; crush.
Qed.

Hint Resolve HT_context_shift.

(** * The main theorem, with the fully generalized induction hypothesis *)


Theorem HT_context_subst : forall Gamma t (e: expr Gamma t) (gamma: substitution Gamma []),
    HT_context gamma -> hereditary_termination (apply_substitution gamma e).
Proof.
  intros.
  generalize dependent gamma.
  induction e; crush.
  - edestruct IHe; crush.
  - eexists; intuition crush.
  - specialize (IHe3 gamma H).
    simplify.
    induction H0; crush.
    dependent induction H1; crush.
    eapply HT_prepend_step; [ | apply step_iter3 ]; crush.
Qed.

(** Specialize [HT_context_subst] to noop_substitution *)
Theorem exprs_ht :
  forall t (e: expr [] t),
    hereditary_termination e.
Proof.
  intros.
  replace e with (apply_substitution noop_substitution e) by crush.
  apply HT_context_subst.
  unfold HT_context; inversion v.
Qed.

(** Derive termination from [hereditary_termination]. *)
Theorem exprs_terminating :
  forall t (e: expr [] t),
    terminating e.
Proof.
  auto using hereditary_termination_terminating, exprs_ht.
Qed.

(** * We now go on to build a well-founded evaluator for System T. *)

(** First we need a computational version of step. The type builds in the
correctness proof, since this is the easiest time to do so. *)
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

(** The well-founded relation for evaluation is step, but reversed, since when e
|-> e', e' is smaller than e in terms of remaining evaluation steps. *)
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

(** We now define the evaluator with just Fix and the above well-founded
relation *)
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

(** The correctness of eval is given by the fact that it returns a value and
satisfies e |->* eval e; such a function is actually unique due to
[step_val_unique] *)

Theorem eval_val : forall t (e: expr [] t), val (eval e).
Proof.
  unfold eval, Fix; intros.
  induction (converse_step_wf e) using Acc_inv_dep; simpl.
  destruct (maybe_step x); eauto.
Qed.

Theorem eval_step : forall t (e: expr [] t),
    e |->* eval e.
Proof.
  unfold eval, Fix; intros.
  induction (converse_step_wf e) using Acc_inv_dep; simpl.
  destruct (maybe_step x) as [[] |]; eauto.
Qed.

(** Here we give an alternate definition using Function *)
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

Theorem eval'_step : forall t (e: expr [] t),
    e |->* eval' e.
Proof.
  intros.
  functional induction (eval' e); eauto.
  destruct e'; eauto.
Qed.

(** The correctness proofs guarantee eval and eval' agree. *)
Theorem eval_eq_eval' : forall t (e: expr [] t),
    eval e = eval' e.
Proof.
  intros.
  eapply (step_val_unique (e := e));
    eauto using eval_step, eval'_step,
    eval_val, eval'_val.
Qed.

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
    rewrite IHval.
    admit.
Admitted.

Lemma expr_denote_step_star : forall t (e e': expr [] t),
    e |->* e' ->
    expr_denote e tt = expr_denote e' tt.
Proof.
  intros.
  induction H; auto.
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
