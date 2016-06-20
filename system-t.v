Require Import String.

Inductive type :=
  | natTy
  | arrow : type -> type -> type.

Inductive expr :=
| var : string -> expr
| zero : expr
| succ : expr -> expr
| iter : forall (ez:expr) (x:string) (e:expr) (n:expr), expr
| abs : string -> type -> expr -> expr
| app : expr -> expr -> expr.

Implicit Types (x:string) (t:type) (e:expr).

Definition mapping := string -> option type.

Definition upd (m: mapping) v0 t : mapping :=
  fun v =>
    if string_dec v v0
    then Some t
    else m v.

Theorem upd_eq : forall m v t v',
    v = v' ->
    upd m v t v' = Some t.
Proof.
  unfold upd; intros.
  destruct (string_dec v' v); congruence.
Qed.

Theorem upd_ne : forall m v t v',
    v <> v' ->
    upd m v t v' = m v'.
Proof.
  unfold upd; intros.
  destruct (string_dec v' v); congruence.
Qed.

Inductive hasTy : mapping -> expr -> type -> Prop :=
| hasTy_var : forall Gamma s t, Gamma s = Some t -> hasTy Gamma (var s) t
| hasTy_zero : forall Gamma, hasTy Gamma zero natTy
| hasTy_succ: forall Gamma e, hasTy Gamma e natTy -> hasTy Gamma (succ e) natTy
| hasTy_iter : forall Gamma e ez t n x,
    hasTy Gamma ez t -> hasTy Gamma n natTy ->
    hasTy (upd Gamma x t) e t ->
    hasTy Gamma (iter ez x e n) t
| hasTy_lambda : forall Gamma x e t1 t2,
    hasTy (upd Gamma x t1) e t2 ->
    hasTy Gamma (abs x t1 e) (arrow t1 t2)
| hasTy_app : forall Gamma e1 e2 t1 t2,
    hasTy Gamma e1 (arrow t1 t2) ->
    hasTy Gamma e2 t1 ->
    hasTy Gamma (app e1 e2) t2.

Infix "==v" := (string_dec) (at level 30, no associativity).

Fixpoint subst x (x': expr) e : expr :=
  match e with
  | var s => if s ==v x then x' else var s
  | zero => zero
  | succ e => succ (subst x x' e)
  | abs v t e => abs v t (if v ==v x then e else subst x x' e)
  | iter ez v e n => let ez' := subst x x' ez in
                    let n' := subst x x' n in
                    iter ez' v (if v ==v x then e else subst x x' e) n'
  | app e1 e2 => app (subst x x' e1) (subst x x' e1)
  end.