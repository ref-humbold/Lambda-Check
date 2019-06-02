Require Import List.
Import ListNotations.
Require Import String.
Open Scope string_scope.
Require Import Sumbool.

Section E_lambdaChurch.

Definition var_L := string.

Inductive type_L : Type :=
| T_bool : type_L
| T_func : type_L -> type_L -> type_L.

Notation "'Bool'" := T_bool (at level 70).
Notation "t ~> u" := (T_func t u) (right associativity, at level 60).

Inductive eq_type : type_L -> type_L -> Prop :=
| Eq_bool : eq_type T_bool T_bool
| Eq_func : forall (t1 t2 u1 u2 : type_L), eq_type t1 u1 -> eq_type t2 u2
              -> eq_type (T_func t1 t2) (T_func u1 u2).

Inductive expr_L : Type :=
| E_true : expr_L
| E_false : expr_L
| E_var : var_L -> expr_L
| E_type : expr_L -> type_L -> expr_L
| E_lambda : var_L -> type_L -> expr_L -> expr_L
| E_app : expr_L -> expr_L -> expr_L
| E_if : expr_L -> expr_L -> expr_L -> expr_L.

Notation "'TRUE'" := E_true (at level 50).
Notation "'FALSE'" := E_false (at level 50).
Notation "% v" := (E_var v) (at level 50).
Notation "p $ q" := (E_app p q) (left associativity, at level 40).
Notation "\ x 'OF' t 'IS' e" := (E_lambda x t e) (at level 30).
Notation "'WHEN' b 'THEN' p 'ELSE' q" := (E_if b p q) (at level 20).
Notation "e 'of' t" := (E_type e t) (at level 10).

Definition context_L := var_L -> option type_L.

Fixpoint add_ctx (ctx : context_L) (v : var_L) (t : type_L) : context_L := 
fun v' => if string_dec v v' then Some t else ctx v'.

Inductive infer (c : context_L) : expr_L -> type_L -> Prop :=
| In_true : infer c E_true T_bool
| In_false : infer c E_false T_bool
| In_var v : forall t : type_L, c v = Some t -> infer c (E_var v) t
| In_type e t : check c e t -> infer c (E_type e t) t
| In_lambda v t e : forall u : type_L, infer (add_ctx c v t) e u
                      -> infer c (E_lambda v t e) (T_func t u)
| In_app e1 e2 : forall (t u : type_L), infer c e1 (T_func t u)
                   -> check c e2 t -> infer c (E_app e1 e2) u
| In_if b e1 e2 : forall (t u : type_L), check c b T_bool -> infer c e1 t
                    -> check c e2 t -> infer c (E_if b e1 e2) t
with check (c : context_L) : expr_L -> type_L -> Prop :=
| Ch_true : check c E_true T_bool
| Ch_false : check c E_false T_bool
| Ch_lambda v t e u : check (add_ctx c v t) e u
                        -> check c (E_lambda v t e) (T_func t u)
| Ch_if b e1 e2 t : check c b T_bool -> check c e1 t -> check c e2 t
| Ch_infer e t : infer c e t -> check c e t.

Lemma eq_type_refl :
forall (t : type_L), eq_type t t.
Proof.
induction t
; constructor
; assumption.
Qed.

Lemma eq_type_sym :
forall (t0 t1 : type_L), eq_type t0 t1 -> eq_type t1 t0.
Proof.
induction 1
; constructor
; subst
; assumption.
Qed.

Lemma eq_type_trans :
forall (t0 t1 t2 : type_L), eq_type t0 t1 -> eq_type t1 t2 -> eq_type t0 t2.
Proof.
induction t0
; intros
; inversion H
; subst.
* assumption.
* inversion H0.
  subst.
  constructor.
** apply (IHt0_1 u1)
   ; assumption.
** apply (IHt0_2 u2)
   ; assumption.
Qed.

Theorem typing_correct :
forall (c : context_L) (e : expr_L), option {t : type_L | check c e t}.
Proof.
induction e.
* refine (Some (exist _ T_bool _)).
  simpl.
  constructor.
* refine (Some (exist _ T_bool _)).
  simpl.
  constructor.
* 


Abort.

End E_lambdaChurch.