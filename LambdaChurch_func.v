Require Import List.
Import ListNotations.
Require Import String.
Open Scope string_scope.
Require Import Bool.
Require Import Sumbool.

Section E_lambdaChurch.

Definition var_L := string.

Inductive type_L : Type :=
| T_bool : type_L
| T_func : type_L -> type_L -> type_L.

Notation "'Bool'" := T_bool (at level 70).
Notation "t ~> u" := (T_func t u) (right associativity, at level 60).

Fixpoint eq_type (t u : type_L) : bool :=
match t, u with
| T_bool, T_bool => true
| T_func t1 t2, T_func u1 u2 => eq_type t1 u1 && eq_type t2 u2
| _, _ => false
end.

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

Fixpoint infer (c : context_L) (exp : expr_L) : option type_L :=
match exp with
| E_true => Some T_bool
| E_false => Some T_bool
| E_var v => c v
| E_type e t => if check c e t then Some t else None
| E_lambda v t e => match infer (add_ctx c v t) e with
                    | Some u => Some (T_func t u)
                    | None => None
                    end
| E_app e1 e2 => match infer c e1 with
                 | Some (T_func t u) => if check c e2 t then Some u else None
                 | _ => None
                 end
| E_if b e1 e2 => if check c b T_bool
                then match infer c e1 with
                     | Some t => if check c e2 t then Some t else None
                     | None => None
                     end
                else None
end
with check (c : context_L) (exp : expr_L) (tp : type_L) : bool :=
match exp with
| E_true | E_false => match tp with
                      | T_bool => true
                      | _ => false
                      end
| E_var v => match c v with
             | Some t' => eq_type t' tp
             | None => false
             end
| E_type e t => eq_type t tp && check c e t
| E_lambda v t e => match tp with
                    | T_func t' u' => eq_type t' t
                                      && check (add_ctx c v t) e u'
                    | _ => false
                    end
| E_app e1 e2 => match infer c e1 with
                 | Some (T_func t' u') => eq_type u' tp && check c e2 t'
                 | _ => false
                 end
| E_if b e1 e2 => check c b T_bool && check c e1 tp && check c e2 tp
end.

Lemma andb_true :
forall a b, andb a b = true -> a = true /\ b = true.
Proof.
destruct a
; destruct b
; intros
; simpl in *
; try discriminate
; split
; assumption.
Qed.

Ltac split_andb H := apply andb_true in H
                     ; let g0 := fresh "G" in
                       let g1 := fresh "G" in
                       destruct H as [g0 g1].

Ltac rewrite_refl H := rewrite H ; reflexivity.

Ltac rewrite_refl_2 H0 H1 := rewrite H0 ; rewrite H1 ; reflexivity.

Lemma eq_type_eq :
forall (t0 t1 : type_L), eq_type t0 t1 = true <-> t0 = t1.
Proof.
induction t0
; destruct t1
; split
; intros
; try reflexivity.
* inversion H.
* inversion H.
* inversion H.
* inversion H.
* inversion H.
  split_andb H1.
  destruct (IHt0_1 t1_1) as [IHt0_1L IHt0_1P].
  destruct (IHt0_2 t1_2) as [IHt0_2L IHt0_2P].
  rewrite_refl_2 (IHt0_1L G) (IHt0_2L G0).
* simpl.
  destruct (IHt0_1 t1_1) as [IHt0_1L IHt0_1P].
  destruct (IHt0_2 t1_2) as [IHt0_2L IHt0_2P].
  rewrite IHt0_1P
  ; try rewrite IHt0_2P
  ; inversion H
  ; reflexivity.
Qed.

Ltac eq H := apply eq_type_eq in H.

Lemma check_on_eq_type :
forall (e : expr_L) (t0 t1 : type_L) (c : context_L),
  t0 = t1 -> check c e t0 = true -> check c e t1 = true.
Proof.
induction e
; destruct t0
; destruct t1
; intros
; try discriminate
; try assumption.
* simpl in H0.
  simpl.
  destruct (c v).
** eq H0.
   apply (eq_trans H0) in H.
   eq H.
   assumption.
** assumption.
* simpl in H0.
  split_andb H0.
  simpl.
  eq G.
  apply (eq_trans G) in H.
  apply eq_type_eq in H.
  rewrite_refl_2 H G0.
* simpl.
  inversion H.
  simpl in H0.
  split_andb H0.
  eq G.
  symmetry in H2.
  apply (eq_trans H2) in G.
  eq G.
  rewrite H3 in G0.
  rewrite_refl_2 G G0.
* simpl in H0.
  simpl.
  destruct (infer c e1)
  ; try assumption.
  destruct t
  ; try assumption.
  split_andb H0.
  eq G.
  apply (eq_trans G) in H.
  eq H.
  rewrite_refl_2 H G0.
* simpl in H0.
  split_andb H0.
  split_andb G.
  simpl.
  specialize (IHe2 (T_func t0_1 t0_2) (T_func t1_1 t1_2) c H G2).
  specialize (IHe3 (T_func t0_1 t0_2) (T_func t1_1 t1_2) c H G0).
  rewrite G1.
  rewrite_refl_2 IHe2 IHe3.
Qed.

Lemma check_is_infer :
forall (e : expr_L) (c : context_L) (t : type_L),
  check c e t = true -> infer c e = Some t.
Proof.
induction e
; intros.
* destruct t
  ; simpl in *.
** reflexivity.
** discriminate.
* destruct t
  ; simpl in *.
** reflexivity.
** discriminate.
* simpl in *.
  destruct (c v)
  ; try discriminate.
  eq H.
  rewrite_refl H.
* inversion H.
  split_andb H1.
  simpl.
  rewrite G0.
  eq G.
  rewrite_refl G.
* simpl in H.
  destruct t0
  ; try discriminate.
  split_andb H.
  eq G.
  specialize (IHe (add_ctx c v t) t0_2 G0).
  simpl.
  rewrite_refl_2 IHe G.
* simpl in H.
  simpl.
  destruct (infer c e1)
  ; try destruct t0
  ; try discriminate.
  split_andb H.
  rewrite G0.
  eq G.
  rewrite_refl G.
* simpl in H.
  split_andb H.
  split_andb G.
  simpl.
  rewrite G1.
  rewrite_refl_2 (IHe2 c t G2) G0.
Qed.

Theorem typing_correct :
forall (e : expr_L) (c : context_L), option {t : type_L | check c e t = true}.
Proof.
induction e
; intros.
* refine (Some (exist _ T_bool _)).
  simpl.
  reflexivity.
* refine (Some (exist _ T_bool _)).
  simpl.
  reflexivity.
* simpl.
  destruct (c v).
** refine (Some (exist _ t _)).
   apply eq_type_eq.
   reflexivity.
** refine None.
* destruct (IHe c).
** destruct s.
   destruct (sumbool_of_bool (eq_type t x)).
*** refine (Some (exist _ x _)).
    simpl.
    rewrite e1.
    simpl.
    apply (check_on_eq_type e x t).
**** eq e1.
     symmetry.
     assumption.
**** assumption.
*** refine None.
** refine None.
* specialize (IHe (add_ctx c v t)).
  destruct IHe.
** destruct s.
   refine (Some (exist _ (T_func t x) _)).
   simpl.
   rewrite e0.
   rewrite andb_true_r.
   apply eq_type_eq.
   reflexivity.
** refine None.
* specialize (IHe1 c).
  specialize (IHe2 c).

Abort.

End E_lambdaChurch.