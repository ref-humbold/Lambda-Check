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
| E_if b e1 e2 => check c b T_bool && check c e1 tp && check c e2 tp
| E_type e t => eq_type t tp && check c e t
| E_lambda v t e => match tp with
                  | T_func t' u' => eq_type t' t
                                    && (match infer (add_ctx c v t) e with
                                        | Some u'' => eq_type u'' u'
                                        | _ => false
                                        end)
                  | _ => false
                  end
| E_app e1 e2 => match infer c e1 with
               | Some (T_func t' u') => eq_type u' tp && check c e2 t'
               | _ => false
               end
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

Ltac rewrite_refl H0 H1 := rewrite H0 ; rewrite H1 ; reflexivity.

Lemma eq_type_refl :
forall (t : type_L), eq_type t t = true.
Proof.
induction t
; simpl.
* reflexivity.
* rewrite_refl IHt1 IHt2.
Qed.

Lemma eq_type_sym :
forall (t0 t1 : type_L), eq_type t0 t1 = true -> eq_type t1 t0 = true.
Proof.
induction t0
; destruct t1
; simpl
; intros
; try assumption.
specialize (IHt0_1 t1_1).
specialize (IHt0_2 t1_2).
split_andb H.
apply IHt0_1 in G.
apply IHt0_2 in G0.
rewrite_refl G G0.
Qed.

Lemma eq_type_trans :
forall (t0 t1 t2 : type_L), eq_type t0 t1 = true -> eq_type t1 t2 = true
  -> eq_type t0 t2 = true.
Proof.
induction t0
; destruct t1
; destruct t2
; intros
; try assumption
; inversion H.
inversion H0.
split_andb H2.
split_andb H3.
specialize (IHt0_1 t1_1 t2_1 G G1).
specialize (IHt0_2 t1_2 t2_2 G0 G2).
simpl.
rewrite IHt0_1.
rewrite IHt0_2.
rewrite_refl G G0.
Qed.

Lemma check_on_eq_type :
forall (t0 t1 : type_L) (c : context_L) (e : expr_L),
  eq_type t0 t1 = true -> check c e t0 = true -> check c e t1 = true.
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
** apply eq_type_trans with (t1:=T_func t0_1 t0_2)
   ; assumption.
** assumption.
* simpl in H0.
  split_andb H0.
  apply (eq_type_trans t (T_func t0_1 t0_2) (T_func t1_1 t1_2)) in G
  ; try assumption.
  simpl.
  rewrite_refl G G0.
* simpl in H0.
  simpl.
  destruct (infer (add_ctx c v t) e).
** simpl in H.
   split_andb H.
   split_andb H0.
   apply eq_type_sym in G.
   apply (eq_type_trans t1_1 t0_1 t) in G
   ; try assumption.
   apply (eq_type_trans t0 t0_2 t1_2) in G2
   ; try assumption.
   rewrite_refl G G2.
** rewrite andb_false_r in H0.
   discriminate.
* simpl in H0.
  simpl.
  destruct (infer c e1)
  ; try assumption.
  destruct t
  ; try assumption.
  split_andb H0.
  apply (eq_type_trans t2 (T_func t0_1 t0_2) (T_func t1_1 t1_2)) in G
  ; try assumption.
  rewrite_refl G G0.
* simpl in H0.
  split_andb H0.
  split_andb G.
  simpl.
  specialize (IHe2 H G2).
  specialize (IHe3 H G0).
  rewrite G1.
  rewrite_refl IHe2 IHe3.
Qed.

Theorem typing_correct :
forall (c : context_L) (e : expr_L), option {t : type_L | check c e t = true}.
Proof.

Abort.

End E_lambdaChurch.