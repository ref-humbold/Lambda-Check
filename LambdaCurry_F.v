Require Import List.
Import ListNotations.
Require Import String.
Open Scope string_scope.
Require Import Bool.
Require Import Sumbool.

Section LambdaCurry.

(* Syntax *)

Definition var_L := string.

Inductive type_L : Type :=
| T_bool : type_L
| T_func : type_L -> type_L -> type_L.

Notation "'Bool'" := T_bool (at level 70).
Notation "t ~> u" := (T_func t u) (right associativity, at level 60).

Inductive expr_L : Type :=
| E_true : expr_L
| E_false : expr_L
| E_var : var_L -> expr_L
| E_type : expr_L -> type_L -> expr_L
| E_lambda : var_L -> expr_L -> expr_L
| E_app : expr_L -> expr_L -> expr_L
| E_if : expr_L -> expr_L -> expr_L -> expr_L.

Notation "'TRUE'" := E_true (at level 50).
Notation "'FALSE'" := E_false (at level 50).
Notation "% v" := (E_var v) (at level 50).
Notation "p $ q" := (E_app p q) (left associativity, at level 40).
Notation "\ x 'IS' e" := (E_lambda x e) (at level 30).
Notation "'WHEN' b 'THEN' p 'ELSE' q" := (E_if b p q) (at level 20).
Notation "e 'OF' t" := (E_type e t) (at level 10).

(* Context *)

Definition context_L := var_L -> option type_L.

Fixpoint add_ctx (ctx : context_L) (v : var_L) (t : type_L) : context_L := 
fun v' => if string_dec v v' then Some t else ctx v'.

(* Typing rules *)

Fixpoint eq_type (t u : type_L) : bool :=
match t, u with
| T_bool, T_bool => true
| T_func t1 t2, T_func u1 u2 => eq_type t1 u1 && eq_type t2 u2
| _, _ => false
end.

Fixpoint infer (c : context_L) (exp : expr_L) : option type_L :=
match exp with
| E_true => Some T_bool
| E_false => Some T_bool
| E_var v => c v
| E_type e t => if check c e t then Some t else None
| E_lambda v e => None
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
| E_lambda v e => match tp with
                  | T_func t u => check (add_ctx c v t) e u
                  | _ => false
                  end
| E_app e1 e2 => match infer c e1 with
                 | Some (T_func t' u') => eq_type u' tp && check c e2 t'
                 | _ => false
                 end
| E_if b e1 e2 => check c b T_bool && check c e1 tp && check c e2 tp
end.

(* Lemmas *)

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
  apply eq_type_and_true_iff in H1.
  destruct H1 as [G G0].
  destruct (IHt0_1 t1_1) as [IHt0_1L IHt0_1P].
  destruct (IHt0_2 t1_2) as [IHt0_2L IHt0_2P].
  rewrite (IHt0_1L G).
  rewrite (IHt0_2L G0).
  reflexivity.
* simpl.
  destruct (IHt0_1 t1_1) as [IHt0_1L IHt0_1P].
  destruct (IHt0_2 t1_2) as [IHt0_2L IHt0_2P].
  rewrite IHt0_1P
  ; try rewrite IHt0_2P
  ; inversion H
  ; reflexivity.
Qed.

Ltac eq H := apply eq_type_eq in H ; subst.

Ltac eq_type_and_true := apply andb_true_iff
                         ; split
                         ; try apply eq_type_eq
                         ; reflexivity.

Lemma context_var_dec :
forall (c : context_L) (v : var_L),
  {t : type_L | c v = Some t} + {c v = None}.
Proof.
intros.
destruct (c v).
* left.
  exists t.
  reflexivity.
* right.
  reflexivity.
Qed.

Theorem make_typecheck :
forall (e : expr_L) (c : context_L) (t : type_L), option (check c e t = true)
with make_typeinfer :
forall (e : expr_L) (c : context_L), option {t : type_L | infer c e = Some t}.
Proof.
* induction e
  ; intros.
** destruct t.
*** refine (Some _).
    reflexivity.
*** refine None.
** destruct t.
*** refine (Some _).
    reflexivity.
*** refine None.
** destruct (context_var_dec c v).
*** destruct s.
    destruct (sumbool_of_bool (eq_type t x)).
**** eq e0.
     refine (Some _).
     simpl.
     rewrite e.
     apply eq_type_eq.
     reflexivity.
**** refine None.
*** refine None.
** destruct (IHe c t0).
*** destruct (sumbool_of_bool (eq_type t t0)).
**** eq e1.
     refine (Some _).
     simpl.
     rewrite e0.
     eq_type_and_true.
**** refine None.
*** refine None.
** destruct t.
*** refine None.
*** destruct (IHe (add_ctx c v t1) t2).
**** refine (Some _).
     simpl.
     assumption.
**** refine None.
** destruct (make_typeinfer e1 c).
*** destruct s.
    destruct x.
**** refine None.
**** destruct (sumbool_of_bool (eq_type t x2)).
***** eq e0.
      destruct (IHe2 c x1).
****** refine (Some _).
       simpl.
       rewrite e.
       rewrite e0.
       eq_type_and_true.
****** refine None.
***** refine None.
*** refine None.
** destruct (IHe1 c T_bool).
*** destruct (IHe2 c t).
**** destruct (IHe3 c t).
***** refine (Some _).
      simpl.
      apply andb_true_iff.
      split
      ; try assumption.
      apply andb_true_iff.
      split
      ; assumption.
***** refine None.
**** refine None.
*** refine None.
* induction e
  ; intros.
** refine (Some (exist _ T_bool _)).
   reflexivity.
** refine (Some (exist _ T_bool _)).
   reflexivity.
** destruct (context_var_dec c v).
*** destruct s.
    refine (Some (exist _ x _)).
    simpl.
    assumption.
*** refine None.
** destruct (make_typecheck e c t).
*** refine (Some (exist _ t _)).
    simpl.
    rewrite e0.
    reflexivity.
*** refine None.
** refine None.
** destruct (IHe1 c).
*** destruct s.
    destruct x.
**** refine None.
**** destruct (make_typecheck e2 c x1).
***** refine (Some (exist _ x2 _)).
      simpl.
      rewrite e.
      rewrite e0.
      reflexivity.
***** refine None.
*** refine None.
** destruct (make_typecheck e1 c T_bool).
*** destruct (IHe2 c).
**** destruct s.
     destruct (make_typecheck e3 c x).
***** refine (Some (exist _ x _)).
      simpl.
      rewrite e.
      rewrite e0.
      rewrite e4.
      reflexivity.
***** refine None.
**** refine None.
*** refine None.
Qed.

End LambdaCurry.
