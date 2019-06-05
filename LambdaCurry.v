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

Ltac split_andb H := apply andb_true_iff in H
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

Ltac eq_subst H := eq H ; subst.

Lemma context_var_dec :
forall (c : context_L) (v : var_L),
  {t : type_L | c v = Some t} + { c v = None}.
Proof.
intros.
destruct (c v).
* left.
  exists t.
  reflexivity.
* right.
  reflexivity.
Qed.

Theorem typing_correct :
forall (e : expr_L) (c : context_L), option {t : type_L | check c e t = true}.
Proof.
induction e
; intros.
* refine (Some (exist _ T_bool _)).
  constructor.
* refine (Some (exist _ T_bool _)).
  constructor.
* destruct (context_var_dec c v).
** destruct s.
   refine (Some (exist _ x _)).
   simpl.
   rewrite e.
   apply eq_type_eq.
   reflexivity.
** refine None.
* destruct (IHe c).
** destruct s.
   destruct (sumbool_of_bool (eq_type t x)).
*** refine (Some (exist _ t _)).
    simpl.
    eq_subst e1.
    rewrite e0.
    apply andb_true_iff.
    split
    ; try apply eq_type_eq
    ; reflexivity.
*** refine None.
** refine None.
* refine None.
(* ????? *)
* destruct (IHe2 c).
** destruct s.
   destruct (IHe1 c).
*** destruct s.
    destruct x0.
**** refine None.
**** destruct (sumbool_of_bool (eq_type x x0_1)).
***** eq_subst e3.
      refine (Some (exist _ x0_2 _)).
      simpl in *.
      (* ????? *)
***** refine None.
*** refine None.
** refine None.
* destruct (IHe1 c).
** destruct s.
   destruct x.
*** destruct (IHe2 c).
**** destruct s.
     destruct (IHe3 c).
***** destruct s.
      destruct (sumbool_of_bool (eq_type x x0)).
****** eq_subst e.
       refine (Some (exist _ x0 _)).
       constructor
       ; try assumption.
****** refine None.
***** refine None.
**** refine None.
*** refine None.
** refine None.
Qed.

End LambdaCurry.
