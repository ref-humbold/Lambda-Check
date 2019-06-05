Require Import List.
Import ListNotations.
Require Import String.
Open Scope string_scope.
Require Import Bool.
Require Import Sumbool.

Section LambdaChurch.

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
| E_lambda : var_L -> type_L -> expr_L -> expr_L
| E_app : expr_L -> expr_L -> expr_L
| E_if : expr_L -> expr_L -> expr_L -> expr_L.

Notation "'TRUE'" := E_true (at level 50).
Notation "'FALSE'" := E_false (at level 50).
Notation "% v" := (E_var v) (at level 50).
Notation "p $ q" := (E_app p q) (left associativity, at level 40).
Notation "\ x 'AT' t 'IS' e" := (E_lambda x t e) (at level 30).
Notation "'WHEN' b 'THEN' p 'ELSE' q" := (E_if b p q) (at level 20).

(* Context *)

Definition context_L := var_L -> option type_L.

Fixpoint add_ctx (ctx : context_L) (v : var_L) (t : type_L) : context_L := 
fun v' => if string_dec v v' then Some t else ctx v'.

(* Typing rules *)

Inductive typing (c : context_L) : expr_L -> type_L -> Prop :=
| Type_true : typing c E_true T_bool
| Type_false : typing c E_false T_bool
| Type_var v : forall t : type_L, c v = Some t -> typing c (E_var v) t
| Type_lambda v t e : forall u : type_L, typing (add_ctx c v t) e u
                        -> typing c (E_lambda v t e) (T_func t u)
| Type_app e1 e2 : forall (t u : type_L), typing c e1 (T_func t u)
                     -> typing c e2 t -> typing c (E_app e1 e2) u
| Type_if b e1 e2 : forall (t : type_L), typing c b T_bool -> typing c e1 t
                      -> typing c e2 t -> typing c (E_if b e1 e2) t.

Fixpoint eq_type (t u : type_L) : bool :=
match t, u with
| T_bool, T_bool => true
| T_func t1 t2, T_func u1 u2 => eq_type t1 u1 && eq_type t2 u2
| _, _ => false
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
  apply andb_true_iff in H1.
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

Theorem typing_correct_1 :
forall (e : expr_L) (c : context_L), option {t : type_L | typing c e t}.
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
   constructor.
   assumption.
** refine None.
* destruct (IHe (add_ctx c v t)).
** destruct s.
   refine (Some (exist _ (T_func t x) _)).
   constructor.
   assumption.
** refine None.
* destruct (IHe2 c).
** destruct s.
   destruct (IHe1 c).
*** destruct s.
    destruct x0.
**** refine None.
**** destruct (sumbool_of_bool (eq_type x x0_1)).
***** apply eq_type_eq in e.
      subst.
      refine (Some (exist _ x0_2 _)).
      apply Type_app with (t:=x0_1)
      ; assumption.
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
****** apply eq_type_eq in e.
       subst.
       refine (Some (exist _ x0 _)).
       constructor
       ; try assumption.
****** refine None.
***** refine None.
**** refine None.
*** refine None.
** refine None.
Qed.

Theorem typing_correct_2 :
forall (e : expr_L) (c : context_L), option {t : type_L | typing c e t}.
Proof.
refine (
  fix tp (ex : expr_L) (ct : context_L) :=
    match ex with
    | E_true => Some (exist _ T_bool _)
    | E_false => Some (exist _ T_bool _)
    | E_var v => match context_var_dec ct v with
                 | inleft (exist _ t d) => Some (exist _ t _)
                 | inright _ => None
                 end
    | E_lambda v t e0 => match tp e0 (add_ctx ct v t) with
                         | Some (exist _ u d) =>
                           Some (exist _ (T_func t u) _)
                         | None => None
                         end
    | E_app e1 e2 => match tp e1 ct with
                     | Some (exist _ (T_func t1 u1) d1) =>
                       match tp e2 ct with
                       | Some (exist _ t2 d2) =>
                         if eq_type t1 t2 then Some (exist _ u1 _) else None
                       | _ => None
                       end
                     | _ => None
                     end
    | E_if b e1 e2 => match tp b ct with
                      | Some (exist _ T_bool db) =>
                        match tp e1 ct with
                        | Some (exist _ t1 d1) =>
                          match tp e2 ct with
                          | Some (exist _ t2 d2) =>
                            if eq_type t1 t2 then Some (exist _ t1 _) else None
                          | None => None
                          end
                        | None => None
                        end
                      | _ => None
                      end
    end).
Abort.

End LambdaChurch.