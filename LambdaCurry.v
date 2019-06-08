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

Inductive infer (c : context_L) : expr_L -> type_L -> Prop :=
| In_true : infer c E_true T_bool
| In_false : infer c E_false T_bool
| In_var v : forall t : type_L, c v = Some t -> infer c (E_var v) t
| In_type e t : check c e t -> infer c (E_type e t) t
| In_app e1 e2 : forall (t u : type_L), infer c e1 (T_func t u)
                   -> check c e2 t -> infer c (E_app e1 e2) u
| In_if b e1 e2 : forall t : type_L, check c b T_bool -> infer c e1 t
                    -> check c e2 t -> infer c (E_if b e1 e2) t
with check (c : context_L) : expr_L -> type_L -> Prop :=
| Ch_true : check c E_true T_bool
| Ch_false : check c E_false T_bool
| Ch_lambda v e : forall (t u : type_L),
                    check (add_ctx c v t) e u
                    -> check c (E_lambda v e) (T_func t u)
| Ch_if b e1 e2 : forall t : type_L, check c b T_bool -> check c e1 t
                    -> check c e2 t -> check c (E_if b e1 e2) t
| Ch_infer e t : infer c e t -> check c e t.

Fixpoint do_infer (c : context_L) (exp : expr_L) : option type_L :=
match exp with
| E_true => Some T_bool
| E_false => Some T_bool
| E_var v => c v
| E_type e t => if do_check c e t then Some t else None
| E_lambda v e => None
| E_app e1 e2 => match do_infer c e1 with
                 | Some (T_func t u) => if do_check c e2 t
                                        then Some u
                                        else None
                 | _ => None
                 end
| E_if b e1 e2 => if do_check c b T_bool
                  then match do_infer c e1 with
                       | Some t => if do_check c e2 t then Some t else None
                       | None => None
                       end
                  else None
end
with do_check (c : context_L) (exp : expr_L) (tp : type_L) : bool :=
match exp with
| E_true | E_false => match tp with
                      | T_bool => true
                      | _ => false
                      end
| E_var v => match c v with
             | Some t' => eq_type t' tp
             | None => false
             end
| E_type e t => eq_type t tp && do_check c e t
| E_lambda v e => match tp with
                  | T_func t u => do_check (add_ctx c v t) e u
                  | _ => false
                  end
| E_app e1 e2 => match do_infer c e1 with
                 | Some (T_func t' u') => eq_type u' tp && do_check c e2 t'
                 | _ => false
                 end
| E_if b e1 e2 => do_check c b T_bool && do_check c e1 tp && do_check c e2 tp
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

Lemma andb_true :
forall a b, andb a b = true <-> a = true /\ b = true.
Proof.
split.
* destruct a
  ; destruct b
  ; intros
  ; simpl in *
  ; try discriminate
  ; split
  ; assumption.
* intros.
  destruct H.
  rewrite H.
  rewrite H0.
  reflexivity.
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

Ltac split_andb H := apply andb_true in H
                     ; let g0 := fresh "G" in
                       let g1 := fresh "G" in
                       destruct H as [g0 g1].

Ltac rewrite_refl H := rewrite H ; reflexivity.

Ltac rewrite_refl_2 H1 H2 := rewrite H1 ; rewrite H2 ; reflexivity.

Ltac eq H := apply eq_type_eq in H ; subst.

Ltac eq_reflexivity H := eq H ; reflexivity.

Ltac eq_type_and_true := apply andb_true_iff
                         ; split
                         ; try apply eq_type_eq
                         ; reflexivity.

(* Equivalence proofs *)

Lemma do_infer_is_do_check :
forall (e : expr_L) (c : context_L) (t : type_L),
  do_infer c e = Some t -> do_check c e t = true.
Proof.
induction e
; intros.
* simpl in H.
  inversion H.
  reflexivity.
* simpl in H.
  inversion H.
  reflexivity.
* simpl in *.
  rewrite H.
  apply eq_type_eq.
  reflexivity.
* simpl in *.
  destruct (do_check c e t)
  ; try discriminate.
  inversion H.
  subst.
  eq_type_and_true.
* simpl in *.
  discriminate.
* simpl in *.
  destruct (do_infer c e1)
  ; try discriminate.
  destruct t0
  ; try discriminate.
  destruct (do_check c e2 t0_1)
  ; try discriminate.
  inversion H.
  subst.
  eq_type_and_true.
* simpl in *.
  destruct (do_check c e1 T_bool)
  ; try discriminate.
  simpl.
  remember (do_infer c e2) as I.
  destruct I
  ; try discriminate.
  symmetry in HeqI.
  apply IHe2 in HeqI.
  destruct (sumbool_of_bool (eq_type t0 t)).
** eq e.
   rewrite HeqI.
   simpl.
   destruct (do_check c e3 t)
   ; try discriminate
   ; reflexivity.
** apply not_true_iff_false in e.
   destruct (do_check c e3 t0)
   ; try discriminate.
   inversion H.
   eq H1.
   contradiction.
Qed.

Theorem check_is_do_check :
forall (e : expr_L) (c : context_L) (t : type_L),
  check c e t -> do_check c e t = true
with infer_is_do_infer :
forall (e : expr_L) (c : context_L) (t : type_L),
  infer c e t -> do_infer c e = Some t.
Proof.
* induction 1.
** simpl.
   reflexivity.
** simpl.
   reflexivity.
** simpl.
   apply IHcheck.
** simpl.
   apply andb_true.
   split
   ; try apply andb_true
   ; try split
   ; assumption.
** apply infer_is_do_infer in H.
   apply do_infer_is_do_check.
   assumption.
* induction 1.
** simpl.
   reflexivity.
** simpl.
   reflexivity.
** simpl.
   assumption.
** simpl.
   apply check_is_do_check in H.
   rewrite_refl H.
** simpl in *.
   rewrite IHinfer.
   apply check_is_do_check in H0.
   rewrite_refl H0.
** simpl.
   apply check_is_do_check in H.
   rewrite H.
   rewrite IHinfer.
   apply check_is_do_check in H1.
   rewrite_refl H1.
Qed.

(* Typing proof *)

Theorem make_typecheck :
forall (e : expr_L) (c : context_L) (t : type_L), option (check c e t)
with make_typeinfer :
forall (e : expr_L) (c : context_L), option {t : type_L | infer c e t}.
Proof.
* induction e
  ; intros.
** destruct t.
*** refine (Some _).
    constructor.
*** refine None.
** destruct t.
*** refine (Some _).
    constructor.
*** refine None.
** destruct (context_var_dec c v).
*** destruct s.
    destruct (sumbool_of_bool (eq_type t x)).
**** eq e0.
     refine (Some _).
     constructor.
     constructor.
     assumption.
**** refine None.
*** refine None.
** destruct (IHe c t0).
*** destruct (sumbool_of_bool (eq_type t t0)).
**** eq e0.
     refine (Some _).
     constructor.
     constructor.
     assumption.
**** refine None.
*** refine None.
** destruct t.
*** refine None.
*** destruct (IHe (add_ctx c v t1) t2).
**** refine (Some _).
     constructor.
     assumption.
**** refine None.
** destruct (make_typeinfer e1 c).
*** destruct s.
    destruct x.
**** refine None.
**** destruct (sumbool_of_bool (eq_type t x2)).
***** eq e.
      destruct (IHe2 c x1).
****** refine (Some _).
       constructor.
       apply In_app with (t:=x1)
       ; assumption.
****** refine None.
***** refine None.
*** refine None.
** destruct (IHe1 c T_bool).
*** destruct (IHe2 c t).
**** destruct (IHe3 c t).
***** refine (Some _).
      constructor
      ; assumption.
***** refine None.
**** refine None.
*** refine None.
* induction e
  ; intros.
** refine (Some (exist _ T_bool _)).
   constructor.
** refine (Some (exist _ T_bool _)).
   constructor.
** destruct (context_var_dec c v).
*** destruct s.
    refine (Some (exist _ x _)).
    constructor.
    assumption.
*** refine None.
** destruct (make_typecheck e c t).
*** refine (Some (exist _ t _)).
    constructor.
    assumption.
*** refine None.
** refine None.
** destruct (IHe1 c).
*** destruct s.
    destruct x.
**** refine None.
**** destruct (make_typecheck e2 c x1).
***** refine (Some (exist _ x2 _)).
      apply In_app with (t:=x1)
      ; assumption.
***** refine None.
*** refine None.
** destruct (make_typecheck e1 c T_bool).
*** destruct (IHe2 c).
**** destruct s.
     destruct (make_typecheck e3 c x).
***** refine (Some (exist _ x _)).
      constructor
      ; assumption.
***** refine None.
**** refine None.
*** refine None.
Qed.

End LambdaCurry.
