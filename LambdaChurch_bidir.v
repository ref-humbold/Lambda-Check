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

Fixpoint do_infer (c : context_L) (exp : expr_L) : option type_L :=
match exp with
| E_true => Some T_bool
| E_false => Some T_bool
| E_var v => c v
| E_lambda v t e => match do_infer (add_ctx c v t) e with
                    | Some u => Some (T_func t u)
                    | None => None
                    end
| E_app e1 e2 => match do_infer c e1 with
                 | Some (T_func t u) => if do_check c e2 t then Some u else None
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
| E_lambda v t e => match tp with
                    | T_func t' u' => eq_type t' t
                                      && do_check (add_ctx c v t) e u'
                    | _ => false
                    end
| E_app e1 e2 => match do_infer c e1 with
                 | Some (T_func t' u') => eq_type u' tp && do_check c e2 t'
                 | _ => false
                 end
| E_if b e1 e2 => do_check c b T_bool && do_check c e1 tp && do_check c e2 tp
end.

(* Lemmas *)

Ltac rewrite_refl H := rewrite H ; reflexivity.

Ltac rewrite_refl_2 H1 H2 := rewrite H1 ; rewrite H2 ; reflexivity.

Lemma eq_type_eq :
forall (t0 t1 : type_L), eq_type t0 t1 = true <-> t0 = t1.
Proof.
induction t0 ; destruct t1 ; split ; intros ; try reflexivity
; try solve [inversion H].
* inversion H.
  apply andb_true_iff in H1.
  destruct H1 as [G G0].
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

Lemma andb_true :
forall a b, andb a b = true <-> a = true /\ b = true.
Proof.
split.
* destruct a ; destruct b ; intros ; simpl in * ; try discriminate ; split
  ; assumption.
* intros.
  destruct H.
  rewrite_refl_2 H H0.
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

Ltac eq H := apply eq_type_eq in H ; subst.

Ltac eq_reflexivity H := eq H ; reflexivity.

Ltac eq_type_and_true := apply andb_true_iff
                         ; split
                         ; try apply eq_type_eq
                         ; reflexivity.

(* Equivalence proofs *)

Lemma do_check_is_do_infer :
forall (e : expr_L) (c : context_L) (t : type_L),
  do_check c e t = true -> do_infer c e = Some t.
Proof.
induction e ; intros.
* destruct t ; simpl in * ; [reflexivity | discriminate].
* destruct t ; simpl in * ; [reflexivity | discriminate].
* simpl in *.
  destruct (c v) ; [eq_reflexivity H | discriminate].
* simpl in H.
  destruct t0 ; try discriminate.
  split_andb H.
  eq G.
  specialize (IHe (add_ctx c v t) t0_2 G0).
  simpl.
  rewrite_refl IHe.
* simpl in *.
  destruct (do_infer c e1) ; try destruct t0 ; try discriminate.
  split_andb H.
  rewrite G0.
  eq_reflexivity G.
* simpl in H.
  split_andb H.
  split_andb G.
  simpl.
  rewrite G1.
  rewrite_refl_2 (IHe2 c t G2) G0.
Qed.

Lemma do_infer_is_do_check :
forall (e : expr_L) (c : context_L) (t : type_L),
  do_infer c e = Some t -> do_check c e t = true.
Proof.
induction e ; intros ; simpl in *.
* inversion H.
  reflexivity.
* inversion H.
  reflexivity.
* rewrite H.
  apply eq_type_eq.
  reflexivity.
* remember (do_infer (add_ctx c v t) e) as I.
  destruct I ; try discriminate.
  destruct t0 ; try inversion H.
  subst.
  symmetry in HeqI.
  apply IHe in HeqI.
  rewrite HeqI.
  eq_type_and_true.
* destruct (do_infer c e1) ; try discriminate.
  destruct t0 ; try discriminate.
  destruct (do_check c e2 t0_1) ; try discriminate.
  inversion H.
  subst.
  eq_type_and_true.
* destruct (do_check c e1 T_bool) ; try discriminate.
  simpl.
  remember (do_infer c e2) as I.
  destruct I ; try discriminate.
  symmetry in HeqI.
  apply IHe2 in HeqI.
  destruct (sumbool_of_bool (eq_type t0 t)).
** eq e.
   rewrite HeqI.
   simpl.
   destruct (do_check c e3 t) ; [reflexivity | discriminate].
** apply not_true_iff_false in e.
   destruct (do_check c e3 t0) ; try discriminate.
   inversion H.
   eq H1.
   contradiction.
Qed.

Lemma typing_is_do_infer :
forall (e : expr_L) (c : context_L) (t : type_L),
  typing c e t -> do_infer c e = Some t.
Proof.
induction 1 ; intros ; simpl.
* reflexivity.
* reflexivity.
* assumption.
* rewrite_refl IHtyping.
* rewrite IHtyping1.
  apply do_infer_is_do_check in IHtyping2.
  rewrite_refl IHtyping2.
* apply do_infer_is_do_check in IHtyping1.
  rewrite IHtyping1.
  rewrite IHtyping2.
  apply do_infer_is_do_check in IHtyping3.
  rewrite_refl IHtyping3.
Qed.

Lemma do_infer_is_typing :
forall (e : expr_L) (c : context_L) (t : type_L),
  do_infer c e = Some t -> typing c e t.
Proof.
induction e ; intros ; simpl in H.
* inversion H.
  subst.
  constructor.
* inversion H.
  subst.
  constructor.
* constructor.
  assumption.
* remember (do_infer (add_ctx c v t) e) as I.
  destruct I ; try discriminate.
  inversion H.
  subst.
  constructor.
  apply IHe.
  symmetry.
  assumption.
* remember (do_infer c e1) as I1.
  destruct I1 ; try destruct t0 ; try discriminate.
  remember (do_check c e2 t0_1) as I2.
  destruct I2 ; try discriminate.
  inversion H.
  subst.
  apply Type_app with (t:=t0_1)
  ; [apply IHe1 | apply IHe2 ; apply do_check_is_do_infer] ; symmetry
  ; assumption.
* simpl in H.
  remember (do_check c e1 T_bool) as I1.
  remember (do_infer c e2) as I2.
  destruct I1 ; try destruct t0 ; try destruct I2 ; try discriminate.
  remember (do_check c e3 t0) as I3.
  destruct I3 ; try discriminate.
  inversion H.
  subst.
  constructor ; [apply IHe1 ; apply do_check_is_do_infer
                | apply IHe2
                | apply IHe3 ; apply do_check_is_do_infer]
  ; symmetry ; assumption.
Qed.

(* Typing proof *)

Theorem make_typecheck_1 :
forall (e : expr_L) (c : context_L), option {t : type_L | typing c e t}.
Proof.
induction e ; intros.
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
      apply Type_app with (t:=x0_1) ; assumption.
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
       constructor ; assumption.
****** refine None.
***** refine None.
**** refine None.
*** refine None.
** refine None.
Qed.

Theorem make_typecheck_2 :
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
    | E_app e1 e2 => match tp e1 ct, tp e2 ct with
                     | Some d1, Some d2 => _
                     | _, _ => None
                     end
    | E_if b e1 e2 => match tp b ct, tp e1 ct, tp e2 ct with
                      | Some (exist _ tb db), Some d1, Some d2 => _
                      | _, _, _ => None
                      end
    end).
* constructor.
* constructor.
* constructor.
  assumption.
* constructor.
  assumption.
* destruct d1.
  destruct x.
** refine None.
** destruct d2.
   destruct (sumbool_of_bool (eq_type x x1)).
*** apply eq_type_eq in e.
    subst.
    refine (Some (exist _ x2 _)).
    apply Type_app with (t:=x1) ; assumption.
*** refine None.
* destruct tb.
** destruct d1.
   destruct d2.
   destruct (sumbool_of_bool (eq_type x x0)).
*** apply eq_type_eq in e.
    subst.
    refine (Some (exist _ x0 _)).
    constructor ; assumption.
*** refine None.
** refine None.
Qed.

End LambdaChurch.