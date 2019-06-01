Require Import List.
Import ListNotations.
Require Import String.
Open Scope string_scope.

Section LambdaChurch.

Definition L_var := string.

Inductive L_type : Type :=
| Bool_T : L_type
| Func_T : L_type -> L_type -> L_type.

Notation "'Bool'" := Bool_T (at level 70).
Notation "t ~> u" := (Func_T t u) (right associativity, at level 60).

Fixpoint eq_type (t u : L_type) : bool :=
match t, u with
| Bool_T, Bool_T => true
| Func_T t1 t2, Func_T u1 u2 => eq_type t1 u1 && eq_type t2 u2
| _, _ => false
end.

Inductive L_expr : Type :=
| Btrue : L_expr
| Bfalse : L_expr
| Var : L_var -> L_expr
| Typing : L_expr -> L_type -> L_expr
| Lambda : L_var -> L_type -> L_expr -> L_expr
| App : L_expr -> L_expr -> L_expr
| If : L_expr -> L_expr -> L_expr -> L_expr.

Notation "'T'" := Btrue (at level 50).
Notation "'F'" := Bfalse (at level 50).
Notation "% v" := (Var v) (at level 50).
Notation "p $ q" := (App p q) (left associativity, at level 40).
Notation "\ x 'of' t , e" := (Lambda x t e) (at level 30).
Notation "'when' b 'do' p 'or' q" := (If b p q) (at level 20).
Notation "e 'at' t" := (Typing e t) (at level 10).

Definition L_context := list (prod L_var L_type).

Fixpoint add (ctx : L_context) (v : L_var) (t : L_type) : L_context := 
match ctx with
| [] => [(v, t)]
| (v', t') :: xs => if string_dec v v'
                    then (v, t) :: xs
                    else (v', t') :: add xs v t
end.

Fixpoint get (ctx : L_context) (v : L_var) : option L_type := 
match ctx with
| [] => None
| (v', t') :: xs => if string_dec v' v then Some t' else get xs v
end.

Fixpoint infer (c : L_context) (exp : L_expr) : option L_type :=
match exp with
| Btrue => Some Bool_T
| Bfalse => Some Bool_T
| Var v => get c v
| Typing e t => if check c e t then Some t else None
| Lambda v t e => match infer (add c v t) e with
                  | Some u => Some (Func_T t u)
                  | None => None
                  end
| App e1 e2 => match infer c e1 with
               | Some (Func_T t u) => if check c e2 t then Some u else None
               | _ => None
               end
| If b e1 e2 => if check c b Bool_T
                then match infer c e1 with
                     | Some t => if check c e2 t then Some t else None
                     | None => None
                     end
                else None
end
with check (c : L_context) (exp : L_expr) (tp : L_type) : bool :=
match exp with
| Btrue | Bfalse => match tp with
                    | Bool_T => true
                    | _ => false
                    end
| Var v => match get c v with
           | Some t' => eq_type t' tp
           | None => false
           end
| If b e1 e2 => check c b Bool_T && check c e1 tp && check c e2 tp
| Typing e tp => check c e tp
| Lambda v t e => match tp with
                  | Func_T t' u' => eq_type t' t
                                    && (match infer (add c v t) e with
                                        | Some u'' => eq_type u'' u'
                                        | _ => false
                                        end)
                  | _ => false
                  end
| App e1 e2 => match infer c e1 with
               | Some (Func_T t' u') => eq_type u' tp && check c e2 t'
               | _ => false
               end
end.

End LambdaChurch.