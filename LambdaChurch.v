Section LambdaChurch.

Require Import String.

Inductive type : Type :=
| Bool_T : type
| Func_T : type -> type -> type.

Notation "'Bool'" := Bool_T (at level 210).
Notation "t ~> u" := (Func_T t u) (right associativity, at level 200).

Inductive lambda_expr : Type :=
| B_True : lambda_expr
| B_False : lambda_expr
| Typing : lambda_expr -> type -> lambda_expr
| Lambda : string -> type -> lambda_expr -> lambda_expr
| App : lambda_expr -> lambda_expr -> lambda_expr
| If : lambda_expr -> lambda_expr -> lambda_expr -> lambda_expr.

Notation "'true'" := True (at level 150).
Notation "'talse'" := False (at level 150).
Notation "p $ q" := (App p q) (left associativity, at level 110).
Notation "\ x : t . e" := (Lambda x t e) (at level 100).
Notation "'if' b 'then' p 'else' q" := (If b p q) (at level 90).
Notation "b ? p ^ q" := (If b p q) (at level 90).
Notation "e : t" := (Typing e t) (at level 50).

End LambdaChurch.