
module LamEval where

---------------------------------------------------------------------
----------------------- Datatype Definition -------------------------
---------------------------------------------------------------------

type Bndr 
  = Int

data Expr 
  = Lam Bndr Expr
  | Var Bndr  
  | App Expr Expr
  | Const Int
  | Plus Expr Expr
 
data Value 
  = Basic   Int
  | Closure Env Expr
  
data Env k v 
  = Emp
  | Bind k v (Env k v) 

{-@ measure isValue      :: Expr -> Prop
    isValue (Const i)    = true 
    isValue (Lam x e)    = true 
    isValue (Var x)      = false
    isValue (App e1 e2)  = false
    isValue (Plus e1 e2) = false 
@-}

{-@ type VExpr = {v: Expr | (isValue v)}       @-}

{-@ data Value = Basic Int | Closure Env VExpr @-}

{-@ type VEnv  = Env Bndr Value                @-} 

---------------------------------------------------------------------
-------------------------- The Evaluator ----------------------------
---------------------------------------------------------------------

{-@ evalVar :: Bndr -> VEnv -> VExpr @-}

evalVar x (Bind y v env) 
  | x == y
  = v
  | otherwise
  = evalVar x env 

evalVar x Emp       
  = error "unbound variable"


{-@ eval :: VEnv -> Expr -> Value @-}

eval env (Const i) 
  = Basic i

eval env (Var x)  
  = evalVar x env 

eval env (Plus e1 e2)
  = case (eval env e1, eval env e2) of
      (Basic i1, Basic i2) -> Basic (i1 + i2)
      _                    -> error "type error: non-integer addition"

eval env (Lam x e) 
  = Closure env (Lam x e)

eval env (App e1 e2)
  = case (eval env e1, eval env e2) of
      (Closure env1 (Lam x1 e1'), v2) -> eval (Bind x1 v2 env) e1'
      _                               -> error "type error: non-function application"


