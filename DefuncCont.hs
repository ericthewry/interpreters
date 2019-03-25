{-# LANGUAGE TypeSynonymInstances, FlexibleInstances #-}

module DefuncCont where

import Prelude hiding ((!!))
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Function 


{- Type Aliases for Readability -}
type Var = String
type Const = Int

instance {-# OVERLAPPING #-} Show Var where
  show s = s

data Appl = Appl Exp Exp   -- Appl f x  is `f (x)`
  deriving Eq

instance Show Appl where
  show (Appl fun arg)  = show fun ++ "(" ++ show arg ++ ")"

data Lambda = Lambda Var Exp -- Lambda x e is `\x.e`
  deriving Eq

instance Show Lambda where
  show (Lambda param body) = "(\\" ++ param ++ " . " ++ show body ++ ")"

data Cond = Cond Exp Exp Exp  -- Cond b t f is `if b then t else f`
  deriving Eq

instance Show Cond where
  show (Cond test etrue efalse) =  "if " ++ show test ++ " then " ++ show etrue ++ " else " ++ show efalse

data LetRec = LetRec Var Lambda Exp  -- LetRec x f e is letrec x be f in e
  deriving Eq

instance Show LetRec where
  show (LetRec x f e) = "let rec " ++ x ++ " be " ++ show f ++ " in " ++ show e

data Exp =
  EConst Const
  | EVar Var
  | EAppl Appl
  | ELambda Lambda
  | ECond Cond
  | ELetRec LetRec
  deriving (Eq)

instance Show Exp where
  show (EConst c) = show c
  show (EVar v) = show v
  show (EAppl a) = show a
  show (ELambda l) = show l
  show (ECond c) = show c
  show (ELetRec r) = show r

letrec :: Var -> Var -> Exp -> Exp -> Exp
letrec x y f e = ELetRec $ LetRec x (Lambda y f) e

gets :: Var -> Exp -> Exp -> Exp
gets x f = letrec x "" f

app :: Exp -> Exp -> Exp
app f a = EAppl $ Appl f a

lambda :: Var -> Exp -> Exp
lambda x e = ELambda $ Lambda x e

cond :: Exp -> Exp -> Exp -> Exp
cond b t f = ECond $ Cond b t f

data FunVal =
  Closure Lambda Env
  | Succ
  | Equal
  | EqConst Value
  deriving (Eq,Show)

data Value =
  VBool Bool
  | VInt Int
  | VArr FunVal
  deriving Eq

to_bool (VBool b) = b
to_bool (VInt _) = error "Cannot convert Int to Bool"
to_bool (VArr _) = error "Cannot convert Function to Bool"

to_int (VInt i) = i
to_int (VBool _) = error "Cannot convert Int to Bool"
to_Int (VArr _) = error "Cannot convert Function to Bool"

to_func (VArr f)  = f
to_func (VInt _)  = error "Cannot convert Int to Function"
to_func (VBool _) = error "Cannot convert Bolean to Function"

instance Show Value where
  show (VBool b) = show b
  show (VInt i) = show i
  show (VArr f) = show f
  
data Env =
  Init                  -- \ () . {}
  | Simp Var Value Env  -- \x v e.   e [x -> v]
  | Rec LetRec Env      -- ?????
  deriving (Eq,Show)

(!!) :: Env -> Var -> Value
Init !! "succ" = VArr Succ
Init !! "equal" = VArr Equal
(Simp key val rest) !! query =
  if query == key
  then val
  else rest !! query
next@(Rec (LetRec var exp body) rest) !! query =
  if query == var
  then VArr $ Closure exp next
  else rest !! query

_ !! _ = error "Hopeless"


-- Defunctionalized Continuation Interpreter

{- Continuations are Linked Lists -}

data Cont =
  Fin             
  | Function Appl Env Cont   -- EvOpn
  | Argument Value Cont      -- ApFun
  | Branch Cond Env Cont     -- Branch
  deriving (Eq, Show)

continue :: Cont -> Value -> Value
continue Fin v = v
continue (Function (Appl _ arg) env cont) v =
  {- Invariant on `Function`:
     + v is a function,
     + arg is the argument
   -}
  eval arg env $   -- evaluate the argument
  Argument v cont  -- apply it to the function in the continuation
  
continue (Argument (VArr fun) cont) v =
  {- Invariant on `Argument`:
     + `v` is the argument to `fun`
   -}
  apply fun v cont

continue (Branch (Cond _ etrue efalse) env cont) v =
  {- Invariant on `Branch`
     + `v` is a boolean premise
     + if `v` evaluates to true, evaluate `etrue`
     + if `v` evaluates to false, evaluate `efalse`
   -}
  if to_bool v
  then eval etrue  env cont
  else eval efalse env cont


apply :: FunVal -> Value -> Cont -> Value
apply Succ        arg cont = VInt (to_int arg + 1) & continue cont
apply Equal       arg cont = (VArr $ EqConst arg)  & continue cont
apply (EqConst v) arg cont = (VBool(v == arg))     & continue cont

apply (Closure (Lambda var body) env) arg cont =
  let env' = Simp var arg env in
  eval body env' cont



eval :: Exp -> Env -> Cont -> Value

{- replace `cont` with `continue cont` -}
eval (EConst c) _ cont    = VInt c                 & continue cont
eval (EVar v) env cont    = env !! v               & continue cont
eval (ELambda f) env cont = (VArr $ Closure f env) & continue cont 

eval (ELetRec l@(LetRec var assgn body)) env cont =
  let env' = Rec l env in -- no change
    eval body env' cont

eval (EAppl a@(Appl fun arg)) env cont =
  eval fun env $      -- first evaluate fun,
  Function a env cont -- then apply the result to
                      -- the evaluation of a in env,
                      -- and continue with cont
  
eval (ECond cond@(Cond test etrue efalse)) env cont =
  eval test env $       -- first evaluate the test
  Branch cond env cont  -- then make a choice!

interp :: Exp -> Value
interp exp = eval exp Init Fin
  
-- TODO Examples
