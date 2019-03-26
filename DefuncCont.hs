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

data Cont = -- abstract machine
  Fin             
  | Function Appl Env Cont   -- EvOpn
  | Argument Value Cont      -- ApFun
  | Branch Cond Env Cont     -- Branch
  deriving (Eq, Show)

continu :: Cont -> Value -> Value
continu Fin v = v
continu (Function (Appl _ arg) env cont) v =
  {- Invariant on `Function`:
     + v the evaluation of f
     + arg is the argument
   -}
  eval arg env $   -- evaluate the argument
  Argument v cont  -- apply it to the function in the continuation
  
continu (Argument (VArr vfun) cont) v =
  {- Invariant on `Argument`:
     + `v` is the argument to `vfun`
   -}
  apply vfun v cont

continu (Branch (Cond _ etrue efalse) env cont) (VBool b) =
  {- Invariant on `Branch`
     + `b` is a boolean premise
   -}
  if b
  then eval etrue  env cont
  else eval efalse env cont


apply :: FunVal -> Value -> Cont -> Value
apply Succ        arg ation = VInt (to_int arg + 1) & continu ation
apply Equal       arg ation = (VArr $ EqConst arg)  & continu ation
apply (EqConst v) arg ation = (VBool(v == arg))     & continu ation

apply (Closure (Lambda var body) env) arg cont =
  let env' = Simp var arg env in
  eval body env' cont



eval :: Exp -> Env -> Cont -> Value
{- replace `cont` with `continu ation` -}
eval (EConst c) _ ation    = VInt c                 & continu ation
eval (EVar v) env ation    = env !! v               & continu ation
eval (ELambda f) env ation = (VArr $ Closure f env) & continu ation 

eval (ELetRec l@(LetRec _ _ body)) env cont =
  let env' = Rec l env in -- no change & NOTHING SERIOUS
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
