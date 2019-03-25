{-# LANGUAGE TypeSynonymInstances, FlexibleInstances #-}

module Interp where

import Prelude hiding ((!!))
import Data.Map (Map)
import qualified Data.Map as Map


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
  deriving Eq

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



data Value =
  VBool Bool
  | VInt Int
  | VArr (Value -> Value)
  -- deriving Show

instance Show Value where
  show (VBool b) = show b
  show (VInt i) = show i
  show (VArr f) = error "Let it be Unwritten"

instance Eq Value where
  VBool b == VBool b' = b == b
  VInt i == VInt i' = i == i'
  VArr _ == VArr _ = error "Function Equality?? Preposterous"
  v == v' = error $ "INcomparable types: " ++ show v ++ " and " ++ show v'

to_bool :: Value -> Bool
to_bool (VBool b) = b
to_bool (VInt _) = error "Borked"
to_bool (VArr _) = error "Hosed"

 
type Env = (Var -> Value)
(!!) :: Env -> Var -> Value
(!!) e v = e v

-- Meta Circular Interpreter

eval :: Exp -> Env -> Value
{- constants are constant! -}
eval (EConst c) env = VInt c
{- lookup variables in the Environment -}
eval (EVar v) env = env !! v

eval (EAppl (Appl fun arg)) env =
  {- evaluate the function -}
  let VArr f = eval fun env in -- pattern matching trick gives error if not VArr
  {- evaluate the argument -}
  let a = eval arg env in  
  f a -- apply
  
eval (ELambda f) env =
  VArr $ evlambda f env -- evaluate the lambda! [BELOW]
  
eval (ECond (Cond test etrue efalse)) env =
    if to_bool $           
         eval test   env   -- evaluate the condition
    then eval etrue  env   -- if true evaluate the true branch
    else eval efalse env   -- if false evaluate the false branch
         
eval (ELetRec (LetRec var {-be-} assgn {-in-} body)) env =
  -- evaluate the body in the newly-constructed environment
  eval body $ recExtend env var assgn

  
evlambda :: Lambda -> Env -> Value -> Value
evlambda (Lambda param body) env arg =
  let env' = extend param arg env in
    eval body env'
  
recExtend :: Env -> Var -> Lambda -> Env
recExtend env key vlam =
  let selfEnv = recExtend env key vlam in        
    \query -> 
      if query == key then
        -- looking up var returns the function
        -- that returns `vlam` evaluated in the context
        -- of itself
        VArr $ evlambda vlam selfEnv
      else
        -- looking up any other [Var] queries the old environment [env']
        env !! query

extend :: Var -> Value -> Env -> Var -> Value
extend key val env query | query == key = val
                         | otherwise = env !! query

initEnv :: Env
initEnv "succ"   = VArr (\(VInt x) -> VInt $ succ x )
initEnv "equal"  = VArr (\ x -> VArr ( \ y -> VBool ( x == y)))
initEnv _ = error "Wasted"

interp :: Exp -> Value
interp e = eval e initEnv


