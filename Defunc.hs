{-# LANGUAGE TypeSynonymInstances, FlexibleInstances #-}

module Defunc where

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


data FunVal =
  Closure Lambda Env
  | Succ
  | Equal
  | EqConst Value
  deriving (Eq, Show)

data Value =
  VBool Bool
  | VInt Int
  | VArr FunVal
  deriving Eq

instance Show Value where
  show (VBool b) = show b
  show (VInt i) = show i
  show (VArr f) = show f
  
to_bool (VBool b) = b
to_bool (VInt _) = error "Borked"
to_bool (VArr _) = error "Hosed"

to_int (VInt i) = i
to_int (VBool _) = error "Buggered"
to_Int (VArr _) = error "Lost at Sea"

to_func (VArr f)  = f
to_func (VInt _)  = error "Belly-Up"
to_func (VBool _) = error "Kaput"


{- environments are association-lists -}
data Env =
  Init                  -- {}
  | Simp Var Value Env  -- \x v e.   e [x -> v]
  | Rec LetRec Env      -- ??? 
  deriving Eq

instance Show Env where
  show Init = "[]"
  show (Simp x v Init) ="[(" ++ x ++ "," ++ show v ++ ")]"
  show (Simp x v e) ="(" ++ x ++ "," ++ show v ++ ") :: " ++ show e
  show (Rec lr e) = "<+ " ++ show lr ++ " +> :: " ++ show e


(!!) :: Env -> Var -> Value
-- encode required functions into the environment
Init !! "succ" = VArr Succ       
Init !! "equal" = VArr Equal

(Simp key val rest) !! query =
  if query == key     -- if the query is the current key
  then val            -- get the associated value
  else rest !! query  -- o/w keep looking

next@(Rec (LetRec var exp _) rest) !! query =
  if query == var                 -- if the query current key
  then VArr $ Closure exp next    -- return the associated function
                                  -- Note that the env is the current one

  else rest !! query              -- o/w keep looking

_ !! _ = error "Hopeless"


-- Defunctionalized Interpreter

apply :: FunVal -> Value -> Value
apply Succ        arg = VInt (to_int arg + 1)
apply Equal       arg = VArr $ EqConst arg
apply (EqConst v) arg = VBool(v == arg)

apply (Closure (Lambda var body) env) arg =
  eval body $ Simp var arg env


eval :: Exp -> Env -> Value
eval (EConst c) _ = VInt c   -- constant
eval (EVar v) env = env !! v  -- lookup
eval (EAppl (Appl fun arg)) env =
  let VArr f = eval fun env in -- eval fun
  let a = eval arg env in      -- eval arg
  apply f a                    -- apply!
eval (ELambda f) env = VArr $
  Closure f env -- Wrap the lambda into a closure
eval (ECond (Cond test etrue efalse)) env =
  if to_bool $
       eval test env
  then eval etrue env
  else eval efalse env
eval (ELetRec l@(LetRec _ _ body)) env =
  let env' = Rec l env in -- extend env with l
  eval body env'          -- evaluate the body 


interp :: Exp -> Value
interp e = eval e Init

