{-# LANGUAGE TypeSynonymInstances, FlexibleInstances #-}

module Continuation where

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
to_bool (VInt _) = error "Borked"
to_bool (VArr _) = error "Hosed"

to_int (VInt i) = i
to_int (VBool _) = error "Buggered"
to_Int (VArr _) = error "Lost at Sea"

to_func (VArr f)  = f
to_func (VInt _)  = error "Belly-up"
to_func (VBool _) = error "Kaput"

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

_ !! _ = undefined


-- Continuation Interpreter

-- CBN Defining Language & CBV Defined Language

-- Serious functions!?!?
--  dont terminate
--  but that's hard to compute
--  so we just say "we can't prove that they terminate"

-- Design Principle
-- If a function `g` calls a serious function `f`,
-- make sure that `g` terminates when `f` terminates
-- and that it returns the result of `f`.
-- g x = f x
-- g x = f (1 + x)
-- g x = (f x) + 1 ******

-- Note that `g` is also serious!

-- So as soon as any serious function returns a result, the whole
-- program returns a result.

-- We design our continuation interpreter to obey the following principle
{-
   f x1 ... xn    is a function and n arguments

   becomes f' defined below

   f' x1 ... xn c  ==  c (f x1 ... xn)
                   ==  f x1 ... xn  & c    evocative Haskell syntax!!
-}

{- Continuations are functions on values -}
type Cont = (Value -> Value)


apply :: FunVal -> Value -> Cont -> Value
{- Easy Cases, just apply the continuation to the result -}
apply Succ        arg cont = VInt (to_int arg + 1) & cont
apply Equal       arg cont = VArr (EqConst arg)    & cont
apply (EqConst v) arg cont = VBool (v == arg)      & cont

apply (Closure (Lambda var body) env) arg cont =
  {-- this case is similar to letrec,
      no "serious" ops --}
  let env' = Simp var arg env in -- env [var |--> arg]
  eval body env' cont



eval :: Exp -> Env -> Cont -> Value

{- The easy cases: just wrap the result in a continuation -}
eval (EConst c) _ cont = VInt c    & cont
eval (EVar v) env cont = env !! v  & cont
eval (ELambda f) env cont = (VArr $ Closure f env) & cont

eval (ELetRec l@(LetRec var assgn body)) env cont =
  {-- instead of applying [const $ eval ..], we pass cont to eval. --}
  {-- Why? the following line is "serious",
     but contains no "serious" operations --}
  let env' = Rec l env in
  eval body env' cont 

eval (EAppl (Appl fun arg)) env cont =
  {- interesting case -}
  {- "Serious" operations:
   -  1. evaluate fun to f (hopefully)
   -  2. evaluate arg to a (hopefully)
   -  3. apply f to a, i.e. `f a` 
   -  4. apply cont to `f a`
   -}

  eval fun env $ \(VArr f) -> -- 1
  eval arg env $ \a ->        -- 2
  apply f a cont              -- 3 & 4

  
eval (ECond (Cond test etrue efalse)) env cont =
  {- interesting case -}
  {- Evaluation Steps:
   - 1. Evaluate the Premise (premiss lol)
   - 2. Evaluate the true branch OR THE FALSE BRANCH
   - 3. apply cont to the result of 2
   -}
  eval test env $ \(VBool b) ->
  if b
  then eval etrue  env cont
  else eval efalse env cont


interp :: Exp ->  Value
interp exp = eval exp Init (\z -> z) -- start with empty continuation


-- TODO Examples
