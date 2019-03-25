import Prelude hiding ((!!))
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Function

{- Type Aliases for Readability -}
type Var = String 
type Const = Int

data Appl = Appl Exp Exp
  deriving Eq

instance Show Appl where
  show (Appl fun arg)  = show fun ++ "   (" ++ show arg ++ " )"

data Lambda = Lambda Var Exp
  deriving Eq

instance Show Lambda where
  show (Lambda param body) = "(\\ " ++ param ++ ". " ++ show body ++ ")"

data Cond = Cond Exp Exp Exp
  deriving Eq

instance Show Cond where
  show (Cond test etrue efalse) =  "if " ++ show test ++ " then " ++ show etrue ++ " else " ++ show efalse

data LetRec = LetRec Var Lambda Exp
  deriving Eq

instance Show LetRec where
  show (LetRec x f e) = "let rec " ++ x ++ " be " ++ show f ++ " in " ++ show e


{- ADDING ESCAPE EXPRESSIONS -}
data Escape = Escape Var Exp
  deriving Eq

instance Show Escape where
  show (Escape x e) = "escape " ++ x ++ " in " ++ show e

data Exp =
  EConst Const
  | EVar Var
  | EAppl Appl
  | ELambda Lambda
  | ECond Cond
  | ELetRec LetRec
  | EEscape Escape
  deriving (Eq)

letrec :: Var -> Var -> Exp -> Exp -> Exp
letrec x y f e = ELetRec $ LetRec x (Lambda y f) e

gets :: Var -> Exp -> Exp -> Exp
gets x f = letrec x "" f


escape :: Var -> Exp -> Exp
escape x e = EEscape $ Escape x e

app :: Exp -> Exp -> Exp
app f a = EAppl $ Appl f a

lambda :: Var -> Exp -> Exp
lambda x e = ELambda $ Lambda x e

cond :: Exp -> Exp -> Exp -> Exp
cond b t f = ECond $ Cond b t f


instance Show Exp where
  show (EConst c) = show c
  show (EVar v) = show v
  show (EAppl a) = show a
  show (ELambda l) = show l
  show (ECond c) = show c
  show (ELetRec r) = show r
  show (EEscape e) = show e

data FunVal =
  Closure Lambda Env
  | Succ
  | Equal
  | EqConst Value
  | EscFun Cont        {-- Escape is a function! -}
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
to_func (VInt _)  = error "Belly-Up"
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

e !! v = "Hopeless: " ++ show e ++ " !! " ++ show v    & error


-- Defunctionalized Continuation Interpreter With Imperative Functionality

data Cont =
  Fin             
  | Function Appl Env Cont   -- EvOpn
  | Argument Value Cont      -- ApFun
  | Branch Cond Env Cont     -- Branch
  deriving (Eq, Show)

continue :: Cont -> Value -> Value
continue Fin v = v
continue (Function (Appl _ arg) env cont) v =
  eval arg env $   
  Argument v cont  
  
continue (Argument (VArr fun) cont) v =
  apply fun v cont

continue (Branch (Cond _ etrue efalse) env cont) v =
  if to_bool v
  then eval etrue  env cont
  else eval efalse env cont

continue c v = "I can't go on: " ++ show c ++ show v    & error

apply :: FunVal -> Value -> Cont -> Value
apply Succ        arg cont = VInt (to_int arg + 1) & continue cont
apply Equal       arg cont = (VArr $ EqConst arg)  & continue cont
apply (EqConst v) arg cont = VBool(v == arg)       & continue cont

apply (Closure (Lambda var body) env) arg cont =
  eval body (Simp var arg env) cont

apply (EscFun cont) arg _ = continue cont arg
  {- throw away the running continuation, and
     interpret arg in the stored continuation -}


eval :: Exp -> Env -> Cont -> Value
eval (EConst c) _ cont    = VInt c                 & continue cont
eval (EVar v) env cont    = env !! v               & continue cont
eval (ELambda f) env cont = (VArr $ Closure f env) & continue cont

eval (ELetRec l@(LetRec var assgn body)) env cont =
  let env' = Rec l env in
    eval body env' cont

eval (EAppl a@(Appl fun arg)) env cont =
  eval fun env $      
  Function a env cont
  
eval (ECond cond@(Cond test etrue efalse)) env cont =
  eval test env $
  Branch cond env cont


eval (EEscape (Escape var body)) env cont =
  {- Extend [env] with var -> cont -}
  let env' = Simp var (VArr $ EscFun cont) env in
  eval body env' cont

interp :: Exp -> Value
interp exp = eval exp Init Fin
  
-- TODO Examples


{-
     let x be const 47 in
     let borked be const 42 in
     escape esc in
     borked $ esc $ x 0
 -}

borked = EVar "borked"
esc = EVar "esc"
x = EVar "x"

example :: Exp
example =
  "x" `gets` EConst 47 $
  "borked" `gets` EConst 42 $
  escape "esc" {- in -} $
  app borked $
  app esc $
  x `app` EConst 0


