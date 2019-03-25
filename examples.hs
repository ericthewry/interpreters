-- import Interp
-- import Defunc
-- import Continuation
import DefuncCont

--  Examples

esucc = EVar "succ"
eequal = EVar "equal"
czero = EConst 0
s = EVar "s"
z = EVar "z"
y = EVar "y"
x = EVar "x"

zero,zero', one, one' :: Exp
zero = lambda "s" $ lambda "z" $ z
zero' = zero `app` esucc `app` czero

one = lambda "s" $ lambda "z" $ app s z
one' = one `app` esucc `app` czero 

identity = lambda "x" x

dontimes =
  lambda "n" $
  lambda "exp" $
  lambda "base" $
  letrec "ntimes" "num_iters"
  (
    cond (eequal `app` EVar "num_iters" `app` EVar "n")
    (EVar "base")
    (app (EVar "exp") $ app (EVar "ntimes") $ esucc `app` EVar "num_iters")
  )
  (EVar "ntimes" `app` czero)

eplus =
  lambda "x" $
  lambda "y" $
  dontimes `app` x `app` esucc `app` y

eplus' n m = eplus `app` EConst n `app` EConst m

etimes =
  lambda "x" $
  lambda "y" $
  dontimes `app` x `app` (eplus `app` y) `app` EConst 0

etimes' n m = etimes `app` EConst n `app` EConst m

etriple = etimes `app` EConst 3
edouble = etimes `app` EConst 2

etrue = eequal `app` EConst 0 `app` EConst 0
efalse = eequal `app` EConst 1 `app` EConst 0

churchpred =
  let s f = lambda "g" $ lambda "h" $ EVar "h" `app` (EVar "g" `app` f) in
  let z x = lambda "" $ x in
  lambda "n" $ lambda "f"$ lambda "x" $
  (((EVar "n" `app` (s $ EVar "f")) `app` (z x)) `app` identity)

epred =
  lambda "n" $ churchpred `app` (dontimes `app` EVar "n") `app` esucc `app` czero

eIsZero = lambda "n" $ eequal `app` EVar "n" `app` EConst 0
eIsOne = lambda "n" $ eequal `app` EVar "n" `app` EConst 1

minustwo = lambda "n" $ epred `app` (epred `app` EVar "n")

eeven =
  letrec "even" "n"
  (cond (eIsZero `app` EVar "n") etrue
    (cond (eIsOne `app` EVar "n") efalse
     (
       eeven `app` (minustwo `app` EVar "n")
     )
    )
  ) {-in-} (EVar "even")


ehalf =
  lambda "n" $
  letrec "search" "i" {-be-}
  (cond
    {-if-}   (eequal `app` EVar "n" `app` (edouble `app` EVar "i"))
    {-then-} (EVar "i")
    {-else-} (EVar "search" `app` (esucc `app` EVar "i"))
  ) {-in-} (EVar "search" `app` EConst 0)

hotpo n = cond
          {-if-} (eeven `app` n)
          {-then-} (ehalf `app` n)
          {-else-} (esucc `app` (etriple `app` n))

collatz :: Exp
collatz = letrec "hotpo" {-be-}
          {- fun -} "y" {- ==> -} (cond (eequal `app` y `app` EConst 1) y  $
                                    EVar "hotpo" `app` hotpo y)
          {-in-}
          (EVar "hotpo")


omega = let omega' = lambda "x" $ app x x in
          app omega' omega'
  
cbn_inherit :: Exp
cbn_inherit = (lambda "x" $ lambda "y" $ y)
              `app` omega
              `app` EConst 47
