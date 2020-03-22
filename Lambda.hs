-- import Control.Monad.State

data Lam a = App (Lam a) (Lam a)
           | Abst a (Lam a)
           | Var a

            --Extended For Integers
           | Const Int
           | Func (Int -> Int -> Int) (Lam a) (Lam a)

           | LBool Bool
           | BFunc (Int -> Int -> Bool) (Lam a) (Lam a)
           | IfThenElse (Lam a) (Lam a) (Lam a)

data DeBru a = DBApp (DeBru a) (DeBru a)
             | DBAbst (DeBru a)
             | DBVar a
             | DBRef Int

             --Extended For Integers
             | DBConst Int
             | DBFunc (Int -> Int -> Int) (DeBru a) (DeBru a)

             -- Extended for Bools
             | DBBool Bool
             | DBBFunc (Int -> Int -> Bool) (DeBru a) (DeBru a)
             | DBIf (DeBru a) (DeBru a) (DeBru a)

data MacCode a = MacApp
             | Acc Int
             | Ret
             | Clo [(MacCode a)]
             | CloEnv [(MacCode a)] [(MacCode a)]
             | MacVar a

             | MacConst Int
             | MacFunc (Int -> Int -> Int)

             | MBool Bool
             | MBFunc (Int -> Int -> Bool)
             | MacIf [(MacCode a)] [(MacCode a)]


type ConvertState a = (Int)
type EvalState a = ([MacCode a], [MacCode a], [MacCode a])


--------------------------------------------------
-- Premade Functions
--------------------------------------------------

omega = App (Abst "x" (App (Var "x") (Var "x"))) (Abst "x" (App (Var "x") (Var "x")))


addOne = App (Abst "x" (Func (\x y -> x + y) (Var "x") (Const 1))) -- Const (n)
chooseOne = App (Abst "x" (IfThenElse (Var "x") (Const 1) (Const 2))) (LBool False)


fact = App (App y 
  (Abst "f" 
    (Abst "i" 
      (IfThenElse 
        (BFunc (\n m -> n == m) (Const 0) (Var "i")) 
        (Const 1) 
        (Func (\n m -> n * m)
          (Var "i")
          (App 
            (Var "f")
            (Func (\n m -> n - m)
              (Var "i")
              (Const 1)
            )
            )
        )
      )
    )
  ))


if_test = App ((Abst "n" (IfThenElse (BFunc (\n m -> n == m) (Const 0) (Var "n")) (Const 1) (Const 2))))
comb_text = App y (Abst "f" (Const 1))

greater = App (App (Abst "x" (Abst "y" 
  (IfThenElse
    (BFunc (\x y -> x > y) (Var "x") (Var "y"))
    (Var "x")
    (Var "y")
  ))) (Const 2)) (Const 4)

first_one = App (App (Abst "x" (Abst "y" (Var ("x")))) (Const 3)) (Const 4)

first_one_d = DBApp (DBApp (DBAbst (DBAbst (DBRef 1))) (DBConst 3)) (DBConst 4)

-- λf.(λa.f (λx.a a x)) (λa.f (λx.a a x))

y = (Abst "f" 
  (App (Abst "a" 
    (App (Var "f") 
      (Abst "x" (App (App (Var "a") (Var "a")) (Var "x")))
    )) 
  (Abst "a" 
    (App (Var "f") 
      (Abst "x" (App (App (Var "a") (Var "a")) (Var "x"))))
   )
  ))

--------------------------------------------------
-- Lambda to de Buijn Conversion
--------------------------------------------------

lambdaToDeBru :: Eq a => (Lam a) -> [a] -> (DeBru a)
lambdaToDeBru (App l1 l2) s = (DBApp (lambdaToDeBru l1 s) (lambdaToDeBru l2 s))
lambdaToDeBru (Abst v l) s = (DBAbst (lambdaToDeBru l ([v] ++ s)))
lambdaToDeBru (Var x) s
    | isBound = (DBRef (findIndex x s))
    | otherwise = (DBVar x)
    where isBound = (any ((==) x) s)

lambdaToDeBru (Func f n m) s    = (DBFunc f (lambdaToDeBru n s) (lambdaToDeBru m s))
lambdaToDeBru (Const c) s       = (DBConst c)

lambdaToDeBru (LBool b) s         = (DBBool b)
lambdaToDeBru (BFunc f n m) s     = (DBBFunc f (lambdaToDeBru n s) (lambdaToDeBru m s))
lambdaToDeBru (IfThenElse i n m) s = (DBIf (lambdaToDeBru i s) (lambdaToDeBru n s) (lambdaToDeBru m s))



findIndex :: Eq a => a -> [a] -> Int
findIndex x (s:ss)
    | x == s = 0
    | otherwise = 1 + (findIndex x ss)


--------------------------------------------------
-- de Buijn to Machine Code Conversion
--------------------------------------------------

deBruToMacCode :: (DeBru a) -> [(MacCode a)]
deBruToMacCode (DBVar v) = [(MacVar v)]
deBruToMacCode (DBRef n) = [(Acc n)]
deBruToMacCode (DBApp t1 t2) = (deBruToMacCode t2) ++ (deBruToMacCode t1) ++ [(MacApp)]
deBruToMacCode (DBAbst f) = [(Clo ((deBruToMacCode f) ++ [Ret]))]

deBruToMacCode (DBFunc f n m) =  (deBruToMacCode m) ++ (deBruToMacCode n) ++ [(MacFunc f)]
deBruToMacCode (DBConst c) = [(MacConst c)]

deBruToMacCode (DBBool b) = [(MBool b)]
deBruToMacCode (DBBFunc f n m) = (deBruToMacCode m) ++ (deBruToMacCode n) ++ [(MBFunc f)]
deBruToMacCode (DBIf i n m) = (deBruToMacCode i) ++ [MacIf ((deBruToMacCode n) ++ [Ret]) ((deBruToMacCode m) ++ [Ret])]


--------------------------------------------------
-- Code Evaluation
--------------------------------------------------


evaluateTerm l = do
    let 
        deBru = lambdaToDeBru l []
        code  = (deBruToMacCode deBru)
        result = evaluate' (code, [], [])
    return (macCodeToString result)


evaluate :: [MacCode a] -> (MacCode a)
evaluate c = evaluate' (c, [], [])

evaluate' :: EvalState a -> (MacCode a)
evaluate' start
    | length c' == 0  = (head stack)
    | otherwise = (evaluate' (c',env,stack))
    where (c',env,stack) = (codeStep start)

-- evaluate :: EvalState a -> (MacCode a)
evaluateWithPrint start
    | length c' == 0  = macCodeToString (head stack)
    | otherwise = macStackString c' ++ "\n" ++ (evaluateWithPrint (c',env,stack))
    where (c',env,stack) = (codeStep start)



codeStep :: EvalState a -> EvalState a
codeStep (c:cs, env, stack) = 
    case c of
        (MacVar v) -> (cs, env, [(MacVar v)]++stack)
        (MacConst c) -> (cs, env, [(MacConst c)]++stack)
        (MacApp)   -> unpackApplication (cs, env, stack)
        (Clo c) -> (cs, env, [(CloEnv c env)] ++ stack)
        (Acc n) -> (cs, env, [(env !! n)] ++ stack)
        (Ret)   -> (applyReturn cs env stack)
        (MacFunc f) -> (applyFunction f cs env stack)
        (MBFunc f) -> (applyBoolFunc f cs env stack)
        (MBool b) -> (cs, env, [MBool b] ++ stack)
        (MacIf c1 c2) -> (applyIf c1 c2 cs env stack)

-- Helper functions for codeStep

applyFunction f cs env ((MacConst n):(MacConst m):stack) = (cs, env, (MacConst (f n m)):stack)

applyBoolFunc f cs env ((MacConst n):(MacConst m):stack) = (cs, env, (MBool (f n m)):stack)

applyIf c1 c2 cs env ((MBool True):stack)  = (c1, env, [CloEnv cs env] ++ stack)
applyIf c1 c2 cs env ((MBool False):stack) = (c2, env, [CloEnv cs env] ++ stack)

applyReturn cs env (v:(CloEnv cs' env'):stack) = (cs', env', v:stack)

unpackApplication (cs, env, ((CloEnv cs' env'):v:rest)) = (cs', (v:env'), (CloEnv cs env):rest)

macCodeToString :: Show a => MacCode a -> String
macCodeToString (MacApp)     = "[App]"
macCodeToString (Ret)        = "[Return]"
macCodeToString (Acc n)      = "[Access " ++ show n ++ " ]"
macCodeToString (MacVar v)   = "[Var " ++ show v ++ " ]"
macCodeToString (MacConst c) = "[Const " ++ show c ++ " ]"
macCodeToString (CloEnv e s) = "[Closure E: " ++ concat (map macCodeToString e) ++ concat (map macCodeToString s) ++ " ]"
macCodeToString (Clo s)      = "[Closure S: " ++ concat (map macCodeToString s) ++ " ]"
macCodeToString (MacFunc f)  = "[Func]"

macStackString s = concat (map macCodeToString s)


printDeBru d = putStrLn (printDeBru' d)

printDeBru' (DBRef n) = "a" ++ (show n)
printDeBru' (DBVar v) = show v
printDeBru' (DBAbst e) = "λ." ++ (printDeBru' e)
printDeBru' (DBApp e1 e2) = "(" ++ (printDeBru' e1) ++ ")(" ++ (printDeBru' e2) ++ ")"
printDeBru' (DBConst c) = show c
printDeBru' (DBFunc f n m) = "func(" ++ (printDeBru' n) ++ ", " ++ (printDeBru' m) ++ ")"
printDeBru' (DBBFunc f n m) = "func(" ++ (printDeBru' n) ++ ", " ++ (printDeBru' m) ++ ")"
printDeBru' (DBBool b) = show b
printDeBru' (DBIf e1 e2 e3) = "if (" ++ (printDeBru' e1) ++ ") then (" ++ (printDeBru' e2) ++ ") else (" ++ (printDeBru' e3) ++ ")"