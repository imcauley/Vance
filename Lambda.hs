-- import Control.Monad.State

data Lam a = App (Lam a) (Lam a)
           | Abst a (Lam a)
           | Var a
           | Const Int
           | Func (Int -> Int -> Int) (Lam a) (Lam a)
           | LBool Bool
           | BFunc (Int -> Int -> Bool) (Lam a) (Lam a)
           | IfThenElse (Lam a) (Lam a) (Lam a)



data DeBru a = DBApp (DeBru a) (DeBru a)
             | DBAbst (DeBru a)
             | DBVar a
             | DBRef Int
             | DBConst Int
             | DBFunc (Int -> Int -> Int) (DeBru a) (DeBru a)

data MacCode a = MacApp
             | Acc Int
             | Ret
             | Clo [(MacCode a)]
             | CloEnv [(MacCode a)] [(MacCode a)]
             | MacVar a
             | MacConst Int
             | MacFunc (Int -> Int -> Int)
            --  deriving (Show)


type ConvertState a = (Int)
type EvalState a = ([MacCode a], [MacCode a], [MacCode a])


--------------------------------------------------
-- Premade Functions
--------------------------------------------------

omega = App (Abst "x" (App (Var "x") (Var "x"))) (Abst "x" (App (Var "x") (Var "x")))


addOne = App (Abst "x" (Func (\x y -> x + y) (Var "x") (Const 1))) -- Const (n)

-- λf.(λa.f (λx.a a x)) (λa.f (λx.a a x))

y = (Abst "f" (App (Abst "a" (App (Var "f") (Abst "x" (App (App (Var "a") (Var "a")) (Var "x"))))) (Abst "a" (App (Var "f") (Abst "x" (App (App (Var "a") (Var "a")) (Var "x"))))) ))

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

lambdaToDeBru (Func f n m) s = (DBFunc f (lambdaToDeBru n s) (lambdaToDeBru m s))
lambdaToDeBru (Const c) s = (DBConst c)

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


--------------------------------------------------
-- Code Evaluation
--------------------------------------------------


evaluateTerm l = do
    let 
        deBru = lambdaToDeBru l []
        code  = (deBruToMacCode deBru)
        result = evaluateWithPrint (code, [], [])
    return result


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
        (Ret)   -> (cs, fst (upackReturn stack), snd (upackReturn stack))
        (MacFunc f) -> (applyFunction f cs env stack)

applyFunction f cs env ((MacConst n):(MacConst m):stack) = (cs, env, (MacConst (f n m)):stack)

upackReturn :: [(MacCode a)] -> ([MacCode a], [MacCode a])
upackReturn (v:(CloEnv e s):_) = (e,v:s)

unpackApplication :: EvalState a -> EvalState a
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

lambdaToString (Var a) = show a
lambdaToString (Abst a l) = "λ" ++ show a ++ "." ++ (lambdaToString l)
lambdaToString (App l1 l2) = "(" ++ (lambdaToString l1) ++ ")(" ++ (lambdaToString l1) ++ ")"