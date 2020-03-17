import Control.Monad.State

data Lam a = App (Lam a) (Lam a)
           | Abst a (Lam a)
           | Var a
           | LNum Int
           | LNumFunc (Int -> Int -> Int)

data DeBru a = DBApp (DeBru a) (DeBru a)
             | DBAbst (DeBru a)
             | DBVar a
             | DBRef Int
             deriving (Show)

data MacCode a = MacApp
             | Acc Int
             | Ret
             | Clo [(MacCode a)]
             | CloEnv [(MacCode a)] [(MacCode a)]
             | MacVar a
             deriving (Show)


type ConvertState a = (Int)
type EvalState a = ([MacCode a], [MacCode a], [MacCode a])


--------------------------------------------------
-- Premade Functions
--------------------------------------------------

omega = App (Abst "x" (App (Var "x") (Var "x"))) (Abst "x" (App (Var "x") (Var "x")))

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


--------------------------------------------------
-- Code Evaluation
--------------------------------------------------


evaluateTerm l = do
    let 
        deBru = lambdaToDeBru l []
        code  = (deBruToMacCode deBru)
        result = evaluate code
    return result


evaluate :: [MacCode a] -> (MacCode a)
evaluate c = evaluate' (c, [], [])

evaluate' :: EvalState a -> (MacCode a)
evaluate' start
    | length c' == 0  = (head stack)
    | otherwise = (evaluate' (c',env,stack))
    where (c',env,stack) = (codeStep start)

codeStep :: EvalState a -> EvalState a
codeStep (c:cs, env, stack) = 
    case c of
        (MacVar v) -> (cs, env, [(MacVar v)]++stack)
        (MacApp)   -> unpackApplication (cs, env, stack)
        (Clo c) -> (cs, env, [(CloEnv c env)] ++ stack)
        (Acc n) -> (cs, env, [(env !! n)] ++ stack)
        (Ret)   -> (cs, fst (upackReturn stack), snd (upackReturn stack))

upackReturn :: [(MacCode a)] -> ([MacCode a], [MacCode a])
upackReturn (v:(CloEnv e s):_) = (e,v:s)

unpackApplication :: EvalState a -> EvalState a
unpackApplication (cs, env, ((CloEnv cs' env'):v:rest)) = (cs', (v:env'), (CloEnv cs env):rest)


lambdaToString (Var a) = show a
lambdaToString (Abst a l) = "λ" ++ show a ++ "." ++ (lambdaToString l)
lambdaToString (App l1 l2) = "(" ++ (lambdaToString l1) ++ ")(" ++ (lambdaToString l1) ++ ")"