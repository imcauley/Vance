import Control.Monad.State

data Lam a = App (Lam a) (Lam a)
           | Abst a (Lam a)
           | Var a 

data DeBru a = DBApp (DeBru a) (DeBru a)
             | DBAbst (DeBru a)
             | DBVar a
             | DBRef Int
             deriving (Show)

data MacCode a = MacApp
             | Acc Int
             | Ret
             | Clo [(MacCode a)]
             | MacVar a
             deriving (Show)

type CState a = (Lam a, [Int], [MacCode a])

deBruToMacCode :: DeBru a -> [MacCode a]
deBruToMacCode (DBVar v) = [(MacVar v)]
deBruToMacCode (DBRef n) = [(Acc n)]
deBruToMacCode (DBApp t1 t2) = (deBruToMacCode t1) ++ (deBruToMacCode t2) ++ [(MacApp)]
deBruToMacCode (DBAbst f) = [(Clo ((deBruToMacCode f) ++ [Ret]))]

lambdaToString (Var a) = show a
lambdaToString (Abst a l) = "λ" ++ show a ++ "." ++ (lambdaToString l)
lambdaToString (App l1 l2) = "(" ++ (lambdaToString l1) ++ ")(" ++ (lambdaToString l1) ++ ")"

test1 = App (Abst "x" (App (Var "x") (Var "x")))(Abst "x" (App (Var "x") (Var "x")))

-- [Clo([Access(1), Access(1), App, Ret]), Clo([Access(1), Access(1), App, Ret]), App]