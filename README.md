# λ Calculator

A λ-Calculus evaluator in Haskell

## Usage

Open Lambda.hs in a Haskell interpreter and run `evaluateTerm` on a λ-Calulus term

## Example Functions

```haskell
-- loops infinitely
omega = App (Abst "x" (App (Var "x") (Var "x"))) (Abst "x" (App (Var "x") (Var "x")))

-- adds one to a constant
addOne = App (Abst "x" (Func (\x y -> x + y) (Var "x") (Const 1))) -- Const (n)

-- chooses out of two constants
chooseOne = App (Abst "x" (IfThenElse (Var "x") (Const 1) (Const 2))) -- (LBool b)

-- factorial 
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
  )) -- (Const n)

-- checks if number is equal to 0
if_test = App ((Abst "n" (IfThenElse (BFunc (\n m -> n == m) (Const 0) (Var "n")) (Const 1) (Const 2))))

-- tests if fixed point combinator returns itself
comb_text = App y (Abst "f" (Const 1))

-- returns the greater of two numbers
greater = App (App (Abst "x" (Abst "y" 
  (IfThenElse
    (BFunc (\x y -> x > y) (Var "x") (Var "y"))
    (Var "x")
    (Var "y")
  ))) (Const 2)) (Const 4)


-- chooses first of two number
first_one = App (App (Abst "x" (Abst "y" (Var ("x")))) (Const 3)) (Const 4)


-- Special Fixed Point Combinator
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
```