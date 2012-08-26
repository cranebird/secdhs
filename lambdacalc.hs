----------------------------------------------------------------
-- lambdacalc.hs - Lambda Calculation
-- Copyright (C) 2012 by @quasicrane (Twitter)
-- my blog: http://d.hatena.ne.jp/cranebird/
-- See "Lecture Notes on the Lambda Calculus", Peter Selinger
----------------------------------------------------------------
module Main where
import System.Environment
import qualified Data.Set as S
import Test.QuickCheck

-- Utility
fixpoint :: Eq a => (a -> a) -> a -> a
fixpoint f x0 = head [ x | (x, y) <- zip xs (tail xs), x == y ]
    where xs = iterate f x0

type Variable = String
-- Lambda Term
data Term = Var Variable
          | App Term Term -- Application
          | Lambda Variable Term -- Abstraction
            deriving (Eq)
-- show Lambda Term
showTerm :: Term -> String
showTerm (Var x) = x
showTerm (App m n) = "(" ++ showTerm m ++ " " ++ showTerm n ++ ")"
showTerm (Lambda x m) = "(^" ++ x ++ "." ++ showTerm m ++ ")"
-- show Lambda Term like lisp
showTerm' :: Term -> String
showTerm' (Var x) = x
showTerm' (App m n) = "(" ++ showTerm' m ++ " " ++ showTerm' n ++ ")"
showTerm' (Lambda x m) = "(lambda (" ++ x ++ ") " ++ showTerm' m ++ ")"

instance Show Term where
    show = showTerm


-- lambda-terms example
-- a) (^x.(xy)) == Lambda "x" (App (Var "x") (Var "y")) == (lambda (x) (x y))
-- b) ((^y.y)(^x.(xy))) == App (Lambda "y" (Var "y")) (Lambda "x" (App (Var "x") (Var "y")))
--                      == ((lambda (y) y) (lambda (x) (x y)))
-- c) (x (^x. (^x.x))) == App (Var "x") (Lambda "x" (Lambda "x" (Var "x")))
-- d) (^x.(yz)) = Lambda "x" (App (Var "y") (Var "z"))

-- Definition 1.6: length of a term
lgh :: Term -> Int
lgh (Var a) = 1
lgh (App m n) = lgh m + lgh n
lgh (Lambda x m) = 1 + lgh m
-- m = App (Var 'x') (Lambda 'y' (App (Var 'y') (App (Var 'u') (Var 'x'))))
-- lgh m = 5

-- Def 1.7 occur
occur :: Term -> Term -> Bool

occur p p' | p == p' = True
occur p (App m n) = occur p m || occur p n
occur p (Lambda x m) = occur p m || p == Var x
occur _ _ = False
-- m = App (App (Var 'x') (Var 'y')) (Lambda 'x' (App (Var 'x') (Var 'y')))

-- Def 1.9 scope
scope :: Term -> Term
scope (Lambda x m) = m

-- Def 1.11 Free and bound variables

-- Free variables
fv :: Term -> S.Set Variable
fv (Var x) = S.singleton x
fv (App m n) = fv m `S.union` fv n
fv (Lambda x m) = S.delete x (fv m)

-- closed term
closed :: Term -> Bool
closed p = S.null (fv p)

-- Example
-- (((xv)(^y.(^z.(yv))))w)
-- App (App (App (Var "x") (Var "v")) (Lambda "y" (Lambda "z" (App (Var "y") (Var "v"))) )) (Var "w")

rename :: Variable -> Variable -> Term -> Term
-- rename new old term -> new-term (like #'subst in Common Lisp)
rename x y (Var z) | x == z = Var y
rename x y (Var z) | x /= z = Var z
rename x y (App m n) = App (rename x y m) (rename x y n)
rename x y (Lambda z m) | x == z = Lambda y (rename x y m)
rename x y (Lambda z m) | x /= z = Lambda z (rename x y m)

-- capture-avoiding substitution
-- x[N/x] == N
-- y[N/x] == y if x /= y
-- (M P) [N/x] == (M[N/x])(P[N/x])
-- (^x.M)[N/x] = ^x.M
-- (^y.M)[N/x] = ^y.(M[N/x]) if x/= y and y notMember FV(N)
-- (^y.M)[N/x] = ^y'.(M{y'/y}[N/x]) if x/= y and y member FV(N), and y' fresh

genvars = map (: []) ['a'..'z'] ++ map (: [] ++ "'") ['a'..'z'] ++ map (\n -> 'x' : show n) [0..]

extractVars :: Term -> S.Set Variable
extractVars (Var x) = S.singleton x
extractVars (App m p) = extractVars m `S.union` extractVars p
extractVars (Lambda x m) = S.singleton x `S.union` extractVars m

freshVar :: [Term] -> Variable
freshVar xs = fn xs S.empty
    where
      fn (y:ys) s = fn ys (s `S.union` extractVars y)
      fn [] s = head $ dropWhile (`S.member` s) genvars

-- subst new old term -> new-term
subst :: Term -> Variable -> Term -> Term
subst n x (Var x') | x == x' = n
subst n x (Var x') | x /= x' = Var x'
subst n x (App m p) = App (subst n x m) (subst n x p)
subst n x (Lambda x' m) | x == x' = Lambda x' m
subst n x (Lambda y m) | x /= y && S.notMember y (fv n)
                           = Lambda y (subst n x m)
subst n x (Lambda y m) | x /= y && S.member y (fv n)
                           = Lambda y' (subst n x (rename y' y m))
                             where
                               y' = freshVar [m, n]

-- [w/x](^y.x)
-- subst (Var "w") "x" (Lambda "y" (Var "x"))
-- => (^y.w)

-- [w/x](^w.x)
-- subst (Var "w") "x" (Lambda "w" (Var "x"))
-- => (^z.w)

-- Exercise 1.14
-- [(uv)/x] (^y.x(^w.vwx))
-- subst (App (Var "u") (Var "v")) "x" (Lambda "y" (App (Var "x") (Lambda "w" (App (Var "v") (App (Var "w") (Var "x"))))))

-- isBetaRedex :: Term -> Bool
-- isBetaRedex (App (Lambda x m) n) = True
-- isBetaRedex _ = False

-- Beta Reduction
beta :: Term -> Term
beta (App (Lambda x m) n) = subst n x m
beta (App m n) | beta m /= m = App (beta m) n
beta (App m n) | beta n /= n = App m (beta n)
beta (App m n) | beta m == m && beta n == n = App m n
beta (Lambda x m) | beta m /= m = Lambda x (beta m)
beta (Lambda x m) | beta m == m = Lambda x m
beta (Var x) = Var x

betaStar :: Term -> Term
betaStar m = fixpoint beta m

i = Lambda "x" (Var "x")
s = Lambda "x" (Lambda "y" (Lambda "z" (App (App (Var "x") (Var "z")) (App (Var "y") (Var "z")))))
k = Lambda "x" (Lambda "y" (Var "x"))
w = Lambda "x" (App (Var "x") (Var "x"))
omega = App w w
-- Y = ^f.(^x.f (x x))(^x.f (x x))
y = Lambda "f" (App (Lambda "x" (App (Var "f") (App (Var "x") (Var "x"))))
                    (Lambda "x" (App (Var "f") (App (Var "x") (Var "x")))))
theta = App (Lambda "x" (Lambda "f" (App (Var "f") (App (App (Var "x") (Var "x")) (Var "f")))))
        (Lambda "x" (Lambda "f" (App (Var "f") (App (App (Var "x") (Var "x")) (Var "f")))))

t = Lambda "x" (Lambda "y" (Var "x"))
f = Lambda "x" (Lambda "y" (Var "y"))

                          