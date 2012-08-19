----------------------------------------------------------------
-- lambdacalc.hs - Lambda Calculation
-- Copyright (C) 2012 by @quasicrane (Twitter)
-- my blog: http://d.hatena.ne.jp/cranebird/
----------------------------------------------------------------
module Main where
import System.Environment
import qualified Data.Set as S
type Variable = Char

data Term = Var Variable
          | App Term Term -- Application
          | Lambda Variable Term -- Abstraction
            deriving (Eq)

showTerm :: Term -> String
showTerm (Var x) = [x]
showTerm (App m n) = "(" ++ showTerm m ++ showTerm n ++ ")"
showTerm (Lambda x m) = "(^" ++ [x] ++ "." ++ showTerm m ++ ")"

instance Show Term where
    show = showTerm

lambda = Lambda

-- lambda-terms example
-- a) (^x.(xy))  == Lambda 'x' (App (Var 'x') (Var 'y')) == (lambda (x) (x y))
-- b) ((^y.y)(^x.(xy))) == App (Lambda 'y' (Var 'y')) (Lambda 'x' (App (Var 'x') (Var 'y'))) 
--                      == ((lambda (y) y) (lambda (x) (x y)))
-- c) (x (^x. (^x.x))) == App (Var 'x') (Lambda 'x' (Lambda 'x' (Var 'x')))
-- d) (^x.(yz)) = Lambda 'x' (App (Var 'y') (Var 'z'))

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

-- Exercise 1.8
-- a) 

-- Def 1.9 scope
scope :: Term -> Term
scope (Lambda x m) = m

-- Def 1.11 Free and bound variables
data VarState = Free | Bound | BoundAndBinding

-- Free variables
fv :: Term -> S.Set Variable

fv (Var x) = S.singleton x
fv (App m n) = fv m `S.union` fv n
--fv (Lambda x m) = S.delete x (fv m)
fv (Lambda x m) = fv m

-- closed term
closed :: Term -> Bool
closed p = S.null (fv p)

-- Example
-- (((xv)(^y.(^z.(yv))))w)
-- App (App (App (Var 'x') (Var 'v')) (Lambda 'y' (Lambda 'z' (App (Var 'y') (Var 'v'))) )) (Var 'w')

subst :: Term -> Variable -> Term -> Term
subst n x (Var x') | x == x' = n
-- TODO; for all atoms
subst n x (App p q) = App (subst n x p) (subst n x q)
subst n x (Lambda x' p) | x == x' = Lambda x p
subst n x (Lambda y p) | x /= y && S.notMember x (fv p) = Lambda y p
subst n x (Lambda y p) | x /= y && S.member x (fv p) && S.notMember y (fv n) = Lambda y (subst n x p)
subst n x (Lambda y p) | x /= y && S.member x (fv p) && S.member y (fv n) =
                           Lambda z (subst n x (subst (Var z) y p))
                               where
                                 z = head [ v | v <- ['a'..], v `S.notMember` (fv (App n p))]
-- [w/x](^y.x)
-- subst (Var 'w') 'x' (Lambda 'y' (Var 'x'))
-- => (^y.w)
-- [w/x](^w.x)
-- subst (Var 'w')