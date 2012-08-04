----------------------------------------------------------------
-- secd.hs - SECD Machine in Haskell
-- Copyright (C) 2012 by @quasicrane (Twitter)
-- my blog: http://d.hatena.ne.jp/cranebird/
----------------------------------------------------------------
-- Based on the note on by Prof. Jia-Huai You (http://webdocs.cs.ualberta.ca/~you/courses/325/Mynotes/Fun/SECD-slides.html)
-- Reference:
-- "LispMe: An Implementation of Scheme for the Palm Pilot", by Fred Bayer.
-- "Write Yourself a Scheme in 48 hours", by Jonathan Tang."http://en.wikibooks.org/wiki/Write_Yourself_a_Scheme_in_48_Hours"

module Main where
import System.Environment
import Text.ParserCombinators.Parsec hiding (spaces)
import IO hiding (try)
import Test.HUnit

import Debug.Trace

instance Show (a -> b)
    where
      show _ = "#'function"

-- Utility
run :: Show a => Parser a -> String -> IO ()
run p input = case parse p "" input of
                Left err -> do {
                              putStr "parse error at ";
                              print err
                            }
                Right x -> print x

symbol :: Parser Char
symbol = oneOf "!#$%*+-/:<=>?@^_~"

spaces :: Parser ()
spaces = skipMany1 space

spaces0 :: Parser ()
spaces0 = skipMany space

data LispVal = Atom String
             | Number Integer
             | String String
             | Bool Bool
             | LispVal :. LispVal -- Cons
             | Nil
             | NIL -- Instruction NIL
             | LDC LispVal
             | LD (Level, Nth)
             | STOP
             | JOIN
             | SEL
             | LDF LispVal
             | AP
             | CONS
             | CAR
             | CDR
             | ATOM
             | RTN
             | DUM
             | RAP
             | OMEGA
             | OP String -- BuiltIn Operator
               deriving (Eq, Show)

infixr 0 :.

-- instance Show LispVal where
--     show = showLispVal

-- CONS Utility
consp :: LispVal -> Bool
consp (_ :. _) = True
consp _ = False

car :: LispVal -> LispVal
car (a :. _) = a
car x = error ("car Not cons: " ++ show x)
cdr :: LispVal -> LispVal
cdr (_ :. a) = a
cdr x = error ("cdr Not cons: " ++ show x)
cons :: LispVal -> LispVal -> LispVal 
cons = (:.)

reverseList lst = reverseList' lst Nil
    where
      reverseList' (a :. Nil) acc = a :. acc
      reverseList' (a :. b) acc = reverseList' b (a :. acc)

mapcar f lst = mapcar' f lst Nil
    where
      mapcar' f Nil acc = acc
      mapcar' f (a :. b) acc = f a :. mapcar' f b acc

list1 a = a :. Nil
list2 a b = a :. b :. Nil
list3 a b c = a :. b :. c :. Nil

isProperList :: LispVal -> Bool
isProperList Nil = True
isProperList (x :. Nil) = True
isProperList ((:.) x y) = isProperList y
isProperList _ = False

-- (.) = cons
-- infixr 0 .

-- show cons cell; see HyperSpec "22.1.3.5 Printing Lists And Conses"
showCons x = step1 x ""
    where
      step1 x res = step2 x (res ++ "(")
      step2 x res = step3 x (res ++ showLispVal (car x))
      step3 x res = if consp (cdr x)
                    then
                        step2 (cdr x) (res ++ " ")
                    else
                        step4 x res
      step4 x res = if cdr x /= Nil
                    then
                        step5 x (res ++ " . " ++ showLispVal (cdr x))
                    else
                        step5 x res
      step5 x res = res ++ ")"

showLispVal :: LispVal -> String
showLispVal (Atom a) = a
showLispVal (String s) = "\"" ++ s ++ "\""
showLispVal (a :. b) = showCons (a :. b)
showLispVal (Number a) = show a
showLispVal (Bool True) = "#t"
showLispVal (Bool False) = "#f"
showLispVal Nil = "()"
showLispVal NIL = "NIL"
showLispVal (LDC a) = "LDC " ++ showLispVal a
showLispVal STOP = "STOP"
showLispVal (OP x) = "OP " ++ x
showLispVal SEL = "SEL"
showLispVal JOIN = "JOIN"
showLispVal (LDF x) = "LDF " ++ showLispVal x
showLispVal AP = "AP"
showLispVal RTN = "RTN"
showLispVal CONS = "CONS"
showLispVal (LD (l, n)) = "LD " ++ show (l, n)
showLispVal x = show x

-- Parse S-Expression
parseString :: Parser LispVal
parseString = do
  spaces0
  char '"'
  x <- many (noneOf "\"")
  char '"'
  spaces0
  return $ String x

parseAtom :: Parser LispVal
parseAtom = do
  spaces0
  first <- letter <|> symbol
  rest <- many (letter <|> digit <|> symbol)
  let atom = first:rest
  return $ case atom of
             "#t" -> Bool True
             "#f" -> Bool False
             _ -> Atom atom

-- TODO; parse negative number
parseNumber :: Parser LispVal
parseNumber = do
  spaces0
  n <- many1 digit
  return $ Number (read n)

parseList :: Parser LispVal
parseList = do
  elts <- many parseExpr
  return $ foldr (:.) Nil elts

parseDotted :: Parser LispVal
parseDotted = do
  elts <- many1 parseExpr
  char '.'
  spaces
  tail <- parseExpr
  return $ foldr (:.) tail elts

parseQuoted :: Parser LispVal
parseQuoted = do
  char '\''
  x <- parseExpr
  return $ (:.) (Atom "quote") ((:.) x Nil)

parseExpr :: Parser LispVal
parseExpr = do
  spaces0
  res <- try parseAtom 
            <|> try parseString
            <|> try parseNumber
            <|> try parseQuoted
            <|> do spaces0
                   char '('
                   x <- try parseDotted <|> parseList
                   spaces0
                   char ')'
                   return x
  spaces0
  return res

readExpr :: String -> LispVal
readExpr input = case parse parseExpr "lisp" input of
                   Left err -> String $ "No match: " ++ show err
                   Right val -> val

----------------------------------------------------------------
-- Compiler
----------------------------------------------------------------
type Insn = LispVal
type Level = Int
type Nth = Int

type Env = [[ (LispVal, Nth) ]]

-- Compile-time Env.
-- Example: env= [ [(a, 1), (b, 2) ], [ (c, 1), (d, 2)] ]
-- lookup a env => (1, 1) (level, nth)
-- lookup b env => (1, 2)
-- lookup c env => (2, 1)

lookupVar :: LispVal -> Env -> Maybe (Level, Nth)
lookupVar a = lookupVar' a 1
    where
      lookupVar' a level [] = Nothing
      lookupVar' a level (e:envs) = case lookup a e of
                                      Just nth -> Just (level, nth)
                                      Nothing -> lookupVar' a (level + 1) envs

isSelfEvalutating :: LispVal -> Bool
isSelfEvalutating (Number _) = True
isSelfEvalutating (String _) = True
isSelfEvalutating (Bool _) = True
isSelfEvalutating Nil = True
isSelfEvalutating _ = False

isBuiltin x = x `elem` ["+", "-", "*", ">", "<", "=" ]

----------------------------------------------------------------
-- Compiler
----------------------------------------------------------------
comp :: LispVal -> Insn
comp exp = comp' exp [] STOP
comp' :: LispVal -> Env -> Insn -> Insn
-- Nil
comp' Nil _ c = NIL :. c
-- Self Evaluating
comp' e _ c | isSelfEvalutating e = LDC e :. c
-- variable
comp' (Atom x) e c = LD location :. c
    where
      location = case lookupVar (Atom x) e of
                   Just (level, nth) -> (level, nth)
                   Nothing -> error ("var " ++ x ++ " not found")
-- quote
comp' (Atom "quote" :. x :. Nil) env c = LDC x :. c
-- Builtin operator
comp' (Atom op :. x :. y :. Nil) env c | isBuiltin op =
    comp' y env (comp' x env (OP op :. c))
-- if
comp' (Atom "if" :. e :. et :. ef :. Nil) env c =
    comp' e env (SEL :. comp' et env (JOIN :. Nil) :. comp' ef env (JOIN :. Nil) :. c)
-- Nonrecursive Functions
comp' (Atom "lambda" :. plist :. body :. Nil) env c = LDF (compBody body (RTN :. Nil)) :. c
    where
      plistToList Nil acc = acc
      plistToList (x :. xs) acc = plistToList xs (x:acc)
      extendEnv env = zip (reverse $ plistToList plist []) [1..] : env
      env' = extendEnv env
      compBody Nil acc = acc
      compBody x acc = comp' x env' acc

-- let
-- (let ((x x0)) body) => ((lambda (x) body) x0)
-- (let ((x x0) (y y0)) body) => ((lambda (x y) body) x0 y0)
comp' (Atom "let" :. bindings :. body) env c =
    comp' ((Atom "lambda" :. mapcar car bindings :. body) :. 
           mapcar (car . cdr) bindings) env c

-- (letrec ((x x0)
--          (y y0))
--  body)
-- =>
-- DUM NIL y0' CONS x0' CONS LDF (body' RTN) RAP
comp' (Atom "letrec" :. bindings :. body) env c = 
    DUM :. NIL :. genargs' inits (LDF (comp' (car body) newenv (RTN :. Nil)) :. RAP :. c)
    where
      plistToList Nil acc = acc
      plistToList (x :. xs) acc = plistToList xs (x:acc)
      vars = mapcar car bindings
      inits = mapcar (car . cdr) bindings
      newenv = zip (reverse $ plistToList vars []) [1..] : env
      genargs' Nil cc = cc
      genargs' (e :. es) cc = genargs' es (comp' e newenv (CONS :. cc))

-- procedure call
-- (f) => NIL f' AP
-- (f e1 e2) => NIL e2' CONS e1' CONS f' AP
comp' (f :. es) env c
    | isProperList es = NIL :. args2cons es (comp' f env (AP :. c))
    where
      args2cons Nil c = c
      args2cons (e :. Nil) c = comp' e env (CONS :. c)
      args2cons es c = args2cons (cdr es) (comp' (car es) env (CONS :. c))

-- util
lispNth 1 x = car x
lispNth i x = lispNth (i-1) (cdr x)
locate (i,j) e = lispNth j (lispNth i e)

-- The SECD virtual machine
type SECD = (
             LispVal, -- Stack
             LispVal, -- Environment
             LispVal, -- Code
             LispVal  -- Dump
            )
-- State transition
transit :: SECD -> SECD
transit (s, e, LDC x :. c, d) = (x :. s, e, c, d)
transit (s, e, NIL :. c, d) = (Nil :. s, e, c, d)
-- Ptimitive
transit (Number a :. Number b :. s, e, OP "=" :. c, d) = (Bool (a == b) :. s, e, c, d)
transit (Number a :. Number b :. s, e, OP "+" :. c, d) = (Number (a + b) :. s, e, c, d)
transit (Number a :. Number b :. s, e, OP "-" :. c, d) = (Number (a - b) :. s, e, c, d)
transit (Number a :. Number b :. s, e, OP "*" :. c, d) = (Number (a * b) :. s, e, c, d)
transit (Number a :. Number b :. s, e, OP ">" :. c, d) = (Bool (a > b) :. s, e, c, d)
transit (Number a :. Number b :. s, e, OP "<" :. c, d) = (Bool (a < b) :. s, e, c, d)
-- Conditionals
transit (Bool True :. s, e, SEL :. ct :. _ :. c, d) = (s, e, ct, c :. d)
transit (Bool False :. s, e, SEL :. _ :. cf :. c, d) = (s, e, cf, c :. d)
transit (s, e, JOIN :. _, c :. d) = (s, e, c, d)
-- Procedure call
transit (s, e, LDF f :. c, d) =  ((f :. e) :. s, e, c, d)
transit ((c' :. e') :. v :. s, e, AP :. c, d) = (Nil, v :. e', c', s :. e :. c :. d)
transit (x :. _, e', RTN :. _, s :. e :. c :. d) = (x :. s, e, c, d)
transit (s, e, LD (i, j) :. c, d) = (locate (i,j) e :. s, e, c, d)
-- Cons
transit (a :. b :. s, e, CONS :. c, d) = ((a :. b) :. s, e, c, d)
transit (a :. _ :. s, e, CAR :. c, d) = (a :. s, e, c, d)
transit (_ :. b :. s, e, CDR :. c, d) = (b :. s, e, c, d)
transit ((_ :. _) :. s, e, ATOM :. c, d) = (Bool True :. s, e, c, d)
transit (_ :. s, e, ATOM :. c, d) = (Bool False :. s, e, c, d)
-- Recursion
transit (s, e, DUM :. c, d) = (s, OMEGA :. e, c, d)
transit ((c' :. (OMEGA :. e')) :. v :. s, OMEGA :. e, RAP :. c, d) =
    (Nil, gencirc (OMEGA :. e') v,  c', s :. e :. c :. d)
-- Base case
transit (s,e,c,d) = error (show (car c))

gencirc e' v = mapcar f v :. gencirc e' v
    where
      f (en :. (OMEGA :. e)) = en :. gencirc e' v
      f x = x

-- for debug
-- Be care to use for circular structure.
-- transit' (s, e, c, d) = trace ("S:"++show s ++"\nE:" ++show e ++ "\nC:" ++ show c ++ "\nD:" ++ show d)
--                         $ transit (s,e,c,d)

exec c = iter (Atom "s", Atom "e", c, Atom "d")
    where
      iter (s, e, STOP, d) = (s, e, STOP, d)
      iter (s, e, STOP :. c, d) = (s, e, c, d)
      iter (s, e, c, d) = iter (transit (s, e, c, d))

eval :: LispVal -> String
eval expr = showLispVal $ car s
    where
      (s, e, c, d) = exec (comp expr)

eval' :: String -> String
eval' = eval . readExpr

-- Simple REPL
-- See "Write Yourself a Scheme in 48 Hours"
flushStr :: String -> IO ()
flushStr str = putStr str >> hFlush stdout

readPrompt :: String -> IO String
readPrompt prompt = flushStr prompt >> getLine

evalString :: String -> IO String
evalString expr = return $ eval' expr

evalAndPrint :: String -> IO ()
evalAndPrint expr = evalString expr >>= putStrLn

--until_ :: Monad m => (a -> Bool) -> m a -> (
until_ pred prompt action = do
  result <- prompt
  if pred result
  then
      return ()
  else
      action result >> until_ pred prompt action

runRepl :: IO ()
runRepl = until_ (== "quit") (readPrompt "SECD>>> ") evalAndPrint

main :: IO ()
main = do runRepl

----------------------------------------------------------------
-- HUnit Test
-- runTestTT tests
-- runTestTT testeval
----------------------------------------------------------------
testeval = test [
            -- simple
            "e1" ~: "num" ~: "3" ~=? eval' "3",
            "e1" ~: "num2" ~: "0" ~=? eval' "0",
            -- fixme add minus
            -- primitive
            "e2" ~: "add1" ~: "7" ~=? eval' "(+ 3 4)",
            "e2" ~: "add2" ~: "12" ~=? eval' "(+ 4 8)",
            "e2" ~: "add3" ~: "10" ~=? eval' "(+ (+ 2 4) 4)",
            "e2" ~: "add4" ~: "19" ~=? eval' "(+ (+ 2 4) (+ 5 8))",
            "e2" ~: "sub1" ~: "1" ~=? eval' "(- 3 2)",
            "e2" ~: "sub2" ~: "9" ~=? eval' "(- 15 (+ 5 1))",
            "e2" ~: "sub3" ~: "5" ~=? eval' "(- (- 9 1) (- 5 2))",
            "e2" ~: "mul1" ~: "10" ~=? eval' "(* 2 5)",
            "e2" ~: "mul2" ~: "18" ~=? eval' "(* 2 (+ 3 6))",
            -- procedure call
            "p1" ~: "lambda1" ~: "0" ~=? eval' "((lambda () 0))",
            "p1" ~: "lambda2" ~: "13" ~=? eval' "((lambda () 13))",
            "p1" ~: "lambda3" ~: "8" ~=? eval' "((lambda (x) (+ x x)) 4)",
            "p1" ~: "lambda4" ~: "12" ~=? eval' "((lambda (x) (* 2 x)) 6)",
            "p2" ~: "carlambda1" ~: "6" ~=? eval' "((let ((f (lambda (x) (* 2 x)))) f) 3)",
            "p2" ~: "carlambda2" ~: "30" ~=? eval' "((let ((f (lambda (x) (* 2 x))) (g (lambda (x) (* 10 x)))) g) 3)",
            "p2" ~: "carlambda3" ~: "60" ~=? eval' "((let ((f (lambda (x) (* 2 x))) (g (lambda (x) (* 10 x))))  (lambda (n) (f (g n)))) 3)",
            -- conditionals
            "c1" ~: "if1" ~: "#t" ~=? eval' "(if #t #t #f)",
            "c1" ~: "if2" ~: "#f" ~=? eval' "(if #t #f #t)",
            "c1" ~: "if3" ~: "#t" ~=? eval' "(if #f #f #t)",
            "c1" ~: "if4" ~: "#f" ~=? eval' "(if (> 1 10) #t #f)",
            "c1" ~: "if5" ~: "#f" ~=? eval' "(if (> 1 10) #t #f)",
            "c1" ~: "if6" ~: "4" ~=? eval' "(if #t 4 10)",
            -- let
            "l1" ~: "let1" ~: "6" ~=? eval' "(let ((x 13)) 6)",
            "l1" ~: "let2" ~: "13" ~=? eval' "(let ((x 13)) x)",
            "l1" ~: "let3" ~: "26" ~=? eval' "(let ((x 13)) (* x 2))",
            "l1" ~: "let4" ~: "11" ~=? eval' "(let ((x 13)) (- x 2))",
            "l1" ~: "let5" ~: "26" ~=? eval' "(let ((x 13)) (+ x x))",
            "l1" ~: "let6" ~: "3" ~=? eval' "(let ((x 13) (y 3)) y)",
            "l1" ~: "let7" ~: "16" ~=? eval' "(let ((x 13) (y 3)) (+ y x))",
            "l1" ~: "let8" ~: "19" ~=? eval' "(let ((x 13) (y 3) (z 2)) (+ (* z y) x))",
            "l2" ~: "lm1" ~: "6" ~=? eval' "(let ((f (lambda (x) (* 2 x)))) (f 3))",
            "l2" ~: "lm2" ~: "30" ~=? eval' "(let ((f (lambda (x) (* 2 x))) (g (lambda (x) (* 10 x)))) (g 3))",
            "l2" ~: "lm2" ~: "60" ~=? eval' "(let ((f (lambda (x) (* 2 x))) (g (lambda (x) (* 10 x)))) (f (g 3)))",
            "lr1" ~: "letrec1" ~: "3" ~=? eval' "(letrec ((f 3)) f)",
            "lr1" ~: "letrec2" ~: "3" ~=? eval' "(letrec ((f 3) (g 5)) f)",
            "lr1" ~: "letrec3" ~: "3" ~=? eval' "(letrec ((f 3) (g 5) (h 9)) f)",
            "lr1" ~: "letrec4" ~: "2" ~=? eval' "(letrec ((f 3) (g 5) (h 9)) (- g f))",
            "lr1" ~: "letrec5" ~: "2" ~=? eval' "(letrec ((f 3) (g (- 4 2))) g)",
            "lr1" ~: "letrec6" ~: "8" ~=? eval' "(letrec ((f (- 9 1)) (g (- 4 2))) f)",
            "lr1" ~: "letrec7" ~: "15" ~=? eval' "(letrec ((x 3) (y 5) (z 12)) (+ x z))",
            "lr1" ~: "letrec8" ~: "12" ~=? eval' "(letrec ((f (lambda (x) x))) (f 12))",
            "lr1" ~: "letrec9" ~: "4" ~=? eval' "(letrec ((f (lambda (x) x)) (g 4)) (f g))",
            "lr1" ~: "letrec10" ~: "4" ~=? eval' "(letrec ((f (lambda (x) g)) (g 4)) (f 12))",
            "fa1" ~: "fact1" ~: "3628800" ~=? eval' "(letrec ((fact (lambda (n) (if (= n 0) 1 (* n (fact (- n 1)))))))  (fact 10))",
            "fa1" ~: "fact2" ~: "3628800" ~=? eval' "(letrec ((fact (lambda (n res) (if (= n 0) res (fact (- n 1) (* n res)))))) (fact 10 1))",
            "fib" ~: "fib1" ~: "6765" ~=? eval' "(letrec ((fib (lambda (n) (if (< n 2) n (+ (fib (- n 1)) (fib (- n 2))))))) (fib 20))"
           ]

tests = test [
         "t1" ~: "atom1" ~: Atom "a" ~=? readExpr "a",
         "t1" ~: "atom2" ~: Atom "abc" ~=? readExpr "abc",
         "t1" ~: "atom3" ~: Atom "xyz123" ~=? readExpr "xyz123",
         "t1" ~: "number1" ~: Number 1 ~=? readExpr "1",
         "t1" ~: "number2" ~: Number 123 ~=? readExpr "123",
         "t1" ~: "number3" ~: Number 0 ~=? readExpr "0",
         "t1" ~: "str1" ~: String "a" ~=? readExpr "\"a\"",
         "t1" ~: "str2" ~: String "abc" ~=? readExpr "\"abc\"",
         "t1" ~: "str3" ~: String "abc def" ~=? readExpr "\"abc def\"",
         "t2" ~: "cons1" ~: (Atom "a" :. Nil) ~=? readExpr "(a)",
         "t2" ~: "cons2" ~: (Atom "a" :. Nil) ~=? readExpr "(a )",
         "t2" ~: "cons3" ~: (Atom "a" :. Nil) ~=? readExpr "( a)",
         "t2" ~: "cons4" ~: (Atom "a" :. Nil) ~=? readExpr "( a )",
         "t2" ~: "cons5" ~: (Atom "a" :. Atom "b") ~=? readExpr "(a . b)",
         "t2" ~: "cons6" ~: (Atom "a" :. Atom "b") ~=? readExpr "( a . b )",
         "t2" ~: "cons7" ~:
                  (Atom "a" :. Atom "b" :. Atom "c") ~=? readExpr "(a b . c )",
         "t2" ~: "cons7" ~:
                  (Atom "a" :. Atom "b" :. Atom "cd") ~=? readExpr "(  a b . cd)",
         "t3" ~: "l1" ~: (Atom "a" :. Atom "b" :. Nil) ~=? readExpr "(a b)",
         "t3" ~: "l2" ~: (Atom "a" :. Atom "b" :. Nil) ~=? readExpr "( a b)",
         "t3" ~: "l3" ~: (Atom "a" :. Atom "b" :. Atom "c" :. Nil) ~=? readExpr "( a b c )",
         "t4" ~: "l1" ~: (Atom "a" :. (Atom "b" :. Nil) :. Nil) ~=? readExpr "(a (b))",
         "t4" ~: "l2" ~: (Atom "a" :. ((Atom "b" :. Nil) :. (Atom "c" :. Nil))) ~=?
              readExpr "(a (b) c)",
         "t4" ~: "l3" ~: (Atom "a" :. ((Atom "b" :. Atom "c") :. (Atom "d" :. Nil))) ~=?
              readExpr "(a (b . c) d)",
         "t5" ~: "q1" ~: (Atom "quote" :. (Atom "x" :. Nil)) ~=? readExpr "'x",
         "t5" ~: "q2" ~:
              (:.) (Atom "quote") ((:.) (Atom "abc") Nil) ~=?
                   readExpr "'abc",
         "t5" ~: "q3" ~:
              (:.) (Atom "quote") ((:.) ((:.) (Atom "abc") Nil) Nil) ~=?
                   readExpr "'(abc)",
         "t5" ~: "q4" ~:
                  (:.) (Atom "quote") ((:.) ((:.) (Atom "abc") ((:.) (Atom "def") Nil)) Nil) ~=?
                       readExpr "'(abc def)"

        ]
