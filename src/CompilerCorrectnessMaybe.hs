{-@ LIQUID "--reflection" @-}
module Compiler where

import Prelude hiding ((++), Monad(..))
import Lib.Derivations


-- Operators from Prelude

infixr 5 ++
{-@ infixr 5 ++ @-}
{-@ reflect ++ @-}
(++) :: [a] -> [a] -> [a]
[] ++ ys = ys
(x:xs) ++ ys = x:(xs ++ ys)

infixl 1 >>=
{-@ infixl 1 >>= @-}
{-@ reflect >>= @-}
(>>=) :: Maybe a -> (a -> Maybe b) -> Maybe b
(Just x) >>= f = f x
Nothing  >>= _ = Nothing


-- Facts about ++

{-@ appRightIdP :: xs:[a] -> {xs ++ [] = xs} @-}
appRightIdP [] =
  [] ++ []
  ==. []
  *** QED
appRightIdP (x:xs) =
  (x:xs) ++ []
  ==. x:(xs ++ [])
  ? appRightIdP xs
  ==. x:xs
  *** QED

{-@ appAssocP :: xs:[a] -> ys:[a] -> zs:[a] -> {(xs ++ ys) ++ zs = xs ++ ys ++ zs} @-}
appAssocP [] ys zs =
  ([] ++ ys) ++ zs
  ==. ys ++ zs
  ==. [] ++ ys ++ zs
  *** QED
appAssocP (x:xs) ys zs =
  ((x:xs) ++ ys) ++ zs
  ==. (x:(xs ++ ys)) ++ zs
  ==. x:((xs ++ ys) ++ zs)
  ? appAssocP xs ys zs
  ==. x:(xs ++ ys ++ zs)
  ==. (x:xs) ++ ys ++ zs
  *** QED


-- Syntax and semantics

data Expr = Val Int | Add Expr Expr
{-@ data Expr [exprSize] @-}

{-@ measure exprSize @-}
{-@ exprSize :: Expr -> Nat @-}
exprSize :: Expr -> Int
exprSize (Val _) = 1
exprSize (Add x y) = 1 + exprSize x + exprSize y

{-@ reflect eval @-}
eval :: Expr -> Int
eval (Val n) = n
eval (Add x y) = eval x + eval y


-- Stack machine

type Stack = [Int]
type Code = [Op]
data Op = PUSH Int | ADD

{-@ reflect exec @-}
exec :: Code -> Stack -> Maybe Stack
exec [] s = Just s
exec (PUSH n:c) s = exec c (n:s)
exec (ADD:c) (m:n:s) = exec c (n + m:s)
exec _ _ = Nothing


-- Naive compiler and correctness proof

{-@ reflect comp @-}
comp :: Expr -> Code
comp (Val n) = [PUSH n]
comp (Add x y) = comp x ++ comp y ++ [ADD]

{-@ correctnessP :: e:Expr -> {exec (comp e) [] = Just [eval e]} @-}
correctnessP :: Expr -> Proof
correctnessP e = generalizedCorrectnessP e []

{-@ generalizedCorrectnessP :: e:Expr -> s:Stack
                            -> {exec (comp e) s = Just (cons (eval e) s)} @-}
generalizedCorrectnessP :: Expr -> Stack -> Proof
generalizedCorrectnessP (Val n) s =
  exec (comp (Val n)) s
  ==. exec [PUSH n] s
  ==. exec [] (n:s)
  ==. Just (n:s)
  ==. Just (eval (Val n):s)
  *** QED

generalizedCorrectnessP (Add x y) s =
  exec (comp (Add x y)) s
  ==. exec (comp x ++ comp y ++ [ADD]) s
  ? sequenceP (comp x) (comp y ++ [ADD]) s
  ==. (exec (comp x) s >>= exec (comp y ++ [ADD]))
  ? generalizedCorrectnessP x s
  ==. (Just (eval x:s) >>= exec (comp y ++ [ADD]))
  ==. exec (comp y ++ [ADD]) (eval x:s)
  ? sequenceP (comp y) [ADD] (eval x:s)
  ==. (exec (comp y) (eval x:s) >>= exec [ADD])
  ? generalizedCorrectnessP y (eval x:s)
  ==. (Just (eval y:eval x:s) >>= exec [ADD])
  ==. exec [ADD] (eval y:eval x:s)
  ==. exec [] (eval x + eval y:s)
  ==. Just (eval x + eval y:s)
  ==. Just (eval (Add x y):s)
  *** QED

{-@ sequenceP :: c:Code -> d:Code -> s:Stack -> {exec (c ++ d) s = exec c s >>= exec d} @-}
sequenceP :: Code -> Code -> Stack -> Proof
sequenceP [] d s =
  exec ([] ++ d) s
  ==. exec d s
  ==. (Just s >>= exec d)
  ==. (exec [] s >>= exec d)
  *** QED
sequenceP (PUSH n:c) d s =
  exec ((PUSH n:c) ++ d) s
  ==. exec (PUSH n:(c ++ d)) s
  ==. exec (c ++ d) (n:s)
  ? sequenceP c d (n:s)
  ==. (exec c (n:s) >>= exec d)
  ==. (exec (PUSH n:c) s >>= exec d)
  *** QED
sequenceP (ADD:c) d (m:n:s) =
  exec ((ADD:c) ++ d) (m:n:s)
  ==. exec (ADD:(c ++ d)) (m:n:s)
  ==. exec (c ++ d) (n + m:s)
  ? sequenceP c d (n + m:s)
  ==. (exec c (n + m:s) >>= exec d)
  ==. (exec (ADD:c) (m:n:s) >>= exec d)
  *** QED
sequenceP (ADD:c) d s =
  exec ((ADD:c) ++ d) s
  ==. exec (ADD:(c ++ d)) s
  ==. Nothing
  ==. (Nothing >>= exec d)
  ==. (exec (ADD:c) s >>= exec d)
  *** QED


-- Optimized compiler derivation, using `eq` instead of ==. so that
-- it's reflected correctly.

{-@ reflect compApp @-}
{-@ compApp :: e:Expr -> c:Code -> {d:Code | d = comp e ++ c} @-}
compApp (Val n) c =
  comp (Val n) ++ c
  `eq` [PUSH n] ++ c
  `eq` PUSH n:([] ++ c)
  `eq` PUSH n:c
compApp (Add x y) c =
  comp (Add x y) ++ c
  `eq` (comp x ++ (comp y ++ [ADD])) ++ c
  ? appAssocP (comp x) (comp y ++ [ADD]) c
  `eq` comp x ++ ((comp y ++ [ADD]) ++ c)
  ? appAssocP (comp y) [ADD] c
  `eq` comp x ++ comp y ++ [ADD] ++ c
  `eq` comp x ++ comp y ++ ADD:([] ++ c)
  `eq` comp x ++ comp y ++ ADD:c
  `eq` compApp x (comp y ++ ADD:c)
  `eq` compApp x (compApp y (ADD:c))

{-@ reflect comp' @-}
comp' :: Expr -> Code
comp' e = compApp e []


-- Proof of correctness for optimized compiler by showing equivalence
-- to original compiler

{-@ equivP :: e:Expr -> {comp' e = comp e} @-}
equivP e =
  comp' e
  ==. compApp e []
  ==. comp e ++ []
  ? appRightIdP (comp e)
  ==. comp e
  *** QED

{-@ equivCorrectnessP :: e:Expr -> {exec (comp' e) [] = Just [eval e]} @-}
equivCorrectnessP e =
  exec (comp' e) []
  ? equivP e
  ==. exec (comp e) []
  ? correctnessP e
  ==. Just [eval e]
  *** QED


-- Proof of correctness of optimized compiler from scratch

{-@ generalizedCorrectnessP' :: e:Expr -> s:Stack -> c:Code
                             -> {exec (compApp e c) s = exec c (cons (eval e) s)} @-}
generalizedCorrectnessP' :: Expr -> Stack -> Code -> Proof
generalizedCorrectnessP' (Val n) s c =
  exec (compApp (Val n) c) s
  ==. exec (PUSH n:c) s
  ==. exec c (n:s)
  ==. exec c (eval (Val n):s)
  *** QED

generalizedCorrectnessP' (Add x y) s c =
  exec (compApp (Add x y) c) s
  ==. exec (compApp x (compApp y (ADD:c))) s
  ? generalizedCorrectnessP' x s (compApp y (ADD:c))
  ==. exec (compApp y (ADD:c)) (eval x:s)
  ? generalizedCorrectnessP' y (eval x:s) (ADD:c)
  ==. exec (ADD:c) (eval y:eval x:s)
  ==. exec c (eval x + eval y:s)
  ==. exec c (eval (Add x y):s)
  *** QED
  
{-@ correctnessP' :: e:Expr -> {exec (comp' e) [] = Just [eval e]} @-}
correctnessP' :: Expr -> Proof
correctnessP' e =
  exec (comp' e) []
  ==. exec (compApp e []) []
  ? generalizedCorrectnessP' e [] []
  ==. exec [] [eval e]
  ==. Just [eval e]
  *** QED
