{-@ LIQUID "--exactdc"        @-}
{-@ LIQUID "--higherorder"    @-}
{-@ LIQUID "--prune-unsorted" @-}
{-@ LIQUID "--automatic-instances=liquidinstanceslocal" @-}
{-# LANGUAGE CPP #-}

{-@ infix :  @-}
{-@ infix ++ @-}

module Data.Compiler where

import Prelude hiding ((++))
import Lib.Derivations 

-------------------------------------------------------------------------------
-- | Derivation of comp' ------------------------------------------------------
-------------------------------------------------------------------------------

-- Using `eq` instead of `==.` because https://github.com/ucsd-progsys/liquidhaskell/issues/1247

{-@ reflect comp' @-}
{-@ comp' :: e:Expr -> c:Code 
          -> {o:Code | o = comp e ++ c && addCount c + exprAdds e == addCount o} @-}
comp' :: Expr -> Code -> Code 
comp' (Val n) c 
  =    comp (Val n) ++ c 
  `eq` [PUSH n] ++ c 
  `eq` PUSH n:([]++c)
  `eq` PUSH n:c

comp' (Add x y) c 
  =   comp (Add x y) ++ c 
  `eq` ((comp x ++ comp y) ++ [ADD]) ++ c 
      ? assoc (comp x) (comp y) [ADD]
  `eq` (comp x ++ (comp y ++ [ADD])) ++ c 
      ? assoc (comp x) (comp y ++ [ADD]) c  
  `eq` comp x ++ (comp y ++ [ADD] ++ c) 
  `eq` comp' x ((comp y ++ [ADD]) ++ c)
      ? assoc (comp y) [ADD] c 
  `eq` comp' x (comp y ++ ([ADD] ++ c))
  `eq` comp' x (comp' y ([ADD] ++ c)) 
  `eq` comp' x (comp' y (ADD:([] ++ c))) 
  `eq` comp' x (comp' y (ADD:c))


-------------------------------------------------------------------------------
-- | Optimized Correctness ----------------------------------------------------
-------------------------------------------------------------------------------

{-@ correctness' :: e:Expr -> c:Code 
  -> s:{Stack |(addCount c) + (addCount c) + (exprAdds e) + (exprAdds e) <=  len s } 
  -> { exec (comp' e c) s == exec c (eval e : s) } 
   @-}
correctness' :: Expr -> Code -> Stack -> Proof 
correctness' (Val n) c s  
  =   exec (comp' (Val n) c) s 
  ==. exec (PUSH n:c) s 
  ==. exec c (n:s) 
  ==. exec c (eval (Val n) : s)
  *** QED 

correctness' (Add x y) c s
  =   exec (comp' (Add x y) c)         s 
  ==. exec (comp' x (comp' y (ADD:c))) s 
      ? correctness' x (comp' y (ADD:c)) s
  ==. exec (comp' y (ADD:c)) (eval x:s)
      ? correctness' y (ADD:c) (eval x:s) 
  ==. exec (ADD:c) (eval y : (eval x:s))
  ==. exec c ((eval y+eval x) :s) 
  ==. exec c ((eval x+eval y) :s)
  ==. exec c ((eval (Add x y)):s)
  *** QED 

-------------------------------------------------------------------------------
-- | Definitions & Proofs -----------------------------------------------------
-------------------------------------------------------------------------------


data Expr = Val Int | Add Expr Expr 

{-@ measure exprAdds @-}
{-@ exprAdds :: Expr -> Nat @-} 
exprAdds :: Expr -> Int 
exprAdds (Add e1 e2) = 1 + exprAdds e1 + exprAdds e2  
exprAdds (Val _)     = 0 


{-@ data Expr [size] @-}

{-@ measure size @-}
{-@ size :: Expr -> Nat @-} 
size :: Expr -> Int 
size (Val _)   = 1 
size (Add l r) = 1 + size l + size r 


{-@ reflect eval @-}
eval :: Expr -> Int 
eval (Val n) = n 
eval (Add x y) = eval x + eval y 

type Stack = [Int]
type Code  = [Op] 
data Op    = PUSH Int | ADD 

{-@ reflect exec @-}
exec :: Code -> [Int] -> [Int]
{-@ exec :: c:Code -> {s:[Int] | (addCount c) + (addCount c) <=  len s} 
         -> {o:[Int] | len o == len s - (addCount c) + len c - addCount c} @-}
exec [] s              = s 
exec (PUSH n:c) s      = exec c (n:s)
exec (ADD:c)   (m:n:s) = exec c (n+m:s)

{-@ reflect comp @-}
{-@ comp :: e:Expr -> {ops:[Op] | exprAdds e == addCount ops } @-} 
comp :: Expr -> [Op] 
comp (Val n)   = [PUSH n]
comp (Add x y) = (comp x ++ comp y) ++ [ADD]



{-@ measure addCount @-}
{-@ addCount :: Code -> Nat @-} 
addCount :: Code -> Int 
addCount []         = 0 
addCount (ADD:c) = 1 + addCount c 
addCount (_:c) = addCount c 

{-@ correctness :: e:Expr -> s:{Stack |(exprAdds e) + (exprAdds e) <=  len s } 
  -> { exec (comp e) s == eval e : s} 
   @-}
correctness :: Expr -> Stack -> Proof 
correctness (Val n) s   
  =   exec (comp (Val n)) s 
  ==. exec [PUSH n] s 
  ==. exec [] (n:s)
  ==. n:s
  ==. eval (Val n):s
  *** QED 
correctness (Add x y) s 
  =   exec (comp (Add x y)) s
  ==. exec ((comp x ++ comp y) ++ [ADD]) s 
      ? assoc (comp x) (comp y) [ADD] 
  ==. exec (comp x ++ (comp y ++ [ADD])) s
      ? distributivity (comp x) (comp y ++ [ADD]) s 
  ==. exec (comp y ++ [ADD]) (exec (comp x) s)
      ? correctness x s 
  ==. exec (comp y ++ [ADD]) (eval x:s)
      ? distributivity (comp y) [ADD] (eval x:s)
  ==. exec [ADD] (exec (comp y) (eval x:s))
      ? correctness y (eval x:s)   
  ==. exec [ADD] (eval y :(eval x:s))
  ==. exec [] ((eval y+eval x):s)
  ==. (eval y + eval x) : s 
  ==. (eval x + eval y) : s 
  ==. eval (Add x y) : s 
  *** QED  

{-@ distributivity :: c:[Op] -> d:[Op] 
    -> s:{[Int] | (addCount c) + (addCount c) + (addCount d) + (addCount d) <=  len s} 
    -> {exec (c ++ d) s == exec d (exec c s)}  @-}
distributivity :: [Op] -> [Op] -> [Int] -> Proof 
distributivity [] d s 
  =   exec ([] ++ d) s
  ==. exec d s 
  ==. exec d (exec [] s)
  *** QED   
distributivity (PUSH n:c) d s 
  =   exec ((PUSH n:c) ++ d) s 
  ==. exec (PUSH n:(c ++ d)) s 
  ==. exec (PUSH n:(c ++ d)) s 
  ==. exec (c ++ d) (n:s) 
      ? distributivity c d (n:s) 
  ==. exec d (exec c (n:s)) 
  ==. exec d (exec (PUSH n:c) s)
  *** QED  
distributivity (ADD:c) d (n:m:s) 
  =   exec ((ADD:c) ++ d) (n:m:s) 
  ==. exec (ADD:(c++d)) (n:m:s) 
  ==. exec (c++d) (n+m:s) 
      ? distributivity c d (n+m:s) 
  ==. exec d (exec c (n+m:s))
  ==. exec d (exec (ADD:c) (n:m:s))
  *** QED  

{-@ infix   ++ @-}
{-@ reflect ++ @-}
{-@ (++) :: os1:[Op] -> os2:[Op] -> {os:[Op] | addCount os == addCount os1 + addCount os2 } @-}
(++) :: [Op] -> [Op] -> [Op]
[]     ++ ys = ys
(x:xs) ++ ys = x:(xs ++ ys)  

{-@ automatic-instances assoc @-}
{-@ assoc :: xs:[Op] -> ys:[Op] -> zs:[Op] 
          -> { xs ++ (ys ++ zs) == (xs ++ ys) ++ zs }  @-}
assoc :: [Op] -> [Op] -> [Op] -> () 
assoc [] _ _       = ()
assoc (x:xs) ys zs = assoc xs ys zs