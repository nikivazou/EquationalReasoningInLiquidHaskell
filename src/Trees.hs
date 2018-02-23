{-@ LIQUID "--exactdc" @-}
{-@ LIQUID "--higherorder" @-}
{-@ LIQUID "--automatic-instances=liquidinstanceslocal" @-}
{-@ infix   ++ @-}
{-# LANGUAGE CPP #-}

module Trees where

import Prelude hiding (reverse, (++), length)
import Data.List
{-@ infix   ++ @-}

-- Lib included instead of imported to allow for inlining
-- #define InlineProofCombinators
-- #include "Lib/Derivations.hs"   

import Lib.Derivations
    

-------------------------------------------------------------------------------
-- | Derivation of reverse' ---------------------------------------------------
-------------------------------------------------------------------------------

flatten' :: Tree -> [Int] -> [Int]
{-@ flatten' :: t:Tree -> ns:[Int] -> {v:[Int] | v = flatten t ++ ns } @-}
flatten' (Leaf n) ns 
  =   flatten (Leaf n) ++ ns  
  ==. [n] ++ ns 
  ==. n:([] ++ ns)
  ==. [] ++ (n:ns)
  ==. n:ns
  ^^^ Defined

flatten' (Node l r) ns
  =   flatten (Node l r) ++ ns 
  ==. (flatten l ++ flatten r) ++ ns 
      ? assoc (flatten l) (flatten r) ns 
  ==. flatten l ++ (flatten r ++ ns) 
  ==. flatten l ++ (flatten' r ns)
  ==. flatten' l (flatten' r ns) 
  ^^^ Defined 


-------------------------------------------------------------------------------
-- | Helpers: Definitions & Theorems Used -------------------------------------
-------------------------------------------------------------------------------

data Tree = Leaf Int | Node Tree Tree 

{-@ data Tree [size] @-}

{-@ invariant {t:Tree | 0 <= size t }  @-}
-- LH: required because of https://github.com/ucsd-progsys/liquidhaskell/issues/1198

{-@ measure size @-}
{-@ size :: Tree -> Nat @-} 
size :: Tree -> Int 
size (Leaf _)   = 1 
size (Node l r) = 2 + size l + size r 

{-@ reflect flatten @-}
flatten :: Tree -> [Int]
flatten (Leaf n)   = [n]
flatten (Node l r) = flatten l ++ flatten r  



flattenOpt :: Tree -> [Int]
{-@ flattenOpt :: t:Tree -> {v:[Int] | v = flatten t } @-}
flattenOpt t = flatten' t [] `withTheorem` leftIdP (flatten t)


