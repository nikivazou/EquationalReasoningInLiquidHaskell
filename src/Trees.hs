{-@ LIQUID "--exactdc" @-}
{-@ LIQUID "--higherorder" @-}
{-@ LIQUID "--automatic-instances=liquidinstanceslocal" @-}
{-@ infix   ++ @-}
{-# LANGUAGE CPP #-}

module Trees where

import Prelude hiding (reverse, (++))
import Data.List 
{-@ infix   ++ @-}

-- Lib included instead of imported to allow for inlining
#include "Lib/Derivations.hs"   

-------------------------------------------------------------------------------
-- | Specification of flatten' ------------------------------------------------
-------------------------------------------------------------------------------

{-@ specFlatten' :: t:Tree -> ns:[Int] 
                 -> {flatten' t ns = flatten t ++ ns} @-}
specFlatten' :: Tree -> [Int] -> ()
specFlatten' _ _ = undefined    

-------------------------------------------------------------------------------
-- | Derivation of reverse' ---------------------------------------------------
-------------------------------------------------------------------------------

flatten' :: Tree -> [Int] -> [Int]
{-@ flatten' :: t:Tree -> ns:[Int] -> {flatten' t ns = flatten t ++ ns} @-}
flatten' (Leaf n) ns 
  =   flatten (Leaf n) ++ ns  
      ? specFlatten' (Leaf n) ns
  ==. (n:[]) ++ ns 
  ==. [] ++ (n:ns)
  ==. n:ns
  ^^^ Defined
flatten' (Node l r) ns
  =   flatten (Node l r) ++ ns 
      ? specFlatten' (Node l r) ns 
  ==. (flatten l ++ flatten r) ++ ns 
  ==. flatten l ++ (flatten r ++ ns) 
      ? assoc (flatten l) (flatten r) ns 
  ==. flatten l ++ (flatten' r ns)
      ? specFlatten' r ns
  ==. flatten' l (flatten' r ns) 
      ? specFlatten' l (flatten' r ns)
  ^^^ Defined 


-------------------------------------------------------------------------------
-- | Helpers: Definitions & Theorems Used -------------------------------------
-------------------------------------------------------------------------------

data Tree = Leaf Int | Node Tree Tree 

{-@ data Tree [size] @-}

{-@ lazy size @-}
{-@ measure size @-}
{-@ size :: Tree -> Nat @-} 
size :: Tree -> Int 
size (Leaf _) = 1 
size (Node l r) = 1 + size l + size r 

{-@ reflect flatten @-}
flatten :: Tree -> [Int]
flatten (Leaf n)   = [n]
flatten (Node l r) = flatten l ++ flatten r  



