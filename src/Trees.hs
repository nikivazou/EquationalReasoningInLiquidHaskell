{-@ LIQUID "--exactdc" @-}
{-@ LIQUID "--higherorder" @-}
{-@ LIQUID "--automatic-instances=liquidinstanceslocal" @-}
{-@ infix   ++ @-}

module Trees where

import Prelude hiding ((++))
import Lib.Derivations

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

flatten' :: Tree -> [Int] -> [a]
{-@ flatten' :: t:Tree -> ns:[Int] -> {flatten' t ns = flatten t ++ ns} @-}
flatten' = undefined 


-------------------------------------------------------------------------------
-- | Helpers: Definitions & Theorems Used -------------------------------------
-------------------------------------------------------------------------------

data Tree = Leaf Int | Node Tree Tree 

{-@ reflect flatten @-}
flatten :: Tree -> [Int]
flatten (Leaf n)   = [n]
flatten (Node l r) = flatten l ++ flatten r  


{-@ reflect ++ @-}
(++) :: [a] -> [a] -> [a]
[]     ++ ys = ys
(x:xs) ++ ys = x:(xs ++ ys)




