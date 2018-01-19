{-@ LIQUID "--exactdc" @-}
{-@ LIQUID "--higherorder" @-}
{-@ LIQUID "--automatic-instances=liquidinstanceslocal" @-}
{-@ infix   ++ @-}

module Reverse where

import Prelude hiding (reverse, (++))
import Lib.Derivations

-------------------------------------------------------------------------------
-- | Specification of reverse' ------------------------------------------------
-------------------------------------------------------------------------------

{-@ specReverse' :: xs:[a] -> ys:[a] 
                 -> {reverse' xs ys = reverse xs ++ ys} @-}
specReverse' :: [a] -> [a] -> ()
specReverse' _ _ = undefined   

-------------------------------------------------------------------------------
-- | Derivation of reverse' ---------------------------------------------------
-------------------------------------------------------------------------------

reverse' :: [a] -> [a] -> [a]
{-@ reverse' :: xs:[a] -> ys:[a] -> { reverse' xs ys = reverse xs ++ ys } @-}
reverse' [] ys 
  =   reverse [] ++ ys 
  ==? [] ++ ys ? specReverse' [] ys 
  ==. ys 
  ^^^ Defined 


reverse' (x:xs) ys 
  =   reverse (x:xs) ++ ys  
  ==? (reverse xs ++ [x]) ++ ys ? specReverse' (x:xs) ys
  ==? reverse xs ++ ([x] ++ ys) ? assoc (reverse xs) [x] ys
  ==. reverse xs ++ (x:ys) 
  ==. reverse' xs (x:ys)
  ^^^ Defined 

-------------------------------------------------------------------------------
-- | Helpers: Definitions & Theorems Used -------------------------------------
-------------------------------------------------------------------------------

{-@ reflect reverse @-}
reverse :: [a] -> [a]
reverse []     = []
reverse (x:xs) = reverse xs ++ [x]

{-@ reflect ++ @-}
(++) :: [a] -> [a] -> [a]
[]     ++ ys = ys
(x:xs) ++ ys = x:(xs ++ ys)


{-@ automatic-instances assoc @-}
{-@ assoc :: xs:[a] -> ys:[a] -> zs:[a] 
          -> { xs ++ (ys ++ zs) == (xs ++ ys) ++ zs }  @-}
assoc :: [a] -> [a] -> [a] -> () 
assoc [] _ _       = ()
assoc (x:xs) ys zs = assoc xs ys zs



