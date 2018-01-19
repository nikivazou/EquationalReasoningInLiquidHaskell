{-@ LIQUID "--exactdc" @-}
{-@ LIQUID "--higherorder" @-}
{-@ LIQUID "--automatic-instances=liquidinstanceslocal" @-}
{-@ infix   ++ @-}

module Reverse where

import Prelude hiding (reverse, (++))
import Language.Haskell.Liquid.ProofCombinators

-------------------------------------------------------------------------------
-- | Specification of reverse' ------------------------------------------------
-------------------------------------------------------------------------------

{-@ specReverse' :: xs:[a] -> ys:[a] 
                 -> {reverse' xs ys = reverse xs ++ ys} @-}
specReverse' :: [a] -> [a] -> Proof
specReverse' _ _ = undefined   

-------------------------------------------------------------------------------
-- | Derivation of reverse' ---------------------------------------------------
-------------------------------------------------------------------------------

derivationReverse' :: [a] -> [a] -> Proof 
{-@ derivationReverse' :: xs:[a] -> ys:[a] -> { reverse' xs ys = reverse xs ++ ys } @-}
derivationReverse' [] ys 
  =   reverse' [] ys 
  ==. reverse [] ++ ys ? specReverse' [] ys 
  ==. [] ++ ys 
  ==. ys 
  ^^^ Defined 
derivationReverse' (x:xs) ys 
  =   reverse' (x:xs) ys
  ==. reverse (x:xs) ++ ys ? specReverse' (x:xs) ys 
  ==. (reverse xs ++ [x]) ++ ys
  ==. reverse xs ++ ([x] ++ ys) ? assoc (reverse xs) [x] ys
  ==. reverse xs ++ (x:ys) 
  ==. reverse' xs (x:ys)    ? derivationReverse' xs (x:ys) 
  ^^^ Defined 

-------------------------------------------------------------------------------
-- | Goal: Automatic Derivation of reverse' -----------------------------------
-------------------------------------------------------------------------------

{-@ reflect reverse' @-}
reverse' :: [a] -> [a] -> [a]
reverse' [] ys     = ys 
reverse' (x:xs) ys = reverse' xs (x:ys)


-------------------------------------------------------------------------------
-- | Helpers: Definitions & Theorems Used -------------------------------------
-------------------------------------------------------------------------------


data Defined = Defined
infixl 2 ^^^
_ ^^^ Defined = ()   

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
assoc :: [a] -> [a] -> [a] -> Proof 
assoc [] _ _       = ()
assoc (x:xs) ys zs = assoc xs ys zs



