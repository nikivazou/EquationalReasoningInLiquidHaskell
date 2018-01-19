{-@ LIQUID "--exactdc" @-}
{-@ LIQUID "--higherorder" @-}

{-# LANGUAGE CPP #-}

module Reverse where

import Prelude hiding (reverse, (++))

import Data.List 
{-@ infix   ++ @-}

-- Lib included instead of imported to allow for inlining
#include "Lib/Derivations.hs"   

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
  =   reverse [] ++ ys ? specReverse' [] ys 
  ==. [] ++ ys 
  ==. ys 
  ^^^ Defined 


reverse' (x:xs) ys 
  =   reverse (x:xs) ++ ys    
      ? specReverse' (x:xs) ys
  ==. (reverse xs ++ [x]) ++ ys 
      ? assoc (reverse xs) [x] ys
  ==. reverse xs ++ ([x] ++ ys) 
  ==. reverse xs ++ (x:ys) 
  ==. reverse' xs (x:ys)
  ^^^ Defined 
