{-@ LIQUID "--exactdc" @-}
{-@ LIQUID "--higherorder" @-}

{-# LANGUAGE CPP #-}

module ReverseNoAssume where

import Prelude hiding (reverse, (++), length)

import Data.List 
{-@ infix   ++ @-}

-- Lib included instead of imported to allow for inlining
-- #define InlineProofCombinators
-- #include "Lib/Derivations.hs"   

import Lib.Derivations

-------------------------------------------------------------------------------
-- | Starting with an inefficent reverse'
-------------------------------------------------------------------------------

{-@ reverse1' :: xs:[a] -> ys:[a] -> {zs:[a] | zs == reverse xs ++ ys} @-}
reverse1' :: [a] -> [a] -> [a]
reverse1' xs ys = reverse xs ++ ys

-------------------------------------------------------------------------------
-- | Doing the case split
-------------------------------------------------------------------------------

{-@ reverse2' :: xs:[a] -> ys:[a] -> {zs:[a] | zs == reverse xs ++ ys} @-}
reverse2' :: [a] -> [a] -> [a]
reverse2' [] ys = reverse [] ++ ys
reverse2' (x:xs) ys = reverse (x:xs) ++ ys

-------------------------------------------------------------------------------
-- | Completing the base case
-------------------------------------------------------------------------------

{-@ reverse3' :: xs:[a] -> ys:[a] -> {zs:[a] | zs == reverse xs ++ ys} @-}
reverse3' :: [a] -> [a] -> [a]
reverse3' [] ys
  =   reverse [] ++ ys
  ==. [] ++ ys
  ==. ys
  ^^^ Defined
reverse3' (x:xs) ys = reverse (x:xs) ++ ys

-------------------------------------------------------------------------------
-- | Working on the inductive case (just to show that we can check any intermediate step)
-------------------------------------------------------------------------------

{-@ reverse4' :: xs:[a] -> ys:[a] -> {zs:[a] | zs == reverse xs ++ ys} @-}
reverse4' :: [a] -> [a] -> [a]
reverse4' [] ys
  =   reverse [] ++ ys
  ==. [] ++ ys
  ==. ys
  ^^^ Defined
reverse4' (x:xs) ys
  =   reverse (x:xs) ++ ys
  ==. (reverse xs ++ [x]) ++ ys
  ^^^ Defined

-------------------------------------------------------------------------------
-- | More work on the inductive case (includes the recursive call)
-------------------------------------------------------------------------------

{-@ reverse5' :: xs:[a] -> ys:[a] -> {zs:[a] | zs == reverse xs ++ ys} @-}
reverse5' :: [a] -> [a] -> [a]
reverse5' [] ys
  =   reverse [] ++ ys
  ==. [] ++ ys
  ==. ys
  ^^^ Defined
reverse5' (x:xs) ys
  =   reverse (x:xs) ++ ys
  ==. (reverse xs ++ [x]) ++ ys
  ==. reverse xs ++ [x] ++ ys    ? assoc (reverse xs) [x] ys
  ==. reverse5' xs ([x] ++ ys)
  ^^^ Defined

-------------------------------------------------------------------------------
-- | The final thing
-------------------------------------------------------------------------------

{-@ reverse' :: xs:[a] -> ys:[a] -> {zs:[a] | zs == reverse xs ++ ys} @-}
reverse' :: [a] -> [a] -> [a]
reverse' [] ys
  =   reverse [] ++ ys
  ==. [] ++ ys
  ==. ys
  ^^^ Defined

reverse' (x:xs) ys
  =   reverse (x:xs) ++ ys
  ==. (reverse xs ++ [x]) ++ ys
  ==. reverse xs ++ [x] ++ ys    ? assoc (reverse xs) [x] ys
  ==. reverse' xs ([x] ++ ys)
  ==. reverse' xs (x:([] ++ ys))
  ==. reverse' xs (x:ys)
  ^^^ Defined
