{-# LANGUAGE TemplateHaskell #-}
{-# OPTIONS_GHC -O -fplugin Test.Inspection.Plugin #-}
module InspectionTests where

import Prelude hiding (reverse, (++), length)

import Lib.Derivations
import Data.List

import Test.Inspection


reverse' :: [a] -> [a] -> [a]
reverse' [] ys
  =   reverse [] ++ ys
  ==. [] ++ ys
  ==. ys
  ^^^ Defined

reverse' (x:xs) ys
  =   reverse (x:xs) ++ ys
  ==. (reverse xs ++ [x]) ++ ys
      ? assoc (reverse xs) [x] ys
  ==. reverse xs ++ [x] ++ ys
  ==. reverse' xs ([x] ++ ys)
  ==. reverse' xs (x:([] ++ ys))
  ==. reverse' xs (x:ys)
  ^^^ Defined

reverse2 :: [a] -> [a] -> [a]
reverse2 [] ys = ys
reverse2 (x:xs) ys = reverse2 xs (x:ys)

inspect $ 'reverse' === 'reverse2
