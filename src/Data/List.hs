{-# LANGUAGE CPP #-}
{-@ LIQUID "--exactdc" @-}
{-@ LIQUID "--higherorder" @-}
{-@ LIQUID "--automatic-instances=liquidinstanceslocal" @-}

module Data.List where

import Prelude hiding (reverse, (++), length)
import Lib.Derivations  

{-@ measure length @-}
{-@ length :: [a] -> Nat @-} 
length :: [a] -> Int 
length []     = 0 
length (_:xs) = 1 + length xs

{-@ infix   : @-}
{-@ reflect reverse @-}
{-@ reverse :: is:[a] -> {os:[a] | length is == length os} @-}
reverse :: [a] -> [a]
reverse []     = []
reverse (x:xs) = reverse xs ++ [x]

{-@ infix   ++ @-}
{-@ reflect ++ @-}
{-@ (++) :: xs:[a] -> ys:[a] -> {os:[a] | length os == length xs + length ys} @-}
(++) :: [a] -> [a] -> [a]
[]     ++ ys = ys
(x:xs) ++ ys = x:(xs ++ ys)


singletonP :: a -> Proof
{-@ singletonP :: x:a -> { reverse [x] == [x] } @-}
singletonP x
  =   reverse [x]
  ==. reverse [] ++ [x]
  ==. [] ++ [x]
  ==. [x]
  *** QED 


singleton42P :: Proof
{-@ singleton42P :: { reverse [42] == [42] } @-}
singleton42P
  =   reverse [42] ? singletonP 42 
  ==. [42]
  *** QED 


{-@ involutionP :: xs:[a] -> {reverse (reverse xs) == xs } @-}
involutionP :: [a] -> Proof 
involutionP [] 
  =   reverse (reverse []) 
      -- applying inner reverse
  ==. reverse []
      -- applying reverse
  ==. [] 
  *** QED 
involutionP (x:xs) 
  =   reverse (reverse (x:xs))
      -- applying inner reverse
  ==. reverse (reverse xs ++ [x])
      ? distributivityP (reverse xs) [x]
  ==. reverse [x] ++ reverse (reverse xs) 
      ? involutionP xs 
  ==. reverse [x] ++ xs 
      ? singletonP x 
  ==. [x] ++ xs
      -- applying append on []
  ==. x:([]++ xs)
      -- applying ++
  ==. (x:xs)
  *** QED 



distributivityP :: [a] -> [a] -> Proof
{-@ distributivityP :: xs:[a] -> ys:[a] -> {reverse (xs ++ ys) == reverse ys ++ reverse xs} @-}
distributivityP [] ys
  =   reverse ([] ++ ys)
  ==. reverse ys 
       ? leftIdP (reverse ys) 
  ==. reverse ys ++ []
  ==. reverse ys ++ reverse []
  *** QED 
distributivityP (x:xs) ys 
  =   reverse ((x:xs) ++ ys)
  ==. reverse (x:(xs ++ ys))
  ==. reverse (xs ++ ys) ++ [x]
       ? distributivityP xs ys 
  ==. (reverse ys ++ reverse xs) ++ [x]
       ? assoc (reverse ys) (reverse xs) [x]
  ==. reverse ys ++ (reverse xs ++ [x])
  ==. reverse ys ++ reverse (x:xs)
  *** QED 


{-@ automatic-instances leftIdP @-}
leftIdP :: [a] -> Proof
{-@ leftIdP :: xs:[a] -> { xs ++ [] == xs } @-}
leftIdP []     = ()
leftIdP (_:xs) = leftIdP xs 


{-@ automatic-instances assoc @-}
{-@ assoc :: xs:[a] -> ys:[a] -> zs:[a] 
          -> { xs ++ (ys ++ zs) == (xs ++ ys) ++ zs }  @-}
assoc :: [a] -> [a] -> [a] -> () 
assoc [] _ _       = ()
assoc (x:xs) ys zs = assoc xs ys zs