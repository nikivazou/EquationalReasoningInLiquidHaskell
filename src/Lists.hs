{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--automatic-instances=liquidinstanceslocal" @-}

module Lists where

import Prelude hiding (reverse, (++), length)
{-@ infix   : @-}
import Language.Haskell.Liquid.Equational

-- | Linear Arithmetic

{-@ measure length @-}
{-@ length :: [a] -> Nat @-} 
length :: [a] -> Int 
length []     = 0 
length (_:xs) = 1 + length xs

{-@ infix   ++ @-}
{-@ reflect ++ @-}
{-@ (++) :: xs:[a] -> ys:[a] -> {os:[a] | length os == length xs + length ys} @-}
(++) :: [a] -> [a] -> [a]
[]     ++ ys = ys
(x:xs) ++ ys = x:(xs ++ ys)

-- | Deep Reasoning


{-@ reflect reverse @-}
{-@ reverse :: is:[a] -> {os:[a] | length is == length os} @-}
reverse :: [a] -> [a]
reverse []     = []
reverse (x:xs) = reverse xs ++ [x]

singletonP :: a -> Proof
{-@ singletonP :: x:a -> { reverse [x] == [x] } @-}
singletonP x
  =   reverse [x]
  ==. reverse [] ++ [x]
  ==. [] ++ [x]
  ==. [x]
  *** QED 


singleton1P :: Proof
{-@ singleton1P :: { reverse [1] == [1] } @-}
singleton1P
  =   reverse [1] 
      ? singletonP 1 
  ==. [1]
  *** QED 

-- | Induction on Lists

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
       ? assocP (reverse ys) (reverse xs) [x]
  ==. reverse ys ++ (reverse xs ++ [x])
  ==. reverse ys ++ reverse (x:xs)
  *** QED 

-- | Proof Automation

{-@ rightIdP :: xs:[a] -> { xs ++ [] == xs } @-}
rightIdP :: [a] -> Proof
rightIdP []     
  =   [] ++ [] 
  ==. [] 
  *** QED 
rightIdP (x:xs)
  =   (x:xs) ++ [] 
  ==. x : (xs ++ [])
      ? rightIdP xs
  ==. x : xs
  *** QED

{-@ ple leftIdP @-}
leftIdP :: [a] -> Proof
{-@ leftIdP :: xs:[a] -> { xs ++ [] == xs } @-}
leftIdP []     = ()
leftIdP (_:xs) = leftIdP xs 

{-@ ple assocP @-}
{-@ assocP :: xs:[a] -> ys:[a] -> zs:[a] 
          -> { xs ++ (ys ++ zs) == (xs ++ ys) ++ zs }  @-}
assocP :: [a] -> [a] -> [a] -> () 
assocP [] _ _       = ()
assocP (x:xs) ys zs = assocP xs ys zs

