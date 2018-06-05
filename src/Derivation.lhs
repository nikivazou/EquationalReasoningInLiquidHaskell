\begin{code}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--automatic-instances=liquidinstanceslocal" @-}
{-@ infix   ++ @-}

module Derivation where 

-- import Lists 
import Prelude hiding (reverse, (++), length)
import Language.Haskell.Liquid.Equational

{-@ reverseApp :: xs:[a] -> ys:[a] -> {zs:[a] | zs == reverse xs ++ ys} @-}
reverseApp :: [a] -> [a] -> [a]
reverseApp [] ys
  =   reverse [] ++ ys
  ==. [] ++ ys
  ==. ys

reverseApp (x:xs) ys
  =   reverse (x:xs) ++ ys
  ==. (reverse xs ++ [x]) ++ ys
  ==. reverse xs ++ [x] ++ ys    
      ? assocP (reverse xs) [x] ys
  ==. reverseApp xs ([x] ++ ys)
  ==. reverseApp xs (x:([] ++ ys))
  ==. reverseApp xs (x:ys)

{-@ reverse' :: xs:[a] -> {v:[a] | v == reverse xs } @-}
reverse' :: [a] -> [a]
reverse' xs 
  =   reverse xs 
    ? rightIdP (reverse xs)
  ==. reverse xs ++ [] 
  ==. reverseApp xs []  
\end{code}


Repeating code from `Lists`
\begin{code}
{-@ measure length @-}
{-@ length :: [a] -> Nat @-} 
length :: [a] -> Int 
length []     = 0 
length (_:xs) = 1 + length xs

{-@ reflect ++ @-}
{-@ (++) :: xs:[a] -> ys:[a] -> {os:[a] | length os == length xs + length ys} @-}
(++) :: [a] -> [a] -> [a]
[]     ++ ys = ys
(x:xs) ++ ys = x:(xs ++ ys)


{-@ reflect reverse @-}
{-@ reverse :: is:[a] -> {os:[a] | length is == length os} @-}
reverse :: [a] -> [a]
reverse []     = []
reverse (x:xs) = reverse xs ++ [x]

{-@ ple rightIdP @-}
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

{-@ ple assocP @-}
{-@ assocP :: xs:[a] -> ys:[a] -> zs:[a] 
          -> { xs ++ (ys ++ zs) == (xs ++ ys) ++ zs }  @-}
assocP :: [a] -> [a] -> [a] -> () 
assocP [] _ _       = ()
assocP (x:xs) ys zs = assocP xs ys zs
\end{code}
