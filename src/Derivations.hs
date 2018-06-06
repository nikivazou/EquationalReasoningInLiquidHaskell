{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--structural" @-}
{-@ LIQUID "--automatic-instances=liquidinstanceslocal" @-}
{-@ infix   ++ @-}
{-@ infix   :  @-}

module Derivations where 

import Lists 
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

data Tree = Leaf Int | Node Tree Tree 

{-@ reflect flatten @-}
flatten :: Tree -> [Int]
flatten (Leaf n)   = [n]
flatten (Node l r) = flatten l ++ flatten r



flattenApp :: Tree -> [Int] -> [Int]
{-@ flattenApp :: t:Tree -> ns:[Int] -> {v:[Int] | v = flatten t ++ ns } @-}
flattenApp (Leaf n) ns 
  =   flatten (Leaf n) ++ ns  
  ==. [n] ++ ns 
  ==. n:([] ++ ns)
  ==. [] ++ (n:ns)
  ==. n:ns

flattenApp (Node l r) ns
  =   flatten (Node l r) ++ ns 
  ==. (flatten l ++ flatten r) ++ ns 
      ? assocP (flatten l) (flatten r) ns 
  ==. flatten l ++ (flatten r ++ ns) 
  ==. flatten l ++ (flattenApp r ns)
  ==. flattenApp l (flattenApp r ns) 


flatten' :: Tree -> [Int]
{-@ flatten' :: l:Tree -> {v:[Int] | v = flatten l } @-}
flatten' l 
  =   flatten l 
      ? rightIdP (flatten l)
  ==. flatten l ++ [] 
  ==. flattenApp l []

