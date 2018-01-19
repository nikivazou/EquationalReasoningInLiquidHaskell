{-@ LIQUID "--exactdc" @-}
{-@ LIQUID "--higherorder" @-}
{-@ LIQUID "--automatic-instances=liquidinstanceslocal" @-}
{-@ infix   ++ @-}

module Reverse where

import Prelude hiding (reverse, (++))

-------------------------------------------------------------------------------
-- | Specification of reverse' ------------------------------------------------
-------------------------------------------------------------------------------

{-@ specReverseOpt :: xs:[a] -> ys:[a] 
                 -> {reverseOpt xs ys = reverse xs ++ ys} @-}
specReverseOpt :: [a] -> [a] -> ()
specReverseOpt _ _ = undefined   

-------------------------------------------------------------------------------
-- | Derivation of reverse' ---------------------------------------------------
-------------------------------------------------------------------------------

-- LH TODO: LH is not letting you define a measure and a Haskell function
-- with the same name, for now...
{-@ measure reverseOpt :: [a] -> [a] -> [a] @-}
reverse' :: [a] -> [a] -> [a]
{-@ reverse' :: xs:[a] -> ys:[a] -> { reverseOpt xs ys = reverse xs ++ ys } @-}
reverse' [] ys 
  =   reverse [] ++ ys 
  ==? [] ++ ys ? specReverseOpt [] ys 
  ==. ys 
  ^^^ Defined 


reverse' (x:xs) ys 
  =   reverse (x:xs) ++ ys  
  ==? (reverse xs ++ [x]) ++ ys ? specReverseOpt (x:xs) ys
  ==? reverse xs ++ ([x] ++ ys) ? assoc (reverse xs) [x] ys
  ==. reverse xs ++ (x:ys) 
  ==. reverse' xs (x:ys)
  ^^^ Defined 

data Defined = Defined
infixl 2 ^^^
x ^^^ Defined = x 

{-# INLINE (^^^) #-} 
infixl 3 ==?, ==., ? 

f ? x = f x 
_ ==. x = x 
(==?) _ _ x = x 
{-# INLINE (?)   #-} 
{-# INLINE (==.) #-} 
{-# INLINE (==?) #-} 


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



