module Lib.Derivations where


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

