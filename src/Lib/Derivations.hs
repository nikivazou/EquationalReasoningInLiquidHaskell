-- module Lib.Derivations where


data Defined = Defined
infixl 2 ^^^
x ^^^ Defined = x 

{-# INLINE (^^^) #-} 
infixl 3 ==., ? 

x ? _ = x 

(==.) :: a -> a -> a 
_ ==. x = x 

{-# INLINE (?)   #-} 
{-# INLINE (==.) #-} 

