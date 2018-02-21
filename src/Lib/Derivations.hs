{-# LANGUAGE CPP #-}
#ifdef InlineProofCombinators
#else  
module Lib.Derivations where 
#endif

type Proof = ()

data QED = QED 

infixl 2 ***
x *** QED = () 

data Defined = Defined
infixl 2 ^^^
x ^^^ Defined = x 

{-# INLINE (^^^) #-} 
infixl 3 ==., ? 

(?) :: a -> Proof -> a 
x ? _ = x 

{-@ (==.) :: x:a -> y:{a | x == y} -> {v:a | v == y && v == x} @-}
(==.) :: a -> a -> a 
_ ==. x = x 

{-# INLINE (?)   #-} 
{-# INLINE (==.) #-} 

