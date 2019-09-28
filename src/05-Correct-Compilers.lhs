Case Study: Correct Compilers
------------------------------

So far, all the proofs we have seen have been very simple.  To show
that Liquid Haskell scales to more involved arguments, we
show how it can be used to calculate a correct and efficient compiler
for arithmetic expressions with addition, as in [Graham's book](http://www.cs.nott.ac.uk/~pszgmh/pih.html).

\begin{code}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple-local" @-}
{-@ infix    :   @-}
{-@ infixl 1 >>= @-}
{-@ infixr 5 ++  @-}

module Compiler where

import Prelude hiding ((++), Monad(..))
import Language.Haskell.Liquid.Equational
\end{code}

We begin by defining an expression as an integer value or the
addition of two expressions, and a function that returns the
integer value of such an expression:

\begin{code}
data Expr = Val Int | Add Expr Expr 

{-@ reflect eval @-}
eval :: Expr -> Int 
eval (Val n)   = n 
eval (Add x y) = eval x + eval y
\end{code}


A simple stack machine
-----------------------

The target for our compiler will be a simple stack-based machine.
In this setting, a stack is simply a list of integers, and code for the machine
is a list of push and add operations that manipulate the stack:

\begin{code}
type Stack = [Int]
type Code  = [Op] 
data Op    = PUSH Int | ADD 
\end{code}

The meaning of such code is given by a function that executes
a piece of code on an initial stack to give a final stack:

\begin{spec}
exec :: Code -> Stack -> Stack
exec []         s       = s
exec (PUSH n:c) s       = exec c (n:s)
exec (ADD:c)    (m:n:s) = exec c (n+m:s)
\end{spec}

That is, `PUSH` places a new integer on the top of the stack,
while `ADD` replaces the top two integers by their sum.

A note on totality
--------------------

The function `exec` is not total --- in particular, the result of
executing an `ADD` operation on a stack with fewer than two
elements is undefined.  Like most proof systems, Liquid Haskell
requires all functions to be total in order to preserve soundness.
There are a number of ways we can get around this problem, such as:

- Using Haskell's `Maybe` type to express the possibility
of failure directly in the type of the `exec` function.

- Adding a refinement to `exec` to specify that it can only
be used with ``valid'' code and stack arguments.

- Arbitrarily defining how `ADD` operates on a small stack,
for example by making it a no-operation.

- Using dependent types to specify the stack demands of each
operation in our language. For example, we could
specify that `ADD` transforms a stack of length $n+2$ to a stack of
length $n+1$.

For simplicity, we adopt the first approach here, and rewrite
`exec` as a total function that returns `Nothing` in the case of
failure, and `Just s` in the case of success:


\begin{code}
{-@ reflect exec @-}
exec :: Code -> Stack -> Maybe Stack
exec []         s       = Just s
exec (PUSH n:c) s       = exec c (n:s)
exec (ADD:c)    (m:n:s) = exec c (n+m:s)
exec _          _       = Nothing
\end{code}



Compilation
------------

We now want to define a compiler from expressions to code.
The property that we want to ensure is that executing the resulting
code will leave the value of the expression on top of the stack.
Using this property, it is clear that an integer value should be
compiled to code that simply pushes the value onto the stack, while
addition can be compiled by first compiling the two argument
expressions, and then adding the resulting two values:

\begin{code}
{-@ reflect comp @-}
comp :: Expr -> Code
comp (Val n)   = [PUSH n]  
comp (Add x y) = comp x ++ comp y ++ [ADD] 
\end{code}

Note that when an add operation is performed, the value of the
expression `y` will be on top of the stack and the value of 
expression `x` will be below it, hence the swapping of these
two values in the definition of the `exec` function.


Correctness
------------

The correctness of the compiler for expressions is expressed by the
following equation:
\begin{spec}
exec (comp e) [] == Just [eval e]
\end{spec}

That is, compiling an expression and executing the resulting 
code on an empty stack always succeeds, and leaves the value of
the expression as the single item on the stack.  In order to 
prove this result, however, we will find that it is necessary
to generalize to an arbitrary initial stack:

\begin{spec}
  exec (comp e) s == Just (eval e : s)
\end{spec}

We prove correctness of the compiler in Liquid Haskell by
defining a function `generalizedCorrectnessP` with a
refinement type specification that encodes the above equation.
We define the body of this function by recursion on the type
`Expr`, which is similar to induction for the type `Tree` 
[before](04-Function-Optimization.html).  We begin as before by expanding definitions:

\begin{spec}
{-@ generalizedCorrectnessP 
  :: e:Expr -> s:Stack
  -> {exec (comp e) s == Just (eval e:s)} @-}
generalizedCorrectnessP 
  :: Expr -> Stack -> Proof
generalizedCorrectnessP (Val n) s
  =   exec (comp (Val n)) s
  ==. exec [PUSH n] s
  ==. exec [] (n:s)
  ==. Just (n:s)
  ==. Just (eval (Val n):s)
  *** QED

generalizedCorrectnessP (Add x y) s
  =   exec (comp (Add x y)) s 
  ==. exec (comp x ++ comp y ++ [ADD]) s
\end{spec}

That is, we complete the proof for `Val` by simply expanding
definitions while for `Add` we quickly reach a point where 
we need to think further.  Intuitively, we require a lemma
which states that executing code of the form `c ++ d` would give
the same result as executing `c` and then executing `d`:

\begin{spec}
  exec (c ++ d) s = exec d (exec c s)
\end{spec}

Unfortunately, this doesn't typecheck, because `exec`
takes a `Stack` but returns a `Maybe Stack`.  What we need is
some way to run `exec d` only if `exec c` succeeds.  Fortunately,
this already exists in Haskell --- it's just monadic bind for
the `Maybe` type, which we reflect in Liquid Haskell as follows:

\begin{code}
infixl 3 >>=
{-@ reflect >>= @-}
(>>=) :: Maybe a -> (a -> Maybe b) -> Maybe b
(Just x) >>= f = f x
Nothing  >>= _ = Nothing
\end{code}

We can now express our desired lemma using bind

\begin{spec}
  exec (c ++ d) s = exec c s >>= exec d
\end{spec}

and its proof proceeds by straightforward structural induction
on the first code argument, with separate cases for success and
failure of an addition operator:

\begin{code}
{-@ sequenceP :: c:Code -> d:Code -> s:Stack ->
     {exec (c ++ d) s = exec c s >>= exec d} @-}
sequenceP :: Code -> Code -> Stack -> Proof
sequenceP [] d s 
  =   exec ([] ++ d) s
  ==. exec d s
  ==. (Just s >>= exec d)
  ==. (exec [] s >>= exec d)
  *** QED

sequenceP (PUSH n:c) d s 
  =   exec ((PUSH n:c) ++ d) s
  ==. exec (PUSH n:(c ++ d)) s
  ==. exec (c ++ d) (n:s)
      ? sequenceP c d (n:s)
  ==. (exec c (n:s) >>= exec d)
  ==. (exec (PUSH n:c) s >>= exec d)
  *** QED
    
sequenceP (ADD:c) d (m:n:s)
  =   exec ((ADD:c) ++ d) (m:n:s)
  ==. exec (ADD:(c ++ d)) (m:n:s)
  ==. exec (c ++ d) (n + m:s)
      ? sequenceP c d (n + m:s)
  ==. (exec c (n + m:s) >>= exec d)
  ==. (exec (ADD:c) (m:n:s) >>= exec d)
  *** QED

sequenceP (ADD:c) d s 
  =   exec ((ADD:c) ++ d) s
  ==. exec (ADD:(c ++ d)) s
  ==. Nothing
  ==. (Nothing >>= exec d)
  ==. exec (ADD:c) s >>= exec d
  *** QED
\end{code}

With this lemma in hand, we can complete the `Add` case of
our `generalizedCorrectnessP` proof:
%
\begin{code}
{-@ generalizedCorrectnessP 
  :: e:Expr -> s:Stack
  -> {exec (comp e) s == Just (eval e:s)} @-}
generalizedCorrectnessP 
  :: Expr -> Stack -> Proof
generalizedCorrectnessP (Val n) s
  =   exec (comp (Val n)) s
  ==. exec [PUSH n] s
  ==. exec [] (n:s)
  ==. Just (n:s)
  ==. Just (eval (Val n):s)
  *** QED

generalizedCorrectnessP (Add x y) s
  =   exec (comp (Add x y)) s
  ==. exec (comp x ++ comp y ++ [ADD]) s
  ? sequenceP (comp x) (comp y ++ [ADD]) s
  ==. (exec (comp x) s >>= exec (comp y ++ [ADD]))
  ? generalizedCorrectnessP x s
  ==. (Just (eval x:s) >>= exec (comp y ++ [ADD]))
  ==. exec (comp y ++ [ADD]) (eval x:s)
  ? sequenceP (comp y) [ADD] (eval x:s)
  ==. (exec (comp y) (eval x:s) >>= exec [ADD])
  ? generalizedCorrectnessP y (eval x:s)
  ==. (Just (eval y:eval x:s) >>= exec [ADD])
  ==. exec [ADD] (eval y:eval x:s)
  ==. exec [] (eval x + eval y:s)
  ==. Just (eval x + eval y:s)
  ==. Just (eval (Add x y):s)
  *** QED
\end{code}

Now that we have proven a generalized version of our correctness
theorem, we can recover the original theorem by replacing the
arbitrary state `s` by the empty state `[]`:

\begin{code}
{-@ correctnessP :: e:Expr ->
      {exec (comp e) [] == Just [eval e]} @-}
correctnessP :: Expr -> Proof
correctnessP e = generalizedCorrectnessP e []
\end{code}


A faster compiler
-------------------

Notice that like `reverse` and `flatten`, our compiler uses the append operator
`(++)` in the recursive case.  This means that our compiler can be optimized.
We can use the same strategy as we used for `reverse` and `flatten` to derive
an optimized version of `comp`.

We begin by defining a function `compApp` with the property
`compApp e c == comp e ++ c`.  As previously, we proceed from this
property by expanding definitions and applying lemmata to obtain
an optimized version:

\begin{code}
{-@ reflect compApp @-}
{-@ compApp :: e:Expr -> c:Code ->
      {d:Code | d == comp e ++ c} @-}
compApp (Val n) c
  =    comp (Val n) ++ c
  ==.  [PUSH n] ++ c
  ==.  PUSH n:([] ++ c)
  ==.  PUSH n:c
  `eq` PUSH n:c

compApp (Add x y) c 
  =    comp (Add x y) ++ c
  ==.  (comp x ++ comp y ++ [ADD]) ++ c
       ? appAssocP (comp x) (comp y ++ [ADD]) c
  ==.  comp x ++ (comp y ++ [ADD]) ++ c 
       ? appAssocP (comp y) [ADD] c
  ==.  comp x ++ comp y ++ [ADD] ++ c 
  ==.  comp x ++ comp y ++ ADD:([] ++ c)
  ==.  comp x ++ comp y ++ ADD:c
  ==.  comp x ++ compApp y (ADD:c)
  ==.  compApp x (compApp y (ADD:c))
  `eq` compApp x (compApp y (ADD:c))
\end{code}

**Note:** We conclude the definitions by `eq`
to tell Liquid Haskell to reflect the definitions of `compApp` using only the 
last equality. In the imported library `Equational` we define `eq _ x = x`. 
But, `eq` is special in that Liquid Haskell knows that the translation of `eq p x`
in the logic in only `x`.

Similarly, the Haskell compiler automatically optimizes away all the equational
reasoning steps to derive the following definition for `compApp`,
which no longer makes use of append:

\begin{spec}
compApp :: Expr -> Code -> Code 
compApp (Val n)   c = PUSH n:c
compApp (Add x y) c =
  compApp x (compApp y (ADD:c))
\end{spec}

From this definition, we can construct the optimized compiler
by supplying the empty list as the second argument:

\begin{code}
{-@ reflect comp' @-}
comp' :: Expr -> Code
comp' e = compApp e []
\end{code}

In turn, we can then prove that new compiler `comp'` is equivalent to
the original version `comp`, and is hence correct:

\begin{code}
{-@ equivP :: e:Expr -> {comp' e == comp e} @-}
equivP e 
  =   comp' e
  ==. compApp e []
  ==. comp e ++ [] ? appRightIdP (comp e)
  ==. comp e 
  *** QED

{-@ equivCorrectnessP :: e:Expr ->
      {exec (comp' e) [] == Just [eval e]} @-}
equivCorrectnessP e =
  exec (comp' e) []    ? equivP e
  ==. exec (comp e) [] ? correctnessP e
  ==. Just [eval e]    
  *** QED
\end{code}

However, we can also prove the correctness of `comp'` without using
`comp` at all --- and it turns out that this proof is much simpler.
Again, we generalize our statement of correctness, this time to any
initial stack and any additional code:

\begin{spec}
  exec (compApp e c) s = exec c (cons (eval e) s)
\end{spec}

We can then prove this new correctness theorem by induction
on the structure of the expression argument:

\begin{code}
{-@ generalizedCorrectnessP' 
      :: e:Expr -> s:Stack -> c:Code ->
           { exec (compApp e c) s ==
             exec c (cons (eval e) s)} @-}
generalizedCorrectnessP' 
      :: Expr -> Stack -> Code -> Proof
generalizedCorrectnessP' (Val n) s c
  =   exec (compApp (Val n) c) s
  ==. exec (PUSH n:c) s
  ==. exec c (n:s)
  ==. exec c (eval (Val n):s)
  *** QED

generalizedCorrectnessP' (Add x y) s c 
  =   exec (compApp (Add x y) c) s
  ==. exec (compApp x (compApp y (ADD:c))) s
      ? generalizedCorrectnessP' x s 
         (compApp y (ADD:c))
  ==. exec (compApp y (ADD:c)) (eval x:s)
      ? generalizedCorrectnessP' y (eval x:s) 
         (ADD:c)
  ==. exec (ADD:c) (eval y:eval x:s)
  ==. exec c (eval x + eval y:s)
  ==. exec c (eval (Add x y):s)
  *** QED
\end{code}

Finally, we recover our original correctness theorem by specializing
both the stack `s` and code `c` to empty lists:

\begin{code}
{-@ correctnessP' :: e:Expr ->
      {exec (comp' e) [] == Just [eval e]} @-}
correctnessP' :: Expr -> Proof
correctnessP' e 
  =   exec (comp' e) []
  ==. exec (compApp e []) []
      ? generalizedCorrectnessP' e [] []
  ==. exec [] [eval e] 
  ==. Just [eval e]
  *** QED
\end{code}

In summary, there are two key benefits to our new compiler.  First
of all, it no longer uses append, and is hence more efficient.
And secondly, its correctness proof no longer requires the
`sequenceP` lemma, and is hence simpler and more concise.  Counterintuitively,
code optimized using Liquid Haskell can be easier to prove correct,
not harder!

Appendix
---------
Since the **online demo** does not let us import functions, 
we close by repeating the required function definitions 
and theorems on lists. 

\begin{code}
infixr 5 ++
{-@ reflect ++ @-}
(++) :: [a] -> [a] -> [a]
[] ++ ys = ys
(x:xs) ++ ys = x:(xs ++ ys)

{-@ ple appRightIdP @-}
{-@ appRightIdP :: xs:[a] -> {xs ++ [] = xs} @-}
appRightIdP :: [a] -> Proof 
appRightIdP []     = ()
appRightIdP (_:xs) = appRightIdP xs

{-@ ple appAssocP @-}
{-@ appAssocP :: xs:[a] -> ys:[a] -> zs:[a] -> {(xs ++ ys) ++ zs = xs ++ ys ++ zs} @-}
appAssocP :: [a] -> [a] -> [a] -> Proof 
appAssocP [] _ _ = ()
appAssocP (_:xs) ys zs = appAssocP xs ys zs
\end{code}
