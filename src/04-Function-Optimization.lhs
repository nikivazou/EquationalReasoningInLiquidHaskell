Function Optimization
---------------------

Equational reasoning is not only useful to verify existing code, it can also be
used to derive new, more performant function definitions from specifications.

\begin{code}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--structural" @-}
{-@ LIQUID "--automatic-instances=liquidinstanceslocal" @-}
{-@ infix   ++ @-}

module Derivation where 

-- import Lists 
import Prelude hiding (reverse, (++), length)
import Language.Haskell.Liquid.Equational
\end{code}


Example: Reversing a List
---------------------------

The `reverse` function that we defined in [before](02-Reasoning-About-Programs.html) was simple and easy
to reason about, but it is rather inefficient.  In particular, for each element in
the input list, `reverse` appends it to the end of the reversed tail of the list:
%
\begin{spec}
  reverse (x:xs) = reverse xs ++ [x]
\end{spec}
%
Because the runtime of `++` is linear in the length of its first argument,
the runtime of `reverse` is quadratic.  For example, reversing a list of ten thousand
elements would take around fifty million reduction steps, which is excessive.


To improve the performance, we would like to define a function that does the
reversing and appending *at the same time*; that is, to define a new function

\begin{code}
reverseApp :: [a] -> [a] -> [a]
\end{code}

that reverses its first argument and appends its second. We can express this as
a Liquid Haskell specification:
\begin{code}
{-@ reverseApp :: xs:[a] -> ys:[a] ->
     {zs:[a] | zs == reverse xs ++ ys} @-}
\end{code}

We now seek to derive an implementation for `reverseApp` that satisfies this
specification and is efficient.

**Step 0: Specification**
We begin by writing a definition for `reverseApp` that trivially satisfies
the specification and is hence accepted by Liquid Haskell, but is not yet efficient:

\begin{code}
{-@ reverseApp0 :: xs:[a] -> ys:[a] ->
       {zs:[a] | zs == reverse xs ++ ys} @-}
reverseApp0 :: [a] -> [a] -> [a]
reverseApp0 xs ys = reverse xs ++ ys
\end{code}

We then seek to improve the definition for `reverseApp`
in step-by-step manner, using Liquid Haskell's equational
reasoning facilities to make sure that we don't make any
mistakes, *i.e.,* that we do not violate the specification.


**Step 1: Case Splitting**
Most likely, the function has to analyse its argument, so let us
pattern match on the first argument `xs` and update the
right-hand side accordingly:

\begin{code}
{-@ reverseApp1 :: xs:[a] -> ys:[a] ->
       {zs:[a] | zs == reverse xs ++ ys} @-}
reverseApp1 :: [a] -> [a] -> [a]
reverseApp1 []     ys = reverse []     ++ ys
reverseApp1 (x:xs) ys = reverse (x:xs) ++ ys
\end{code}

Liquid Haskell ensures that our pattern match is total, and that we
updated the right-hand side correctly.

**Step 2: Equational Rewriting**
Now we want to rewrite the right-hand sides of `reverseApp` to more efficient
forms, while ensuring that our function remains correct.  To do so, we
can use the the `(==.)`operator to show that each change we make gives us the
same function.  Whenever we add a line, Liquid Haskell confirms
that this step is valid.  We begin by simply expanding definitions:

\begin{code}
reverseApp [] ys
  =   reverse [] ++ ys
  ==. [] ++ ys
  ==. ys
reverseApp (x:xs) ys
  =   reverse (x:xs) ++ ys
  ==. (reverse xs ++ [x]) ++ ys
\end{code}

At this point, we have expanded as much as we can, but `reverseApp` still
uses the original, inefficient `reverse` functions, so we are not done.
However, we proved at the end of [Section 2](02-Reasoning-About-Programs.html) that append is
associative, so we can use this fact to transform `(reverse xs ++ [x]) ++ ys`
into `reverse xs ++ ([x] ++ ys)`, and then continue expanding:
\begin{code}
  ==. (reverse xs ++ [x]) ++ ys
         ? assocP (reverse xs) [x] ys
  ==. reverse xs ++ ([x] ++ ys)
  ==. reverse xs ++ (x:([] ++ ys))
  ==. reverse xs ++ (x:ys)
\end{code}

We're still using `reverse`, so we're not quite done.  To finish
the definition, we just need to observe that the last line has the
form `reverse as ++ bs` for some lists `as` and `bs`.  This is
precisely the form of the specification for `reverseApp as bs`, so
we can rewrite the last line in terms of `reverseApp`:

\begin{code}
  ==. reverse xs ++ (x:ys)
  ==. reverseApp xs (x:ys)
\end{code}

In summary, our definition for `reverseApp` no longer mentions
the `reverse` function or the append operator.  Instead, it
contains a recursive call to `reverseApp`, which means we have
derived the following, self-contained definition:

\begin{spec}
reverseApp :: [a] -> [a] -> [a]
reverseApp []     ys = ys
reverseApp (x:xs) ys = reverseApp xs (x:ys)
\end{spec}

The runtime performance of this definition is linear in the length
of its first argument, a significant improvement.

**Step 4: Optimizing reverse**
The goal of this exercise was of course not to have an efficient
reverse-and-append function, but to have an efficient reverse function.  
However, we can define this using `reverseApp`, again starting from its
specification and deriving the code that we want to run. Here we need
to turn `reverse xs` into `reverse xs ++ ys` for some list `ys`. This
requires us to use the theorem `rightIdP`:

\begin{code}
{-@ reverse' :: xs:[a] ->
      {v:[a] | v == reverse xs } @-}
reverse' :: [a] -> [a]
reverse' xs 
  =   reverse xs
      ? rightIdP (reverse xs)
  ==. reverse xs ++ []
  ==. reverseApp xs []
\end{code}

The above derivation follows the same steps as the pen-and-paper
version in [Graham's book](http://www.cs.nott.ac.uk/~pszgmh/pih.html), with one key difference: the correctness
of each step, and the derived program, is now automatically
checked by Liquid Haskell.

Example: Flattening a Tree
---------------------------

We can use the same technique to derive an optimized function for
flattening trees.  Our trees are binary trees with integers
in the leaves, as in [Graham's book](http://www.cs.nott.ac.uk/~pszgmh/pih.html):

\begin{code}
data Tree = Leaf Int | Node Tree Tree
\end{code}

We wish to define an efficient function that flattens such a
tree to a list.  As with `reverse`, we begin with a simple but
inefficient version that uses the append operator:

\begin{code}
{-@ reflect flatten @-}
flatten :: Tree -> [Int]
flatten (Leaf n)   = [n]
flatten (Node l r) = flatten l ++ flatten r
\end{code}

Because we want to refer to this function in our specifications
and reasoning, we instruct Liquid Haskell to lift it to the
refinement type level using `reflect` keyword.
Liquid Haskell’s structural termination checker
accepts this and all following functions on
trees, and there is no need to define a measure on trees.

We can use `flatten` as the basis of a specification for a more efficient
version.  As before, the trick is to combine `flatten` with list
appending and define a function

\begin{code}
flattenApp :: Tree -> [Int] -> [Int]
\end{code}

with the specification `flattenApp t ns == flatten t ++ ns`, which we can state
as a Liquid Haskell type signature:

\begin{code}
{-@ flattenApp :: t:Tree -> ns:[Int] ->
      {v:[Int] | v == flatten t ++ ns } @-}
\end{code}

As in the previous example, we begin by using the specification as
a correct but inefficient implementation

\begin{code}
{-@ flattenApp0 :: t:Tree -> ns:[Int] ->
      {v:[Int] | v == flatten t ++ ns } @-}
flattenApp0 :: Tree -> [Int] -> [Int]
flattenApp0 t ns = flatten t ++ ns
\end{code}

and use equational reasoning in Liquid Haskell to work our way
towards an implementation that avoids the use of the inefficient
`flatten` and append functions:

\begin{code}
flattenApp (Leaf n) ns 
  =   flatten (Leaf n) ++ ns
  ==. [n] ++ ns
  ==. n:([] ++ ns)
  ==. n:ns
flattenApp (Node l r) ns 
  =   flatten (Node l r) ++ ns
  ==. (flatten l ++ flatten r) ++ ns
      ? assocP (flatten l) (flatten r) ns
  ==. flatten l ++ (flatten r ++ ns)
  ==. flatten l ++ (flattenApp r ns)
  ==. flattenApp l (flattenApp r ns)
\end{code}

Again, this derivation serves both as an implementation and a
verification, and is operationally equivalent to:

\begin{spec}
flattenApp :: Tree -> [Int] -> [Int]
flattenApp (Leaf n)   ns = n:ns
flattenApp (Node l r) ns =
  flattenApp l (flattenApp r ns)
\end{spec}

Finally, we can then derive the optimized flatten function by means
of the following simple reasoning:

\begin{code}
{-@ flatten' :: t:Tree ->
      {v:[Int] | v == flatten t} @-}
flatten' :: Tree -> [Int]
flatten' l 
  =   flatten l
      ? rightIdP (flatten l)
  ==. flatten l ++ []
  ==. flattenApp l []
\end{code}

In conclusion, the derivation once again follows the same steps as
the original pen-and-paper version, but is now mechanically checked
for correctness.

Appendix
---------
Since the **online demo** does not let us import functions, 
we close by repeating the required function definitions 
and theorems on lists. 

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
rightIdP []     = () 
rightIdP (_:xs) = rightIdP xs

{-@ ple assocP @-}
{-@ assocP :: xs:[a] -> ys:[a] -> zs:[a] 
          -> { xs ++ (ys ++ zs) == (xs ++ ys) ++ zs }  @-}
assocP :: [a] -> [a] -> [a] -> () 
assocP [] _ _       = ()
assocP (x:xs) ys zs = assocP xs ys zs
\end{code}
