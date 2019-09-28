Totality and Termination
------------------------

At this point some readers might be concerned that using a recursive function 
to model a proof by induction is not sound if the recursive function is partial 
or non-terminating. However, Liquid Haskell also provides a powerful totality 
and termination checker and rejects any definition that it cannot prove to be 
total and terminating.

Totality Checking
------------------------

Liquid Haskell uses GHC's pattern completion mechanism to ensure that all functions
are total. For example, if the `involutionP` was only defined for the empty list case,

\begin{code}
involutionP :: [a] -> () 
involutionP [] = ()
\end{code}

then an error message would be displayed:

\begin{spec}
Your function isn't total:
  some patterns aren't defined.
\end{spec}

To achieve this result, GHC first completes the `involutionP` definition by adding a call 
to the `patError` function:

\begin{code}
involutionP' :: [a] -> ()
involutionP' [] = ()
involutionP' _  = patError "function involutionP"
\end{code}

Liquid Haskell then enables totality checking by refining the `patError` function with 
a false precondition:

\begin{code}
{-@ patError :: { i:String | false } -> a @-}
patError :: String -> a 
patError = error 
\end{code}

Because there is no argument that satisfies false, when calls to the `patError` 
function cannot be proved to be dead code, Liquid Haskell raises a totality error.



Termination Checking
------------------------

Liquid Haskell checks that all the functions are terminating, using either structural or semantic termination checking.

**Structural Termination** 
Structural termination checking is fully automatic and detects the common recursion patterns where 
the argument to the recursive call is a (direct or indirect) subterm of the original function argument 
(as seen in `length`). If the functions has multiple arguments, then at least one argument must get smaller, 
and all arguments before that must be unchanged (lexicographic order).

In fact, all recursive functions in this paper are recognized by the structural termination checker. 
This shows that language learners can do a lot before they have to deal with termination proof issues. 
Eventually, though, they will reach the limits of structural recursion, which is when they can turn to 
semantic termination.

Structural termination checking can be deactivated using the `--no-structural-termination` pragma.

**Semantic Termination** 
When the structural termination check fails, Liquid Haskell tries to prove termination using a semantic argument,
which requires an explicit termination argument: an expression that calculates a natural number 
from the function’s argument and which decreases in each recursive call. 
We can use this termination check for the proof `involutionP`, using the syntax `/ [len xs]`:

\begin{code}
{-@ involutionP'' :: xs:[a] -> () / [len xs] @-}
involutionP'' [] 
  = ()
involutionP'' (x:xs)
  = involutionP'' (x:xs)
\end{code}


Generally, a termination argument is of the form `/ [e1, ..., en]`. 
The expressions `ei` depend on the function arguments and produce natural numbers. 
They should lexicographically decrease at each recursive call. 
These proof obligations are checked by the SMT solver, together with all the refinement types 
of the function.

If the user does not specify a termination metric, but the structural termination check fails, 
Liquid Haskell tries to guess a termination metric where the first non-function argument is decreasing.

Semantic termination has two main benefits over structural termination: 
Firstly, not every function is structurally recursive (and making it structurally recursive 
by adding additional parameters can be cumbersome and cluttering). 
And secondly, since termination is checked by the SMT solver, it can make use of 
refinement properties of the inputs. 
However, semantic termination also has two main drawbacks. 
Firstly, when the termination argument is trivial, then the calls to the solver are expensive. 
And secondly, termination checking often requires to explicitly provide the termination metric, 
such as the length of an input list.


Uncaught termination
---------------------

Because Haskell is pure, the only effects it allows are divergence and incomplete patterns. 
If we rule out both these effects, using termination and totality checking, 
the user can rest assured that their functions are total, and thus correctly encode 
mathematical proofs.

Unfortunately, creative use of certain features of Haskell, 
in particular data types with non-negative recursion and higher-rank types, 
can be used to write non-terminating functions that pass Liquid Haskell’s current checks. 
Until this is fixed, users need to be careful when using such features.