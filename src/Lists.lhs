Reasoning about Programs
=========================

The goal of Liquid Haskell is to move reasoning about
Haskell programs into the programs themselves and to automate this reasoning as
much as possible. It accomplishes this goal by extending the Haskell language
with refinement types, which are checked by an
external SMT solver.

\begin{code}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--automatic-instances=liquidinstanceslocal" @-}

module Lists where

import Prelude hiding (reverse, (++), length)
{-@ infix   : @-}
import Language.Haskell.Liquid.Equational
\end{code}

Lightweight Reasoning
------------------------


The power of SMT solving allows Liquid Haskell to prove certain properties
entirely automatically, with no user input; we call these *lightweight
program properties*.

1.  Linear Arithmetic

Many properties involving arithmetic can be proved automatically
in this manner.  For example, given the standard length function on lists

\begin{code}
length :: [a] -> Int 
length []     = 0 
length (_:xs) = 1 + length xs
\end{code}
we might find it useful to specify that the length of a list is never
negative. Liquid Haskell extends the syntax of Haskell by interpreting
comments of the form `{-@ ... @-}`
as declarations, using which we can express this property by:

\begin{code}
{-@ length :: [a] -> Nat @-} 
\end{code}

Liquid Haskell is able to verify this specification automatically due
to the standard refinement typing checking automated by the SMT
solver:

- In the first equation in the definition for `length`, the
value $v$ is $0$, so the SMT solver determines that $0 \leq v$.

-  In the second equation, the value $v$ is $1 + v'$, where $v'$ is
  the result of the recursive call to `length xs`.
  From the refinement type of `length`, Liquid Haskell knows $0 \leq v'$, and
  the SMT solver can deduce that $0 \leq v$.

Proving that the length of a list is nonnegative is thus fully
automated by the SMT solver.  This is because SMT solvers can efficiently
decide linear arithmetic queries, so verifying this kind of property is
tractable. Note that the refinement type does not actually *mention* the
recursive function `length`.


**Measures**
In order to allow Haskell functions to appear in refinement types, we
need to lift them to the refinement type level.  Liquid Haskell provides a
simple mechanism for performing this lifting on a particular restricted set of
functions, called *measures*.  Measures are functions which: take one
parameter, which must be an algebraic data type; are defined by a single
equation for each constructor; and whose body calls only primitive (*e.g.,*
arithmetic) functions and measures.
For this restricted class of functions, refinement types can still be checked
fully automatically.

For instance, `length` is a measure: it has one argument, is defined by one
equation for each constructor, and calls only itself and the arithmetic
operator `(+)`.  To allow `length` to appear in refinements, we declare it to
be a measure:
%
\begin{code}
{-@ measure length @-}
\end{code}

For example, we can now state that the length of two lists
appended together is the sum of their lengths:

\begin{code}
{-@ infix   ++ @-}
{-@ reflect ++ @-}
{-@ (++) :: xs:[a] -> ys:[a] -> {os:[a] | length os == length xs + length ys} @-}
(++) :: [a] -> [a] -> [a]
[]     ++ ys = ys
(x:xs) ++ ys = x:(xs ++ ys)
\end{code}

Liquid Haskell checks this refinement type in two steps:

-  In the first equation in the definition of `(++)`, the list
`xs` is empty, thus its length is `0`, and the SMT solver
can discharge this case via linear arithmetic.

- In the second equation case, the input list is known to be `x:xs`,
thus its length is `1 + length xs`.
The recursive call additionally indicates that
`length (xs ++ ys) = length xs + length ys`
and the SMT solver can also discharge this case using linear
arithmetic.

2. Deep Reasoning

We saw that because `length` is a measure, it can be lifted to the refinement
type level while retaining completely automatic reasoning. We cannot expect that for recursive functions in general, as quantifier instantiation leads to unpredictable
performance.

The append function, for example, takes two arguments, and therefore is not a measure.  If
we lift it to the refinement type level, the SMT solver will not be able to
automatically check refinements involving it.  Liquid Haskell still allows
reasoning about such functions, but this limitation means the user may have to
supply the proofs.  We call properties that the SMT solver cannot solve
entirely automatically *deep program properties*.

For example, consider the following definition for the reverse
function on lists in terms of the append function:

\begin{code}
{-@ reverse :: is:[a] -> {os:[a] | length is == length os} @-}
reverse :: [a] -> [a]
reverse []     = []
reverse (x:xs) = reverse xs ++ [x]
\end{code}

Because the definition uses append, which is not a measure, the
reverse function itself is not a measure, so reasoning about it
will not be fully automatic.

Instead, Liquid Haskell can lift arbitrary Haskell functions into the
refinement type level via the notion of
*reflection*.  Rather than using the
straightforward translation available for measures, which completely describes
the function to the SMT solver, reflection gives the SMT solver only the value
of the function for the arguments on which it is actually called.  Restricting
the information available to the SMT solver in this way ensures that checking
refinement types remains decidable.

To see this in action, we prove that reversing a singleton list
does not change it, *i.e.,* `reverse [x] == [x]`.  We first declare
`reverse` and the append function as reflected:

\begin{code}
{-@ infix   ++ @-}
{-@ reflect ++ @-}
{-@ reflect reverse @-}
\end{code}

We then introduce the function `singletonP`, whose
refinement type expresses the desired result, and whose body
provides the proof in equational reasoning style:

\begin{code}
singletonP :: a -> Proof
{-@ singletonP :: x:a -> { reverse [x] == [x] } @-}
singletonP x
  =   reverse [x]
  ==. reverse [] ++ [x]
  ==. [] ++ [x]
  ==. [x]
  *** QED 
\end{code}


We can understand this function as mapping a value `x` to a proof of
`reverse [x] = [x]`.  The type `Proof` is simply Haskell's unit type `()`, and
`{reverse [x] = x}` is syntactic sugar for `{v:() | reverse [x] = x}`, a
refinement of the unit type.
This syntax hides the irrelevant value `v :: ()`.

Note that the body of the `singletonP` function looks very much like a typical
pen-and-paper proof, such as the one in Graham's book.  The
correspondence is so close that we claim proving a property in Liquid Haskell
can be just as easy as proving it on paper by equational reasoning --- but
the proof in Liquid Haskell is machine-checked!

As always, Liquid Haskell uses an SMT solver to check this proof.  Because
the body of `singletonP` syntactically contains the three terms
`reverse [x]`, `reverse []` and `[] ++ [x]`,
Liquid Haskell passes the corresponding equations
\begin{spec}
  reverse [x] = reverse [] ++ [x]
  reverse []  = []
  [] ++ [x]   = [x]
\end{spec}
to the SMT solver, which then easily derives the desired
property `reverse [x] = [x]`.  Note that the following
definition would constitute an equally valid proof:
\begin{spec}
  singletonP x =
    const () (reverse [x], reverse [], [] ++ [x])
\end{spec}
But such a compressed ``proof'' is neither easy to come up
with directly, nor is it readable or very insightful. Therefore,
we use proof combinators to write readable equational-style
proofs, where each reasoning step is checked.



**Proof Combinators**
As already noted in the previous section, we use
Haskell's unit type to represent a proof:
\begin{spec}
  type Proof = ()
\end{spec}
This unit type is sufficient because a theorem is expressed as a
refinement on the arguments of a function. In other words, the ``value'' of a
theorem has no meaning.

Proof combinators themselves are then simply Haskell
functions, defined in in the `proof-combinators`.  The most basic 
example is the `***` function that takes any expression and ignores
its value, returning a proof:
\begin{spec}
  data QED = QED

  (***) :: a -> QED -> Proof
  _ *** QED = ()
  infixl 2 ***
\end{spec}
The `QED` argument serves a purely aesthetic purpose, allowing us
to conclude proofs with `*** QED`.


**Equational Reasoning**
The key combinator for equational reasoning is the operator `(==.)`.  Its
refinement type ensures its arguments are equal, and it returns its second
argument, so that multiple uses of `(==.)` can be chained together:
\begin{spec}
  {-@ (==.) :: x:a -> y:{a | x == y} ->
        {o:a | o == y && o == x} @-}

  (==.) :: a -> a -> a
  _ ==. x = x
\end{spec}


**Explanations**
Sometimes we need to refer to other theorems in our proofs.
Because theorems are just Haskell functions, all we need is
an operator that accepts an argument of type `Proof`, 
which is defined as follows:
\begin{spec}
  (?) :: a -> Proof -> a
  x ? _ = x
\end{spec}
For example, we can invoke the theorem `singletonP` for
the value @1@ simply by mentioning `singletonP 1` in a proof:
\begin{code}
singleton1P :: Proof
{-@ singleton1P :: { reverse [1] == [1] } @-}
singleton1P
  =   reverse [1] 
      ? singletonP 1 
  ==. [1]
  *** QED 
\end{code}

Note that although the `?` operator is suggestively placed next
to the equation that we want to justify, its placement in the proof is
actually immaterial --- the body of a function equation is checked all
at once.



Induction on Lists
------------------

Structural induction is a fundamental technique for proving properties
of functional programs.  For the list type in Haskell, the principle
of induction states that to prove that a property holds for all (finite)
lists, it suffices to show that:

- It holds for the empty list `[]` (the base case), and
- It holds for any non-empty list `x:xs` assuming it holds
for the tail `xs` of the list (the inductive case).  


Induction does not require a new proof combinator.  Instead, proofs by
induction can be expressed as recursive functions in Liquid
Haskell.  For example, let us prove that `reverse` is its own inverse,
*i.e.,* `reverse (reverse xs) == xs`.  We express this property as the
type of a function `involutionP`, whose body constitutes the proof:

\begin{code}
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
\end{code}

Because `involutionP` is a recursive function, this constitutes a proof
by induction.  The two equations for `involutionP` correspond to the two
cases of the principle of induction:

-  In the base case, because the body of the function contains
the terms `reverse (reverse [])` and `reverse []`, the corresponding 
equations are passed to the SMT solver, which then proves that
`reverse (reverse []) = []`.

-  In the inductive case, we need to show that
`reverse (reverse (x:xs)) = (x:xs)`, which
proceeds in several steps.  The validity of each step is checked
by Liquid Haskell when verifying that the refinement type of `(==.)` is satisfied.
Some of the steps follow directly from definitions, and we just add a
comment for clarity.  Other steps require external lemmas or the
inductive hypothesis, which we invoke via the explanation operator `(?)`.


We use the lemma `distributivityP`, which states that list
reversal distributes (contravariantly) over list append:
%


\begin{code}
distributivityP :: [a] -> [a] -> Proof
{-@ distributivityP :: xs:[a] -> ys:[a] -> {reverse (xs ++ ys) == reverse ys ++ reverse xs} @-}
\end{code}

Again, we define `distributivityP` as a recursive function,
as the property can be proven by induction:

\begin{code}
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
\end{code}


This proof itself requires additional lemmas about append, namely
right identity (`rightIdP`) and associativity (`assocP`), which we
tackle with further automation below.


Proof Automation
-----------------

In the proofs presented so far, we explicitly wrote every step of
a function's evaluation.  For example, in the base case of `involutionP`
we twice applied the function `reverse` to the empty list.  Writing proofs
explicitly in this way is often helpful (for instance, it makes clear
that to prove that `reverse` is an involution we need to prove that
it distributes over append) but it can quickly become tedious.

To simplify proofs, Liquid Haskell employs the complete and
terminating proof technique of *Proof By (Logical) Evaluation*
(PLE).  Conceptually, PLE executes
functions for as many steps as needed and automatically provides
all the resulting equations to the SMT solver.

Without using this technique, we could prove that the empty list
is append's right identity as follows:

\begin{code}
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
\end{code}

However, we can activate PLE in the definition of `rightIdP` using
the `ple rightIdP` annotation. This automates all the rewriting
steps, and the proof can be simplified to:

\begin{code}
{-@ ple leftIdP @-}
leftIdP :: [a] -> Proof
{-@ leftIdP :: xs:[a] -> { xs ++ [] == xs } @-}
leftIdP []     = ()
leftIdP (_:xs) = leftIdP xs 
\end{code}

That is, the base case is fully automated by PLE, while in the inductive
case we must make a recursive call to get the induction
hypothesis, but the rest is taken care of by PLE.

Using this technique we can also prove the remaining lemma, namely
the associativity of append:
\begin{code}
{-@ ple assocP @-}
{-@ assocP :: xs:[a] -> ys:[a] -> zs:[a] 
          -> { xs ++ (ys ++ zs) == (xs ++ ys) ++ zs }  @-}
assocP :: [a] -> [a] -> [a] -> () 
assocP [] _ _       = ()
assocP (x:xs) ys zs = assocP xs ys zs
\end{code}
Again, we only have to give the structure of the induction and the
arguments to the recursive call, and the PLE machinery adds
all the necessary equations to complete the proof.

PLE is a powerful tool that makes proofs shorter and easier to write.
However, proofs using this technique are usually more difficult to read, as
they hide the details of function expansion.  For this reason, while we could
apply PLE to simplify many of the proofs in this paper, we prefer to
spell out each step.  Doing so keeps our proofs easier to
understand and in close correspondence with the pen-and-paper
proofs we reference in Graham's book.