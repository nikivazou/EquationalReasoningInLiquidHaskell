Related Work
------------

The equational proofs presented in this document are inductive proofs
about terminating Haskell functions, so it is straightforward to
reproduce them in most general-purpose theorem provers.

**Coq** [Coq](https://coq.inria.fr/) is the prototypical
example of a theorem prover based on dependent types. We could use Coq
to prove that the list append operator is associative as follows:
\begin{spec}
  Theorem app_assoc : forall l1 l2 l3 : natlist,
    (l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3).
  Proof.
    intros l1 l2 l3.
    induction l1 as [| n l1' IHl1'].
    - reflexivity.
    - simpl. rewrite -> IHl1'. reflexivity.
  Qed.
\end{spec}

This proof resembles the PLE-enabled version of the Liquid Haskell
proof presented in [Section 2](02-Reasoning-About-Programs.html).
However, while the proof in Liquid Haskell can be easily expanded to
show all steps in an equational-reasoning style, there is no
straightforward way to do the same in Coq.
Moreover, to reason about Haskell code in Coq, we must first translate
our Haskell code into Coq's programming language, Gallina.

While the recently developed tool [hs-to-coq](https://github.com/antalsz/hs-to-coq) can automate this
translation, Haskell programmers still have to learn Coq to actually prove
results about the translated code.
By contrast, equational reasoning in Liquid Haskell allows the users
to reason about their Haskell code while expressing their proofs using
Haskell's syntax and semantics.

Coq is not without [its benefits](https://nikivazou.github.io/static/Haskell17/a-tale.pdf), however.
Coq provides an extensive standard library of theorems, interactive
proof assistance, and a tiny trusted code base, all of which are
currently lacking from Liquid Haskell.
Of course, these benefits are not limited to Coq.
We could similarly port our code, theorems, and proofs to other
dependently-typed languages, like [Idris](https://www.idris-lang.org/) and [F*](https://www.fstar-lang.org/).

**Isabelle** We can use proofs based on higher-order logic,
such as [Isabelle](https://isabelle.in.tum.de/). Isabelle’s powerful automation based on term
rewriting requires us to merely indicate the right induction principle:
\begin{spec}
  lemma app_assoc:
    "(xs ++ ys) ++ zs = xs ++ (ys ++ zs)"
    by (induction xs) auto
\end{spec}
This proofs resembles the concise PLE version of the Liquid Haskell proof.
Isabelle’s language for declarative proofs, Isar, supports equational
reasoning, and if we want, we can spell out the proof in full detail:
\begin{spec}
  lemma app_assoc:
    "(xs ++ ys) ++ zs = xs ++ (ys ++ zs)"
  proof(induction xs)
    case Nil
    have "([] ++ ys) ++ zs = ys ++ zs" by simp
    also have "... = [] ++ (ys ++ zs)" by simp
    finally show ?case.
  next
    case (Cons x xs)
    have "(x:xs ++ ys) ++ zs = x:(xs ++ ys) ++ zs"
      by simp
    also have "... = x:xs ++ (ys ++ zs)"
      by (simp add: Cons.IH)
    also have "... = (x:xs) ++ (ys ++ zs)" by simp
    finally show ?case.
  qed
\end{spec}
Each equational step is verified by Isabelle, using its term rewriting engine
`simp`; the use of the inductive hypothesis (`Cons.IH`) is clearly marked.

The tool Haskabelle can translate Haskell function definitions into
Isabelle.

**Other theorem provers**
Support for equational reasoning in this style is also built into [Lean](https://leanprover.github.io/), a general semi-automated theorem prover
and [Dafny](https://rise4fun.com/dafny), an imperative programming language with built-in
support for specification and verification using SMT solvers, where this
feature is called [verified calculations](https://pdfs.semanticscholar.org/eb11/6f8567b33b0e2092d3da6003f4b13c1c590d.pdf).

Operator-based Equational Reasoning
------------------------------------

The support for equational reasoning in Isabelle, Lean and Dafny is built into
their syntax, while in Liquid Haskell, the operators for equational reasoning
can be provided by a library. This is highly inspired by Agda.

[Agda](http://wiki.portal.chalmers.se/agda/pmwiki.php) is a general theorem prover based on dependent type theory. Its type system and syntax is flexible enough to allow the library-defined operator

\begin{spec}
  _≡⟨_⟩_ :∀ (x {y z} : A) -> x ≡ y -> y ≡ z -> x ≡ z
\end{spec}
which expresses an equality together with its proof. 
Observe the similarity between Liquid Haskell's `(==.)` operator.

\begin{spec}
  a ≡⟨explanation⟩ b     -- Agda
  a ==. b ? explanation  -- Liquid Haskell
\end{spec}

One disadvantages of the operator-based equational reasoning in Liquid Haskell over built-in support like in, say, Dafny is that there each equation is checked independently, whereas Liquid Haskell checks all equalities in one function at once, which can be slower.


While the above tools allow equational reasoning, Liquid Haskell is
unique in extending an existing, general-purpose programming language
to support theorem proving.
This makes Liquid Haskell a more natural choice for verifying Haskell
code, both because it is familiar to Haskell programmers, and
because it does not require porting code to a separate verification
language.

Verification in Haskell
-----------------------

Liquid Haskell is far from the first attempt to bring theorem proving
to Haskell.
[Zeno](https://hackage.haskell.org/package/zeno) generates proofs by term
rewriting and [Halo](https://dl.acm.org/citation.cfm?id=2429121&dl=ACM&coll=DL) uses an axiomatic
encoding to verify contracts.
Both these tools are automatic, but unpredictable and not
programmer-extensible, which has limited them to verifying much
simpler properties than the ones checked here.
Another tool, [HERMIT](http://hackage.haskell.org/package/hermit), proves equalities by rewriting
the GHC core language, guided by user specified scripts.
Compared to these tools, 
in Liquid Haskell the proofs are Haskell programs
while SMT solvers are used to automate reasoning.

Haskell itself is [dependently typed](https://cs.brynmawr.edu/~rae/papers/2016/thesis/eisenberg-thesis.pdf), where inductive proofs can be encoded as type class constraints.
However, proofs in dependent Haskell do not have the
straightforward equational-reasoning style that Liquid Haskell allows
and are not SMT-aided.

