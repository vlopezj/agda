..
  ::
  module language.function-definitions where

  open import language.built-ins

.. _function-definitions:

********************
Function Definitions
********************


Introduction
============

A function is defined by first declaring its type followed by a number of
equations called *clauses*. Each clause consists of the function being defined
applied to a number of *patterns*, followed by ``=`` and a term called the
*right-hand side*. For example:
::

  not : Bool → Bool
  not true  = false
  not false = true

Functions are allowed to call themselves recursively, for example:
::

  twice : Nat → Nat
  twice zero    = zero
  twice (suc n) = suc (suc (twice n))

General form
============

The general form for defining a function is

.. code-block:: agda

 f : (x₁ : A₁) → … → (xₙ : Aₙ) → B
 f p₁ … pₙ = d
 …
 f q₁ … qₙ = e

where ``f`` is a new identifier, ``pᵢ`` and ``qᵢ`` are patterns of type ``Aᵢ``,
and ``d`` and ``e`` are expressions.

The declaration above gives the identifier ``f`` the type
``(x₁ : A₁) → … → (x₁ : A₁) → B`` and ``f`` is defined by the defining
equations. Patterns are matched from top to bottom, i.e., the first pattern
that matches the actual parameters is the one that is used.

By default, Agda checks the following properties of a function definition:

- The patterns in the left-hand side of each clause should consist only of
  constructors and variables.
- No variable should occur more than once on the left-hand side of a single
  clause.
- The patterns of all clauses should together cover all possible inputs of
  the function.
- The function should be terminating on all possible inputs, see
  :ref:`termination-checking`.

Special patterns
================

In addition to constructors consisting of constructors and variables, Agda
supports two special kinds of patterns: dot patterns and absurd patterns.

.. _dot-patterns:

Dot patterns
------------

A dot pattern (also called *inaccessible pattern*) can be used when
the only type-correct value of the argument is determined by the
patterns given for the other arguments.
The syntax for a dot pattern is ``.t``.

As an example, consider the datatype ``Square`` defined as follows
::

  data Square : Nat → Set where
    sq : (m : Nat) → Square (m * m)

Suppose we want to define a function ``root : (n : Nat) → Square n → Nat`` that
takes as its arguments a number ``n`` and a proof that it is a square, and
returns the square root of that number. We can do so as follows:
::

  root : (n : Nat) → Square n → Nat
  root .(m * m) (sq m) = m

Notice that by matching on the argument of type ``Square n`` with the constructor
``sq : (m : Nat) → Square (m * m)``, ``n`` is forced to be equal to ``m * m``.

In general, when matching on an argument of type ``D i₁ … iₙ`` with a constructor
``c : (x₁ : A₁) → … → (xₘ : Aₘ) → D j₁ … jₙ``, Agda will attempt to unify
``i₁ … iₙ`` with ``j₁ … jₙ``. When the unification algorithm instantiates a
variable ``x`` with value ``t``, the corresponding argument of the function
can be replaced by a dot pattern ``.t``. Using a dot pattern is optional, but
can help readability. The following are also legal definitions of
``root``:

Since Agda 2.4.2.4::

  root₁ : (n : Nat) → Square n → Nat
  root₁ _ (sq m) = m

Since Agda 2.5.2::

  root₂ : (n : Nat) → Square n → Nat
  root₂ n (sq m) = m

In the case of ``root₂``, ``n`` evaluates to ``m * m`` in the body of the
function and is thus equivalent to

::

  root₃ : (n : Nat) → Square n → Nat
  root₃ _ (sq m) = let n = m * m in m

.. _absurd-patterns:

Absurd patterns
---------------

Absurd patterns can be used when none of the constructors for a particular
argument would be valid. The syntax for an absurd pattern is ``()``.

As an example, if we have a datatype ``Even`` defined as follows
::

  data Even : Nat → Set where
    even-zero  : Even zero
    even-plus2 : {n : Nat} → Even n → Even (suc (suc n))

then we can define a function ``one-not-even : Even 1 → ⊥`` by using an absurd
pattern:
::

  one-not-even : Even 1 → ⊥
  one-not-even ()

Note that if the left-hand side of a clause contains an absurd pattern, its
right-hand side must be omitted.

In general, when matching on an argument of type ``D i₁ … iₙ`` with an absurd
pattern, Agda will attempt for each constructor
``c : (x₁ : A₁) → … → (xₘ : Aₘ) → D j₁ … jₙ`` of the datatype ``D`` to unify
``i₁ … iₙ`` with ``j₁ … jₙ``. The absurd pattern will only be accepted if all
of these unifications end in a conflict.

As-patterns
-----------

As-patterns (or ``@-patterns``) can be used to name a pattern. The name has the
same scope as normal pattern variables (i.e. the right-hand side, where clause,
and dot patterns). The name reduces to the value of the named pattern. For example::

  module _ {A : Set} (_<_ : A → A → Bool) where
    merge : List A → List A → List A
    merge xs [] = xs
    merge [] ys = ys
    merge xs@(x ∷ xs₁) ys@(y ∷ ys₁) =
      if x < y then x ∷ merge xs₁ ys
               else y ∷ merge xs ys₁

As-patterns are properly supported since Agda 2.5.2.


Case trees
==========

Internally, Agda represents function definitions as *case trees*. For example,
a function definition
::

  max : Nat → Nat → Nat
  max zero    n       = n
  max m       zero    = m
  max (suc m) (suc n) = suc (max m n)

will be represented internally as a case tree that looks like this:

.. code-block:: agda

  max m n = case m of
    zero   -> n
    suc m' -> case n of
      zero   -> suc m'
      suc n' -> suc (max m' n')

Note that because Agda uses this representation of the function ``max``
the equation ``max m zero = m`` will not hold by definition, but must be
proven instead. Since 2.5.1 you can have Agda warn you when a situation like this
occurs by adding ``{-# OPTIONS --exact-split #-}`` at the top of your file.
