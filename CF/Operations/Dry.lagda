\begin{code}
open import Prelude

open import CF.Syntax
open import CF.Operations.Base using (ch; fgt)

module CF.Operations.Dry where
\end{code}

  The operations in CF.Operations.Base have a "permeable"
  traversal. Note the following cases for ch:

    > ...
    > ch i       (red el) = map unpop (ch (suc i) el)
    > ch zero    (top el) = pop el ∷ []
    > ch (suc i) (top el) = map pop (ch i el)
    > ...

  We say that the children at level i of a (red el : ElU (def F x) t)
  is just the children at level (i + 1) of (el : ElU F (x ∷ t))
  Later on, when the function actually gets to a variable,
  (pattern matches on top) it decides whether to return this specific
  term or to traverse deeper.

  Analogously, we could have defined a "dry" version of children:

    > ...
    > ch' i       (red el)
    >    =  map unpop (ch' (suc i) el) ++ map (ch' i) (ch' 0 el)
    > ch' zero    (top el) = pop el ∷ []
    > ch' (suc i) (top el) = []
    > ...

  Here, we are saying that the children' i of (red el) are
  the children' (i + i) of el AND the children' i
  of the children' 0 of el.

  It is not very complicated to see that both ways of traversing the
  term will yield the same result. The first one beeing
  much more "pattern-matching" friendly; for why we choose
  it as the base version.

  For messing with derivatives, however, we need to estabilish some
  relations between these traversals; as the definition of derivatives
  uses a "dry" approach (the reason for this being that the permeable traverssal
  only works if we also have the telescope at hand, but the derivative is
  an operation defined over ∀ n . U n → U n).

\begin{code}
  drop : {n : ℕ}{t : T n}{ty : U n}
          → (i k : ℕ) → ElU ty t
          → ElU ty (tel-drop i k t)
  drop i k unit    = unit
  drop i k (inl x) = inl (drop i k x)
  drop i k (inr x) = inr (drop i k x)
  drop i k (x , y) = drop i k x , drop i k y
  drop i k (mu x)           = mu  (drop (suc i) k x)
  drop i k (red x)          = red (drop (suc i) k x)
  drop zero zero    (top x) = top x
  drop zero (suc k) (top x) = top unit
  drop (suc i) k    (top x) = top (drop i k x)
  drop zero zero    (pop x) = pop x
  drop zero (suc k) (pop x) = pop (drop 0 k x)
  drop (suc i) k    (pop x) = pop (drop i k x)  
\end{code}

Compute the "dry arity" of a given variable i in a term x.
  That is, how many "direct" arrows to i we have in our arrow diagram.

  Rephrasing, how many times a term of type (tel-lkup i) appear directly, dry,
  in x. Not counting the amount of times it appears as variable (i-1) in the
  variable 0 of x.

\begin{code}
  {-# TERMINATING #-}
  ar-dry : {n : ℕ}{t : T n}{ty : U n}
         → (i : ℕ)(x : ElU ty t) → ℕ
  ar-dry i unit    = 0
  ar-dry i (inl x) = ar-dry i x
  ar-dry i (inr x) = ar-dry i x
  ar-dry i (x , y) = ar-dry i x + ar-dry i y
  ar-dry i (mu x)
    = ar-dry (suc i) x + sum (map (ar-dry (suc i)) (ch 0 x)) 
  ar-dry i (red x)
    = ar-dry (suc i) x + sum (map (ar-dry (suc i)) (ch 0 x))
  ar-dry zero    (top x) = 1
  ar-dry (suc i) (top x) = 0
  ar-dry zero    (pop x) = 0
  ar-dry (suc i) (pop x) = ar-dry i x
\end{code}

\begin{code}
  {-# TERMINATING #-}
  ch-dry : {n : ℕ}{t : T n}{ty : U n}
         → (i : ℕ)(x : ElU ty t) → List (ElU (tel-lkup i t) (tel-drop 0 i t))
  ch-dry i unit = []
  ch-dry i (inl x) = ch-dry i x
  ch-dry i (inr x) = ch-dry i x
  ch-dry i (x , y) = ch-dry i x ++ ch-dry i y
  ch-dry i (mu x)
    = map unpop (ch-dry (suc i) x)
    ++ concat (map (ch-dry i ∘ unpop) (ch-dry 0 x))
  ch-dry i (red x)
    = map unpop (ch-dry (suc i) x)
    ++ concat (map (ch-dry i ∘ unpop) (ch-dry 0 x))
  ch-dry zero    (top x) = pop x ∷ []
  ch-dry (suc i) (top x) = []
  ch-dry zero    (pop x) = []
  ch-dry (suc i) (pop x) = map pop (ch-dry i x)
\end{code}
