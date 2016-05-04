\begin{code}
open import Prelude
open import Prelude.Vector

open import CF.Syntax
open import CF.Operations.Base using (ch; fgt)

module CF.Operations.Dry where
\end{code}

\begin{code}
  drop : {n : ℕ}{t : T n}{ty : U n}
          → (i : ℕ) → ElU ty t
          → ElU ty (tel-drop i t)
  drop {t = []} i x           = x
  drop {t = t ∷ ts} zero x    = x
  drop {t = t ∷ ts} (suc i) x = fgt i (drop i x)
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
