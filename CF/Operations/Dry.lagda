\begin{code}
open import Prelude

open import CF.Syntax
open import CF.Operations.Base using (ch; fgt)

module CF.Operations.Dry where
\end{code}

begin{code}
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
end{code}

\begin{code}
  drop : {n : ℕ}{t : T n}{ty : U n}
        → (i k : ℕ) → ElU ty t
        → ElU ty (tel-drop i k t)
  drop {t = []}     i j x       = x
  drop {t = t ∷ ts} i zero x    = x
  drop {t = t ∷ ts} i (suc k) x = fgt i (drop (suc i) k x)  
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
