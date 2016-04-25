\begin{code}
open import Prelude
open import Prelude.Vector

open import CF.Syntax

module CF.Operations where
\end{code}

\begin{code}
  ch : {n : ℕ}{t : T n}{ty : U n}
         → (i : ℕ) → ElU ty t
         → List (ElU (tel-lkup i t) t)
  ch i unit        = []
  ch i (inl el)    = ch i el
  ch i (inr el)    = ch i el
  ch i (ela , elb) = ch i ela ++ ch i elb
  ch i (mu el)     = map unpop (ch (suc i) el)
  ch i (red el)    = map unpop (ch (suc i) el)
  ch zero    (top el) = pop el ∷ []
  ch (suc i) (top el) = map pop (ch i el)
  ch zero    (pop el) = []
  ch (suc i) (pop el) = map pop (ch i el)
\end{code}

\begin{code}
  fgt : {n : ℕ}{t : T n}{ty : U n}
      → (i : ℕ) → ElU ty t
      → ElU ty (tel-forget i t)
  fgt i unit        = unit
  fgt i (inl el)    = inl (fgt i el)
  fgt i (inr el)    = inr (fgt i el)
  fgt i (ela , elb) = fgt i ela , fgt i elb
  fgt i (mu el)     = mu (fgt (suc i) el)
  fgt i (red el)    = red (fgt (suc i) el)
  fgt zero    (top el) = top unit
  fgt (suc i) (top el) = top (fgt i el)
  fgt zero    (pop el) = pop el
  fgt (suc i) (pop el) = pop (fgt i el)
\end{code}

\begin{code}
  ar : {n : ℕ}{t : T n}{ty : U n}
     → ℕ → ElU ty t → ℕ
  ar i unit        = 0
  ar i (inl el)    = ar i el
  ar i (inr el)    = ar i el
  ar i (ela , elb) = ar i ela + ar i elb
  ar i (mu el)     = ar (suc i) el
  ar i (red el)    = ar (suc i) el
  ar zero    (top el) = 1
  ar (suc i) (top el) = ar i el
  ar zero    (pop el) = 0
  ar (suc i) (pop el) = ar i el
\end{code}

\begin{code}
  ar* : {n : ℕ}{t : T n}{ty : U n}
      → (i : ℕ) → List (ElU ty t) → ℕ
  ar* i []       = 0
  ar* i (x ∷ xs) = ar i x + ar* i xs
\end{code}

\begin{code}
  ar*v : {n k : ℕ}{t : T n}{ty : U n}
       → (i : ℕ) → Vec (ElU ty t) k → ℕ
  ar*v i []       = 0
  ar*v i (x ∷ xs) = ar i x + ar*v i xs
\end{code}

