\begin{code}
open import Prelude
open import CF.Syntax
open import CF.Operations.Mu

module CF.Measures where
\end{code}

  It will be convenient to have some generic measures
  over our universe.

%<*countU>
\begin{code}
  countU : {n : ℕ} → Fin n → U n → ℕ
  countU i u0 = 0
  countU i u1 = 0
  countU i (a ⊕ b) = countU i a + countU i b
  countU i (a ⊗ b) = countU i a + countU i b
  countU i (def F x) = countU i x + countU (fs i) F
  countU i (μ u) = countU (fs i) u
  countU fz var = 1
  countU (fs i) var = 0
  countU fz (wk u) = 0
  countU (fs i) (wk u) = countU i u
\end{code}
%</countU>

%<*sizeU>
\begin{code}
  sizeU : {n : ℕ} → U n → ℕ
  sizeU u0 = 0
  sizeU u1 = 1
  sizeU (a ⊕ b) = sizeU a + sizeU b
  sizeU (a ⊗ b) = sizeU a * sizeU b
  sizeU (def F x) = sizeU x * countU fz F + sizeU F
  sizeU (μ u) = sizeU u
  sizeU var = 1
  sizeU (wk u) = sizeU u
\end{code}
%</sizeU>

\begin{code}
  {-# TERMINATING #-}
\end{code}
%<*sizeEl>
\begin{code}
  sizeElU : {n : ℕ}{t : T n}{u : U n} → ElU u t → ℕ
  sizeElU unit        = 1
  sizeElU (inl el)    = 1 + sizeElU el
  sizeElU (inr el)    = 1 + sizeElU el
  sizeElU (ela , elb) = sizeElU ela + sizeElU elb
  sizeElU (top el)    = sizeElU el
  sizeElU (pop el)    = sizeElU el
  sizeElU (mu el)
    = let (hdE , chE) = μ-open (mu el)
      in sizeElU hdE + foldr _+_ 0 (map sizeElU chE)
  sizeElU (red el)    = sizeElU el
\end{code}
%</sizeEl>

