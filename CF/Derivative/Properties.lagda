\begin{code}
open import Prelude
open import Prelude.Vector
open import CF.Syntax
open import CF.Operations
open import CF.Derivative
open import CF.Derivative.Operations

module CF.Derivative.Properties where
\end{code}

\begin{code}
  δ-ar-lemma : {n : ℕ}{t : T n}{ty : U (suc n)}
             → (x : ElU ty (μ ty ∷ t))
             → length (δ 0 x) ≡ ar 0 x
  δ-ar-lemma unit = {!!}
  δ-ar-lemma (inl x) = {!!}
  δ-ar-lemma (inr x) = {!!}
  δ-ar-lemma (x , x₁) = {!!}
  δ-ar-lemma (top x) = {!!}
  δ-ar-lemma (pop x) = {!!}
  δ-ar-lemma (mu x) = {!!}
  δ-ar-lemma (red x₁) = {!!}
