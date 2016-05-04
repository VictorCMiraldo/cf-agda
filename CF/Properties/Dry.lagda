\begin{code}
{-# OPTIONS --rewriting #-}
open import Prelude
open import Prelude.NatProperties
  using (+-comm)

open import CF.Syntax
open import CF.Operations.Base
open import CF.Operations.Dry
open import CF.Operations.Vec
open import CF.Properties.Base

module CF.Properties.Dry where
\end{code}

\begin{code}
  ar-dry-lemma
    : {n : ℕ}{t : T n}{ty : U n}
    → (i : ℕ)(x : ElU ty t)
    → ar-dry i x ≡ ar i (drop 0 i x)

  drop-ch-lemma
    : {n : ℕ}{t : T n}{ty : U n}
    → (i j : ℕ)(x : ElU ty t)
    → ar (suc i) (drop (suc j) i x)
    ≡ ar-dry (suc i) x + sum (map (ar-dry (suc i)) (ch j x))
  drop-ch-lemma i zero x = {!!}
  drop-ch-lemma i (suc j) x = {!!}

  tel-drop-lemma
    : {n : ℕ}(i j : ℕ)(a : U n)(t : T n)
    → tel-drop (suc i) j (a ∷ t) ≡ a ∷ tel-drop i j t
  tel-drop-lemma i zero a []      = refl
  tel-drop-lemma i zero a (x ∷ t) = refl
  tel-drop-lemma i (suc j) a t    = {!!}
\end{code}

begin{code}
  drop-lemma
    : {n : ℕ}{t : T n}{ty : U n}
    → (i j : ℕ)(x : ElU ty t)
    → fgt j (drop (suc j) i x) ≡ drop j i x
  drop-lemma i j unit = {!!}
  drop-lemma i j (inl x) = {!!}
  drop-lemma i j (inr x) = {!!}
  drop-lemma i j (x , x₁) = {!!}
  drop-lemma i j (top x) = {!!}
  drop-lemma i j (pop x) = {!!}
  drop-lemma i j (mu x) = {!!}
  drop-lemma i j (red x₁) = {!!}
end{code}

\begin{code}
  {-# REWRITE tel-drop-lemma #-}
  drop-mu : {n : ℕ}{t : T n}{ty : U (suc n)}
          → (i j : ℕ)(x : ElU ty (μ ty ∷ t))
          → drop i j (mu x) ≡ mu (drop (suc i) j x)
  drop-mu i zero x = {!!}
  drop-mu i (suc j) x
    = {!!}
  
\end{code}

\begin{code}
  ar-dry-lemma i unit = {!!}
  ar-dry-lemma i (inl x) = {!!}
  ar-dry-lemma i (inr x) = {!!}
  ar-dry-lemma i (x , x₁) = {!!}
  ar-dry-lemma zero (top x) = refl
  ar-dry-lemma (suc i) (top x) = {!!}
  ar-dry-lemma zero (pop x) = refl
  ar-dry-lemma (suc i) (pop x) = {!!} 
  ar-dry-lemma i (mu x)
    rewrite drop-mu 0 i x
          | ar-std-lemma (suc i) 0 (drop (suc 0) i x)
          = {!!}
  ar-dry-lemma i (red x) = {!!}
\end{code}

  rewrite 
