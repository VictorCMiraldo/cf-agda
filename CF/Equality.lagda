\begin{code}
open import Prelude
open import CF.Syntax

module CF.Equality where
\end{code}

%<*equality-type>
\begin{code}
  _≟-U_ : {n : ℕ}{t : T n}{u : U n}
          (x y : ElU u t) → Dec (x ≡ y)
\end{code}
%</equality-type>
%<*equality-def>
\begin{code}
  _≟-U_ {u = u1} unit unit = yes refl

  _≟-U_ {u = a ⊕ b} (inl a1) (inl a2) with a1 ≟-U a2
  ...| yes p = yes (cong inl p)
  ...| no  p = no (p ∘ inj-inl)
  _≟-U_ {u = a ⊕ b} (inr b1) (inr b2) with b1 ≟-U b2
  ...| yes p = yes (cong inr p)
  ...| no  p = no (p ∘ inj-inr)
  _≟-U_ {u = a ⊕ b} (inl a1) (inr b2) = no (λ ())
  _≟-U_ {u = a ⊕ b} (inr b1) (inl a2) = no (λ ())

  _≟-U_ {u = a ⊗ b} (xa , ya) (xb , yb) with xa ≟-U xb
  ...| no  px = no (px ∘ p1 ∘ inj-,)
  ...| yes px with ya ≟-U yb
  ...| no  py = no (py ∘ p2 ∘ inj-,)
  ...| yes py = yes (cong₂ _,_ px py)

  _≟-U_ {u = μ u} (mu x) (mu y) with x ≟-U y
  ...| yes p = yes (cong mu p)
  ...| no  p = no (p ∘ inj-mu)
  _≟-U_ {u = var} (top x) (top y) with x ≟-U y
  ...| yes p = yes (cong top p)
  ...| no  p = no (p ∘ inj-top)
  _≟-U_ {u = wk u} (pop x) (pop y) with x ≟-U y
  ...| yes p = yes (cong pop p)
  ...| no  p = no (p ∘ inj-pop)
  _≟-U_ {u = def F a} (red x) (red y) with x ≟-U y
  ...| yes p = yes (cong red p)
  ...| no  p = no (p ∘ inj-red)
\end{code}
%</equality-def>

\begin{code}
  ≟-U-refl : {n : ℕ}{t : T n}{ty : U n}
           → (x : ElU ty t)
           → x ≟-U x ≡ yes refl
  ≟-U-refl x with x ≟-U x
  ...| no absurd = ⊥-elim (absurd refl)
  ...| yes refl  = refl
\end{code}

\begin{code}
  ≟-U-≡ : {n : ℕ}{t : T n}{ty : U n}
        → {x y : ElU ty t}(hip : x ≡ y)
        → x ≟-U y ≡ yes hip
  ≟-U-≡ {x = x} {.x} refl = ≟-U-refl x
\end{code}
