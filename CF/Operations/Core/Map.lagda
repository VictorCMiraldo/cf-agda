\begin{code}
open import Prelude

open import CF.Syntax

module CF.Operations.Core.Map where
\end{code}

  The basic operations we can do must rely on a telescope mapping.

%<*tel-map-data>
\begin{code}
  data _⟶ₜ_ : {n : ℕ} → T n → T n → Set where
    []   : [] ⟶ₜ []
    _∷_  : {n : ℕ}{t v : T n}{ty tv : U n}
         → (ElU ty t → ElU tv v) → t ⟶ₜ v → (ty ∷ t) ⟶ₜ (tv ∷ v)
    tid  : {n : ℕ}{t v : T n}{ty : U n}
         → t ⟶ₜ v → (ty ∷ t) ⟶ₜ (ty ∷ v)
\end{code}
%</tel-map-data>

  Once we have a way to consistently map telescopes, we should also be
  able to define a generic map.

%<*gmap-type>
\begin{code}
  gmap  : {n : ℕ}{t v : T n}{ty : U n}
        → (t ⟶ₜ v) → ElU ty t → ElU ty v
\end{code}
%</gmap-type>
%<*gmap-def>
\begin{code}
  gmap f unit     = unit
  gmap f (inl x)  = inl (gmap f x)
  gmap f (inr x)  = inr (gmap f x)
  gmap f (x , y)  = gmap f x , gmap f y
  gmap f (mu x)   = mu (gmap (tid f) x)
  gmap f (red x)  = red (gmap (tid f) x)
  gmap (f ∷ g) (top x) = top (f x)
  gmap (tid f) (top x) = top (gmap f x)
  gmap (f ∷ g) (pop x) = pop (gmap g x)
  gmap (tid f) (pop x) = pop (gmap f x)
\end{code}
%</gmap-def>

