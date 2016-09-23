\begin{code}
open import Prelude
open import CF.Syntax

module CF.Relations.Subterm where
\end{code}

  McBride defines this relation in terms of ElU, not codes.
  Trying to define the rule for var shows why...

\begin{code}
  data _≤-UT_ : {n : ℕ}{t : T n}{ty tv : U n} → ElU ty t → ElU tv t → Set
      where
    UT-refl : {n : ℕ}{t : T n}{ty : U n}(x : ElU ty t)
            → x ≤-UT x
    UT-inl  : {n : ℕ}{t : T n}{ty tv tu : U n}{x : ElU ty t}{y : ElU tv t}
            → x ≤-UT y
            → x ≤-UT (inl {b = tu} y)
    UT-red  : {n : ℕ}{t : T n}{ty tv : U n}{F : U (suc n)}{x : ElU ty t}{y : ElU F (tv ∷ t)}
            → pop x ≤-UT y
            → x ≤-UT (red y)
\end{code}

\begin{code}
  
\end{code}
