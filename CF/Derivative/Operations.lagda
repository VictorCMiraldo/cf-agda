\begin{code}
open import Prelude
open import Prelude.Vector
open import CF.Syntax
open import CF.Operations
open import CF.Derivative

module CF.Derivative.Operations where
\end{code}

  Cartesian Product of two lists

\begin{code}
  _**_ : {A B : Set} → List A → List B → List (A × B)
  [] ** _ = []
  _ ** [] = []
  (a ∷ as) ** bs = map (λ y → (a , y)) bs ++ (as ** bs)  
\end{code}

 Given an element and a natural number, compute
 all the possible contexts that variable i
 could have inside the element.

%<*delta-i-type>
\begin{code}
  {-# TERMINATING #-}
  δ : {n : ℕ}{t : T n}{a : U n}
    → (i : ℕ)(x : ElU a t)
    → List (Ctx i a t)
\end{code}
%</delta-i-type>
%<*delta-i-def>
\begin{code}
  δ i unit = []
  δ i (inl x) = map φ-left (δ i x)
  δ i (inr x) = map φ-right (δ i x)
  δ i (x , y)
    =  map (λ C → φ-fst C y) (δ i x)
    ++ map (λ C → φ-snd C x) (δ i y)
  δ zero    (top x) = φ-hole ∷ []
  δ (suc i) (top x) = []
  δ zero (pop x) = []
  δ (suc i) (pop x) = map φ-pop (δ i x)
  δ i (mu x)
    = let δi+1 = δ (suc i) x
          δ0   = δ 0 x
          δch  = concat (map (δ i) (map unpop (ch 0 x)))
      in map φ-muhd δi+1 ++ map (uncurry φ-mutl) (δ0 ** δch)
  δ i (red x)
    = let δi+1 = δ (suc i) x
          δ0   = δ 0 x
          δch  = concat (map (δ i) (map unpop (ch 0 x)))
      in map φ-defhd δi+1 ++ map (uncurry φ-deftl) (δ0 ** δch)
\end{code}
%</delta-i-def>

  This gives an interesting and utterly inneficient way of computing children! :)
  First we compute all the contexts in which variable 0 could appear in
  an element, we then try to match those contexts with the element in question;
  those that match give us the child in that position.  

\begin{code}
  δ-ch : {n : ℕ}{t : T n}{a : U n}
       → (i : ℕ) → ElU a t → List (ElU (tel-lkup i t) t)
  δ-ch i x = filter-just (map (λ c → match c x) (δ i x))
    where
      filter-just : {A : Set} → List (Maybe A) → List A
      filter-just [] = []
      filter-just (nothing ∷ as) = filter-just as
      filter-just (just a  ∷ as) = a ∷ filter-just as
\end{code}
