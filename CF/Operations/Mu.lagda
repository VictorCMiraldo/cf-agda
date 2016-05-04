\begin{code}
open import Prelude
open import Prelude.Vector

open import CF.Syntax
open import CF.Operations.Base
open import CF.Properties.Base

module CF.Operations.Mu where
\end{code}

%<*mu-open>
\begin{code}
  μ-open : {n : ℕ}{t : T n}{ty : U (suc n)} 
         → ElU (μ ty) t → ElU ty (u1 ∷ t) × List (ElU (μ ty) t)
  μ-open (mu el) 
    = let hdEl , chEl = unplug 0 el
       in hdEl , map unpop chEl
\end{code}
%</mu-open>

%<*mu-hd-def>
\begin{code}
  μ-hd : {n : ℕ}{t : T n}{ty : U (suc n)} 
       → ElU (μ ty) t → ElU ty (u1 ∷ t)
  μ-hd = p1 ∘ μ-open
\end{code}
%</mu-hd-def>

%<*mu-ar-def>
\begin{code}
  μ-ar : {n : ℕ}{t : T n}{ty : U (suc n)} 
       → ElU (μ ty) t → ℕ
  μ-ar = ar 0 ∘ μ-hd
\end{code}
%</mu-ar-def>

%<*mu-ch-def>
\begin{code}
  μ-ch : {n : ℕ}{t : T n}{ty : U (suc n)} 
       → ElU (μ ty) t → List (ElU (μ ty) t)
  μ-ch = p2 ∘ μ-open
\end{code}
%</mu-ch-def>

\begin{code}
  open import Data.List.Properties using (length-map)

  list-split : {m : ℕ}{A : Set}(l : List A)
             → m ≤ length l
             → Σ (List A × List A) (λ ls → length (p1 ls) ≡ m)
  list-split [] z≤n = ([] , []) , refl
  list-split (x ∷ l) z≤n = ([] , (x ∷ l)) , refl
  list-split (x ∷ l) (s≤s p) with list-split l p
  ...| (la , lb) , prf = ((x ∷ la) , lb) , (cong suc prf)

  list-split-lemma 
    : {m : ℕ}{A : Set}(l1 l2 : List A){p : m ≤ length (l1 ++ l2)}
    → (q : length l1 ≡ m)
    → list-split (l1 ++ l2) p ≡ ((l1 , l2) , q)
  list-split-lemma [] [] {z≤n} refl = refl
  list-split-lemma [] (x ∷ l2) {z≤n} refl = refl
  list-split-lemma (x ∷ l1) l2 {s≤s p} refl
    with list-split-lemma l1 l2 {p} refl
  ...| hip rewrite hip = refl

  length-lemma 
    : {n : ℕ}{A : Set}(l1 l2 : List A)
    → length l1 ≡ n → n ≤ length (l1 ++ l2)
  length-lemma [] l2 refl = z≤n
  length-lemma (x ∷ l1) l2 refl = s≤s (length-lemma l1 l2 refl)
\end{code}

%<*mu-close>
\begin{code}
  μ-close : {n : ℕ}{t : T n}{ty : U (suc n)} 
          → ElU ty (u1 ∷ t) → List (ElU (μ ty) t) 
          → Maybe (ElU (μ ty) t × List (ElU (μ ty) t))
  μ-close hdX chs with ar 0 hdX ≤?-ℕ length chs
  ...| no  _ = nothing
  ...| yes p with list-split chs p
  ...| (chX , rest) , prf 
     = (λ x → mu x , rest) <M> plug 0 hdX (map pop chX)
\end{code}
%</mu-close>


