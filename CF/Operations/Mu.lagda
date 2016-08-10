\begin{code}
open import Prelude

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

%<*mu-close>
\begin{code}
  μ-close : {n : ℕ}{t : T n}{ty : U (suc n)} 
          → ElU ty (u1 ∷ t) → List (ElU (μ ty) t) 
          → Maybe (ElU (μ ty) t × List (ElU (μ ty) t))
  μ-close hdX chs with ar 0 hdX ≤?-ℕ length chs
  ...| no  _ = nothing
  ...| yes p with lsplit (ar 0 hdX) chs
  ...| chX , rest 
     = (λ x → mu x , rest) <M> plug 0 hdX (map pop chX)
\end{code}
%</mu-close>

\begin{code}
  {-# TERMINATING #-}
\end{code}
%<*serialize-def>
\begin{code}
  serialize : {n : ℕ}{t : T n}{ty : U (suc n)}
            → ElU (μ ty) t → List (ElU ty (u1 ∷ t))
  serialize x = μ-hd x ∷ concat (map serialize (μ-ch x))
\end{code}
%</serialize-def>

