\begin{code}
{-# OPTIONS --rewriting #-}
open import Prelude
open import Prelude.Vector

open import Prelude.ListProperties
  using (length-map)

open import CF.Syntax
open import CF.Operations.Base
open import CF.Properties.Base
  using (ch-ar-lemma; fgt-ar-lemma; ch-fgt-ar-lemma)
open import CF.Operations.Mu

module CF.Operations.Vec where
\end{code}

\begin{code}
  ar*v : {n k : ℕ}{t : T n}{ty : U n}
       → (i : ℕ) → Vec (ElU ty t) k → ℕ
  ar*v i []       = 0
  ar*v i (x ∷ xs) = ar i x + ar*v i xs
\end{code}

%<*chv-type>
\begin{code}
  chv : {n : ℕ}{t : T n}{ty : U n}
      → (i : ℕ)(el : ElU ty t)
      → Vec (ElU (tel-lkup i t) t) (ar i (fgt i el))
\end{code}
%</chv-type>
\begin{code}
  chv i el = vec (ch i el) (ch-fgt-ar-lemma i el)
\end{code}

%<*unplugv-type>
\begin{code}
  unplugv : {n : ℕ}{t : T n}{ty : U n}
         → (i : ℕ)(el : ElU ty t)
         → Σ (ElU ty (tel-forget i t))
             (Vec (ElU (tel-lkup i t) t) ∘ (ar i))
\end{code}
%</unplugv-type>
\begin{code}
  unplugv i el
    = fgt i el
    , vec (ch i el) (trans (ch-ar-lemma i el) (fgt-ar-lemma i el))
\end{code}

%<*plugv-type>
\begin{code}
  plugv : {n : ℕ}{t : T n}{ty : U n}
       → (i : ℕ)(el : ElU ty (tel-forget i t))
       → Vec (ElU (tel-lkup i t) t) (ar i el)
       → ElU ty t
\end{code}
%</plugv-type>
\begin{code}
  plugv {ty = u0} i () v
  plugv {ty = u1} i el v = unit
  plugv {ty = ty ⊕ tv} i (inl el) v = inl (plugv i el v)
  plugv {ty = ty ⊕ tv} i (inr el) v = inr (plugv i el v)
  plugv {ty = ty ⊗ tv} i (ela , elb) v 
    = let va , vb = vsplit (ar i ela) v
      in plugv i ela va , plugv i elb vb
  plugv {ty = def F x} i (red el) v 
    = red (plugv (suc i) el (vmap pop v))
  plugv {ty = μ ty} i (mu el) v
    = mu (plugv (suc i) el (vmap pop v))
  plugv {t = t ∷ ts} {ty = var} zero (top el) (pop v ∷ []) 
    = top v
  plugv {t = t ∷ ts} {ty = var} (suc i) (top el) v 
    = top (plugv i el (vmap unpop v))
  plugv {t = t ∷ ts} {ty = wk ty} zero (pop el) v 
    = pop el
  plugv {t = t ∷ ts} {ty = wk ty} (suc i) (pop el) v
    = pop (plugv i el (vmap unpop v))
\end{code}


%<*mu-openv>
\begin{code}
  μ-openv : {n : ℕ}{t : T n}{ty : U (suc n)} 
          → ElU (μ ty) t → Σ (ElU ty (u1 ∷ t)) (Vec (ElU (μ ty) t) ∘ (ar 0))
  μ-openv (mu el) 
    = let hdEl , chEl = unplugv 0 el
       in hdEl , vmap unpop chEl
\end{code}
%</mu-openv>

%<*mu-hdv-def>
\begin{code}
  μ-hdv : {n : ℕ}{t : T n}{ty : U (suc n)} 
       → ElU (μ ty) t → ElU ty (u1 ∷ t)
  μ-hdv = p1 ∘ μ-openv
\end{code}
%</mu-hdv-def>

%<*mu-hd-def>
\begin{code}
  μ-hd-hdv-lemma : {n : ℕ}{t : T n}{ty : U (suc n)} 
                 → (x : ElU (μ ty) t) → p1 (μ-openv x) ≡ p1 (μ-open x)
  μ-hd-hdv-lemma (mu x) = refl
\end{code}
%</mu-hd-def>

%<*mu-chv-def>
\begin{code}
  {-# REWRITE μ-hd-hdv-lemma #-}
  μ-chv : {n : ℕ}{t : T n}{ty : U (suc n)} 
        → (x : ElU (μ ty) t) → Vec (ElU (μ ty) t) (μ-ar x)
  μ-chv x = p2 (μ-openv x)      
\end{code}
%</mu-chv-def>

%<*mu-chv-def>
\begin{code}
  μ-ch-chv-lemma 
    : {n : ℕ}{t : T n}{ty : U (suc n)}
    → (x : ElU (μ ty) t)
    → μ-ch x ≡ toList (μ-chv x)
  μ-ch-chv-lemma (mu x) 
    = sym (trans (cong toList (vmap-vec unpop (ch 0 x) {p = ch-fgt-ar-lemma 0 x}
                       {q = trans (length-map unpop (ch 0 x)) (ch-fgt-ar-lemma zero x)})) 
                 (toList-vec (map unpop (ch zero x))))
\end{code}
%</mu-chv-def>

%<*mu-closev>
\begin{code}
  μ-closev : {n j : ℕ}{t : T n}{ty : U (suc n)} 
           → (a : ElU ty (u1 ∷ t))
           → Vec (ElU (μ ty) t) (ar 0 a + j) 
           → Vec (ElU (μ ty) t) (suc j)
  μ-closev a as
    = let vas , vrs = vsplit (ar 0 a) as
      in mu (plugv 0 a (vmap pop vas)) ∷ vrs
\end{code}
%</mu-closev>
