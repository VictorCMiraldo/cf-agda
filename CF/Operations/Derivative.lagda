\begin{code}
open import Prelude

open import CF.Syntax
open import CF.Operations.Base
open import CF.Derivative

module CF.Operations.Derivative where
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
    =  map (φ-fst y) (δ i x)
    ++ map (φ-snd x) (δ i y)
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

  We can, hence, compute all zippers for a given value!

\begin{code}
  zippers : {n : ℕ}{t : T n}{a : U n}
          → (i : ℕ) → ElU a t → List (Ctx i a t × ElU (tel-lkup i t) t)
  zippers i x = filter-just (map (λ c → (c ,_) <M> match c x) (δ i x))
\end{code}

  Here's an inductive way to compute the zippers of something.
  This is slightly more confortable to work with, as it reduces
  through pattern matching.

\begin{code}
  Zipper : {n : ℕ}(i : ℕ)(ty : U n)(t : T n) → Set
  Zipper i ty t = Ctx i ty t × ElU (tel-lkup i t) t

  ZipperFor : {n i : ℕ}{t : T n}{ty : U n}
        → (x : ElU ty t)(z : Zipper i ty t)
        → Set
  ZipperFor x (ctx , a) = x ≡ ctx ◂ a
\end{code}

\begin{code}
  {-# TERMINATING #-}
  Z : {n : ℕ}{t : T n}{ty : U n}
    → (i : ℕ) → ElU ty t
    → List (Zipper i ty t)
  Z i unit = []
  Z i (inl x) = map (φ-left ×' id) (Z i x)
  Z i (inr x) = map (φ-right ×' id) (Z i x)
  Z i (x , y) = map (φ-fst y ×' id) (Z i x)
             ++ map (φ-snd x ×' id) (Z i y)
  Z zero (top x) = (φ-hole , pop x) ∷ []
  Z (suc i) (top x) = []
  Z zero (pop x) = []
  Z (suc i) (pop x) = map (φ-pop ×' pop) (Z i x)
  Z {n} {t} {μ a} i (mu x)
    = map (φ-muhd ×' unpop) (Z (suc i) x)
       ++ concat (map (λ { (ctx0 , chX)
                       → map (φ-mutl ctx0 ×' id) (Z i (unpop chX)) }) (Z 0 x))
  Z {n} {t} {def F z} i (red x)
    = map (φ-defhd ×' unpop) (Z (suc i) x)
       ++ concat (map (λ { (ctx0 , chX)
                       → map (φ-deftl ctx0 ×' id) (Z i (unpop chX)) }) (Z 0 x))
\end{code}

