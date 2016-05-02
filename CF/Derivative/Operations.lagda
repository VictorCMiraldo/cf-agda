\begin{code}
open import Prelude
open import Prelude.Vector
open import Prelude.Propositions
open import CF.Syntax
open import CF.Operations
open import CF.Derivative

open import Data.List.Properties using (length-map; length-++)
open import Data.Nat.Properties.Simple using (+-comm)

module CF.Derivative.Operations where
\end{code}

  Cartesian Product of two lists

\begin{code}
  _**_ : {A B : Set} → List A → List B → List (A × B)
  [] ** _ = []
  _ ** [] = []
  (a ∷ as) ** bs = map (λ y → (a , y)) bs ++ (as ** bs)  
\end{code}

  Compute the "dry arity" of a given variable i in a term x.
  That is, how many "direct" arrows to i we have in our arrow diagram.

  Rephrasing, how many times a term of type (tel-lkup i) appear directly, dry,
  in x. Not counting the amount of times it appears as variable (i-1) in the
  variable 0 of x.

\begin{code}
  ar-dry : {n : ℕ}{t : T n}{ty : U n}
         → (i : ℕ)(x : ElU ty t) → ℕ
  ar-dry i unit = 0
  ar-dry i (inl x) = ar-dry i x
  ar-dry i (inr x) = ar-dry i x
  ar-dry i (x , y) = ar-dry i x + ar-dry i y
  ar-dry zero (top x) = 1
  ar-dry (suc i) (top x) = 0
  ar-dry zero (pop x) = 0
  ar-dry (suc i) (pop x) = ar-dry i x
  ar-dry i (mu x) = ar-dry (suc i) x
  ar-dry i (red x) = ar-dry (suc i) x
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
  {-# TERMINATING #-}
  Z : {n : ℕ}{t : T n}{a : U n}
    → (i : ℕ) → ElU a t
    → List (Ctx i a t × ElU (tel-lkup i t) t)
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
       ++ concat (map (λ { (f , el) → map (f ×' id) (Z i el) })
                 (map (φ-mutl ×' unpop) (Z 0 x)))
  Z {n} {t} {def F z} i (red x)
    = map (φ-defhd ×' unpop) (Z (suc i) x)
       ++ concat (map (λ { (f , el) → map (f ×' id) (Z i el) })
                 (map (φ-deftl ×' unpop) (Z 0 x)))
\end{code}

\begin{code}
  private
    nat-1-≤-aux : (n m : ℕ) → 1 ≤ n + m → 1 ≤ n ⊎ 1 ≤ m
    nat-1-≤-aux zero    m hip = i2 hip
    nat-1-≤-aux (suc n) m hip = i1 (s≤s z≤n)
\end{code}

  And now, the important bunch, as long as the dry-arity
  of a term is positive, then we have at least one zipper
  for such term.

\begin{code}
  length-Z
    : {n : ℕ}{t : T n}{a : U n}
    → (i : ℕ)(x : ElU a t)(hip : 1 ≤ ar-dry i x)
    → ∃ (λ n → suc n ≡ length (Z i x))
\end{code}
\begin{code}
  length-Z i unit ()
  length-Z i (inl x) hip
    with length-Z i x hip
  ...| (n , prf)
     = n , trans prf (sym (length-map (λ xy → φ-left (p1 xy) , p2 xy) (Z i x)))
  length-Z i (inr x) hip
    with length-Z i x hip
  ...| (n , prf)
     = n , trans prf (sym (length-map (λ xy → φ-right (p1 xy) , p2 xy) (Z i x)))
  length-Z i (x , y) hip
    with nat-1-≤-aux (ar-dry i x) (ar-dry i y) hip
  length-Z i (x , y) hip | i1 hipx
    with length-Z i x hipx
  ...| (k , prf) = k + length (Z i y)
                 , sym (trans (length-++ (map (λ xy → φ-fst y (p1 xy) , p2 xy) (Z i x)))
                       (trans (cong₂ _+_ (length-map (λ xy → φ-fst y (p1 xy) , p2 xy) (Z i x))
                                         (length-map (λ xy → φ-snd x (p1 xy) , p2 xy) (Z i y)))
                              (cong (_+ length (Z i y)) (sym prf))))
  length-Z i (x , y) hip | i2 hipy
    with length-Z i y hipy
  ...| (k , prf) = k + length (Z i x)
                 , sym (trans (length-++ (map (λ xy → φ-fst y (p1 xy) , p2 xy) (Z i x)))
                       (trans (cong₂ _+_ (length-map (λ xy → φ-fst y (p1 xy) , p2 xy) (Z i x))
                                         (length-map (λ xy → φ-snd x (p1 xy) , p2 xy) (Z i y)))
                       (trans (+-comm (length (Z i x)) (length (Z i y)))
                              (cong (_+ length (Z i x)) (sym prf)))))
  length-Z zero (top x) hip = 0 , refl
  length-Z (suc i) (top x) ()
  length-Z zero (pop x) ()
  length-Z (suc i) (pop x) hip
    with length-Z i x hip
  ...| (k , prf) = k , sym (trans (length-map (λ xy → φ-pop (p1 xy) , pop (p2 xy)) (Z i x))
                                  (sym prf))
  length-Z {n} {t} {μ a} i (mu x) hip
    with length-Z (suc i) x hip
  ...| (k , prf)
      = let z : List (Ctx i (μ a) t × ElU (tel-lkup i t) t)
            z = concat (map (λ fel → map (λ xy → p1 fel (p1 xy) , p2 xy) (Z i (p2 fel)))
                       (map (λ xy → φ-mutl (p1 xy) , unpop (p2 xy)) (Z 0 x)))
                       
            y : List (Ctx i (μ a) t × ElU (tel-lkup i t) t)
            y = map (λ xy → φ-muhd (p1 xy) , unpop (p2 xy)) (Z (suc i) x)
            
         in k + length z
          , sym (trans (length-++ y {ys = z})
                (trans (cong (_+ length z) (length-map _ (Z (suc i) x)))
                       (cong (_+ length z) (sym prf))))
  length-Z {n} {t} {def F a} i (red x) hip
    with length-Z (suc i) x hip
  ...| (k , prf)
      = let z : List (Ctx i (def F a) t × ElU (tel-lkup i t) t)
            z = concat (map (λ fel → map (λ xy → p1 fel (p1 xy) , p2 xy) (Z i (p2 fel)))
                       (map (λ xy → φ-deftl (p1 xy) , unpop (p2 xy)) (Z 0 x)))
                       
            y : List (Ctx i (def F a) t × ElU (tel-lkup i t) t)
            y = map (λ xy → φ-defhd (p1 xy) , unpop (p2 xy)) (Z (suc i) x)
            
         in k + length z
          , sym (trans (length-++ y {ys = z})
                (trans (cong (_+ length z) (length-map _ (Z (suc i) x)))
                       (cong (_+ length z) (sym prf))))
\end{code}
