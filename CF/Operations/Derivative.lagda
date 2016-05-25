\begin{code}
open import Prelude

open import CF.Syntax
open import CF.Equality
open import CF.Operations.Base
open import CF.Derivative

module CF.Operations.Derivative where
\end{code}

  Given an element and a natural number, computing
  all the possible contexts that variable i
  could have inside the element is a central operation for
  the diffing algorithm.

  We could simply enumerate the elements that inhabit
  ElU (φ i ty) t, this would be hard to work with however.

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

  Moreover, given a context, we should be able to compute
  which of the possible contexts we were given.

\begin{code}
  Zidx : {n i : ℕ}{t : T n}{ty : U n}
       → Ctx i ty t → ℕ
  Zidx φ-hole = 0
  Zidx (φ-left ctx) = Zidx ctx
  Zidx (φ-right ctx) = Zidx ctx
  Zidx (φ-fst x ctx) = Zidx ctx
  Zidx {i = i} (φ-snd x ctx) = ar i x + Zidx ctx
  Zidx (φ-pop ctx) = Zidx ctx
  Zidx (φ-defhd ctx) = Zidx ctx
  Zidx {i = i} (φ-deftl cF cX) = φ-ar i cF + Zidx cX 
  Zidx (φ-muhd ctx) = Zidx ctx
  Zidx {i = i} (φ-mutl c0 rec) = φ-ar i c0 + Zidx rec
\end{code}

  Another handy operation is being able to compare
  contexts for equality.

\begin{code}
  _≟-Ctx_ : {n i : ℕ}{t : T n}{ty : U n}
          → (p q : Ctx i ty t)
          → Dec (p ≡ q)
  φ-hole ≟-Ctx φ-hole = yes refl
  φ-left p ≟-Ctx φ-left q
    with p ≟-Ctx q
  ...| yes p≡q = yes (cong φ-left p≡q)
  ...| no ¬p≡q = no  (¬p≡q ∘ inj-φ-left)
  φ-left p ≟-Ctx φ-right q = no (λ ())
  φ-right p ≟-Ctx φ-left q = no (λ ())
  φ-right p ≟-Ctx φ-right q
    with p ≟-Ctx q
  ...| yes p≡q = yes (cong φ-right p≡q)
  ...| no ¬p≡q = no  (¬p≡q ∘ inj-φ-right)
  φ-fst x p ≟-Ctx φ-fst y q
    with x ≟-U y | p ≟-Ctx q
  ...| yes x≡y | yes p≡q = yes (cong₂ φ-fst x≡y p≡q)
  ...| yes x≡y | no ¬p≡q = no (¬p≡q ∘ p2 ∘ inj-φ-fst)
  ...| no ¬x≡y | _       = no (¬x≡y ∘ p1 ∘ inj-φ-fst)
  φ-fst x p ≟-Ctx φ-snd y q = no (λ ())
  φ-snd x p ≟-Ctx φ-fst y q = no (λ ())
  φ-snd x p ≟-Ctx φ-snd y q
    with x ≟-U y | p ≟-Ctx q
  ...| yes x≡y | yes p≡q = yes (cong₂ φ-snd x≡y p≡q)
  ...| yes x≡y | no ¬p≡q = no (¬p≡q ∘ p2 ∘ inj-φ-snd)
  ...| no ¬x≡y | _       = no (¬x≡y ∘ p1 ∘ inj-φ-snd)
  φ-pop p ≟-Ctx φ-pop q
    with p ≟-Ctx q
  ...| yes p≡q = yes (cong φ-pop p≡q)
  ...| no ¬p≡q = no  (¬p≡q ∘ inj-φ-pop)
  φ-defhd p ≟-Ctx φ-defhd q
    with p ≟-Ctx q
  ...| yes p≡q = yes (cong φ-defhd p≡q)
  ...| no ¬p≡q = no  (¬p≡q ∘ inj-φ-defhd)
  φ-defhd p ≟-Ctx φ-deftl q q₁ = no (λ ())
  φ-deftl p p₁ ≟-Ctx φ-defhd q = no (λ ())
  φ-deftl p p₁ ≟-Ctx φ-deftl q q₁
    with p ≟-Ctx q | p₁ ≟-Ctx q₁
  ...| yes pq | yes pq1 = yes (cong₂ φ-deftl pq pq1)
  ...| yes pq | no ¬pq1 = no  (¬pq1 ∘ p2 ∘ inj-φ-deftl)
  ...| no ¬pq | _       = no  (¬pq  ∘ p1 ∘ inj-φ-deftl)
  φ-muhd p ≟-Ctx φ-muhd q
    with p ≟-Ctx q
  ...| yes p≡q = yes (cong φ-muhd p≡q)
  ...| no ¬p≡q = no  (¬p≡q ∘ inj-φ-muhd)
  φ-muhd p ≟-Ctx φ-mutl q q₁ = no (λ ())
  φ-mutl p p₁ ≟-Ctx φ-muhd q = no (λ ())
  φ-mutl p p₁ ≟-Ctx φ-mutl q q₁
    with p ≟-Ctx q | p₁ ≟-Ctx q₁
  ...| yes pq | yes pq1 = yes (cong₂ φ-mutl pq pq1)
  ...| yes pq | no ¬pq1 = no  (¬pq1 ∘ p2 ∘ inj-φ-mutl)
  ...| no ¬pq | _       = no  (¬pq  ∘ p1 ∘ inj-φ-mutl)
\end{code}
