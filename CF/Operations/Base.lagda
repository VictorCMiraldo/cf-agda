\begin{code}
open import Prelude
open import Prelude.NatProperties
open import Prelude.ListProperties
open import CF.Syntax
open import CF.Operations.Core.Distr

module CF.Operations.Base where

  {-# TERMINATING #-}
  ch : {n : ℕ}{t : T n}{ty : U n}
     → (i : ℕ) → ElU ty t → List (ElT (e↑ ⊥) i t)
  ch i (hole ())
  ch i unit     = []
  ch i (inl x)  = ch i x
  ch i (inr x)  = ch i x
  ch i (x , y)  = ch i x ++ ch i y
  ch zero    (top x) = x ∷ []
  ch (suc i) (top x) = []
  ch zero (pop x)    = []
  ch (suc i) (pop x) = ch i x
  ch i (mu x)   
    = ch (suc i) x ++ concat (map (ch i) (ch 0 x))
  ch i (red x)  
    = ch (suc i) x ++ concat (map (ch i) (ch 0 x))

  {-# TERMINATING #-}
  ar : {n : ℕ}{t : T n}{ty : U n}
     → (i : ℕ) → ElU ty t → ℕ
  ar i (hole ())
  ar i unit     = 0
  ar i (inl x)  = ar i x
  ar i (inr x)  = ar i x
  ar i (x , y)  = ar i x + ar i y
  ar zero    (top x) = 1
  ar (suc i) (top x) = 0
  ar zero (pop x)    = 0
  ar (suc i) (pop x) = ar i x
  ar i (mu x)   
    = ar (suc i) x + sum (map (ar i) (ch 0 x))
  ar i (red x)  
    = ar (suc i) x + sum (map (ar i) (ch 0 x))

  IsVar : {n : ℕ}(i : ℕ) → U n → T n → Set
  IsVar 0       var    t        = Unit
  IsVar (suc i) (wk u) (t ∷ ts) = IsVar i u ts
  IsVar i       u      t        = ⊥

  fgt : {n : ℕ}{t : T n}{ty : U n}
      → (i j : ℕ) → ElU ty t
      → E (e↑ Unit) ty t
  fgt i j (hole ())
  fgt i j unit = unit
  fgt i j (inl x) = inl (fgt i j x)
  fgt i j (inr x) = inr (fgt i j x)
  fgt i j (x , y) = fgt i j x , fgt i j y
  fgt i j (mu x)  = mu (fgt (suc i) j x)
  fgt i j (red x) = red (fgt (suc i) j x)
  fgt zero   zero    (top x) = top (e-cast x)
  fgt zero   (suc k) (top x) = hole unit
  fgt (suc i) j      (top x) = top (fgt i j x)
  fgt zero zero    (pop x)   = pop (e-cast x)
  fgt zero (suc j) (pop x)   = pop (fgt 0 j x)
  fgt (suc i) j (pop x)      = pop (fgt i j x) 


  LTREE-sop : forall {n} -> U (3 + n)
  LTREE-sop = (wk (wk var) ⊕ wk var ⊗ var ⊗ var)

  LTREE : ∀{n} → U (2 + n)
  LTREE = μ LTREE-sop
  
  LEAF : ∀{n}{t : T n}{a : U (suc n)}{b : U n}
       → ElU b t → ElU LTREE (a ∷ b ∷ t)
  LEAF l = mu (inl (pop (pop (top l))))

  BRANCH : ∀{n}{t : T n}{a : U (suc n)}{b : U n}
       → ElU a (b ∷ t) → ElU LTREE (a ∷ b ∷ t)
       → ElU LTREE (a ∷ b ∷ t) → ElU LTREE (a ∷ b ∷ t)
  BRANCH e l r = mu (inr ((pop (top e)) , ((top l) , (top r))))

  BOOL : ∀{n} → U n
  BOOL = u1 ⊕ u1

  TT : ∀{n}{t : T n} → ElU BOOL t
  TT = inl unit

  FF : ∀{n}{t : T n} → ElU BOOL t
  FF = inr unit

  DELTA : ∀{n} → U (suc n)
  DELTA = var ⊗ var

  uu : ∀{n}{t : T n} → ElU DELTA (u1 ∷ t)
  uu = top unit , top unit

  t1 : ElU LTREE (BOOL ∷ DELTA ∷ u1 ∷ [])
  t1 = BRANCH TT (BRANCH TT (LEAF uu) (LEAF uu)) (LEAF uu)

\end{code}


  open import Data.List 
    renaming (monoid to list-monoid)
  open import Algebra

  private
    nat-monoid : Monoid _ _
    nat-monoid = record
      { Carrier  = ℕ
      ; ε        = 0
      ; _∙_      = _+_
      ; _≈_      = _≡_
      ; isMonoid = record 
          { isSemigroup = record 
              { isEquivalence 
                  = record { refl = refl ; sym = sym ; trans = trans } 
              ; assoc = +-assoc 
              ; ∙-cong = cong₂ _+_ 
              } 
          ; identity = (λ x → refl) , (λ x → +-comm x 0) 
          }
      }
  
  ch : {n : ℕ}{t : T n}{a : U n}{ty : U (suc n)}
     → ElU ty (a ∷ t) → List (ElU a t)
  ch {n} {t} {a} {ty} = dive (list-monoid (ElU a t)) (isHere (λ x → x ∷ []))

  ar : {n : ℕ}{t : T n}{a : U n}{ty : U (suc n)}
     → ElU ty (a ∷ t) → ℕ
  ar {n} {t} {a} {ty} = dive nat-monoid (isHere (λ _ → 1))

  test : {n : ℕ}{t : T n}{a : U n}{ty : U (suc n)}
       → (x : ElU ty (a ∷ t))
       → ar x ≡ length (ch x)
  test unit = refl
  test (inl x) = test x
  test (inr x) = test x
  test (x , y) 
    = sym (trans (length-++ (ch x)) 
          (sym (cong₂ _+_ (test x) (test y))))
  test (top x) = refl
  test (pop x) = refl
  test (mu x) = {!test x!}
  test (red x₁) = {!!}

  LTREE-sop : forall {n} -> U (3 + n)
  LTREE-sop = (wk (wk var) ⊕ wk var ⊗ var ⊗ var)

  LTREE : ∀{n} → U (2 + n)
  LTREE = μ LTREE-sop
  
  LEAF : ∀{n}{t : T n}{a : U (suc n)}{b : U n}
       → ElU b t → ElU LTREE (a ∷ b ∷ t)
  LEAF l = mu (inl (pop (pop (top l))))

  BRANCH : ∀{n}{t : T n}{a : U (suc n)}{b : U n}
       → ElU a (b ∷ t) → ElU LTREE (a ∷ b ∷ t)
       → ElU LTREE (a ∷ b ∷ t) → ElU LTREE (a ∷ b ∷ t)
  BRANCH e l r = mu (inr ((pop (top e)) , ((top l) , (top r))))

  BOOL : ∀{n} → U n
  BOOL = u1 ⊕ u1

  TT : ∀{n}{t : T n} → ElU BOOL t
  TT = inl unit

  FF : ∀{n}{t : T n} → ElU BOOL t
  FF = inr unit

  t1 : ElU LTREE (BOOL ∷ u1 ∷ [])
  t1 = BRANCH TT (BRANCH TT (LEAF unit) (LEAF unit)) (LEAF unit)
\end{code}
