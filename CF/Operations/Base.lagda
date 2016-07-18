\begin{code}
open import Prelude
open import CF.Syntax

module CF.Operations.Base where

  open import Data.List renaming (monoid to list-monoid)
  
  ch : {n : ℕ}{t : T n}{a : U n}{ty : U (suc n)}
     → ElU ty (a ∷ t) → List (ElU a t)
  ch {n} {t} {a} {ty} = gcata (end (λ x → x ∷ []))
    where
      open import CF.Operations.Core.MonoidCata (list-monoid (ElU a t))

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
