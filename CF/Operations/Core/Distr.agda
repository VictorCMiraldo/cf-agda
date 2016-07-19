open import Prelude
open import CF.Syntax

module CF.Operations.Core.Distr where
{-
  open import Algebra.Structures
    using (IsMonoid; IsSemigroup) public
  open import Algebra
    using (Monoid) public
  open import Relation.Binary.Core
    using (IsEquivalence) public

  open Monoid


  data _⊣_ {c ℓ}(M : Monoid c ℓ) : {n : ℕ} → T n → Set c where
    isEmpty  : M ⊣ []
    isHere   : {n : ℕ}{t : T n}{ty : U n}
             → (ElU ty t → Carrier M) → M ⊣ (ty ∷ t)
    isLocal  : {n : ℕ}{t : T n}{ty : U n}
             → M ⊣ t → M ⊣ (ty ∷ t)

  dive : ∀{c ℓ}{n : ℕ}{t : T n}{ty : U n}(M : Monoid c ℓ)
       → M ⊣ t → ElU ty t → Carrier M
  dive M f            unit     = ε M
  dive M f            (inl x)  = dive M f x
  dive M f            (inr x)  = dive M f x
  dive M f            (x , y)  = _∙_ M (dive M f x) (dive M f y)
  dive M (isHere f)   (top x)  = f x
  dive M (isLocal f)  (top x)  = dive M f x
  dive M (isHere f)   (pop x)  = ε M
  dive M (isLocal f)  (pop x)  = dive M f x
  dive M f            (mu x)   = dive M (isLocal f) x
  dive M f            (red x)  = dive M (isLocal f) x
-}
