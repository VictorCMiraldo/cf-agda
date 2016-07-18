open import Prelude
open import CF.Syntax
open import Algebra.Structures
  using (IsMonoid; IsSemigroup)
open import Algebra
  using (Monoid)
open import Relation.Binary.Core
  using (IsEquivalence)

module CF.Operations.Core.MonoidCata {c ℓ}(Mon : Monoid c ℓ) where
  
  M : Set c
  M = Monoid.Carrier Mon

  infixr 20 _∙_
  infix 4 _≈_

  _≈_ : M → M → Set ℓ
  x ≈ y = Monoid._≈_ Mon x y

  ε : M
  ε = Monoid.ε Mon

  _∙_ : M → M → M
  x ∙ y = Monoid._∙_ Mon x y

  module Laws where

    open IsMonoid

    ≈-equiv : IsEquivalence _≈_
    ≈-equiv = IsSemigroup.isEquivalence (isSemigroup (Monoid.isMonoid Mon))

    ≈-refl : {x : M} → x ≈ x
    ≈-refl = IsEquivalence.refl ≈-equiv

    ≈-sym : {x y : M} → x ≈ y → y ≈ x
    ≈-sym = IsEquivalence.sym ≈-equiv

    ≈-trans : {x y z : M} → x ≈ y → y ≈ z → x ≈ z
    ≈-trans = IsEquivalence.trans ≈-equiv
    
    ε∙x≈x : (x : M) → ε ∙ x ≈ x
    ε∙x≈x = p1 (identity (Monoid.isMonoid Mon))

    x∙ε≈x : (x : M) → x ∙ ε ≈ x
    x∙ε≈x = p2 (identity (Monoid.isMonoid Mon))
    
    ∙-assoc : (x y z : M) → (x ∙ y) ∙ z ≈ x ∙ y ∙ z
    ∙-assoc = IsSemigroup.assoc (isSemigroup (Monoid.isMonoid Mon))

    ∙-cong₂ : {x y w z : M} → x ≈ y → w ≈ z → x ∙ w ≈ y ∙ z
    ∙-cong₂ h1 h2 = IsSemigroup.∙-cong (isSemigroup (Monoid.isMonoid Mon)) h1 h2

    ∙-cong-l : {x y z : M} → x ≈ y → x ∙ z ≈ y ∙ z
    ∙-cong-l h = ∙-cong₂ h ≈-refl

    ∙-cong-r : {x y z : M} → x ≈ y → z ∙ x ≈ z ∙ y
    ∙-cong-r h = ∙-cong₂ ≈-refl h


  data TAlg : {n : ℕ} → T n → Set c where
    end : {n : ℕ}{t : T n}{ty : U n}
        → (ElU ty t → M) → TAlg (ty ∷ t)
    tid : {n : ℕ}{t : T n}{ty : U n}
        → TAlg t → TAlg (ty ∷ t)


  gcata : {n : ℕ}{t : T n}{ty : U n}
        → TAlg t → ElU ty t → M
  gcata alg unit     = ε
  gcata alg (inl x)  = gcata alg x
  gcata alg (inr x)  = gcata alg x
  gcata alg (x , y)  = gcata alg x ∙ gcata alg y
  gcata alg (mu x)   = gcata (tid alg) x
  gcata alg (red x)  = gcata (tid alg) x
  gcata (end f)   (top x) = f x
  gcata (tid alg) (top x) = gcata alg x
  gcata (end f)   (pop x) = ε
  gcata (tid alg) (pop x) = gcata alg x
