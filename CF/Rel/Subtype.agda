open import Prelude

open import CF.Syntax

module CF.Rel.Subtype where

  -- Directions on context free types
  --
  -- Can also be seen as a subtyping relation.
  infix 15 _≥_
  data _≥_ : {n : ℕ} → U n → U n → Set where
    -- The regular types are easy
    here : {n : ℕ}{ty : U n} → ty ≥ ty
    fst  : {n : ℕ}{k ty tv : U n}
         → ty ≥ k → ty ⊗ tv ≥ k
    snd  : {n : ℕ}{k ty tv : U n}
         → tv ≥ k → ty ⊗ tv ≥ k
    lft  : {n : ℕ}{k ty tv : U n}
         → ty ≥ k → ty ⊕ tv ≥ k
    rgt  : {n : ℕ}{k ty tv : U n}
         → tv ≥ k → ty ⊕ tv ≥ k

    -- Weakenings drop themselves
    dwk : {n : ℕ}{ty k : U n}
        → ty ≥ k → wk ty ≥ wk k

    -- Definitions start to pose a problem,
    -- yet, getting some inspiration from derivatives we get there!
    -- 
    -- We can either have a direction for the weakening of a type
    -- in ty, or, given a direction of a variable in ty, get
    -- a direction for k in tv.
    dhd  : {n : ℕ}{ty : U (suc n)}{tv k : U n}
         → ty ≥ wk k → def ty tv ≥ k
    dtl  : {n : ℕ}{ty : U (suc n)}{tv k : U n}
         → ty ≥ var → tv ≥ k → def ty tv ≥ k

    -- Fixpoints follow the same fashion
    μhd : {n : ℕ}{ty : U (suc n)}{k : U n}
        → ty ≥ wk k → μ ty ≥ k
    μtl : {n : ℕ}{ty : U (suc n)}{k : U n}
        → ty ≥ var → μ ty ≥ k → μ ty ≥ k
