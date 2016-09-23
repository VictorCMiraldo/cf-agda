open import Prelude

open import CF.Syntax

module CF.Rel.Subtype where

  -- Directions on context free types
  --
  -- Can also be seen as a subtyping relation.
  infix 15 _[_]≥_[_]
  data _[_]≥_[_] : {n m : ℕ} → U m → T m → U n → T n → Set where
    -- The regular types are easy
    here : {n : ℕ}{t : T n}{ty : U n} → ty [ t ]≥ ty [ t ]
    fst  : {n m : ℕ}{t' : T n}{t : T m}{k : U n}{ty tv : U m}
         → ty [ t ]≥ k [ t' ] → ty ⊗ tv [ t ]≥ k [ t' ]
    snd  : {n m : ℕ}{t' : T n}{t : T m}{k : U n}{ty tv : U m}
         → tv [ t ]≥ k [ t' ] → ty ⊗ tv [ t ]≥ k [ t' ]
    lft  : {n m : ℕ}{t' : T n}{t : T m}{k : U n}{ty tv : U m}
         → ty [ t ]≥ k [ t' ] → ty ⊕ tv [ t ]≥ k [ t' ]
    rgt  : {n m : ℕ}{t' : T n}{t : T m}{k : U n}{ty tv : U m}
         → tv [ t ]≥ k [ t' ] → ty ⊕ tv [ t ]≥ k [ t' ]

    -- Weakenings drop themselves
    dwk  : {n m : ℕ}{t' : T n}{t : T m}{k : U n}{ty b : U m}
         → ty [ t ]≥ k [ t' ] → wk ty [ b ∷ t ]≥ k [ t' ]

    ddef : {n m : ℕ}{t' : T n}{t : T m}{k : U n}{ty : U (suc m)}{tv : U m}
         → ty [ tv ∷ t ]≥ k [ t' ] → def ty tv [ t ]≥ k [ t' ]
    {- ddef1 : {n : ℕ}{t : T n}{ty : U (suc n)}{tv k : U n}
          → ty [ t ]≥ var [ tv ∷ t ] → tv [ t ]≥ k [ t ] → def ty tv [ t ]≥ k [ t ]
    -}

    dmu  : {n m : ℕ}{t' : T n}{t : T m}{k : U n}{ty : U (suc m)}
         → ty [ μ ty ∷ t ]≥ k [ t' ] → μ ty [ t ]≥ k [ t' ]

    dvar : {n m : ℕ}{t' : T n}{t : T m}{k : U n}{x : U m}
         → x [ t ]≥ k [ t' ] → var [ x ∷ t ]≥ k [ t' ]
{-
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
-}

  on : {A : Set}{n m : ℕ}{t : T n}{t' : T m}{ty : U n}{tv : U m}
     → ty [ t ]≥ tv [ t' ] → (ElU tv t' → Maybe A) → ElU ty t → Maybe A
  on here f x = f x
  on (fst dir) f (x , y) = on dir f x
  on (snd dir) f (x , y) = on dir f y
  on (lft dir) f (inl x) = on dir f x
  on (lft dir) f (inr x) = nothing
  on (rgt dir) f (inl x) = nothing
  on (rgt dir) f (inr x) = on dir f x
  on (dwk dir) f (pop x) = on dir f x
  on (ddef dir) f (red x) = on dir f x
  -- on (ddef1 dir0 dir1) f (red x) = on dir0 (λ { (top k) → on dir1 f k }) x
  on (dmu dir) f (mu x) = on dir f x
  on (dvar dir) f (top x) = on dir f x

