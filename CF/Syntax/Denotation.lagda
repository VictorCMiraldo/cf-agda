\begin{code}
open import Prelude
open import CF.Syntax.Core
open import CF.Syntax.El

module CF.Syntax.Denotation where
\end{code}

  This module provides a denotational semantics
  onto Set, the category of sets and functions,
  
  The insight here is that, since our codes require
  a telescopic enviroment to be interpreted, we need
  to pass information around the telescope.

  Take (ty : U n), then define:

    n = 0; ElU ty []                  = ⟦ ty ⟧
    n = 1; ElU ty (t₀ ∷ [])           = ⟦ ty ⟧ ⟦ t₀ ⟧
    n = 2; ElU ty (t₀ ∷ t₁ ∷ [])      = ⟦ ty ⟧ (⟦ tₒ ⟧ ⟦ t₁ ⟧) ⟦ t₁ ⟧
    n = 3; ElU ty (t₀ ∷ t₁ ∷ t2 ∷ []) = ⟦ ty ⟧ (⟦ t₀ ⟧ (⟦ t₁ ⟧ ⟦ t₂ ⟧) ⟦ t₂ ⟧) 
                                               (⟦ t₁ ⟧ ⟦ t₂ ⟧) 
                                                ⟦ t₂ ⟧
    n = 4; ...

  Hence, for all n and (ty : U n): 
    
    ⟦ ty ⟧ : Setⁿ → Set

  Let's now define this construction!
  We begin with some basic definitions, namelly
  level polymorphic unit and exponentiation
  and level 0 W-types.

\begin{code}
  data ⊤ {a} : Set a where
    top : ⊤

  _^_ : ∀{a} → Set a → ℕ → Set a
  s ^ zero  = ⊤
  s ^ suc n = s × (s ^ n)

  data W (S : Set)(P : S → Set) : Set where
    sup : (s : S)(f : P s → W S P) → W S P
\end{code}

\begin{code}
  mutual
    ⟦_⟧ : {n : ℕ} → U n → Set ^ n → Set

    P : {n : ℕ}(k : ℕ)(ty : U n)(as : Set ^ n) 
      → ⟦ ty ⟧ as →  Set

    ⟦ u0 ⟧ _           = ⊥
    ⟦ u1 ⟧ _           = Unit
    ⟦ ty ⊕ tv ⟧ as     = ⟦ ty ⟧ as ⊎ ⟦ tv ⟧ as
    ⟦ ty ⊗ tv ⟧ as     = ⟦ ty ⟧ as × ⟦ tv ⟧ as 
    ⟦ def ty tv ⟧ as   = ⟦ ty ⟧ (⟦ tv ⟧ as , as)
    ⟦ μ ty ⟧ as        = W (⟦ ty ⟧ (Unit , as)) (P 0 ty (Unit , as))     
    ⟦ var ⟧   (a , as) = a
    ⟦ wk ty ⟧ (a , as) = ⟦ ty ⟧ as

    -- conjecture
    -- 
    -- P i ty t (el : ElU ty t)  ≈ ar i el

    P k u0 as ()
    P k u1 as sem = ⊥
    P k (ty ⊕ tv) as (i1 x) = P k ty as x
    P k (ty ⊕ tv) as (i2 y) = P k tv as y
    P k (ty ⊗ tv) as (py , pv) = P k ty as py ⊎ P k tv as pv
    P k (def ty tv) as sem 
      = P (suc k) ty (⟦ tv ⟧ as , as) sem
    P k (μ ty) as (sup s f) 
      = (Σ (P 0 ty (Unit , as) s) (λ ps → P k (μ ty) as (f ps))) ⊎
        (P (suc k) ty (Unit , as) s)
    P zero var (a , as) sem = Unit
    P (suc k) var as sem = ⊥
    P zero (wk ty) as sem = ⊥
    P (suc k) (wk ty) (a , as) sem = P k ty as sem
\end{code}

  Now we just close the recursive knot with
  a semantics for a telescope of size n, which produce n distinct types
  in the correct fashion.

\begin{code}
  ⟦_⟧ₜ : {n : ℕ} → T n → Set ^ n
  ⟦ []     ⟧ₜ = top
  ⟦ t ∷ ts ⟧ₜ = (⟦ t ⟧ ⟦ ts ⟧ₜ) , ⟦ ts ⟧ₜ
\end{code}

  Finally, we need to provide some isomorphisms
  to translate back and forth between representations.
  
  But first, we need to represent P as a more descriptive datatype.

\begin{code}
  open import CF.Operations.Base
  open import CF.Properties.Base
  open import CF.Operations.Dry
  open import CF.Properties.Dry
    using (ar-dry-0-lemma)
  open import Prelude.FinProperties
  open import Prelude.ListProperties
    using (length-map)
\end{code}

\begin{code}
  mutual
    {-# TERMINATING #-}
    to-elu : {n : ℕ}{t : T n}{ty : U n}
         → ⟦ ty ⟧ ⟦ t ⟧ₜ
         → ElU ty t

    {-# TERMINATING #-}
    to-den : {n : ℕ}{t : T n}{ty : U n}
         → (x : ElU ty t)
         → ⟦ ty ⟧ ⟦ t ⟧ₜ

    iso-den-elu 
      : {n : ℕ}{t : T n}{ty : U n}
      → (x : ⟦ ty ⟧ ⟦ t ⟧ₜ)
      → to-den (to-elu {n} {t} {ty} x) ≡ x

    to-elu {ty = u0} ()
    to-elu {ty = u1} x = unit
    to-elu {ty = ty ⊕ tv} (i1 x) = inl (to-elu x)
    to-elu {ty = ty ⊕ tv} (i2 y) = inr (to-elu y)
    to-elu {ty = ty ⊗ tv} (x , y) = to-elu x , to-elu y
    to-elu {ty = def ty tv} x = red (to-elu x)
    to-elu {t = t ∷ ts} {var} x = top (to-elu x)
    to-elu {t = t ∷ ts} {wk ty} x = pop (to-elu x)
    to-elu {t = t} {ty = μ ty} (sup s f) 
      = let hdS = to-elu s
            chS = Fink→A≈ListA (f ∘ (Fin-to-P {t = u1 ∷ t} {ty = ty} 0 s))
         in mu (plugₜ 0 hdS (map (pop ∘ to-elu) chS) 
               (trans (length-map (pop ∘ to-elu {ty = μ ty}) chS) 
               (trans (Fink→A≈ListA-length (f ∘ (Fin-to-P {t = u1 ∷ t} {ty = ty} 0 s)))
                      (ar-dry-0-lemma {t = u1 ∷ t} {ty = ty} (to-elu s)))))

    Fin-to-P : {n : ℕ}{t : T n}{ty : U n}
             → (i : ℕ)(el : ⟦ ty ⟧ ⟦ t ⟧ₜ)
             → Fin (ar-dry i (to-elu {n} {t} {ty} el))
             → P i ty ⟦ t ⟧ₜ el
    Fin-to-P {ty = u0} i () f
    Fin-to-P {ty = u1} i el ()
    Fin-to-P {ty = ty ⊕ tv} i (i1 x) f 
      = Fin-to-P {ty = ty} i x f
    Fin-to-P {ty = ty ⊕ tv} i (i2 y) f 
      = Fin-to-P {ty = tv} i y f
    Fin-to-P {ty = ty ⊗ tv} i (el₀ , el₁) f 
      = [ i1 ∘ Fin-to-P {ty = ty} i el₀ , i2 ∘ Fin-to-P {ty = tv} i el₁ ]′ (Fin-split f)
    Fin-to-P {t = t} {ty = def ty tv} i el f 
      = Fin-to-P {t = tv ∷ t} {ty = ty} (suc i) el {!!}
    Fin-to-P {ty = var} zero el f = unit
    Fin-to-P {t = t ∷ ts} {var} (suc i) el ()
    Fin-to-P {t = t ∷ ts} {wk ty} zero el ()
    Fin-to-P {t = t ∷ ts} {wk ty} (suc i) el f 
      = Fin-to-P {t = ts} {ty} i el f
    Fin-to-P {ty = μ ty} i (sup h c) f 
      = let k = Fin-split f
         in {!!}
             

    P-to-Fin : {n : ℕ}{t : T n}{ty : U n}
             → (i : ℕ)(el : ⟦ ty ⟧ ⟦ t ⟧ₜ)
             → P i ty ⟦ t ⟧ₜ el
             → Fin (ar-dry i (to-elu {n} {t} {ty} el))
    P-to-Fin {ty = u0} i () p
    P-to-Fin {ty = u1} i el ()
    P-to-Fin {ty = ty ⊕ tv} i (i1 x) p 
      = P-to-Fin {ty = ty} i x p
    P-to-Fin {ty = ty ⊕ tv} i (i2 x) p 
      = P-to-Fin {ty = tv} i x p
    P-to-Fin {ty = ty ⊗ tv} i (el₀ , el₁) (i1 x) 
      = {!!} -- finject (ar {ty = tv} i (to-elu el₁)) (P-to-Fin {ty = ty} i el₀ x)
    P-to-Fin {ty = ty ⊗ tv} i (el₀ , el₁) (i2 x) 
      = {!!} -- fraise (ar {ty = ty} i (to-elu el₀)) (P-to-Fin {ty = tv} i el₁ x)
    P-to-Fin {t = t} {ty = def ty tv} i el p 
      = {!!} -- P-to-Fin {t = tv ∷ t} {ty = ty} (suc i) el p
    P-to-Fin {t = t ∷ ts} {var} zero el p = fz
    P-to-Fin {t = t ∷ ts} {var} (suc i) el ()
    P-to-Fin {t = t ∷ ts} {wk ty} zero el ()
    P-to-Fin {t = t ∷ ts} {wk ty} (suc i) el p 
      = P-to-Fin {t = ts} {ty = ty} i el p
    P-to-Fin {ty = μ ty} i (sup s f) (i1 (x , px)) = {!!}
    P-to-Fin {ty = μ ty} i (sup s f) (i2 y) 
      = {!!}
           
\end{code}

\begin{code}
    to-den unit = unit
    to-den (inl x) = i1 (to-den x)
    to-den (inr x) = i2 (to-den x)
    to-den (x , y) = (to-den x) , (to-den y)
    to-den (top x) = to-den x
    to-den (pop x) = to-den x
    to-den (red x) = to-den x
    to-den (mu x)  
      =  sup (to-den (fgt 0 x)) (λ y → {!!})

    iso-elu-den 
      : {n : ℕ}{t : T n}{ty : U n}
      → (x : ElU ty t)
      → to-elu (to-den x) ≡ x
    iso-elu-den x = {!!}

    iso-den-elu x = {!!}

    ElU≈⟦⟧ : {n : ℕ}{t : T n}{ty : U n}
           → Iso (ElU ty t) (⟦ ty ⟧ ⟦ t ⟧ₜ)
    ElU≈⟦⟧ {n} {t} {ty} 
      = iso to-den to-elu (iso-den-elu {n} {t} {ty}) iso-elu-den
\end{code}

  Here we test it out with rose-trees,
  although the resulting type is extremely verbose, it is isomorphic
  to rose-trees! :)

\begin{code}
  private 
    module Test where
      open import CF.Lab

      elTest : ⟦ RTREE {n = 0} ⟧ (ℕ , top)
      elTest = sup (34 , sup (i2 (unit , unit)) (λ _ → sup (i2 (unit , unit)) (λ _ → sup (i1 unit) (λ ()))) )
                   (λ { (i1 ()) 
                      ; (i2 (i1 (i1 () , y))) 
                      ; (i2 (i1 (i2 x0 , i1 (y0 , i1 (() , z))))) 
                      ; (i2 (i1 (i2 x0 , i1 (y0 , i2 ())))) 
                      ; (i2 (i1 (i2 x0 , i2 (i1 y)))) 
                        → sup (42 , sup (i1 unit) (λ ())) 
                              (λ { (i1 ())
                                 ; (i2 (i1 (() , k))) 
                                 ; (i2 (i2 ())) 
                                 })
                      ; (i2 (i1 (i2 x0 , i2 (i2 ())))) 
                      ; (i2 (i2 (i2 ())))
                      ; (i2 (i2 (i1 x))) 
                        → sup (24 , sup (i2 (unit , unit)) (λ _ → sup (i1 unit) (λ ()))) 
                              (λ { (i1 ()) 
                                 ; (i2 (i1 (i1 () , j))) 
                                 ; (i2 (i1 (i2 k0 , i1 (() , j)))) 
                                 ; (i2 (i1 (i2 k0 , i2 ()))) 
                                 ; (i2 (i2 (i1 k))) 
                                   → sup (17 , sup (i1 unit) (λ ())) 
                                         (λ { (i1 ())
                                            ; (i2 (i1 (() , k))) 
                                            ; (i2 (i2 ())) 
                                            })
                                 ; (i2 (i2 (i2 ())))
                                 })
                      }) 
\end{code}


  
