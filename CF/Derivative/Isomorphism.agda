open import Prelude

open import CF.Syntax
open import CF.Derivative

module CF.Derivative.Isomorphism where

  {-
      Here we prove the isomorphism between our Ctx type
    and the elements inhabiting McBride's derivative notion.
    Although trivial, it's a good idea to prove this explicetely
    for posterity.
  -}

  toEl : {n : ℕ}{i : ℕ}{u : U n}{t : T n}
       → Ctx i u t → ElU (φ u i) t
  toEl φ-hole = unit
  toEl (φ-left ctx)
    = inl (toEl ctx)
  toEl (φ-right ctx)
    = inr (toEl ctx) 
  toEl (φ-fst x ctx)
    = inl (toEl ctx , x)
  toEl (φ-snd x ctx)
    = inr (x , toEl ctx)
  toEl (φ-pop ctx)
    = pop (toEl ctx)
  toEl (φ-defhd ctx)
    = inl (red (toEl ctx))
  toEl (φ-deftl ctxF ctxX)
    = inr (red (toEl ctxF) , toEl ctxX)
  toEl (φ-muhd ctx)
    = mu (inl (pop (red (toEl ctx))))
  toEl (φ-mutl ctxU rec)
    = mu (inr ((pop (red (toEl ctxU))) , (top (toEl rec))))
  

  toCtx : {n : ℕ}{i : ℕ}{u : U n}{t : T n}
        → ElU (φ u i) t → Ctx i u t
  toCtx {u = u0} ()
  toCtx {u = u1} ()
  toCtx {u = u ⊕ v} (inl el)
    = φ-left (toCtx el)
  toCtx {u = u ⊕ v} (inr el)
    = φ-right (toCtx el)
  toCtx {u = u ⊗ v} (inl (el , x))
    = φ-fst x (toCtx el)
  toCtx {u = u ⊗ v} (inr (x , el))
    = φ-snd x (toCtx el)
  toCtx {u = def F x} (inl (red el))
    = φ-defhd (toCtx el)
  toCtx {u = def F x} (inr (red el , k))
    = φ-deftl (toCtx el) (toCtx k)
  toCtx {u = μ u} (mu (inl (pop (red el))))
    = φ-muhd (toCtx el)
  toCtx {u = μ u} (mu (inr (pop (red el) , top rec)))
    = φ-mutl (toCtx el) (toCtx rec)
  toCtx {i = zero} {u = var} unit
    = φ-hole
  toCtx {i = suc i} {u = var} ()
  toCtx {i = zero} {u = wk u} ()
  toCtx {i = suc i} {u = wk u} (pop el)
    = φ-pop (toCtx el)

  
  proof-1 : {n : ℕ}(i : ℕ){u : U n}{t : T n}
          → (el : ElU (φ u i) t)
          → toEl {i = i} {u} (toCtx {i = i} {u} el) ≡ el
  proof-1 i {u = u0} ()
  proof-1 i {u = u1} ()
  proof-1 i {u = u ⊕ v} (inl el)
    = cong inl (proof-1 i {u} el)
  proof-1 i {u = u ⊕ v} (inr el)
    = cong inr (proof-1 i {v} el)
  proof-1 i {u = u ⊗ v} (inl (el , x))
    = cong inl (cong₂ _,_ (proof-1 i {u} el) refl)
  proof-1 i {u = u ⊗ v} (inr (x , el))
    = cong inr (cong₂ _,_ refl (proof-1 i {v} el))
  proof-1 i {def F x} (inl (red el))
    = cong (inl ∘ red) (proof-1 (suc i) {F} el)
  proof-1 i {def F x} (inr (red el , k))
    = cong inr (cong₂ _,_ (cong red (proof-1 0 {F} el)) (proof-1 i {x} k))
  proof-1 i {μ u} (mu (inl (pop (red el))))
    = cong (mu ∘ inl ∘ pop ∘ red) (proof-1 (suc i) {u} el)
  proof-1 i {μ u} (mu (inr (pop (red el) , top rec)))
    = cong (mu ∘ inr)
      (cong₂ _,_ (cong (pop ∘ red) (proof-1 0 {u} el)) (cong top (proof-1 i {μ u} rec)))
  proof-1 zero {u = var} unit
    = refl
  proof-1 (suc i) {u = var} ()
  proof-1 zero {wk u} ()
  proof-1 (suc i) {wk u} (pop el)
    = cong pop (proof-1 i {u} el)

  proof-2 : {n : ℕ}(i : ℕ){u : U n}{t : T n}
          → (ctx : Ctx i u t)
          → toCtx (toEl ctx) ≡ ctx
  proof-2 .0 φ-hole = refl
  proof-2 i (φ-left ctx) = cong φ-left (proof-2 i ctx)
  proof-2 i (φ-right ctx) = cong φ-right (proof-2 i ctx)
  proof-2 i (φ-fst x ctx) = cong (φ-fst x) (proof-2 i ctx)
  proof-2 i (φ-snd x ctx) = cong (φ-snd x) (proof-2 i ctx)
  proof-2 (suc i) (φ-pop ctx) = cong φ-pop (proof-2 i ctx)
  proof-2 i (φ-defhd ctx) = cong φ-defhd (proof-2 (suc i) ctx)
  proof-2 i (φ-deftl ctxF ctxX) = cong₂ φ-deftl (proof-2 zero ctxF) (proof-2 i ctxX)
  proof-2 i (φ-muhd ctx) = cong φ-muhd (proof-2 (suc i) ctx)
  proof-2 i (φ-mutl ctx rec) = cong₂ φ-mutl (proof-2 zero ctx) (proof-2 i rec)
