\begin{code}
open import Prelude

open import CF.Syntax
open import CF.Equality
open import CF.Operations.Base using (ar)

module CF.Derivative where
\end{code}

  We can always compute the actual derivative
  of an element of U, like in McBride's paper.

\begin{code}
  φ : {n : ℕ} → U n → ℕ → U n
  φ var zero    = u1
  φ var (suc i) = u0
  φ u0 i        = u0
  φ u1 i        = u0
  φ (u ⊕ v) i   = φ u i ⊕ φ v i
  φ (u ⊗ v) i   = (φ u i ⊗ v) ⊕ (u ⊗ φ v i)
  φ (def F x) i = def (φ F (suc i)) x
                ⊕ def (φ F 0) x ⊗ φ x i
  φ (μ u) i     = μ (wk (def (φ u (suc i)) (μ u))
                  ⊕ (wk (def (φ u 0) (μ u))) ⊗ var)
  φ (wk u) zero    = u0
  φ (wk u) (suc i) = wk (φ u i)
\end{code}

  However, writing things like this makes programming fairly more complicated.
  To simplify our life, let us directly encode the elements of the derivative.

\begin{code}
  data Ctx : {n : ℕ} → ℕ → U n → T n → Set where
    φ-hole  : {n : ℕ}{t : T (suc n)} → Ctx 0 var t
    φ-left  : {n i : ℕ}{t : T n}{a b : U n}
            → Ctx i a t → Ctx i (a ⊕ b) t
    φ-right : {n i : ℕ}{t : T n}{a b : U n}
            → Ctx i b t → Ctx i (a ⊕ b) t
    φ-fst   : {n i : ℕ}{t : T n}{a b : U n}
            → ElU b t → Ctx i a t → Ctx i (a ⊗ b) t
    φ-snd   : {n i : ℕ}{t : T n}{a b : U n}
            → ElU a t → Ctx i b t → Ctx i (a ⊗ b) t
    φ-pop   : {n i : ℕ}{t : T n}{a b : U n}
            → Ctx i a t → Ctx (suc i) (wk a) (b ∷ t)
    φ-defhd : {n i : ℕ}{t : T n}{x : U n}{F : U (suc n)}
            → Ctx (suc i) F (x ∷ t) → Ctx i (def F x) t
    φ-deftl : {n i : ℕ}{t : T n}{x : U n}{F : U (suc n)}
            → Ctx 0 F (x ∷ t) → Ctx i x t → Ctx i (def F x) t
    φ-muhd  : {n i : ℕ}{t : T n}{u : U (suc n)}
            → Ctx (suc i) u (μ u ∷ t) → Ctx i (μ u) t
    φ-mutl  : {n i : ℕ}{t : T n}{u : U (suc n)}
            → Ctx 0 u (μ u ∷ t) → Ctx i (μ u) t → Ctx i (μ u) t
\end{code}

  Hence, we have:

    ElU (φ i u) t ≅ Ctx i u t

  The isomorphism proof is in CF.Derivative.Isomorphism.

  In our CF.MuPlugging, we could see the (el : ElU a (u1 ∷ t)) as
  the element with all variables indexed by 0 in type a unplugged.
  Another way to implement these one-hole contexts would be to
  have elements (el : ElU a (u1 ⊕ b ∷ t)), where

    (length ∘ filter is-inr ∘ children) el ≡ k

  To enforce that we only get k holes. The derivative approach
  seems better, however. Not only it has been studied before,
  but it allows for a very natural encoding and has (indirect)
  existing support in many programming languages

  Now, we'll encode pluging operations over our Ctx type.

\begin{code}
  _◂_ : {n : ℕ}{t : T n}{u : U n}{i : ℕ}
      → Ctx i u t → ElU (tel-lkup i t) t → ElU u t
  _◂_ {t = t ∷ ts} φ-hole (pop x) = top x
  φ-left ctx  ◂ x = inl (ctx ◂ x)
  φ-right ctx ◂ x = inr (ctx ◂ x)
  φ-fst k ctx ◂ x = (ctx ◂ x , k)
  φ-snd k ctx ◂ x = (k , ctx ◂ x)
  φ-pop ctx   ◂ (pop x) = pop (ctx ◂ x)
  φ-defhd ctx       ◂ x = red (ctx ◂ (pop x))
  φ-deftl ctxF ctxX ◂ x = red (ctxF ◂ pop (ctxX ◂ x))
  φ-muhd ctx        ◂ x = mu (ctx ◂ pop x)
  φ-mutl ctx rec    ◂ x = mu (ctx ◂ pop (rec ◂ x))
\end{code}

  And the inverse, "matching", operation

\begin{code}
  match : {n : ℕ}{t : T n}{u : U n}{i : ℕ}
        → Ctx i u t → ElU u t → Maybe (ElU (tel-lkup i t) t)
  match φ-hole (top el) = just (pop el)
  match (φ-left ctx) (inl el) = match ctx el
  match (φ-left ctx) (inr el) = nothing
  match (φ-right ctx) (inl el) = nothing
  match (φ-right ctx) (inr el) = match ctx el
  match (φ-fst x ctx) (ela , elb)
    with x ≟-U elb
  ...| yes _ = match ctx ela
  ...| no  _ = nothing
  match (φ-snd x ctx) (ela , elb)
    with x ≟-U ela
  ...| yes _ = match ctx elb
  ...| no  _ = nothing 
  match (φ-pop ctx) (pop el) = pop <M> match ctx el
  match (φ-defhd ctx) (red el) = unpop <M> match ctx el
  match (φ-deftl ctxF ctxX) (red el)
    with match ctxF el
  ...| nothing      = nothing
  ...| just (pop m) = match ctxX m
  match (φ-muhd ctx) (mu el) = unpop <M> match ctx el
  match (φ-mutl ctx rec) (mu el)
    with match ctx el
  ...| nothing      = nothing
  ...| just (pop m) = match rec m
\end{code}

  Here we prove the isomorphism between our Ctx type
  and the elements inhabiting McBride's derivative notion.
  Although trivial, it's a good idea to prove this explicetely
  for posterity.

\begin{code}
  module DerivIso where
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
\end{code}

  As usual, we need to count arities of contexts too.

\begin{code}
  φ-ar : {n i : ℕ}{t : T n}{ty : U n}
       → (j : ℕ) → Ctx i ty t → ℕ
  φ-ar j (φ-left ctx)      = φ-ar j ctx
  φ-ar j (φ-right ctx)     = φ-ar j ctx
  φ-ar j (φ-fst x ctx)     = φ-ar j ctx + ar j x
  φ-ar j (φ-snd x ctx)     = φ-ar j ctx + ar j x
  φ-ar zero    (φ-pop ctx) = 0
  φ-ar (suc j) (φ-pop ctx) = φ-ar j ctx
  φ-ar zero     φ-hole     = 1
  φ-ar (suc j)  φ-hole     = 0
  φ-ar j (φ-defhd ctx)     = φ-ar (suc j) ctx
  φ-ar j (φ-deftl cF cX)   = φ-ar (suc j) cF + φ-ar j cX
  φ-ar j (φ-muhd ctx)      = φ-ar (suc j) ctx
  φ-ar j (φ-mutl ctx rec)  = φ-ar (suc j) ctx + φ-ar j rec
\end{code}

  And last, but not least, injection proofs do come in handy.

\begin{code}
  inj-φ-left : {n i : ℕ}{t : T n}{a b : U n}
             → {p q : Ctx i a t}
             → φ-left {b = b} p ≡ φ-left q
             → p ≡ q
  inj-φ-left refl = refl

  inj-φ-right : {n i : ℕ}{t : T n}{a b : U n}
              → {p q : Ctx i b t}
              → φ-right {a = a} p ≡ φ-right q
              → p ≡ q
  inj-φ-right refl = refl

  inj-φ-fst : {n i : ℕ}{t : T n}{a b : U n}
            → {x y : ElU b t}{p q : Ctx i a t}
            → φ-fst x p ≡ φ-fst y q
            → x ≡ y × p ≡ q
  inj-φ-fst refl = refl , refl

  inj-φ-snd : {n i : ℕ}{t : T n}{a b : U n}
            → {x y : ElU a t}{p q : Ctx i b t}
            → φ-snd x p ≡ φ-snd y q
            → x ≡ y × p ≡ q
  inj-φ-snd refl = refl , refl

  inj-φ-pop : {n i : ℕ}{t : T n}{a b : U n}
            → {p q : Ctx i a t}
            → φ-pop {b = b} p ≡ φ-pop q
            → p ≡ q
  inj-φ-pop refl = refl

  inj-φ-muhd : {n i : ℕ}{t : T n}{a : U (suc n)}
             → {p q : Ctx (suc i) a (μ a ∷ t)}
             → φ-muhd p ≡ φ-muhd q
             → p ≡ q
  inj-φ-muhd refl = refl

  inj-φ-defhd : {n i : ℕ}{t : T n}{x : U n}{F : U (suc n)}
              → {p q : Ctx (suc i) F (x ∷ t)}
              → φ-defhd p ≡ φ-defhd q
              → p ≡ q
  inj-φ-defhd refl = refl

  inj-φ-mutl : {n i : ℕ}{t : T n}{a : U (suc n)}
             → {c0 d0 : Ctx 0 a (μ a ∷ t)}{c1 d1 : Ctx i (μ a) t}
             → φ-mutl c0 c1 ≡ φ-mutl d0 d1
             → c0 ≡ d0 × c1 ≡ d1
  inj-φ-mutl refl = refl , refl

  inj-φ-deftl : {n i : ℕ}{t : T n}{x : U n}{F : U (suc n)}
             → {c0 d0 : Ctx 0 F (x ∷ t)}{c1 d1 : Ctx i x t}
             → φ-deftl c0 c1 ≡ φ-deftl d0 d1
             → c0 ≡ d0 × c1 ≡ d1
  inj-φ-deftl refl = refl , refl
\end{code}
