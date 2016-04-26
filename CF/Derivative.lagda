\begin{code}
open import Prelude

open import CF.Syntax
open import CF.Equality

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
            → Ctx i a t → ElU b t → Ctx i (a ⊗ b) t
    φ-snd   : {n i : ℕ}{t : T n}{a b : U n}
            → Ctx i b t → ElU a t → Ctx i (a ⊗ b) t
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
  φ-fst ctx k ◂ x = (ctx ◂ x , k)
  φ-snd ctx k ◂ x = (k , ctx ◂ x)
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
  match (φ-fst ctx x) (ela , elb)
    with x ≟-U elb
  ...| yes _ = match ctx ela
  ...| no  _ = nothing
  match (φ-snd ctx x) (ela , elb)
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

  For the sake of completeness, we shall prove correctness
  of both operations.

\begin{code}

  module Properties where

    match-correct : {n : ℕ}{t : T n}{u : U n}{i : ℕ}
                  → (ctx : Ctx i u t)(x : ElU (tel-lkup i t) t)
                  → match ctx (ctx ◂ x) ≡ just x
    match-correct ctx x = {!!}
      where
        aux : {n : ℕ}{t : T n}{u : U n}{i : ℕ}
            → (ctx : Ctx i u t)(x : ElU (tel-lkup i t) t)
            → (y : ElU u t)
            → (hip : ctx ◂ x ≡ y)
            → match ctx y ≡ just x
        aux {t = t ∷ ts} φ-hole (pop x) (top y) hip
          rewrite inj-top (sym hip) = refl
        aux (φ-left ctx₁) x₁ (inl y) hip = {!!}
        aux (φ-left ctx₁) x₁ (inr y) hip = {!!}
        aux (φ-right ctx₁) x₁ (inl y) hip = {!!}
        aux (φ-right ctx₁) x₁ (inr y) hip = {!!}
        aux (φ-fst ctx₁ x₁) x₂ (ya , yb) hip
          with x₁ ≟-U yb
        ...| no  _ = {!!}
        ...| yes _ = {!!}
        aux (φ-snd ctx₁ x₁) x₂ y hip = {!!}
        aux (φ-pop ctx₁) x₁ y hip = {!!}
        aux (φ-defhd ctx₁) x₂ y hip = {!!}
        aux (φ-deftl ctx₁ ctx₂) x₂ y hip = {!!}
        aux (φ-muhd ctx₁) x₁ y hip = {!!}
        aux (φ-mutl ctx₁ ctx₂) x₁ y hip = {!!}

    

\end{code}
