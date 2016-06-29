\begin{code}
open import Prelude
open import CF.Syntax.Core

module CF.Syntax.El where
\end{code}

%<*ElU-def>
\begin{code}
  data ElU : {n : ℕ} → U n → T n → Set where
    unit  : {n : ℕ}{t : T n} 
          → ElU u1 t
    inl   : {n : ℕ}{t : T n}{a b : U n}
          (x : ElU a t) → ElU (a ⊕ b) t
    inr   : {n : ℕ}{t : T n}{a b : U n}
          (x : ElU b t) → ElU (a ⊕ b) t
    _,_   : {n : ℕ}{t : T n}{a b : U n} 
          → ElU a t → ElU b t → ElU (a ⊗ b) t
    top   : {n : ℕ}{t : T n}{a : U n}   
          → ElU a t → ElU var (a ∷ t)
    pop   : {n : ℕ}{t : T n}{a b : U n} 
          → ElU b t → ElU (wk b) (a ∷ t)
    mu    : {n : ℕ}{t : T n}{a : U (suc n)} 
          → ElU a (μ a ∷ t) → ElU (μ a) t
    red   : {n : ℕ}{t : T n}{F : U (suc n)}{x : U n}
          → ElU F (x ∷ t)
          → ElU (def F x) t
\end{code}
%</ElU-def>

\begin{code}
  inj-inl : {n : ℕ}{t : T n}{a b : U n}{x y : ElU a t} 
          → inl {n} {t} {a} {b} x ≡ inl y → x ≡ y
  inj-inl refl = refl

  inj-inr : {n : ℕ}{t : T n}{a b : U n}{x y : ElU b t} 
          → inr {n} {t} {a} {b} x ≡ inr y → x ≡ y
  inj-inr refl = refl

  inj-, : {n : ℕ}{t : T n}{a b : U n}{xa ya : ElU a t}{xb yb : ElU b t}
        → _≡_ {a = lz} {A = ElU (a ⊗ b) t} (_,_ {n} {t} {a} {b} xa xb) (ya , yb) 
        → (xa ≡ ya × xb ≡ yb)
  inj-, refl = refl , refl

  inj-top : {n : ℕ}{t : T n}{a : U n}{x y : ElU a t}
          → top {n} {t} {a} x ≡ top y → x ≡ y
  inj-top refl = refl

  inj-pop : {n : ℕ}{t : T n}{a b : U n}{x y : ElU b t}
          → pop {n} {t} {a} {b} x ≡ pop y → x ≡ y
  inj-pop refl = refl

  inj-mu : {n : ℕ}{t : T n}{a : U (suc n)}{x y : ElU a (μ a ∷ t)}
         → mu {n} {t} {a} x ≡ mu y → x ≡ y
  inj-mu refl = refl

  inj-red : {n : ℕ}{t : T n}{F : U (suc n)}{x : U n}{a b : ElU F (x ∷ t)}
           → red {n} {t} {F} {x} a ≡ red b
           → a ≡ b
  inj-red refl = refl
\end{code}

\begin{code}
  unpop : {n : ℕ}{t : T n}{x : U n}{a : U n}
        → ElU (wk a) (x ∷ t) → ElU a t
  unpop (pop el) = el
\end{code}

\begin{code}
  unmu : {n : ℕ}{t : T n}{a : U (suc n)}
        → ElU (μ a) t → ElU a (μ a ∷ t)
  unmu (mu el) = el
\end{code}

\begin{code}
  inl≡inr→⊥ : {n : ℕ}{t : T n}{a b : U n}
            → {x : ElU a t}{y : ElU b t}
            → inl x ≡ inr y → ⊥
  inl≡inr→⊥ ()
\end{code}
