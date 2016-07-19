\begin{code}
open import Prelude
open import CF.Syntax.Core

module CF.Syntax.El where
\end{code}

\begin{code}
  E-Set : Set₁
  E-Set = {n : ℕ} → U n → T n → Set

  _⇉_ : E-Set → E-Set → Set
  A ⇉ B = {n : ℕ}{t : T n}{ty : U n} → A ty t → B ty t
\end{code}

%<*E-def>
\begin{code}
  data E (A : E-Set) : {n : ℕ} → U n → T n → Set where
    hole  : {n : ℕ}{t : T n}{ty : U n}
          → A ty t → E A ty t
    unit  : {n : ℕ}{t : T n} 
          → E A u1 t
    inl   : {n : ℕ}{t : T n}{a b : U n}
          (x : E A a t) → E A (a ⊕ b) t
    inr   : {n : ℕ}{t : T n}{a b : U n}
          (x : E A b t) → E A (a ⊕ b) t
    _,_   : {n : ℕ}{t : T n}{a b : U n} 
          → E A a t → E A b t → E A (a ⊗ b) t
    top   : {n : ℕ}{t : T n}{a : U n}   
          → E A a t → E A var (a ∷ t)
    pop   : {n : ℕ}{t : T n}{a b : U n} 
          → E A b t → E A (wk b) (a ∷ t)
    mu    : {n : ℕ}{t : T n}{a : U (suc n)} 
          → E A a (μ a ∷ t) → E A (μ a) t
    red   : {n : ℕ}{t : T n}{F : U (suc n)}{x : U n}
          → E A F (x ∷ t)
          → E A (def F x) t
\end{code}
%</E-def>

\begin{code}
  e↑ : Set → E-Set
  e↑ A = λ {_} _ _ → A

  ElU : {n : ℕ} → U n → T n → Set
  ElU = E (e↑ ⊥)

  ElT : {n : ℕ} → E-Set → ℕ → T n → Set
  ElT A i       []       = ⊥
  ElT A zero    (x ∷ t)  = E A x t
  ElT A (suc i) (x ∷ t)  = ElT A i t
\end{code}

\begin{code}
  inj-inl : {A : E-Set}{n : ℕ}{t : T n}{a b : U n}{x y : E A a t} 
          → inl {A} {n} {t} {a} {b} x ≡ inl y → x ≡ y
  inj-inl refl = refl

  inj-inr : {A : E-Set}{n : ℕ}{t : T n}{a b : U n}{x y : E A b t} 
          → inr {A} {n} {t} {a} {b} x ≡ inr y → x ≡ y
  inj-inr refl = refl

  inj-, : {A : E-Set}{n : ℕ}{t : T n}{a b : U n}{xa ya : E A a t}{xb yb : E A b t}
        → _≡_ {a = lz} {A = E A (a ⊗ b) t} (_,_ {A} {n} {t} {a} {b} xa xb) (ya , yb) 
        → (xa ≡ ya × xb ≡ yb)
  inj-, refl = refl , refl

  inj-top : {A : E-Set}{n : ℕ}{t : T n}{a : U n}{x y : E A a t}
          → top {A} {n} {t} {a} x ≡ top y → x ≡ y
  inj-top refl = refl

  inj-pop : {A : E-Set}{n : ℕ}{t : T n}{a b : U n}{x y : E A b t}
          → pop {A} {n} {t} {a} {b} x ≡ pop y → x ≡ y
  inj-pop refl = refl

  inj-mu : {A : E-Set}{n : ℕ}{t : T n}{a : U (suc n)}{x y : E A a (μ a ∷ t)}
         → mu {A} {n} {t} {a} x ≡ mu y → x ≡ y
  inj-mu refl = refl

  inj-red : {A : E-Set}{n : ℕ}{t : T n}{F : U (suc n)}{x : U n}{a b : E A F (x ∷ t)}
           → red {A} {n} {t} {F} {x} a ≡ red b
           → a ≡ b
  inj-red refl = refl

  inj-hole : {A : E-Set}{n : ℕ}{t : T n}{ty : U n}{x y : A ty t}
           → hole {A} {n} {t} {ty} x ≡ hole y → x ≡ y
  inj-hole refl = refl
\end{code}

\begin{code}
  e-map : {A B : E-Set}{n : ℕ}{t : T n}{ty : U n}
        → (f : A ⇉ B) → E A ty t → E B ty t
  e-map f (hole x)  = hole (f x)
  e-map f unit      = unit
  e-map f (inl x)   = inl (e-map f x)
  e-map f (inr x)   = inr (e-map f x)
  e-map f (x , y)   = e-map f x , e-map f y
  e-map f (top x)   = top (e-map f x)
  e-map f (pop x)   = pop (e-map f x)
  e-map f (mu x)    = mu (e-map f x)
  e-map f (red x)   = red (e-map f x)

  e-cast : {A : E-Set}{n : ℕ}{t : T n}{ty : U n}
         → E (e↑ ⊥) ty t → E A ty t
  e-cast = e-map ⊥-elim

  e-count : {A : E-Set}{n : ℕ}{t : T n}{ty : U n}
          → E A ty t → ℕ
  e-count (hole x) = 1
  e-count unit = 0
  e-count (inl x) = e-count x
  e-count (inr x) = e-count x
  e-count (x , y) = e-count x + e-count y
  e-count (top x) = e-count x
  e-count (pop x) = e-count x
  e-count (mu x) = e-count x
  e-count (red x) = e-count x
\end{code}

\begin{code}
  unpop : {n : ℕ}{t : T n}{x : U n}{a : U n}
        → ElU (wk a) (x ∷ t) → ElU a t
  unpop (hole ())
  unpop (pop el) = el
\end{code}

\begin{code}
  unmu : {n : ℕ}{t : T n}{a : U (suc n)}
        → ElU (μ a) t → ElU a (μ a ∷ t)
  unmu (hole ())
  unmu (mu el) = el
\end{code}

\begin{code}
  inl≡inr→⊥ : {A : E-Set}{n : ℕ}{t : T n}{a b : U n}
            → {x : E A a t}{y : E A b t}
            → inl x ≡ inr y → ⊥
  inl≡inr→⊥ ()
\end{code}
