\begin{code}
open import Prelude
open import Prelude.Vector

open import Data.Nat
  using (_≤_; z≤n; s≤s)
open import Data.Nat.Properties.Simple
  using (+-comm; +-assoc)
open import Data.List.Properties
    using (length-map; length-++; map-compose)

open import CF.Syntax
open import CF.Operations

module CF.Operations.Properties where
\end{code}

  This module provides a bunch of lemmas relating
  the operations defined in CF.Operations.

  The most important lemma being 'ar-lemma' in its both variants.


%<*ch-ar-lemma-type>
\begin{code}
  ch-ar-lemma : {n : ℕ}{t : T n}{ty : U n}
              → (i : ℕ)(el : ElU ty t)
              → length (ch i el) ≡ ar i el
\end{code}
%</ch-ar-lemma-type>
\begin{code}
  ch-ar-lemma i unit = refl
  ch-ar-lemma i (inl el) = ch-ar-lemma i el
  ch-ar-lemma i (inr el) = ch-ar-lemma i el
  ch-ar-lemma i (ela , elb) 
    = trans (length-++ (ch i ela)) 
            (cong₂ _+_ (ch-ar-lemma i ela) (ch-ar-lemma i elb))
  ch-ar-lemma zero (top el) 
    = refl
  ch-ar-lemma (suc i) (top el) 
    = trans (length-map pop (ch i el)) 
            (ch-ar-lemma i el)
  ch-ar-lemma zero (pop el) 
    = refl
  ch-ar-lemma (suc i) (pop el) 
    = trans (length-map pop (ch i el)) 
            (ch-ar-lemma i el)
  ch-ar-lemma i (mu el) 
    = trans (length-map unpop (ch (suc i) el))
            (ch-ar-lemma (suc i) el)
  ch-ar-lemma i (red el) 
    = trans (length-map unpop (ch (suc i) el))
            (ch-ar-lemma (suc i) el)
\end{code}


%<*fgt-ar-lemma-type>
\begin{code}
  fgt-ar-lemma : {n : ℕ}{t : T n}{ty : U n}
               → (i : ℕ)(el : ElU ty t)
               → ar i el ≡ ar i (fgt i el)
\end{code}
%</fgt-ar-lemma-type>
\begin{code}
  fgt-ar-lemma i unit = refl
  fgt-ar-lemma i (inl el) = fgt-ar-lemma i el
  fgt-ar-lemma i (inr el) = fgt-ar-lemma i el
  fgt-ar-lemma i (ela , elb) 
    = cong₂ _+_ (fgt-ar-lemma i ela) (fgt-ar-lemma i elb)
  fgt-ar-lemma zero (top el) = refl
  fgt-ar-lemma (suc i) (top el) = fgt-ar-lemma i el
  fgt-ar-lemma zero (pop el) = refl
  fgt-ar-lemma (suc i) (pop el) = fgt-ar-lemma i el
  fgt-ar-lemma i (mu el) = fgt-ar-lemma (suc i) el
  fgt-ar-lemma i (red el) = fgt-ar-lemma (suc i) el
\end{code}

%<*fgt-all-ar-dry-lemma-type>
\begin{code}
  FGT-ar-dry-lemma
    : {n : ℕ}{t : T n}{ty : U n}
    → (i : ℕ)(el : ElU ty t)
    → ar-dry i el ≡ ar i (FGT i el)
\end{code}
%</fgt-all-ar-dry-lemma-type>
\begin{code}
  FGT-ar-dry-lemma i unit = {!!}
  FGT-ar-dry-lemma i (inl el) = {!!}
  FGT-ar-dry-lemma i (inr el) = {!!}
  FGT-ar-dry-lemma i (el , el₁) = {!!}
  FGT-ar-dry-lemma i (top el) = {!!}
  FGT-ar-dry-lemma i (pop el) = {!!}
  FGT-ar-dry-lemma {t = []}     i (mu el)
    = {!FGT-ar-dry-lemma (suc i) el!}
  FGT-ar-dry-lemma {t = t ∷ ts} i (mu el) = {!i!}
  FGT-ar-dry-lemma i (red el) = {!!}
\end{code}


%<*fgt-ar-lemma-type>
\begin{code}
  ch-fgt-ar-lemma 
    : {n : ℕ}{t : T n}{ty : U n}
    → (i : ℕ)(el : ElU ty t)
    → length (ch i el) ≡ ar i (fgt i el)
\end{code}
%</fgt-ar-lemma-type>
\begin{code}
  ch-fgt-ar-lemma i el = trans (ch-ar-lemma i el) (fgt-ar-lemma i el)
\end{code}

\begin{code}
  ch-v : {n : ℕ}{t : T n}{ty : U n}
       → (i : ℕ)(el : ElU ty t)
       → Vec (ElU (tel-lkup i t) t) (ar i (fgt i el))
  ch-v i el = vec (ch i el) (ch-fgt-ar-lemma i el)
\end{code}

\begin{code}
  ar*-unpop : {n : ℕ}{t : T n}{a ty : U n}
            → (i : ℕ)(es : List (ElU (wk ty) (a ∷ t)))
            → ar* i (map unpop es) ≡ ar* (suc i) es
  ar*-unpop i []           = refl
  ar*-unpop i (pop x ∷ es) = cong (λ P → ar i x + P) (ar*-unpop i es)

  ar*-pop : {n : ℕ}{t : T n}{a ty : U n}
          → (i : ℕ)(es : List (ElU ty t))
          → ar* (suc i) (map (pop {a = a}) es) ≡ ar* i es
  ar*-pop i [] = refl
  ar*-pop i (x ∷ es) = cong (λ P → ar i x + P) (ar*-pop i es)

  private
    ar*-zero-pop : {n : ℕ}{t : T n}{a ty : U n}
                 → (es : List (ElU ty t))
                 → ar* 0 (map (pop {a = a}) es) ≡ 0
    ar*-zero-pop []       = refl
    ar*-zero-pop (x ∷ es) = ar*-zero-pop es

  ar*-++-commute 
    : {n : ℕ}{t : T n}{ty : U n}
    → (i : ℕ)(xs ys : List (ElU ty t))
    → ar* i (xs ++ ys) ≡ ar* i xs + ar* i ys
  ar*-++-commute i [] ys = refl
  ar*-++-commute i (x ∷ xs) ys 
    = trans (cong (λ P → ar i x + P) (ar*-++-commute i xs ys))
            (sym (+-assoc (ar i x) (ar* i xs) (ar* i ys)))

  +-exch : (m n o p : ℕ)
         → (m + n) + (o + p) ≡ (m + o) + (n + p)
  +-exch m n o p = 
    trans (sym (+-assoc (m + n) o p)) (
      trans (cong (λ P → P + p) (+-assoc m n o)) (
        trans (cong (λ P → m + P + p) (+-comm n o)) (
          trans (cong (λ P → P + p) (sym (+-assoc m o n)))
                (+-assoc (m + o) n p)
          )))
\end{code}

%<*ar-lemma-type>
\begin{code}
  ar-lemma : {n : ℕ}{t : T n}{ty : U n}
           → (i j : ℕ)(el : ElU ty t)
           → ar i el 
           ≡ ar i (fgt j el) + ar* i (ch j el)
\end{code}
%</ar-lemma-type>
\begin{code}
  ar-lemma i j unit     = refl
  ar-lemma i j (inl el) = ar-lemma i j el
  ar-lemma i j (inr el) = ar-lemma i j el
  ar-lemma i j (ela , elb) 
    rewrite ar*-++-commute i (ch j ela) (ch j elb)
          | +-exch (ar i (fgt j ela)) (ar i (fgt j elb))
                   (ar* i (ch j ela)) (ar* i (ch j elb))
          = cong₂ _+_ (ar-lemma i j ela) (ar-lemma i j elb)
  ar-lemma i j (mu el) 
    rewrite ar*-unpop i (ch (suc j) el)
          = ar-lemma (suc i) (suc j) el
  ar-lemma i j (red el) 
    rewrite ar*-unpop i (ch (suc j) el)
          = ar-lemma (suc i) (suc j) el 
  ar-lemma zero zero (top el) 
    = refl
  ar-lemma (suc i) zero (top el) 
    = sym (+-comm (ar i el) 0)
  ar-lemma zero (suc j) (top el) 
    = sym (cong suc (ar*-zero-pop (ch j el)))
  ar-lemma (suc i) (suc j) (top {a = a} el) 
    rewrite ar*-pop {a = a} i (ch j el) 
          = ar-lemma i j el
  ar-lemma zero zero (pop el) 
    = refl
  ar-lemma zero (suc j) (pop el) 
    = sym (ar*-zero-pop (ch j el))
  ar-lemma (suc i) zero (pop el) 
    = sym (+-comm (ar i el) 0)
  ar-lemma (suc i) (suc j) (pop {a = a} el) 
    rewrite ar*-pop {a = a} i (ch j el)
          = ar-lemma i j el
\end{code}

\begin{code}
  ar*-sum-map-lemma 
    : {n : ℕ}{t : T n}{ty : U n}(i : ℕ)(xs : List (ElU ty t))
    → ar* i xs ≡ sum (map (ar i) xs)
  ar*-sum-map-lemma i [] = refl
  ar*-sum-map-lemma i (x ∷ xs) 
    = cong (λ P → ar i x + P) (ar*-sum-map-lemma i xs)
\end{code}

%<*ar-std-lemma-type>
\begin{code}
  ar-std-lemma 
    : {n : ℕ}{t : T n}{ty : U n}
    → (i j : ℕ)(el : ElU ty t)
    → ar i el 
    ≡ ar i (fgt j el) + sum (map (ar i) (ch j el))
\end{code}
%</ar-std-lemma-type>
\begin{code}
  ar-std-lemma i j el 
    = trans (ar-lemma i j el) 
            (cong (λ P → ar i (fgt j el) + P) 
                  (ar*-sum-map-lemma i (ch j el)))
\end{code}

\begin{code}
  ar*v-reduce : {n j k : ℕ}{t : T n}{ty : U n}(i : ℕ)
              → (xs : Vec (ElU ty t) j)(ys : Vec (ElU ty t) k)
              → ar*v i (xs ++v ys) ≡ ar* i (toList xs) + ar*v i ys
  ar*v-reduce i [] ys = refl
  ar*v-reduce i (x ∷ xs) ys 
    = trans (cong (λ P → ar i x + P) (ar*v-reduce i xs ys)) 
            (sym (+-assoc (ar i x) (ar* i (toList xs)) (ar*v i ys)))
\end{code}
