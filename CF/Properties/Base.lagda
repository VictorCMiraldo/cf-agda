\begin{code}
open import Prelude
open import Prelude.Vector

open import Prelude.NatProperties
  using (+-comm; +-assoc; m+n∸n≡m)
open import Prelude.ListProperties
  using (length-map; length-++; map-compose)

open import CF.Syntax
open import CF.Operations.Base

module CF.Properties.Base where
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

  Simple algebraic manipulation of ar-lemma gives us:
  
\begin{code}
  ar-fgt-lemma-sub
    : {n : ℕ}{t : T n}{ty : U n}
    → (i j : ℕ)(el : ElU ty t)
    → ar i (fgt j el) ≡ ar i el ∸ ar* i (ch j el)
  ar-fgt-lemma-sub i j el
    rewrite ar-lemma i j el
      = sym (m+n∸n≡m (ar i (fgt j el)) (ar* i (ch j el)))
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


%<*plug-just-lemma-type>
\begin{code}
  plug-just-lemma
    : {n : ℕ}{t : T n}{ty : U n}
    → (i : ℕ)(el : ElU ty (tel-forget i t))
    → (as : List (ElU (tel-lkup i t) t))
    → ar i el ≤ length as
    → Is-Just (plug i el as)
\end{code}
%</plug-just-lemma-type>
%<*plug-just-lemma-def>
\begin{code}
  plug-just-lemma {ty = u0} i () as hip
  plug-just-lemma {ty = u1} i unit as hip = indeed unit
  plug-just-lemma {ty = ty ⊕ tv} i (inl el) as hip 
    = Is-Just-<M> (plug-just-lemma i el as hip)
  plug-just-lemma {ty = ty ⊕ tv} i (inr el) as hip
    = Is-Just-<M> (plug-just-lemma i el as hip)
  plug-just-lemma {ty = ty ⊗ tv} i (ela , elb) as hip 
    = let hipA , hipB = lsplit-length-lemma as (ar i ela) (ar i elb) hip
          asA  , asB  = lsplit (ar i ela) as
       in Is-Just-<M*> (Is-Just-<M> (plug-just-lemma i ela asA hipA)) 
                       (plug-just-lemma i elb asB hipB)
  plug-just-lemma {ty = def F ty} i (red el) as hip 
    = Is-Just-<M> (plug-just-lemma (suc i) el (map pop as) 
                                   (subst (λ P → ar (suc i) el ≤ P) 
                                   (sym (length-map pop as)) hip))
  plug-just-lemma {ty = μ ty} i (mu el) as hip
    = Is-Just-<M> (plug-just-lemma (suc i) el (map pop as) 
                                   (subst (λ P → ar (suc i) el ≤ P) 
                                   (sym (length-map pop as)) hip))
  plug-just-lemma {t = t ∷ ts} {ty = var} zero (top el) [] () 
  plug-just-lemma {t = t ∷ ts} {ty = var} zero (top el) (a ∷ as) hip 
    = indeed (top (unpop a))
  plug-just-lemma {t = t ∷ ts} {ty = var} (suc i) (top el) as hip 
    = Is-Just-<M> (plug-just-lemma i el (map unpop as) 
                  (subst (λ P → ar i el ≤ P) (sym (length-map unpop as)) hip))
  plug-just-lemma {t = t ∷ ts} {ty = wk ty} zero (pop el) as hip 
    = indeed (pop el)
  plug-just-lemma {t = t ∷ ts} {ty = wk ty} (suc i) (pop el) as hip 
    = Is-Just-<M> (plug-just-lemma i el (map unpop as) 
                  (subst (λ P → ar i el ≤ P) (sym (length-map unpop as)) hip))
\end{code}
%</plug-just-lemma-def>


%<*plug-correct-type>
\begin{code}
  plug-correct 
    : {n : ℕ}{t : T n}{ty : U n}
    → (i : ℕ)(el : ElU ty t)
    → just el ≡ plug i (fgt i el) (ch i el)
\end{code}
%</plug-correct-type>
%<*plug-correct-def>
\begin{code}
  plug-correct i unit = refl
  plug-correct i (inl el) 
    rewrite sym (plug-correct i el) = refl
  plug-correct i (inr el)
    rewrite sym (plug-correct i el) = refl
  plug-correct i (ela , elb) 
    rewrite sym (ch-fgt-ar-lemma i ela)
          | lsplit-++-lemma (ch i ela) (ch i elb)
          | sym (plug-correct i ela) 
          | sym (plug-correct i elb)
          = refl
  plug-correct {t = t ∷ ts} zero (top el) 
    = refl
  plug-correct {t = t ∷ ts} (suc i) (top el) 
    rewrite map-lemma {f = pop {a = t}} {unpop} (ch i el) (λ x → refl)
          | sym (plug-correct i el)
          = refl
  plug-correct {t = t ∷ ts} zero (pop el) = refl
  plug-correct {t = t ∷ ts} (suc i) (pop el)
    rewrite map-lemma {f = pop {a = t}} {unpop} (ch i el) (λ x → refl)
          | sym (plug-correct i el)
          = refl
  plug-correct i (mu el)
    rewrite map-lemma {f = unpop} {pop} (ch (suc i) el) (λ { (pop x) → refl })
          | sym (plug-correct (suc i) el)
          = refl
  plug-correct i (red el)
    rewrite map-lemma {f = unpop} {pop} (ch (suc i) el) (λ { (pop x) → refl })
          | sym (plug-correct (suc i) el)
          = refl
\end{code}
%</plug-correct-def>
