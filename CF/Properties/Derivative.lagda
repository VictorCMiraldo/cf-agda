\begin{code}
open import Prelude
open import Prelude.Vector

open import CF.Syntax
open import CF.Equality
open import CF.Operations.Base
open import CF.Operations.Dry
open import CF.Derivative
open import CF.Operations.Derivative

open import Data.List.Properties using (length-map; length-++; map-++-commute)
open import Data.Nat.Properties.Simple using (+-comm)

module CF.Properties.Derivative where
\end{code}

  For the sake of completeness, we shall prove correctness
  of both operations.

\begin{code}
  match-correct : {n : ℕ}{t : T n}{u : U n}{i : ℕ}
                → (ctx : Ctx i u t)(x : ElU (tel-lkup i t) t)
                → match ctx (ctx ◂ x) ≡ just x
  match-correct {t = []} ctx ()
  match-correct {t = t ∷ ts} φ-hole (pop x)  = refl
  match-correct {t = t ∷ ts} (φ-left ctx) x  = match-correct ctx x
  match-correct {t = t ∷ ts} (φ-right ctx) x = match-correct ctx x
  match-correct {t = t ∷ ts} (φ-fst k ctx) x
    rewrite ≟-U-refl k = match-correct ctx x
  match-correct {t = t ∷ ts} (φ-snd k ctx) x
    rewrite ≟-U-refl k = match-correct ctx x
  match-correct {t = t ∷ ts} (φ-pop ctx) (pop x)
    = <M>-intro (match-correct ctx x)
  match-correct {t = t ∷ ts} (φ-defhd ctx) x
    rewrite match-correct ctx (pop x)
          = refl
  match-correct {t = t ∷ ts} (φ-deftl ctxF ctxX) x
    rewrite match-correct ctxF (pop (ctxX ◂ x))
          = match-correct ctxX x
  match-correct {t = t ∷ ts} (φ-muhd ctx) x
    rewrite match-correct ctx (pop x)
          = refl
  match-correct {t = t ∷ ts} (φ-mutl ctx rec) x
    rewrite match-correct ctx (pop (rec ◂ x))
          = match-correct rec x
\end{code}

\begin{code}
  ◂-correct : {n : ℕ}{t : T n}{u : U n}{i : ℕ}
            → (ctx : Ctx i u t)(x : ElU u t)(y : ElU (tel-lkup i t) t)
            → match ctx x ≡ just y
            → (ctx ◂ y) ≡ x
  ◂-correct {t = []} ctx x () hip
  ◂-correct {t = t ∷ ts} φ-hole (top x) (pop .x) refl
    = refl
  ◂-correct {t = t ∷ ts} (φ-left ctx) (inl x) y hip
    = cong inl (◂-correct ctx x y hip)
  ◂-correct {t = t ∷ ts} (φ-left ctx) (inr x) y ()
  ◂-correct {t = t ∷ ts} (φ-right ctx) (inl x) y ()
  ◂-correct {t = t ∷ ts} (φ-right ctx) (inr x) y hip
    = cong inr (◂-correct ctx x y hip)
  ◂-correct {t = t ∷ ts} (φ-fst k ctx) (xa , xb) y hip
    with k ≟-U xb
  ...| no  _ = ⊥-elim (Maybe-⊥ (sym hip))
  ...| yes p rewrite p = cong (λ P → P , xb) (◂-correct ctx xa y hip)
  ◂-correct {t = t ∷ ts} (φ-snd k ctx) (xa , xb) y hip
    with k ≟-U xa
  ...| no  _ = ⊥-elim (Maybe-⊥ (sym hip))
  ...| yes p rewrite p = cong (λ P → xa , P) (◂-correct ctx xb y hip)
  ◂-correct {t = t ∷ ts} (φ-pop ctx) (pop x) (pop y) hip
    with <M>-elim hip
  ...| .y , refl , r = cong pop (◂-correct ctx x y r)
  ◂-correct {t = t ∷ ts} (φ-defhd ctx) (red x) y hip
    with <M>-elim hip
  ...| (pop .y) , refl , r
     = cong red (◂-correct ctx x (pop y) r)
  ◂-correct {t = t ∷ ts} (φ-deftl ctxF ctxX) (red x) y hip
    with match ctxF x | inspect (match ctxF) x
  ...| nothing      | _  = ⊥-elim (Maybe-⊥ (sym hip))
  ...| just (pop k) | [ R ] rewrite ◂-correct ctxX k y hip
     = cong red (◂-correct ctxF x (pop k) R)
  ◂-correct {t = t ∷ ts} (φ-muhd ctx) (mu x) y hip
    with <M>-elim hip
  ...| (pop .y) , refl , r
     = cong mu (◂-correct ctx x (pop y) r)
  ◂-correct {t = t ∷ ts} (φ-mutl ctx rec) (mu x) y hip
    with match ctx x | inspect (match ctx) x
  ...| nothing      | _  = ⊥-elim (Maybe-⊥ (sym hip))
  ...| just (pop k) | [ R ] rewrite ◂-correct rec k y hip
     = cong mu (◂-correct ctx x (pop k) R)
\end{code}

\begin{code}
  private
    nat-1-≤-aux : (n m : ℕ) → 1 ≤ n + m → 1 ≤ n ⊎ 1 ≤ m
    nat-1-≤-aux zero    m hip = i2 hip
    nat-1-≤-aux (suc n) m hip = i1 (s≤s z≤n)

    length-concat : {A : Set}(l : List (List A))
                  → length (concat l) ≡ sum (map length l)
    length-concat [] = refl
    length-concat (x ∷ xs)
      = trans (length-++ x {ys = concat xs})
              (cong (length x +_) (length-concat xs))

    map-compose : {A B C : Set}(f : A → B)(g : B → C)
                → (l : List A)
                → map g (map f l) ≡ map (g ∘ f) l
    map-compose f g [] = refl
    map-compose f g (x ∷ l) = cong (g (f x) ∷_) (map-compose f g l)

    λ-length-map : {A B C : Set}(f : A → B → C)(l : A → List B)
                 → length ∘ (λ x → map (f x) (l x)) ≡ (λ x → length (l x))
    λ-length-map f l = fun-ext (λ x → length-map (f x) (l x))

    ar-dry-unpop : {n : ℕ}{t : T n}{a b : U n}
                 → (i : ℕ)(x : ElU (wk a) (b ∷ t))
                 → ar-dry i (unpop x) ≡ ar-dry (suc i) x
    ar-dry-unpop i (pop x) = refl
\end{code}

  We can count the zippers of a term by it's dry-arity!

\begin{code}
  Z-ch-lemma : {n : ℕ}{t : T n}{ty : U n}
             → (i : ℕ)(x : ElU ty t)
             → map p2 (Z i x) ≡ ch i x
  Z-ch-lemma i unit = refl
  Z-ch-lemma i (inl x) = {!!}
  Z-ch-lemma i (inr x) = {!!}
  Z-ch-lemma i (x , x₁) = {!!}
  Z-ch-lemma i (top x) = {!!}
  Z-ch-lemma i (pop x) = {!!}
  Z-ch-lemma {n} {t} {μ a} i (mu x)
    = let z : List (List (Ctx i (μ a) t × ElU (tel-lkup i t) t))
          z = map (λ { (ctx0 , chX)
                    → map (φ-mutl ctx0 ×' id) (Z i (unpop chX)) })
              (Z 0 x)

          y : List (Ctx i (μ a) t × ElU (tel-lkup i t) t)
          y = map (λ xy → φ-muhd (p1 xy) , unpop (p2 xy)) (Z (suc i) x)
      in trans (map-++-commute p2 y (concat z))
               {!!}
  Z-ch-lemma i (red x₁) = {!!}
\end{code}

\begin{code}
  {-# TERMINATING #-}
  length-Z-lemma
    : {n : ℕ}{t : T n}{a : U n}
    → (i : ℕ)(x : ElU a t)
    → ar-dry i x ≤ length (Z i x)
\end{code}
\begin{code}
  length-Z-lemma i unit = {!!}
  length-Z-lemma i (inl x) = {!!}
  length-Z-lemma i (inr x) = {!!}
  length-Z-lemma i (x , y) = {!!}
  length-Z-lemma i (top x) = {!!}
  length-Z-lemma i (pop x) = {!!}
  length-Z-lemma {n} {t} {μ a} i (mu x)
    = {!!}
  length-Z-lemma i (red x) = {!!}
\end{code}

begin{code}
  {-# TERMINATING #-}
  length-Z
    : {n : ℕ}{t : T n}{a : U n}
    → (i : ℕ)(x : ElU a t)
    → length (Z i x) ≡ ar-dry i x
end{code}
begin{code}
  length-Z i unit = {!!}
  length-Z i (inl el) = {!!}
  length-Z i (inr el) = {!!}
  length-Z i (el , el₁) = {!!}
  length-Z i (top el) = {!!}
  length-Z i (pop el) = {!!}
  length-Z {n} {t} {μ a} i (mu el)
    = let z : List (List (Ctx i (μ a) t × ElU (tel-lkup i t) t))
          z = map (λ { (ctx0 , chX)
                    → map (φ-mutl ctx0 ×' id) (Z i (unpop chX)) })
              (Z 0 el)

          y : List (Ctx i (μ a) t × ElU (tel-lkup i t) t)
          y = map (λ xy → φ-muhd (p1 xy) , unpop (p2 xy)) (Z (suc i) el)
       in trans (length-++ y {ys = concat z})
         (trans (cong₂ _+_ (length-map _ (Z (suc i) el))
                           (length-concat z))
         (cong₂ _+_ (length-Z (suc i) el)
         (trans (cong sum (map-compose _ length (Z 0 el)))
         (trans (cong (λ P → sum (map P (Z 0 el)))
                      (λ-length-map (λ a → (φ-mutl (p1 a) ×' id))
                      (λ a → Z i (unpop (p2 a)))))
         (trans (cong (λ P → sum (map P (Z 0 el)))
                      (fun-ext (λ x → trans (length-Z i (unpop (p2 x)))
                                            (ar-dry-unpop i (p2 x)))))
         (trans (cong sum (sym (map-compose p2 (λ x → ar-dry (suc i) x) (Z 0 el))))
         (cong (λ P → sum (map (ar-dry (suc i)) P))
               (Z-ch-lemma 0 el))))))))
  length-Z i (red el) = {!!}
end{code}

begin{code}
  length-Z
    : {n : ℕ}{t : T n}{a : U n}
    → (i : ℕ)(x : ElU a t)(hip : 1 ≤ ar-dry i x)
    → ∃ (λ n → suc n ≡ length (Z i x))
end{code}
begin{code}
  length-Z i unit ()
  length-Z i (inl x) hip
    with length-Z i x hip
  ...| (n , prf)
     = n , trans prf (sym (length-map (λ xy → φ-left (p1 xy) , p2 xy) (Z i x)))
  length-Z i (inr x) hip
    with length-Z i x hip
  ...| (n , prf)
     = n , trans prf (sym (length-map (λ xy → φ-right (p1 xy) , p2 xy) (Z i x)))
  length-Z i (x , y) hip
    with nat-1-≤-aux (ar-dry i x) (ar-dry i y) hip
  length-Z i (x , y) hip | i1 hipx
    with length-Z i x hipx
  ...| (k , prf) = k + length (Z i y)
                 , sym (trans (length-++ (map (λ xy → φ-fst y (p1 xy) , p2 xy) (Z i x)))
                       (trans (cong₂ _+_ (length-map (λ xy → φ-fst y (p1 xy) , p2 xy) (Z i x))
                                         (length-map (λ xy → φ-snd x (p1 xy) , p2 xy) (Z i y)))
                              (cong (_+ length (Z i y)) (sym prf))))
  length-Z i (x , y) hip | i2 hipy
    with length-Z i y hipy
  ...| (k , prf) = k + length (Z i x)
                 , sym (trans (length-++ (map (λ xy → φ-fst y (p1 xy) , p2 xy) (Z i x)))
                       (trans (cong₂ _+_ (length-map (λ xy → φ-fst y (p1 xy) , p2 xy) (Z i x))
                                         (length-map (λ xy → φ-snd x (p1 xy) , p2 xy) (Z i y)))
                       (trans (+-comm (length (Z i x)) (length (Z i y)))
                              (cong (_+ length (Z i x)) (sym prf)))))
  length-Z zero (top x) hip = 0 , refl
  length-Z (suc i) (top x) ()
  length-Z zero (pop x) ()
  length-Z (suc i) (pop x) hip
    with length-Z i x hip
  ...| (k , prf) = k , sym (trans (length-map (λ xy → φ-pop (p1 xy) , pop (p2 xy)) (Z i x))
                                  (sym prf))
  length-Z {n} {t} {μ a} i (mu x) hip
    with length-Z (suc i) x {!!}
  ...| (k , prf)
      = let z : List (Ctx i (μ a) t × ElU (tel-lkup i t) t)
            z = concat (map (λ fel → map (λ xy → p1 fel (p1 xy) , p2 xy) (Z i (p2 fel)))
                       (map (λ xy → φ-mutl (p1 xy) , unpop (p2 xy)) (Z 0 x)))
                       
            y : List (Ctx i (μ a) t × ElU (tel-lkup i t) t)
            y = map (λ xy → φ-muhd (p1 xy) , unpop (p2 xy)) (Z (suc i) x)
            
         in k + length z
          , sym (trans (length-++ y {ys = z})
                (trans (cong (_+ length z) (length-map _ (Z (suc i) x)))
                       (cong (_+ length z) (sym prf))))
  length-Z {n} {t} {def F a} i (red x) hip
    with length-Z (suc i) x {!!}
  ...| (k , prf)
      = let z : List (Ctx i (def F a) t × ElU (tel-lkup i t) t)
            z = concat (map (λ fel → map (λ xy → p1 fel (p1 xy) , p2 xy) (Z i (p2 fel)))
                       (map (λ xy → φ-deftl (p1 xy) , unpop (p2 xy)) (Z 0 x)))
                       
            y : List (Ctx i (def F a) t × ElU (tel-lkup i t) t)
            y = map (λ xy → φ-defhd (p1 xy) , unpop (p2 xy)) (Z (suc i) x)
            
         in k + length z
          , sym (trans (length-++ y {ys = z})
                (trans (cong (_+ length z) (length-map _ (Z (suc i) x)))
                       (cong (_+ length z) (sym prf))))
end{code}
