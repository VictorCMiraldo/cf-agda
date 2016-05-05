\begin{code}
{-# OPTIONS --rewriting #-}
open import Prelude
open import Prelude.NatProperties
  using (+-comm)
open import Prelude.ListProperties
  using (map-compose; map-++-commute)

open import CF.Syntax
open import CF.Operations.Base
open import CF.Operations.Dry
open import CF.Operations.Vec
open import CF.Properties.Base

module CF.Properties.Dry where
\end{code}

%<*drop-spec-1-type>
\begin{code}
  {-# REWRITE tel-drop-spec-1 #-}
  drop-spec-1 : {n : ℕ}{t : T n}{ty : U n}
              → (i j : ℕ)(x : ElU ty t)
              → drop i (suc j) x ≡ fgt i (drop (suc i) j x)
\end{code}
%</drop-spec-1-type>
\begin{code}
  drop-spec-1 i j unit = refl
  drop-spec-1 i j (inl x) = cong inl (drop-spec-1 i j x)
  drop-spec-1 i j (inr x) = cong inr (drop-spec-1 i j x)
  drop-spec-1 i j (x , y)
    = cong₂ _,_ (drop-spec-1 i j x) (drop-spec-1 i j y)
  drop-spec-1 i j (mu x)  = cong mu (drop-spec-1 (suc i) j x)
  drop-spec-1 i j (red x) = cong red (drop-spec-1 (suc i) j x)
  drop-spec-1 zero    j (top x) = refl
  drop-spec-1 (suc i) j (top x) = cong top (drop-spec-1 i j x)
  drop-spec-1 zero    j (pop x) = refl
  drop-spec-1 (suc i) j (pop x) = cong pop (drop-spec-1 i j x)
\end{code}

%<*drop-spec-2-type>
\begin{code}
  {-# REWRITE tel-drop-spec-2 #-}
  drop-spec-2 : {n : ℕ}{t : T n}{ty : U n}
              → (i : ℕ)(x : ElU ty t)
              → drop i 0 x ≡ x
\end{code}
%</drop-spec-2-type>
\begin{code}
  drop-spec-2 i unit = refl
  drop-spec-2 i (inl x) = cong inl (drop-spec-2 i x)
  drop-spec-2 i (inr x) = cong inr (drop-spec-2 i x)
  drop-spec-2 i (x , y) = cong₂ _,_ (drop-spec-2 i x) (drop-spec-2 i y)
  drop-spec-2 i (mu x)  = cong mu (drop-spec-2 (suc i) x)
  drop-spec-2 i (red x) = cong red (drop-spec-2 (suc i) x)
  drop-spec-2 zero    (top x) = refl
  drop-spec-2 (suc i) (top x) = cong top (drop-spec-2 i x)
  drop-spec-2 zero    (pop x) = refl
  drop-spec-2 (suc i) (pop x) = cong pop (drop-spec-2 i x)
\end{code}

\begin{code}
  drop-unpop-lemma
    : {n : ℕ}{t : T n}{a ty : U n}
    → (i j : ℕ)(x : ElU (wk ty) (a ∷ t))
    → drop (suc i) j (unpop x) ≡ unpop (drop (suc (suc i)) j x)
  drop-unpop-lemma i j (pop x) = refl
\end{code}

%<*drop-ch-lemma-type>
\begin{code}
  {-# REWRITE tel-lkup-drop-spec #-}
  drop-ch-lemma
    : {n : ℕ}{t : T n}{ty : U n}
    → (i j : ℕ)(x : ElU ty t)
    → ch i (drop (suc i) j x) ≡ map (drop {t = t} {ty = tel-lkup i t} (suc i) j) (ch i x)
\end{code}
%</drop-ch-lemma-type>
\begin{code}
  drop-ch-lemma i j unit = refl
  drop-ch-lemma i j (inl x) = drop-ch-lemma i j x
  drop-ch-lemma i j (inr x) = drop-ch-lemma i j x
  drop-ch-lemma i j (x , y)
    = sym (trans (map-++-commute (drop (suc i) j) (ch i x) (ch i y))
          (cong₂ _++_ (sym (drop-ch-lemma i j x)) (sym (drop-ch-lemma i j y))))
  drop-ch-lemma zero    j (top x) = refl
  drop-ch-lemma (suc i) j (top x)
    rewrite drop-ch-lemma i j x
      = trans (sym (map-compose (ch i x)))
        (sym  (trans (sym (map-compose (ch i x)))
              (cong (λ P → map P (ch i x))
                    (fun-ext (λ x → refl)))))
  drop-ch-lemma zero    j (pop x) = refl
  drop-ch-lemma (suc i) j (pop x)
    rewrite drop-ch-lemma i j x
      = trans (sym (map-compose (ch i x)))
        (sym  (trans (sym (map-compose (ch i x)))
              (cong (λ P → map P (ch i x))
                    (fun-ext (λ x → refl)))))
  drop-ch-lemma i j (mu x)
    rewrite drop-ch-lemma (suc i) j x
      = trans (sym (map-compose (ch (suc i) x)))
              (sym (trans (sym (map-compose (ch (suc i) x)))
                          (cong (λ P → map P (ch (suc i) x))
                          (fun-ext (drop-unpop-lemma i j)))))
  drop-ch-lemma i j (red x)
    rewrite drop-ch-lemma (suc i) j x
      = trans (sym (map-compose (ch (suc i) x)))
              (sym (trans (sym (map-compose (ch (suc i) x)))
                          (cong (λ P → map P (ch (suc i) x))
                          (fun-ext (drop-unpop-lemma i j)))))  
\end{code}

%<*ar-dry-lemma-type>
\begin{code}
  {-# TERMINATING #-}
  ar-dry-lemma
    : {n : ℕ}{t : T n}{ty : U n}
    → (i : ℕ)(x : ElU ty t)
    → ar-dry i x ≡ ar i (drop 0 i x)
\end{code}
%</ar-dry-lemma-type>
\begin{code}
  ar-dry-lemma i unit    = refl
  ar-dry-lemma i (inl x) = ar-dry-lemma i x
  ar-dry-lemma i (inr x) = ar-dry-lemma i x
  ar-dry-lemma i (x , y) = cong₂ _+_ (ar-dry-lemma i x) (ar-dry-lemma i y)
  ar-dry-lemma zero    (top x) = refl
  ar-dry-lemma (suc i) (top x) = refl
  ar-dry-lemma zero    (pop x) = refl
  ar-dry-lemma (suc i) (pop x) = ar-dry-lemma i x 
  ar-dry-lemma i (mu x)
    rewrite ar-std-lemma (suc i) 0 (drop (suc 0) i x)
          | sym (drop-spec-1 0 i x)
          | ar-dry-lemma (suc i) x
          = cong (λ P → ar (suc i) (drop 0 (suc i) x) + P)
            (sym (trans (cong (λ P → sum (map (ar (suc i)) P)) (drop-ch-lemma 0 i x))
                 (trans (cong sum (sym (map-compose (ch 0 x))))
                        (cong (λ P → sum (map P (ch 0 x)))
                              (fun-ext (λ { (pop k) → sym (ar-dry-lemma {n = 0} i k) }))))))
  ar-dry-lemma i (red x)
    rewrite ar-std-lemma (suc i) 0 (drop (suc 0) i x)
          | sym (drop-spec-1 0 i x)
          | ar-dry-lemma (suc i) x
          = cong (λ P → ar (suc i) (drop 0 (suc i) x) + P)
            (sym (trans (cong (λ P → sum (map (ar (suc i)) P)) (drop-ch-lemma 0 i x))
                 (trans (cong sum (sym (map-compose (ch 0 x))))
                        (cong (λ P → sum (map P (ch 0 x)))
                              (fun-ext (λ { (pop k) → sym (ar-dry-lemma {n = 0} i k) }))))))
\end{code} 

%<*ar-dry-0-lemma-type>
\begin{code}
  ar-dry-0-lemma
    : {n : ℕ}{t : T n}{ty : U n}
    → (x : ElU ty t)
    → ar-dry 0 x ≡ ar 0 x
  ar-dry-0-lemma x = trans (ar-dry-lemma 0 x) (cong (ar 0) (drop-spec-2 0 x))
\end{code}
%</ar-dry-0-lemma-type>
