\begin{code}
open import Prelude

open import Prelude.NatProperties
  using (+-comm; +-assoc; m+n∸n≡m)
open import Prelude.ListProperties
  using (length-map; length-++; map-compose; map-id;
         lsplit-++-lemma; map-lemma; lsplit-elim;
         lsplit-length-≡-lemma)

open import CF.Syntax
open import CF.Operations.Base
open import CF.Properties.Base

module CF.Functor where
\end{code}

%<*fmap-def>
\begin{code}
  fmap : {n : ℕ}{t : T n}{a b : U n}{F : U (suc n)}
       → (f : {t' : T n} → ElU a t' → ElU b t')
       → ElU F (a ∷ t) → ElU F (b ∷ t)
  fmap f x = plugₜ 0 (fgt 0 x) (map (pop ∘ f ∘ unpop) (ch 0 x))
                   (trans (length-map (pop ∘ f ∘ unpop) (ch 0 x))
                          (ch-fgt-ar-lemma 0 x))
\end{code}
%</fmap-def>

%<*fmap-id-type>
\begin{code}
  fmap-id : {n : ℕ}{t : T n}{a : U n}{F : U (suc n)}
          → (x : ElU F (a ∷ t))
          → fmap id x ≡ x
\end{code}
%</fmap-id-type>
\begin{code}
  fmap-id {n} {t} {a} {F} x = just-inj 
    (trans (sym (plug-plugₜ-lemma 0 (fgt 0 x) (map (pop ∘ id ∘ unpop) (ch 0 x)) 
                  (trans (length-map (pop ∘ id ∘ unpop) (ch 0 x))
                          (ch-fgt-ar-lemma 0 x)))) 
    (trans (cong (λ P → plug 0 (fgt 0 x) (map P (ch 0 x))) 
                 (fun-ext {A = ElU (wk a) (a ∷ t)} (λ { (pop k) → refl }))) 
    (trans (cong (plug 0 (fgt 0 x)) (map-id (ch 0 x))) 
           (sym (plug-correct 0 x)))))
\end{code}

%<*fmap-compose-type>
\begin{code}
  fmap-compose 
    : {n : ℕ}{t : T n}{a b c : U n}{F : U (suc n)}
    → (f : {t' : T n} → ElU a t' → ElU b t')
    → (g : {t' : T n} → ElU b t' → ElU c t')
    → (x : ElU F (a ∷ t))
    → fmap g (fmap f x) ≡ fmap (g ∘ f) x
\end{code}
%</fmap-compose-type>
\begin{code}
  fmap-compose {n} {t} {a} {b} {c} {F} f g x = just-inj 
    (trans (sym (plug-plugₜ-lemma 0 (fgt 0 (fmap f x)) (map (pop ∘ g ∘ unpop) (ch 0 (fmap f x))) 
                  (trans (length-map (pop ∘ g ∘ unpop) (ch 0 (fmap f x))) 
                         (ch-fgt-ar-lemma 0 (fmap f x))))) 
    (trans (cong₂ (λ P Q → plug 0 P (map (pop ∘ g ∘ unpop) Q)) 
                  (plugₜ-spec-fgt 0 (fgt 0 x) (map (pop ∘ f ∘ unpop) (ch 0 x)) 
                    (trans (length-map (pop ∘ f ∘ unpop) (ch 0 x)) 
                           (ch-fgt-ar-lemma 0 x)))
                  (plugₜ-spec-ch 0 (fgt 0 x) (map (pop ∘ f ∘ unpop) (ch 0 x)) 
                    (trans (length-map (pop ∘ f ∘ unpop) (ch 0 x)) 
                           (ch-fgt-ar-lemma 0 x)))) 
    (trans (cong (λ P → plug 0 (fgt 0 x) P) 
                 (trans (sym (map-compose (ch 0 x))) 
                        (cong (λ P → map P (ch 0 x)) 
                          (fun-ext {A = ElU (wk a) (a ∷ t)} {g = pop ∘ (g ∘ f) ∘ unpop} 
                            (λ { (pop k) → refl })))))
           (plug-plugₜ-lemma zero (fgt zero x)
              (map (λ z → pop (g (f (unpop z)))) (ch zero x))
              (trans (length-map (λ z → pop (g (f (unpop z)))) (ch zero x))
               (trans (ch-ar-lemma zero x) (fgt-ar-lemma zero x)))))))
\end{code}

%<*fold-def>
\begin{code}
  {-# TERMINATING #-}
  fold : {n : ℕ}{t : T n}{a : U n}{F : U (suc n)}
       → (f : {t' : T n} → ElU F (a ∷ t') → ElU a t')
       → ElU (μ F) t → ElU a t
  fold f (mu x) = f (fmap (fold f) x)
\end{code}
%</fold-def>
