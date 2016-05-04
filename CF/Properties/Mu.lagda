\begin{code}
open import Prelude

open import Data.List.Properties
  using (length-map; length-++)

open import CF.Syntax
open import CF.Operations.Base
open import CF.Operations.Mu

open import CF.Properties.Base

module CF.Properties.Mu where
\end{code}

%<*mu-ch-lemma>
\begin{code}
  μ-ch-lemma : {n : ℕ}{t : T n}{ty : U (suc n)}
             → (x : ElU ty (μ ty ∷ t))
             → μ-ch (mu x) ≡ map unpop (ch 0 x)
  μ-ch-lemma x with μ-open (mu x)
  ...| hdX , chX = refl
\end{code}
%</mu-ch-lemma>

%<*mu-open-ar-lemma>
\begin{code}
  μ-open-ar-lemma 
    : {n : ℕ}{t : T n}{ty : U (suc n)} 
    → (el : ElU (μ ty) t)
    → length (μ-ch el) ≡ μ-ar el
\end{code}
%</mu-open-ar-lemma>
\begin{code}
  μ-open-ar-lemma {n} {t} {ty} (mu el) 
     = trans (length-map unpop (ch 0 el)) 
             (ch-fgt-ar-lemma 0 el)
\end{code}

%<*mu-open-ar-++-lemma>
\begin{code}
  μ-open-ar-++-lemma 
    : {n : ℕ}{t : T n}{ty : U (suc n)} 
    → (el : ElU (μ ty) t)(xs : List (ElU (μ ty) t))
    → length (μ-ch el ++ xs) ≡ μ-ar el + length xs
\end{code}
%</mu-open-ar-++-lemma>
\begin{code}
  μ-open-ar-++-lemma {n} {t} {ty} (mu el) xs
     = trans (length-++ (μ-ch (mu el))) 
             (cong (λ P → P + length xs) (μ-open-ar-lemma (mu el)))
\end{code}

%<*mu-close-correct-type>
\begin{code}
  μ-close-correct
    : {n : ℕ}{t : T n}{ty : U (suc n)}{a : ElU (μ ty) t}
      {hdA : ElU ty (u1 ∷ t)}{chA l : List (ElU (μ ty) t)}
    → μ-open a ≡ (hdA , chA)
    → μ-close hdA (chA ++ l) ≡ just (a , l)
\end{code}
%</mu-close-correct-type>
\begin{code}
  μ-close-correct {a = mu a} {l = l} refl
    with ar 0 (μ-hd (mu a)) ≤?-ℕ length (μ-ch (mu a) ++ l)
  ...| no ¬q = ⊥-elim (¬q (length-lemma (μ-ch (mu a)) l (μ-open-ar-lemma (mu a))))
  ...| yes q 
    rewrite list-split-lemma (map unpop (ch 0 a)) l {p = q} 
              (trans (length-map unpop (ch 0 a)) (ch-fgt-ar-lemma 0 a))
          = <M>-intro 
            (trans (cong (plug 0 (fgt 0 a)) (map-lemma (ch 0 a) (λ { (pop x) → refl }))) 
                   (sym (plug-correct 0 a)))
\end{code}

%<*mu-ar-lemma>
\begin{code}
  μ-arity-lemma
    : {n : ℕ}{t : T n}{ty : U (suc n)}(x : ElU (μ ty) t)
    → (i : ℕ) 
    → ar i x ≡ ar (suc i) (μ-hd x) + ar* i (μ-ch x)
  μ-arity-lemma {n} {t} {ty} (mu x) i
    = trans (ar-lemma (suc i) 0 x) 
            (cong (λ P → ar (suc i) (fgt 0 x) + P) 
            (trans (sym (ar*-unpop i (ch 0 x))) 
                   (cong (λ P → ar* i P) (sym (μ-ch-lemma x)))))
\end{code}
%</mu-ar-lemma>

