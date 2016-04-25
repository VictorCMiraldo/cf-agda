\begin{code}
{-# OPTIONS --rewriting #-}
open import Prelude
open import Prelude.Vector

open import Data.Nat.Properties.Simple
  using (+-assoc; +-comm)
open import Data.List.Properties
  using (length-map; length-++)

open import CF.Syntax
open import CF.Operations
open import CF.Operations.Properties
open import CF.MuPlugging
open import CF.MuPlugging.Properties

module CF.Operations.Mu where
\end{code}

%<*mu-open>
\begin{code}
  μ-open : {n : ℕ}{t : T n}{ty : U (suc n)} 
         → ElU (μ ty) t → ElU ty (u1 ∷ t) × List (ElU (μ ty) t)
  μ-open (mu el) 
    = let hdEl , chEl = unplug 0 el
       in hdEl , map unpop chEl
\end{code}
%</mu-open>

%<*mu-openv>
\begin{code}
  μ-openv : {n : ℕ}{t : T n}{ty : U (suc n)} 
          → ElU (μ ty) t → Σ (ElU ty (u1 ∷ t)) (Vec (ElU (μ ty) t) ∘ (ar 0))
  μ-openv (mu el) 
    = let hdEl , chEl = unplugv 0 el
       in hdEl , vmap unpop chEl
\end{code}
%</mu-openv>

%<*mu-hd-def>
\begin{code}
  μ-hd : {n : ℕ}{t : T n}{ty : U (suc n)} 
       → ElU (μ ty) t → ElU ty (u1 ∷ t)
  μ-hd = p1 ∘ μ-open
\end{code}
%</mu-hd-def>

%<*mu-hdv-def>
\begin{code}
  μ-hdv : {n : ℕ}{t : T n}{ty : U (suc n)} 
       → ElU (μ ty) t → ElU ty (u1 ∷ t)
  μ-hdv = p1 ∘ μ-openv
\end{code}
%</mu-hdv-def>

%<*mu-hd-def>
\begin{code}
  μ-hd-hdv-lemma : {n : ℕ}{t : T n}{ty : U (suc n)} 
                 → (x : ElU (μ ty) t) → p1 (μ-openv x) ≡ p1 (μ-open x)
  μ-hd-hdv-lemma (mu x) = refl
\end{code}
%</mu-hd-def>

%<*mu-ar-def>
\begin{code}
  μ-ar : {n : ℕ}{t : T n}{ty : U (suc n)} 
       → ElU (μ ty) t → ℕ
  μ-ar = ar 0 ∘ μ-hd
\end{code}
%</mu-ar-def>

%<*mu-ch-def>
\begin{code}
  μ-ch : {n : ℕ}{t : T n}{ty : U (suc n)} 
       → ElU (μ ty) t → List (ElU (μ ty) t)
  μ-ch = p2 ∘ μ-open
\end{code}
%</mu-ch-def>

%<*mu-chv-def>
\begin{code}
  {-# REWRITE μ-hd-hdv-lemma #-}
  μ-chv : {n : ℕ}{t : T n}{ty : U (suc n)} 
        → (x : ElU (μ ty) t) → Vec (ElU (μ ty) t) (μ-ar x)
  μ-chv x = p2 (μ-openv x)      
\end{code}
%</mu-chv-def>

%<*mu-ch-lemma>
\begin{code}
  μ-ch-lemma : {n : ℕ}{t : T n}{ty : U (suc n)}
             → (x : ElU ty (μ ty ∷ t))
             → μ-ch (mu x) ≡ map unpop (ch 0 x)
  μ-ch-lemma x with μ-open (mu x)
  ...| hdX , chX = refl
\end{code}
%</mu-ch-lemma>

vmap-vec unpop (ch 0 x) 
             {trans (ch-ar-lemma 0 x) (fgt-ar-lemma 0 x)} 
             {trans (length-map unpop (ch 0 x)) 
                    (trans (ch-ar-lemma 0 x) (fgt-ar-lemma 0 x)) }

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

%<*mu-chv-def>
\begin{code}
  μ-ch-chv-lemma 
    : {n : ℕ}{t : T n}{ty : U (suc n)}
    → (x : ElU (μ ty) t)
    → μ-ch x ≡ toList (μ-chv x)
  μ-ch-chv-lemma (mu x) 
    = sym (trans (cong toList (vmap-vec unpop (ch 0 x) {p = ch-fgt-ar-lemma 0 x}
                       {q = trans (length-map unpop (ch 0 x)) (ch-fgt-ar-lemma zero x)})) 
                 (toList-vec (map unpop (ch zero x))))
\end{code}
%</mu-chv-def>

\begin{code}
  private
    list-split : {m : ℕ}{A : Set}(l : List A)
               → m ≤ length l
               → Σ (List A × List A) (λ ls → length (p1 ls) ≡ m)
    list-split [] z≤n = ([] , []) , refl
    list-split (x ∷ l) z≤n = ([] , (x ∷ l)) , refl
    list-split (x ∷ l) (s≤s p) with list-split l p
    ...| (la , lb) , prf = ((x ∷ la) , lb) , (cong suc prf)

    list-split-lemma 
      : {m : ℕ}{A : Set}(l1 l2 : List A){p : m ≤ length (l1 ++ l2)}
      → (q : length l1 ≡ m)
      → list-split (l1 ++ l2) p ≡ ((l1 , l2) , q)
    list-split-lemma [] [] {z≤n} refl = refl
    list-split-lemma [] (x ∷ l2) {z≤n} refl = refl
    list-split-lemma (x ∷ l1) l2 {s≤s p} refl
      with list-split-lemma l1 l2 {p} refl
    ...| hip rewrite hip = refl

    length-lemma 
      : {n : ℕ}{A : Set}(l1 l2 : List A)
      → length l1 ≡ n → n ≤ length (l1 ++ l2)
    length-lemma [] l2 refl = z≤n
    length-lemma (x ∷ l1) l2 refl = s≤s (length-lemma l1 l2 refl)
\end{code}

%<*mu-close>
\begin{code}
  μ-close : {n : ℕ}{t : T n}{ty : U (suc n)} 
          → ElU ty (u1 ∷ t) → List (ElU (μ ty) t) 
          → Maybe (ElU (μ ty) t × List (ElU (μ ty) t))
  μ-close hdX chs with ar 0 hdX ≤?-ℕ length chs
  ...| no  _ = nothing
  ...| yes p with list-split chs p
  ...| (chX , rest) , prf 
     = (λ x → mu x , rest) <M> plug 0 hdX (map pop chX)
\end{code}
%</mu-close>

%<*mu-closev>
\begin{code}
  μ-closev : {n j : ℕ}{t : T n}{ty : U (suc n)} 
           → (a : ElU ty (u1 ∷ t))
           → Vec (ElU (μ ty) t) (ar 0 a + j) 
           → Vec (ElU (μ ty) t) (suc j)
  μ-closev a as
    = let vas , vrs = vsplit (ar 0 a) as
      in mu (plugv 0 a (vmap pop vas)) ∷ vrs
\end{code}
%</mu-closev>

\begin{code}
  private
    j+0 : ∀ j → j + 0 ≡ j
    j+0 j = +-comm j 0

    vsplit-hd-ch : {n : ℕ}{t : T n}{ty : U (suc n)}
                 → (a : ElU (μ ty) t) 
                 → vsplit (ar 0 (μ-hd a)) (μ-chv a ++v []) ≡ (μ-chv a , [])
    vsplit-hd-ch a 
      rewrite vsplit-ump (μ-chv a) [] = refl

    {-# REWRITE j+0 #-}
    ++v-id : {A : Set}{n : ℕ}(v : Vec A n)
         → v ≡ v ++v []
    ++v-id [] = refl
    ++v-id (x ∷ v) = cong (_∷_ x) (++v-id v)
\end{code}

%<*mu-closev>
\begin{code}
  μ-plugv-correct : {n : ℕ}{t : T n}{ty : U (suc n)} 
           → (a : ElU (μ ty) t)
           → mu (plugv 0 (μ-hd a) (vmap pop (vec (p2 (μ-open a)) (μ-open-ar-lemma a)))) 
           ≡ a
  μ-plugv-correct (mu a) with vsplit-hd-ch (mu a)
  ...| prf rewrite sym (++v-id (μ-chv (mu a))) | prf
     = cong mu (trans (cong (λ P → plugv 0 (fgt 0 a) (vmap pop P))
                         (sym (vmap-vec unpop (ch 0 a) {ch-fgt-ar-lemma 0 a} 
                               {trans (length-map unpop (ch 0 a)) (ch-fgt-ar-lemma 0 a)}))) 
               (trans (cong (λ P → plugv 0 (fgt 0 a) P)
                         (vmap-lemma {f = unpop} {pop} (vec (ch 0 a) _) (λ { (pop x) → refl }))) 
                      (sym (plugv-correct 0 a)))) 
\end{code}
%</mu-closev>

%<*mu-closev>
\begin{code}
  μ-closev-correct : {n : ℕ}{t : T n}{ty : U (suc n)} 
           → (a : ElU (μ ty) t)
           → μ-closev {j = 0} (μ-hd a) (μ-chv a) ≡ a ∷ []
  μ-closev-correct (mu a) with vsplit-hd-ch (mu a)
  ...| prf rewrite sym (++v-id (μ-chv (mu a))) | prf 
     = cong (λ P → mu P ∷ []) 
       (trans
        (cong (λ P → plugv 0 (fgt 0 a) P)
              (vmap-lemma {f = unpop} {pop}
              (vec (ch 0 a) (trans (ch-ar-lemma 0 a) (fgt-ar-lemma 0 a))) (λ { (pop x) → refl })))
        (sym (plugv-correct 0 a)))
\end{code}
%</mu-closev>

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

begin{code}
  μ-close-spec
    : {n : ℕ}{t : T n}{ty : U (suc n)}{a : ElU (μ ty) t}
      {hdA : ElU ty (u1 ∷ t)}{chA l : List (ElU (μ-ty

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


%<*mu-ar-lemma-2>
\begin{code}
  μ-arity-lemma-2
    : {n : ℕ}{t : T n}{ty : U (suc n)}(x : ElU (μ ty) t)
    → (i : ℕ)
    → ar i x ≡ ar (suc i) (μ-hd x) + ar* i (toList (μ-chv x))
  μ-arity-lemma-2 {n} {t} {ty} x i
    = trans (μ-arity-lemma x i) 
            (cong (λ P → ar (suc i) (μ-hd x) + ar* i P) (μ-ch-chv-lemma x))
\end{code}
%</mu-ar-lemma-2>

%<*mu-ar-open>
\begin{code}
  μ-ar-open-lemma
    : {n k : ℕ}{t : T n}{ty : U (suc n)}
    → (x : ElU (μ ty) t)(xs : Vec (ElU (μ ty) t) k)
    → (i : ℕ)
    → ar (suc i) (μ-hd x) + ar*v i (μ-chv x ++v xs)
    ≡ ar i x + ar*v i xs
  μ-ar-open-lemma {n} {k} {t} {ty} x xs i 
    rewrite ar*v-reduce i (μ-chv x) xs
          = trans (sym (+-assoc (ar (suc i) (μ-hd x)) 
                                (ar* i (toList (μ-chv x))) 
                                (ar*v i xs))) 
                  (cong (λ P → P + ar*v i xs) (sym (μ-arity-lemma-2 x i)))
\end{code}
%</mu-ar-open>
