\begin{code}
{-# OPTIONS --rewriting #-}
open import Prelude
open import Prelude.Vector

open import Prelude.NatProperties
  using (+-assoc; +-comm)
open import Prelude.ListProperties
  using (length-map; length-++; map-lemma)

open import CF.Syntax
open import CF.Operations.Base
open import CF.Operations.Mu
open import CF.Operations.Vec
open import CF.Properties.Base
open import CF.Properties.Mu

module CF.Properties.Vec where
\end{code}

  Here we prove that "plugv ∘ unplugv ≡ id". 
  Although they actually make an isomoprhism, we don't need
  the proof for "unplugv ∘ plugv ≡ id" anywhere, therefore
  we ommit it.

  There are a bunch of auxiliary lemmas that must be proved
  before hand, however.

\begin{code}
  private
    aux-lemma : {n : ℕ}{A B : Set}{t : T n}{a : U n}
                → (i : ℕ)(el : ElU a t)
                → {f : ElU (tel-lkup i t) t → A}{g : A → B}
                → length (map g (map f (ch i el))) ≡ ar i (fgt i el)
    aux-lemma i el {f = f} {g = g}
      = trans (length-map g (map f (ch i el))) 
        (trans (length-map f (ch i el)) 
         (trans (ch-ar-lemma i el) 
          (fgt-ar-lemma i el)))

    unpop-top
      : {n : ℕ}{t : T n}{a : U n}
      → (i : ℕ)
      → (el : ElU a t)
      → vmap unpop (p2 (unplugv (suc i) (top el)))
      ≡ p2 (unplugv i el)
    unpop-top i el 
      = trans (vmap-vec unpop (map pop (ch i el)) 
                 {q = aux-lemma i el} ) 
              (vec-≡ (map-lemma (ch i el) 
                     (λ x → refl)))

    unpop-pop
      : {n : ℕ}{t : T n}{a b : U n}
      → (i : ℕ)
      → (el : ElU a t)
      → vmap (unpop {x = b}) (p2 (unplugv (suc i) (pop el)))
      ≡ p2 (unplugv i el)
    unpop-pop i el
      = trans (vmap-vec unpop (map pop (ch i el)) 
                 {q = aux-lemma i el} ) 
              (vec-≡ (map-lemma (ch i el) 
                     (λ x → refl)))

    pop-mu
      : {n : ℕ}{t : T n}{a : U (suc n)}
      → (i : ℕ)
      → (el : ElU a (μ a ∷ t))
      → vmap pop (p2 (unplugv i (mu el)))
      ≡ p2 (unplugv (suc i) el)
    pop-mu i el 
      = trans (vmap-vec pop (map unpop (ch (suc i) el))
                 {q = aux-lemma (suc i) el}) 
              (vec-≡ (map-lemma (ch (suc i) el) 
                     (λ { (pop x) → refl })))

    pop-red
      : {n : ℕ}{t : T n}{a : U (suc n)}{b : U n}
      → (i : ℕ)
      → (el : ElU a (b ∷ t))
      → vmap pop (p2 (unplugv i (red el)))
      ≡ p2 (unplugv (suc i) el)
    pop-red i el 
      = trans (vmap-vec pop (map unpop (ch (suc i) el))
                 {q = aux-lemma (suc i) el}) 
              (vec-≡ (map-lemma (ch (suc i) el) 
                     (λ { (pop x) → refl })))
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

%<*plugv-correct-type>
\begin{code}
  plugv-correct
    : {n : ℕ}{t : T n}{ty : U n}
    → (i : ℕ)(el : ElU ty t)
    → el ≡ plugv i (p1 (unplugv i el)) (p2 (unplugv i el))
\end{code}
%</plugv-correct-type>
\begin{code}
  plugv-correct i unit 
    = refl
  plugv-correct i (inl el) 
    = cong inl (plugv-correct i el)
  plugv-correct i (inr el) 
    = cong inr (plugv-correct i el)
  plugv-correct zero (top el) 
    = refl
  plugv-correct (suc i) (top el) 
    = cong top 
      (subst (λ P → el ≡ plugv i (fgt i el) P) 
      (sym (unpop-top i el)) (plugv-correct i el))
  plugv-correct zero (pop el) 
    = refl
  plugv-correct (suc i) (pop el) 
    = cong pop 
      (subst (λ P → el ≡ plugv i (fgt i el) P) 
      (sym (unpop-pop i el)) (plugv-correct i el))
  plugv-correct i (mu el) 
    = cong mu 
      (subst (λ P → el ≡ plugv (suc i) (fgt (suc i) el) P) 
      (sym (pop-mu i el)) (plugv-correct (suc i) el))
  plugv-correct i (red el) 
    = cong red
      (subst (λ P → el ≡ plugv (suc i) (fgt (suc i) el) P) 
      (sym (pop-red i el)) (plugv-correct (suc i) el))
  plugv-correct i (ela , elb) 
    = cong₂ _,_ (sym (prod1 i ela elb)) (sym (prod2 i ela elb))
    where
      prod1 : {n : ℕ}{t : T n}{a b : U n}
            → (i : ℕ)(ela : ElU a t)(elb : ElU b t)
            → plugv i (fgt i ela) (p1
               (vsplit (ar i (fgt i ela))
                 (p2 (unplugv i (ela , elb))))
             ) ≡ ela
      prod1 i ela elb with unplugv i (ela , elb)
      ...| (hdA , hdB) , CH 
         = subst (λ P → plugv i (fgt i ela) P ≡ ela) 
           (sym (trans 
                (vsplit-elim-1 (ch i ela) (ch i elb)) 
                refl)) 
           (sym (plugv-correct i ela))

      prod2 : {n : ℕ}{t : T n}{a b : U n}
            → (i : ℕ)(ela : ElU a t)(elb : ElU b t)
            → plugv i (fgt i elb) (p2
               (vsplit (ar i (fgt i ela))
                 (p2 (unplugv i (ela , elb))))
             ) ≡ elb
      prod2 i ela elb with unplugv i (ela , elb)
      ...| (hdA , hdB) , CH
         = subst (λ P → plugv i (fgt i elb) P ≡ elb) 
           (sym (trans 
                (vsplit-elim-2 
                  {m = ar i (fgt i ela)} 
                  (ch i ela) 
                  (ch i elb)) 
                refl)) 
           (sym (plugv-correct i elb))
\end{code}

%<*fgt-plugv-lemma-type>
\begin{code}
  fgt-plugv-lemma
    : {n : ℕ}{t : T n}{ty : U n}(i : ℕ)
    → (a : ElU ty (tel-forget i t))
    → (as : Vec (ElU (tel-lkup i t) t) (ar i a)) 
    → fgt i (plugv i a as) ≡ a
\end{code}
%</fgt-plugv-lemma-type>
\begin{code}
  fgt-plugv-lemma {ty = u0} i () as
  fgt-plugv-lemma {ty = u1} i unit as = refl
  fgt-plugv-lemma {ty = ty ⊕ tv} i (inl a) as 
    = cong inl (fgt-plugv-lemma i a as)
  fgt-plugv-lemma {ty = ty ⊕ tv} i (inr a) as 
    = cong inr (fgt-plugv-lemma i a as)
  fgt-plugv-lemma {ty = ty ⊗ tv} i (a1 , a2) as 
    = let vas1 , vas2 = vsplit (ar i a1) as
       in cong₂ _,_ (fgt-plugv-lemma i a1 vas1) (fgt-plugv-lemma i a2 vas2)
  fgt-plugv-lemma {ty = def F ty} i (red a) as 
    = cong red (fgt-plugv-lemma (suc i) a (vmap pop as))
  fgt-plugv-lemma {ty = μ ty} i (mu a) as
    = cong mu (fgt-plugv-lemma (suc i) a (vmap pop as))
  fgt-plugv-lemma {t = t ∷ ts} {var} zero (top unit) (pop as ∷ [])
    = refl
  fgt-plugv-lemma {t = t ∷ ts} {var} (suc i) (top a) as 
    = cong top (fgt-plugv-lemma i a (vmap unpop as))
  fgt-plugv-lemma {t = t ∷ ts} {wk ty} zero (pop a) as 
    = refl
  fgt-plugv-lemma {t = t ∷ ts} {wk ty} (suc i) (pop a) as 
    = cong pop (fgt-plugv-lemma i a (vmap unpop as))
\end{code}

%<*ch-plugv-lemma-type>
\begin{code}
  ch-plugv-lemma 
    : {n : ℕ}{t : T n}{ty : U n}(i : ℕ)
    → (a : ElU ty (tel-forget i t))
    → (as : Vec (ElU (tel-lkup i t) t) (ar i a)) 
    → ch i (plugv i a as) ≡ toList as
\end{code}
%</ch-plugv-lemma-type>
\begin{code}
  ch-plugv-lemma {ty = u0} i () as
  ch-plugv-lemma {ty = u1} i unit [] = refl
  ch-plugv-lemma {ty = ty ⊕ tv} i (inl a) as 
    = ch-plugv-lemma i a as
  ch-plugv-lemma {ty = ty ⊕ tv} i (inr a) as 
    = ch-plugv-lemma i a as
  ch-plugv-lemma {ty = ty ⊗ tv} i (a1 , a2) as 
    = let vas1 , vas2 = vsplit (ar i a1) as
       in trans (cong₂ _++_ (ch-plugv-lemma i a1 vas1) (ch-plugv-lemma i a2 vas2)) 
                (sym (toList-vsplit-++ {m = ar i a1} as))
  ch-plugv-lemma {ty = def F ty} i (red a) as 
    rewrite ch-plugv-lemma (suc i) a (vmap pop as)
          = trans (map-toList-lemma (vmap pop as) unpop) 
                  (cong toList (vmap-lemma as (λ x → refl)))
  ch-plugv-lemma {ty = μ ty} i (mu a) as 
    rewrite ch-plugv-lemma (suc i) a (vmap pop as)
          = trans (map-toList-lemma (vmap pop as) unpop) 
                  (cong toList (vmap-lemma as (λ x → refl)))
  ch-plugv-lemma {t = t ∷ ts} {var} zero (top a) (pop as ∷ []) 
    = refl
  ch-plugv-lemma {t = t ∷ ts} {var} (suc i) (top a) as 
    rewrite ch-plugv-lemma i a (vmap unpop as)
          = trans (map-toList-lemma (vmap unpop as) pop) 
                  (cong toList (vmap-lemma as (λ { (pop x) → refl })))
  ch-plugv-lemma {t = t ∷ ts} {ty = wk ty} zero (pop a) []
    = refl
  ch-plugv-lemma {t = t ∷ ts} {ty = wk ty} (suc i) (pop a) as
    rewrite ch-plugv-lemma i a (vmap unpop as)
          = trans (map-toList-lemma (vmap unpop as) pop) 
                  (cong toList (vmap-lemma as (λ { (pop x) → refl })))
\end{code}

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
                (vec (ch 0 a) (trans (ch-ar-lemma 0 a) (fgt-ar-lemma 0 a)))
                (λ { (pop x) → refl })))
        (sym (plugv-correct 0 a)))
\end{code}
%</mu-closev>
