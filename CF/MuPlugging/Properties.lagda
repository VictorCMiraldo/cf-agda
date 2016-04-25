\begin{code}
open import Prelude
open import Prelude.Vector

open import Data.List.Properties
  using (length-map)

open import CF.Syntax
open import CF.Operations
open import CF.Operations.Properties
open import CF.MuPlugging

module CF.MuPlugging.Properties where
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

%<*fgt-plug-lemma-type>
begin{code}
  fgt-plug-lemma
    : {n : ℕ}{t : T n}{ty : U n}(i : ℕ)
    → (a : ElU ty (tel-forget i t))
    → (as : List (ElU (tel-lkup i t) t))
    → ar i a ≤ length as
    → fgt i <M> plug i a as ≡ just a
end{code}
%</fgt-plug-lemma-type>
begin{code}
  fgt-plug-lemma {ty = u0} i () as x
  fgt-plug-lemma {ty = u1} i unit as x = refl
  fgt-plug-lemma {ty = ty ⊕ tv} i (inl el) as x 
    = {!!}
  fgt-plug-lemma {ty = ty ⊕ tv} i (inr el) as x = {!!}
  fgt-plug-lemma {ty = ty ⊗ tv} i el as x = {!!}
  fgt-plug-lemma {ty = def F ty} i el as x = {!!}
  fgt-plug-lemma {ty = μ ty} i el as x = {!!}
  fgt-plug-lemma {ty = var} i el as x = {!!}
  fgt-plug-lemma {ty = wk ty} i el as x = {!!}
end{code}


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
