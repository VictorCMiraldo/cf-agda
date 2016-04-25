\begin{code}
open import Prelude
open import Prelude.Vector

open import CF.Syntax
open import CF.Operations
open import CF.Operations.Properties

module CF.MuPlugging where
\end{code}

  Here we provide plugging and unplugging 
  elements in their vector and list variants.

%<*unplugv-type>
\begin{code}
  unplugv : {n : ℕ}{t : T n}{ty : U n}
         → (i : ℕ)(el : ElU ty t)
         → Σ (ElU ty (tel-forget i t))
             (Vec (ElU (tel-lkup i t) t) ∘ (ar i))
\end{code}
%</unplugv-type>
\begin{code}
  unplugv i el
    = fgt i el
    , vec (ch i el) (trans (ch-ar-lemma i el) (fgt-ar-lemma i el))
\end{code}

%<*unplug-type>
\begin{code}
  unplug : {n : ℕ}{t : T n}{ty : U n}
         → (i : ℕ)(el : ElU ty t)
         → (ElU ty (tel-forget i t)) × (List (ElU (tel-lkup i t) t))
\end{code}
%</unplug-type>
\begin{code}
  unplug i el = fgt i el , ch i el
\end{code}

%<*plugv-type>
\begin{code}
  plugv : {n : ℕ}{t : T n}{ty : U n}
       → (i : ℕ)(el : ElU ty (tel-forget i t))
       → Vec (ElU (tel-lkup i t) t) (ar i el)
       → ElU ty t
\end{code}
%</plugv-type>
\begin{code}
  plugv {ty = u0} i () v
  plugv {ty = u1} i el v = unit
  plugv {ty = ty ⊕ tv} i (inl el) v = inl (plugv i el v)
  plugv {ty = ty ⊕ tv} i (inr el) v = inr (plugv i el v)
  plugv {ty = ty ⊗ tv} i (ela , elb) v 
    = let va , vb = vsplit (ar i ela) v
      in plugv i ela va , plugv i elb vb
  plugv {ty = def F x} i (red el) v 
    = red (plugv (suc i) el (vmap pop v))
  plugv {ty = μ ty} i (mu el) v
    = mu (plugv (suc i) el (vmap pop v))
  plugv {t = t ∷ ts} {ty = var} zero (top el) (pop v ∷ []) 
    = top v
  plugv {t = t ∷ ts} {ty = var} (suc i) (top el) v 
    = top (plugv i el (vmap unpop v))
  plugv {t = t ∷ ts} {ty = wk ty} zero (pop el) v 
    = pop el
  plugv {t = t ∷ ts} {ty = wk ty} (suc i) (pop el) v
    = pop (plugv i el (vmap unpop v))
\end{code}

%<*plug-type>
\begin{code}
  plug : {n : ℕ}{t : T n}{ty : U n}
       → (i : ℕ)(el : ElU ty (tel-forget i t))
       → List (ElU (tel-lkup i t) t)
       → Maybe (ElU ty t)
\end{code}
%</plug-type>
\begin{code}
  plug {ty = u0} i () v
  plug {ty = u1} i unit args = just unit
  plug {ty = ty ⊕ tv} i (inl el) v = inl <M> plug i el v
  plug {ty = ty ⊕ tv} i (inr el) v = inr <M> plug i el v
  plug {ty = ty ⊗ tv} i (ela , elb) v 
    = let va , vb = lsplit (ar i ela) v
       in _,_ <M> plug i ela va <M*> plug i elb vb
  plug {ty = def F ty} i (red el) v 
    = red <M> plug (suc i) el (map pop v)
  plug {ty = μ ty} i (mu el) v 
    = mu <M> plug (suc i) el (map pop v)
  plug {t = t ∷ ts} {var} zero (top el) v 
    = top <M> lhead (map unpop v)
  plug {t = t ∷ ts} {ty = var} (suc i) (top el) v 
    = top <M> plug i el (map unpop v)
  plug {t = t ∷ ts} {ty = wk ty} zero (pop el) v 
    = just (pop el)
  plug {t = t ∷ ts} {ty = wk ty} (suc i) (pop el) v 
    = pop <M> plug i el (map unpop v)
\end{code}
