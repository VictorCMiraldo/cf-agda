\begin{code}
open import Prelude

open import CF.Syntax

module CF.Operations.Base where
\end{code}

  Here we define a few important operations over generic elements
  of CF. One can visualize these operations as follows.

  Take an element (x : ElU ty (t₁ ∷ t₂ ∷ t₃ ∷ t₄ []))
  We can see this element as a tree with 4 + 1 levels; one for x itself
  and 4 for each type in the telescope.

      ty                    x                   
                            |
                ---------------------------      
                |     |     |             |
      t₁        a₁    a₂    a₃            |    var
                |           |             |
              -----         ---------     |
              |   |         |       |     |
      t₂      b₁  b₂        b₃      |     b₄   wk var
              |   |         |       |
              |   |      -------    |
              |   |      |     |    |
      t₃      c₁  |      c₂    c₃   c₄         wk (wk var)
                  |      |
                  |      |
                  |      |
      t₄          d₁     d₂                    wk (wk (wk var))

  We can now illustrate a few functions.
  The (ch n x) function returns the list
  of elements that are n+1-levels below and connected to x.

    > ch 0 x ≡ [a₁ , a₂ , a]
    >
    > ch 1 x ≡ [b₁ , b₂ , b₃ , b₄]
    >
    > ch 0 a₁ ≡ [b₁ , b₂]

  The (ar n x) returns the length of the aforementioned list.
  The (ar-dry n x), on the other hand, will cound the number
  of children that are immediatly connected to x, but
  live n+1 levels lower.

    > ar-dry 1 x ≡ 1

  Note that although (ar 1 x ≡ 4), b₁ and b₂ are connected through a₁
  and b₃ is connected through a₃. Only b₄ is directly connected to x.

  The (fgt n x) will "forget" the levels below n+1 for x.
  Here,

    > fgt 0 a₃ ≡ y, for y depicted as:


     t₁            y             
                   |             
              ---------     
              |       |     
     u1      unit     |     var
                      |
                      |
                      |
     t₃               c₄    wk var



     t₄                     wk (wk var)

  By repeatedly applying forget, we can manage to relate ar and ar-dry;
  for instance, ar-dry n x ≡ ar n (fgt n (ftg (n-1) (... (fgt 0 x))))
  This iterative application of fgt is precisely what fgt-all does.

%<*ch-type>
\begin{code}
  ch : {n : ℕ}{t : T n}{ty : U n}
         → (i : ℕ) → ElU ty t
         → List (ElU (tel-lkup i t) t)
\end{code}
%</ch-type>
%<*ch-def>
\begin{code}
  ch i unit        = []
  ch i (inl el)    = ch i el
  ch i (inr el)    = ch i el
  ch i (ela , elb) = ch i ela ++ ch i elb
  ch i (mu el)     = map unpop (ch (suc i) el)
  ch i (red el)    = map unpop (ch (suc i) el)
  ch zero    (top el) = pop el ∷ []
  ch (suc i) (top el) = map pop (ch i el)
  ch zero    (pop el) = []
  ch (suc i) (pop el) = map pop (ch i el)
\end{code}
%</ch-def>

%<*fgt-type>
\begin{code}
  fgt : {n : ℕ}{t : T n}{ty : U n}
      → (i : ℕ) → ElU ty t
      → ElU ty (tel-forget i t)
\end{code}
%</fgt-type>
%<*fgt-def>
\begin{code}
  fgt i unit        = unit
  fgt i (inl el)    = inl (fgt i el)
  fgt i (inr el)    = inr (fgt i el)
  fgt i (ela , elb) = fgt i ela , fgt i elb
  fgt i (mu el)     = mu (fgt (suc i) el)
  fgt i (red el)    = red (fgt (suc i) el)
  fgt zero    (top el) = top unit
  fgt (suc i) (top el) = top (fgt i el)
  fgt zero    (pop el) = pop el
  fgt (suc i) (pop el) = pop (fgt i el)
\end{code}
%</fgt-def>

%<*ar-type>
\begin{code}
  ar : {n : ℕ}{t : T n}{ty : U n}
     → ℕ → ElU ty t → ℕ
\end{code}
%</ar-type>
%<*ar-def>
\begin{code}
  ar i unit        = 0
  ar i (inl el)    = ar i el
  ar i (inr el)    = ar i el
  ar i (ela , elb) = ar i ela + ar i elb
  ar i (mu el)     = ar (suc i) el
  ar i (red el)    = ar (suc i) el
  ar zero    (top el) = 1
  ar (suc i) (top el) = ar i el
  ar zero    (pop el) = 0
  ar (suc i) (pop el) = ar i el
\end{code}
%</ar-def>

\begin{code}
  ar* : {n : ℕ}{t : T n}{ty : U n}
      → (i : ℕ) → List (ElU ty t) → ℕ
  ar* i []       = 0
  ar* i (x ∷ xs) = ar i x + ar* i xs
\end{code}

  Now, the infamous plug and unplug.

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
  plug {ty = u1} i unit [] = just unit
  plug {ty = u1} i unit (_ ∷ _) = nothing
  plug {ty = ty ⊕ tv} i (inl el) v = inl <M> plug i el v
  plug {ty = ty ⊕ tv} i (inr el) v = inr <M> plug i el v
  plug {ty = ty ⊗ tv} i (ela , elb) v 
    = let va , vb = lsplit (ar i ela) v
       in _,_ <M> plug i ela va <M*> plug i elb vb
  plug {ty = def F ty} i (red el) v 
    = red <M> plug (suc i) el (map pop v)
  plug {ty = μ ty} i (mu el) v 
    = mu <M> plug (suc i) el (map pop v)
  plug {t = t ∷ ts} {var} zero (top el) (v ∷ []) 
    = just (top (unpop v))
  plug {t = t ∷ ts} {var} zero (top el) _
    = nothing
  plug {t = t ∷ ts} {ty = var} (suc i) (top el) v 
    = top <M> plug i el (map unpop v)
  plug {t = t ∷ ts} {ty = wk ty} zero (pop el) []
    = just (pop el)
  plug {t = t ∷ ts} {ty = wk ty} zero (pop el) (_ ∷ _)
    = nothing
  plug {t = t ∷ ts} {ty = wk ty} (suc i) (pop el) v 
    = pop <M> plug i el (map unpop v)
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
