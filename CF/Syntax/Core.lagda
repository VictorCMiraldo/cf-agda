\begin{code}
open import Prelude

module CF.Syntax.Core where
\end{code}

  This universe and it's semantics were adapted from:
     "Generic Programming with Dependent Types"
  from McBride, Altenkirch and Morris.

%<*U-def>
\begin{code}
  data U : ℕ → Set where
    u0   : {n : ℕ} → U n
    u1   : {n : ℕ} → U n
    _⊕_  : {n : ℕ} → U n → U n → U n
    _⊗_  : {n : ℕ} → U n → U n → U n
    def  : {n : ℕ} → U (suc n) → U n → U n
    μ    : {n : ℕ} → U (suc n) → U n
    var  : {n : ℕ} → U (suc n)
    wk   : {n : ℕ} → U n → U (suc n)
\end{code}
%</U-def>

\begin{code}
  infixr 20 _⊕_
  infixr 25 _⊗_
\end{code}

%<*T-def>
\begin{code}
  data T : ℕ → Set where
    []   : T 0
    _∷_  : {n : ℕ} → U n → T n → T (suc n)
\end{code}
%</T-def>

%<*tel-lkup>
\begin{code}
  tel-lkup : {n : ℕ} → ℕ → T n → U n
  tel-lkup n       []      = u0
  tel-lkup zero    (x ∷ t) = wk x
  tel-lkup (suc n) (x ∷ t) = wk (tel-lkup n t)
\end{code}
%</tel-lkup>

%<*tel-forget>
\begin{code}
  tel-forget : {n : ℕ} → ℕ → T n → T n
  tel-forget n []            = []
  tel-forget zero    (x ∷ t) = u1 ∷ t
  tel-forget (suc n) (x ∷ t) = x ∷ tel-forget n t
\end{code}
%</tel-forget>

  Forgets telescope information, from i to k.
  If

    t = t₁ ∷ t₂ ∷ t₃ ∷ t₄ ∷ t₅ ∷ t₆ ∷ []
    
  then,

    tel-drop 1 2 t = t₁ ∷ u1 ∷ u1 ∷ t₄ ∷ t₅ ∷ t₆ ∷ []

%<*tel-drop>
\begin{code}
  tel-drop : {n : ℕ} → ℕ → ℕ → T n → T n
  tel-drop i j       [] = []
  tel-drop (suc i) j    (t ∷ ts) = t ∷ tel-drop i j ts
  tel-drop zero    zero (t ∷ ts) = t ∷ ts
  tel-drop zero (suc j) (t ∷ ts) = u1 ∷ tel-drop 0 j ts   
\end{code}
%</tel-drop>

  A design by specification might be more intuitive; but hinders
  Agda from reducing the term. Here is the specification lemmas:

%<*tel-drop-spec-1-type>
\begin{code}
  tel-drop-spec-1
    : {n : ℕ}(i j : ℕ)(t : T n)
    → tel-drop i (suc j) t ≡ tel-forget i (tel-drop (suc i) j t)
\end{code}
%</tel-drop-spec-1-type>
\begin{code}
  tel-drop-spec-1 i        j []      = refl
  tel-drop-spec-1 zero    j (t ∷ ts) = refl
  tel-drop-spec-1 (suc i) j (t ∷ ts) = cong (t ∷_) (tel-drop-spec-1 i j ts)
\end{code}

%<*tel-drop-spec-2-type>
\begin{code}
  tel-drop-spec-2
    : {n : ℕ}(i : ℕ)(t : T n)
    → tel-drop i 0 t ≡ t
\end{code}
%</tel-drop-spec-2-type>
\begin{code}
  tel-drop-spec-2 i       []      = refl
  tel-drop-spec-2 zero    (x ∷ t) = refl
  tel-drop-spec-2 (suc i) (x ∷ t) = cong (x ∷_) (tel-drop-spec-2 i t)
\end{code}

%<*tel-lkup-drop-spec-type>
\begin{code}
  tel-lkup-drop-spec
    : {n : ℕ}(i j : ℕ)(t : T n)
    → tel-lkup i (tel-drop (suc i) j t) ≡ tel-lkup i t
\end{code}
%</tel-lkup-drop-spec-type>
\begin{code}
  tel-lkup-drop-spec i j []            = refl
  tel-lkup-drop-spec zero j (x ∷ t)    = refl
  tel-lkup-drop-spec (suc i) j (x ∷ t) = cong wk (tel-lkup-drop-spec i j t)
\end{code}

%<*tel-lkup-drop-id-type>
\begin{code}
  tel-lkup-drop-id
    : {n : ℕ}(i : ℕ)(t : T n)
    → tel-lkup i (tel-drop 0 i t) ≡ tel-lkup i t
\end{code}
%</tel-lkup-drop-id-type>
%<*tel-lkup-drop-id-def>
\begin{code}
  tel-lkup-drop-id i []            = refl
  tel-lkup-drop-id zero (x ∷ t)    = refl
  tel-lkup-drop-id (suc i) (x ∷ t) = cong wk (tel-lkup-drop-id i t)
\end{code}
%</tel-lkup-drop-id-def>

  
