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
    u0  : {n : ℕ} → U n
    u1  : {n : ℕ} → U n
    _⊕_ : {n : ℕ} → U n → U n → U n
    _⊗_ : {n : ℕ} → U n → U n → U n
    def : {n : ℕ} → U (suc n) → U n → U n
    μ   : {n : ℕ} → U (suc n) → U n
    var : {n : ℕ} → U (suc n)
    wk  : {n : ℕ} → U n → U (suc n)
\end{code}
%</U-def>

\begin{code}
  infixr 20 _⊕_
  infixr 25 _⊗_
\end{code}

%<*T-def>
\begin{code}
  data T : ℕ → Set where
    []  : T 0
    _∷_ : {n : ℕ} → U n → T n → T (suc n)
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
