open import Prelude

open import Diffing.Universe.Syntax
open import Diffing.Universe.Operations

module Diffing.Universe.Lab where

  
  {-
    data LTree a b
      = Leaf a | Branch b (LTree a b) (LTree a b)
  -}

  LTREE-sop : forall {n} -> U (3 + n)
  LTREE-sop = (wk (wk var) ⊕ wk var ⊗ var ⊗ var)

  LTREE : ∀{n} → U (2 + n)
  LTREE = μ LTREE-sop
  
  LEAF : ∀{n}{t : T n}{a : U (suc n)}{b : U n}
       → ElU b t → ElU LTREE (a ∷ b ∷ t)
  LEAF l = mu (inl (pop (pop (top l))))

  BRANCH : ∀{n}{t : T n}{a : U (suc n)}{b : U n}
       → ElU a (b ∷ t) → ElU LTREE (a ∷ b ∷ t)
       → ElU LTREE (a ∷ b ∷ t) → ElU LTREE (a ∷ b ∷ t)
  BRANCH e l r = mu (inr ((pop (top e)) , ((top l) , (top r))))

  {-
    data ForkSeq a
      = Leaf | Fork a (TL a) (TL a) | Seq a (TL a)
  -}

  FORKSEQ-sop : ∀{n} → U (2 + n)
  FORKSEQ-sop = u1 ⊕ ((wk var) ⊗ var ⊗ var) ⊕ ((wk var) ⊗ var) 

  FS : ∀{n} → U (1 + n)
  FS = μ FORKSEQ-sop

  FS0 : ∀{n}{t : T n}{a : U n} → ElU FS (a ∷ t)
  FS0 = mu (inl unit)

  FS1 : ∀{n}{t : T n}{a : U n} → ElU a t → ElU FS (a ∷ t) → ElU FS (a ∷ t)  
  FS1 a next = mu (inr (inr ((pop (top a)) , (top next))))

  FS2 : ∀{n}{t : T n}{a : U n} → ElU a t 
      → ElU FS (a ∷ t) → ElU FS (a ∷ t) → ElU FS (a ∷ t)
  FS2 a l r = mu (inr (inl ((pop (top a)) , ((top l) , (top r)))))

  {- 
    data List a 
      = Nil | Cons a (List a)
  -}

  LIST-sop : ∀{n} → U (2 + n)
  LIST-sop = u1 ⊕ wk var ⊗ var

  LIST : ∀{n} → U (suc n)
  LIST = μ LIST-sop

  NIL : ∀{n}{t : T n}{a : U n} → ElU LIST (a ∷ t)
  NIL = mu (inl unit)

  CONS : ∀{n}{t : T n}{a : U n}
       → ElU a t → ElU LIST (a ∷ t) → ElU LIST (a ∷ t)
  CONS x xs = mu (inr (pop (top x) , top xs))

  {-
    data RoseTree a 
      = RT a [RT a]
  -}

  RTREE-sop : ∀{n} → U (2 + n)
  RTREE-sop = (wk var ⊗ (def (wk LIST) var))

  RTREE : ∀{n} → U (suc n)
  RTREE = μ RTREE-sop

  RT : ∀{n}{t : T n}{a : U n}
     → ElU a t → ElU LIST (RTREE ∷ a ∷ t) → ElU RTREE (a ∷ t)
  RT x xs = mu (pop (top x) , red (pop xs))

  RT-leaf : ∀{n}{t : T n}{a : U n}
          → ElU a t → ElU RTREE (a ∷ t)
  RT-leaf x = RT x NIL

  {- 
    data Nat = Z | S Nat 
  -}

  NAT : ∀{n} → U n
  NAT = μ (u1 ⊕ var)

  ZZ : ∀{n}{t : T n} → ElU NAT t
  ZZ = mu (inl unit)

  SS : ∀{n}{t : T n} → ElU NAT t → ElU NAT t
  SS x = mu (inr (top x))

  {-
    data Bool = True | False
  -}

  BOOL : ∀{n} → U n
  BOOL = u1 ⊕ u1

  TT : ∀{n}{t : T n} → ElU BOOL t
  TT = inl unit

  FF : ∀{n}{t : T n} → ElU BOOL t
  FF = inr unit


  -- And finally some elements
  module Elements where
    l1 l2 l3 l4 : ElU LIST (BOOL ∷ [])

    l1 = CONS TT (CONS TT NIL)

    l2 = CONS FF (CONS TT NIL)

    l3 = CONS FF (CONS FF l1)

    l4 = NIL

    aux1 aux2 aux3 : ElU LTREE (NAT ∷ LIST ∷ BOOL ∷ [])
    aux1 = BRANCH ZZ (LEAF l1) (BRANCH (SS ZZ) (LEAF l4) (LEAF l3))

    aux2 = LEAF l2

    aux3 = BRANCH (SS (SS ZZ)) aux1 (BRANCH ZZ aux2 (LEAF l1))

    myTree1 : ElU RTREE (LTREE ∷ NAT ∷ LIST ∷ BOOL ∷ [])
    myTree1 
      = RT aux1 
           (CONS (RT aux3 
                     (CONS (RT-leaf aux1) 
                     (CONS (RT-leaf aux3) 
                     (CONS (RT-leaf aux2) 
                       NIL)))) 
           (CONS (RT-leaf aux2) 
             NIL))

    unμ : {n : ℕ}{t : T n}{ty : U (suc n)}
        → ElU (μ ty) t → ElU ty (μ ty ∷ t)
    unμ (mu x) = x

    compute : (i k l j : ℕ) → ℕ × ℕ × ℕ
    compute i k l j = ar i (unμ myTree1) 
                , ar k (fgt j (unμ myTree1)) 
                , ar* l (ch j (unμ myTree1))

  
