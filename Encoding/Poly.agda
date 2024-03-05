module Encoding.Poly where

-- Natural Numbers
open import Data.Nat using (ℕ ; zero ; suc ; _≤_ ; _+_)
open _≤_
import Data.Nat.Properties as Nat

-- Finite Types
open import Data.Fin.Base hiding (_+_ ; _≤_)

-- Equality Types
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)



-- A univariate polynomial operator with a fixed number of base constants.

data Poly (n : ℕ) : Set where
  Const : Fin n → Poly n
  Var : Poly n
  Zero : Poly n
  One : Poly n
  Sum : Poly n → Poly n → Poly n
  Prod : Poly n → Poly n → Poly n

map-indices : {n m : ℕ} → (Fin n → Fin (n + m)) → Poly n → Poly (n + m)
map-indices f (Const i) = Const (f i)
map-indices f Var = Var
map-indices f Zero = Zero
map-indices f One = One
map-indices f (Sum P Q) = Sum (map-indices f P) (map-indices f Q)
map-indices f (Prod P Q) = Prod (map-indices f P) (map-indices f Q)

-- Although we intend to work with polynomial operators, we will typically work with these weird things, which are
-- constructed entirely to appease Agda's termination checker. They exist because operations I need to write handle
-- the case where P = Prod (Prod P Q) R by simply calling themselves recursively on Prod P (Prod Q R). Of course this
-- terminates as long as they never push the parenthesis the other way (and they don't), but Agda's termination checker
-- can't figure that out. Functions that wish to do recursion on Poly in this way can do it on Poly' instead and
-- then use poly-to-poly'.

data Poly' (n : ℕ) : Set where
  Const : Fin n → Poly' n
  Var : Poly' n
  Zero : Poly' n
  One : Poly' n
  Sum : Poly' n → Poly' n → Poly' n
  Prod-Const : Poly' n → Fin n → Poly' n
  Prod-Var : Poly' n → Poly' n

private
  nodes : {n : ℕ} → Poly n → ℕ
  nodes (Const _) = zero
  nodes Var = zero
  nodes Zero = zero
  nodes One = zero
  nodes (Sum P Q) = suc (nodes P + nodes Q)
  nodes (Prod P Q) = suc (nodes P + nodes Q)

  sum-case-lemma : 
    {n : ℕ} → (ns : ℕ) → (P Q R : Poly n) → 
    suc (nodes P + suc (nodes Q + nodes R)) ≤ ns → suc (nodes P + nodes Q) ≤ ns
  sum-case-lemma ns P Q R h = Nat.≤-trans (s≤s (Nat.m≤m+n _ _)) 
    (
      let h' = Eq.subst (_≤ ns) (Nat.+-suc _ _) (Nat.≤-trans (Nat.n≤1+n _) h) in 
      Eq.subst (λ x → suc x ≤ ns) (Eq.sym (Nat.+-assoc (nodes P) _ _)) h'
    )

  mutual
    polyop-prod-to-polyop' : {n : ℕ} → (ns : ℕ) → (P Q : Poly n) → nodes (Prod P Q) ≤ ns → Poly' n
    polyop-prod-to-polyop' (suc ns) P (Const A) h =
      Prod-Const (polyop-to-polyop' ns P (Eq.subst (_≤ ns) (Nat.+-comm _ zero) (Nat.≤-pred h))) A
    polyop-prod-to-polyop' (suc ns) P Var h =
      Prod-Var (polyop-to-polyop' ns P (Eq.subst (_≤ ns) (Nat.+-comm _ zero) (Nat.≤-pred h)))
    polyop-prod-to-polyop' (suc ns) P Zero h = Zero
    polyop-prod-to-polyop' (suc ns) P One h = polyop-to-polyop' ns P (Eq.subst (_≤ ns) (Nat.+-comm _ zero) (Nat.≤-pred h))
    polyop-prod-to-polyop' (suc ns) P (Sum Q R) h = Sum
      (polyop-prod-to-polyop' (suc ns) P Q (sum-case-lemma (suc ns) P Q R h)) 
      (
        polyop-prod-to-polyop' (suc ns) P R 
        (sum-case-lemma (suc ns) P R Q (Eq.subst (λ x → suc (nodes P + suc x) ≤ (suc ns)) (Nat.+-comm (nodes Q) _) h))
      )
    polyop-prod-to-polyop' (suc ns) P (Prod Q R) h =
      polyop-prod-to-polyop' (suc ns) (Prod P Q) R 
      (Eq.subst (λ x → suc x ≤ (suc ns)) (Eq.trans (Nat.+-suc _ _) (Eq.cong suc (Eq.sym (Nat.+-assoc (nodes P) _ _)))) h)

    polyop-to-polyop' : {n : ℕ} → (ns : ℕ) → (P : Poly n) → nodes P ≤ ns → Poly' n
    polyop-to-polyop' _ (Const A) _ = Const A
    polyop-to-polyop' _ Var _ = Var
    polyop-to-polyop' _ Zero _ = Zero
    polyop-to-polyop' _ One _ = One
    polyop-to-polyop' ns (Sum P Q) h = Sum 
      (polyop-to-polyop' ns P (Nat.≤-trans (Nat.m≤m+n _ _) (Nat.≤-trans (Nat.n≤1+n _) h))) 
      (polyop-to-polyop' ns Q (Nat.≤-trans (Nat.m≤n+m _ _) (Nat.≤-trans (Nat.n≤1+n _) h)))
    polyop-to-polyop' ns (Prod P Q) h = polyop-prod-to-polyop' ns P Q h

poly-to-poly' : {n : ℕ} → Poly n → Poly' n
poly-to-poly' P = polyop-to-polyop' (nodes P) P Nat.≤-refl
