module Encoding.SystemF where

-- Type Universe Levels
open import Level using (Level)

-- Sigma Types
open import Data.Product

-- Natural Numbers
open import Data.Nat using (ℕ ; zero ; suc)

-- Finite Types
open import Data.Fin.Base using (Fin ; zero ; suc)

-- Cartesian-Closed Categories
open import Category.CCC using (CCC) renaming (_^_ to C^)
open import Category.Type

-- Equality Types
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)

-- N-Ary Functions
open import Util.N-Ary



-- Exponential Expressions

data Exps {l : Level} (O : Set l) : Set l where
  Const : O → Exps O
  Exp : Exps O → Exps O → Exps O

-- We can evaluate expressions

exp-eval : ∀ {lo lm} {O : Set lo} {ℂ : CCC {lm = lm} O} → Exps O → O
exp-eval (Const A) = A
exp-eval {ℂ = ℂ} (Exp F G) = C^ ℂ (exp-eval {ℂ = ℂ} F) (exp-eval {ℂ = ℂ} G)

-- We can change their underlying category

exp-map : ∀ {l l'} {O : Set l} {O' : Set l'} → (O → O') → Exps O → Exps O'
exp-map f (Const A) = Const (f A)
exp-map f (Exp F G) = Exp (exp-map f F) (exp-map f G)

-- Map commutes with eval, assuming preservation of exponentiation
 
exp-eval-map :
  ∀ {lo lm lo' lm'} {O : Set lo} {O' : Set lo'} {ℂ : CCC {lm = lm} O} {𝔻 : CCC {lm = lm'} O'} → 
  (f : O → O') → (∀ {A B : O} → f (C^ ℂ A B) ≡ C^ 𝔻 (f A) (f B)) → (E : Exps O) → 
  f (exp-eval {ℂ = ℂ} E) ≡ exp-eval {ℂ = 𝔻} (exp-map f E)
exp-eval-map f _ (Const _) = Eq.refl
exp-eval-map {𝔻 = 𝔻} f h (Exp F G) = 
  Eq.trans h (Eq.cong₂ (λ x y → C^ 𝔻 x y) (exp-eval-map f h F) (exp-eval-map f h G))  

-- Exponential expressions evaluate to n-ary functions

exp-sig : ∀ {l} {O : Set l} → Exps O → (Σ[ n ∈ ℕ ] (Fin n → Exps O)) × O
exp-sig (Const Res) = (zero , λ ()) , Res
exp-sig (Exp F G) = let ((n , Args) , Res) = exp-sig F in ((suc n) , λ { zero → G ; (suc i) → Args i }) , Res
