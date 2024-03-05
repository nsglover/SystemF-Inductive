module Util.N-Ary where

-- Type Universe Levels
open import Level using (Level) renaming (zero to lzero ; suc to lsuc)

-- Natural Numbers
open import Data.Nat using (ℕ ; zero ; suc ; _+_)

-- Product Types
open import Data.Unit
open import Data.Product
open import Data.Product.Properties as Prod

-- Product Sum
open import Data.Empty
open import Data.Sum
open import Data.Sum.Properties as Sum

-- Finite Types
open import Data.Fin.Base as Fin using (Fin ; zero ; suc)
open import Data.Fin.Properties as Fin

-- List Types
open import Data.List as List using (List ; [] ; _∷_)

-- Cartesian-Closed Categories
open import Category.CCC using (CCC)
open import Category.Type

-- Equality Types
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)

-- Safe List Lookup
open import Util.Lookup



Append : ∀ {l} {n m : ℕ} {A : Set l} → (Fin n → A) → (Fin m → A) → (Fin (n + m) → A)
Append {n = n} F G i = [ F , G ] (Fin.splitAt n i)

append : 
  ∀ {l} {n m : ℕ} → {F : Fin n → Set l} → {G : Fin m → Set l} →
  (f : (i : Fin n) → F i) → (g : (i : Fin m) → G i) → ((i : Fin (n + m)) → Append F G i)
append {n = n} {m = m} f g i with Fin.splitAt n i
... | inj₁ i₁ = f i₁
... | inj₂ i₂ = g i₂

split : 
  ∀ {l} {n m : ℕ} → {F : Fin n → Set l} → {G : Fin m → Set l} → 
  ((i : Fin (n + m)) → Append F G i) → ((i : Fin n) → F i) × ((i : Fin m) → G i)
split {n = n} {m = m} h = 
  (λ i → Eq.subst (λ i → [ _ , _ ] i) (Fin.splitAt-join n m (inj₁ i)) (h (Fin.join n m (inj₁ i)))) ,
  (λ i → Eq.subst (λ i → [ _ , _ ] i) (Fin.splitAt-join n m (inj₂ i)) (h (Fin.join n m (inj₂ i))))
