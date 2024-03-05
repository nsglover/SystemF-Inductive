module Util.Lookup where

-- Type Universe Levels
open import Level using (Level)

-- Finite Types
open import Data.Fin.Base using (Fin ; zero ; suc)

-- List Types
open import Data.List using (List ; _∷_ ; length)



lookup : ∀ {l} {S : Set l} → (Δ : List S) → Fin (length Δ) → S
lookup (x ∷ Δ) zero = x
lookup (x ∷ Δ) (suc i) = lookup Δ i 