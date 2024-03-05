
module Category.Type where

-- Type Universe Levels
open import Level using (Level) renaming (zero to lzero ; suc to lsuc)

-- Product Types
open import Data.Unit
open import Data.Product renaming (_×_ to _∧_) hiding (<_,_>)
open import Data.Product.Properties as Prod

-- Sum Types
open import Data.Empty 
open import Data.Sum renaming (_⊎_ to _∨_) hiding ([_,_])
open import Data.Sum.Properties as Sum

-- Equality Types
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)

-- Cartesian-Closed Categories
open import Category.CCC

private
  -- Cheating for the exponential universal property. I thought I could avoid it, but alas.
  postulate extensionality : ∀ {l} {A B : Set l} {f g : A → B} → (∀ x → f x ≡ g x) → f ≡ g

TypeCCC : ∀ {l} → CCC (Set l)
_↦_ TypeCCC A B = A → B
id TypeCCC A = λ x → x
(TypeCCC ∘ G) F = λ x → G (F x)
_≃_ TypeCCC {A} F G = ∀ (a a' : A) → a ≡ a' → F a ≡ G a'
≃-refl TypeCCC {A} {B} {F} _ _ h = Eq.cong F h
≃-sym TypeCCC hxy a a' haa' = Eq.sym (hxy a' a (Eq.sym haa'))
≃-trans TypeCCC hxy hyz a a' haa' = Eq.trans (hxy a a' haa') (hyz a' a' Eq.refl)
ident TypeCCC F = ≃-refl TypeCCC , ≃-refl TypeCCC
assoc TypeCCC F G H a a' haa' = Eq.cong (λ x → H (G (F x))) haa'
𝟘 (TypeCCC {l}) = Level.Lift l ⊥
𝟘-mor TypeCCC A = λ a → ⊥-elim (Level.lower a)
𝟘-univ TypeCCC _ _ _ a = ⊥-elim (Level.lower a)
𝟙 (TypeCCC {l}) = Level.Lift l ⊤
𝟙-mor TypeCCC A = λ _ → (Level.lift tt)
𝟙-univ TypeCCC _ _ _ _ _ = Eq.refl
_+_ TypeCCC A B = A ∨ B
i₁ TypeCCC = inj₁
i₂ TypeCCC = inj₂
[ TypeCCC , F ] G (inj₁ a) = F a
[ TypeCCC , F ] G (inj₂ b) = G b
+-comm TypeCCC F G = ≃-refl TypeCCC , ≃-refl TypeCCC
+-univ TypeCCC F G H (hf , _) (inj₁ a) (inj₁ a') haa' = Eq.sym (hf a' a (inj₁-injective (Eq.sym haa')))
+-univ TypeCCC F G H (_ , hg) (inj₂ b) (inj₂ b') hbb' = Eq.sym (hg b' b (inj₂-injective (Eq.sym hbb')))
_×_ TypeCCC A B = A ∧ B
π₁ TypeCCC = proj₁
π₂ TypeCCC = proj₂
< TypeCCC , F > G = λ x → (F x) , (G x)
×-comm TypeCCC F G = ≃-refl TypeCCC , ≃-refl TypeCCC
×-univ TypeCCC F G H (hf , hg) a a' haa' = ×-≡,≡→≡ (≃-sym TypeCCC hf a a' haa' , ≃-sym TypeCCC hg a a' haa')
_^_ TypeCCC B A = A → B
eval TypeCCC = λ (f , a) → f a
curr TypeCCC F = λ a b → F (a , b)
^-comm TypeCCC F a a' haa' = Eq.subst (λ x → F a ≡ F x) haa' (≃-refl TypeCCC a a' haa')
^-univ TypeCCC {A} F G h a a' haa' = 
  Eq.sym (extensionality λ x → h (a' , x) (a , x) (Eq.cong (λ y → (y , x)) (Eq.sym haa')))
-- I realized I had to cheat on the last axiom, unfortunately. It's alright though; I don't actually need these
-- axioms for the actual inductive type stuff. I just included them for fun. I can imagine there might be a way around
-- this with a better definition of ≃, but I am too lazy to figure that out right now.