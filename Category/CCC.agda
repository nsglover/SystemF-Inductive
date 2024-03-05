module Category.CCC where

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

record CCC {lo lm : Level} (Obj : Set lo) : Set (lsuc (lo Level.⊔ lm)) where
  infix 1 _↦_
  infix 3 _≃_
  infix 8 _∘_

  infix 2 _+_
  infix 2 _×_
  infix 10 _^_
  
  field
    -- Category Definition and Axioms
    _↦_ : Obj → Obj → Set lm
    id : (A : Obj) → (A ↦ A)
    _∘_ : {A B C : Obj} → (B ↦ C) → (A ↦ B) → A ↦ C
    
    _≃_ : ∀ {A B : Obj} → (A ↦ B) → (A ↦ B) → Set lm
    ≃-refl : ∀ {A B : Obj} {f : A ↦ B} → f ≃ f
    ≃-sym : ∀ {A B : Obj} {f g : A ↦ B} → f ≃ g → g ≃ f
    ≃-trans : ∀ {A B : Obj} {f g h : A ↦ B} → f ≃ g → g ≃ h → f ≃ h

    ident : {A B : Obj} → (f : A ↦ B) → (id B ∘ f ≃ f) ∧ (f ≃ f ∘ id A)
    assoc : {A B C D : Obj} → (f : A ↦ B) → (g : B ↦ C) → (h : C ↦ D) → h ∘ (g ∘ f) ≃ (h ∘ g) ∘ f

    -- Initial Object Definitions Axioms
    𝟘 : Obj
    𝟘-mor : (A : Obj) → 𝟘 ↦ A

    𝟘-univ : {A : Obj} → (f : 𝟘 ↦ A) → (g : 𝟘 ↦ A) → f ≃ g

    -- Terminal Object Definition and Axioms
    𝟙 : Obj
    𝟙-mor : (A : Obj) → A ↦ 𝟙
    
    𝟙-univ : {A : Obj} → (f : A ↦ 𝟙) → (g : A ↦ 𝟙) → f ≃ g
    
    -- Binary Sum Definition and Axioms
    _+_ : (A B : Obj) → Obj
    i₁ : {A B : Obj} → A ↦ A + B
    i₂ : {A B : Obj} → B ↦ A + B
    [_,_] : {X A B : Obj} → A ↦ X → B ↦ X → (A + B) ↦ X

    +-comm : {X A B : Obj} → (f : A ↦ X) → (g : B ↦ X) → (f ≃ [ f , g ] ∘ i₁) ∧ (g ≃ [ f , g ] ∘ i₂)
    +-univ : {X A B : Obj} → (f : A ↦ X) → (g : B ↦ X) → (h : A + B ↦ X) → (f ≃ h ∘ i₁) ∧ (g ≃ h ∘ i₂) → h ≃ [ f , g ]

    -- Binary Product Definition and Axioms
    _×_ : (A B : Obj) → Obj
    π₁ : {A B : Obj} → A × B ↦ A
    π₂ : {A B : Obj} → A × B ↦ B
    <_,_> : {X A B : Obj} → X ↦ A → X ↦ B → X ↦ (A × B)
    
    ×-comm : {X A B : Obj} → (f : X ↦ A) → (g : X ↦ B) → (f ≃ π₁ ∘ < f , g >) ∧ (g ≃ π₂ ∘ < f , g >)
    ×-univ : {X A B : Obj} → (f : X ↦ A) → (g : X ↦ B) → (h : X ↦ A × B) → (f ≃ π₁ ∘ h) ∧ (g ≃ π₂ ∘ h) → h ≃ < f , g >

    -- Exponential Object Definition and Axioms
    _^_ : (C B : Obj) → Obj
    eval : {C B : Obj} → (C ^ B) × B ↦ C
    curr : {A C B : Obj} → (A × B ↦ C) → (A ↦ C ^ B)

    ^-comm : {A B C : Obj} → (g : (A × B) ↦ C) → g ≃ eval ∘ (< curr g ∘ π₁ , π₂ >)
    ^-univ : {A B C : Obj} → (g : (A × B) ↦ C) → (h : A ↦ C ^ B) → g ≃ eval ∘ (< h ∘ π₁ , π₂ >) → h ≃ curr g
open CCC public 