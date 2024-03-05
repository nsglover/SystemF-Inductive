
module Category.QPER where

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
open import Category.Type



-- I had to de-parameterize QPER's like this; I don't know how else to put them into a category.
record QPER' {l : Level} : Set (lsuc l) where 
  field
    Dom : Set l
    Cod : Set l
    Rel' : (a : Dom) (b : Cod) → Set l
    zzc' : {a a' : Dom} {b b' : Cod} → Rel' a b → Rel' a' b' → Rel' a' b → Rel' a b'
open QPER' public

-- A helpful result is that we can re-parameterize them without much issue.

record QPER {l : Level} (A B : Set l) : Set (lsuc l) where
  field
    Rel : (a : A) (b : B) → Set l
    zzc : {a a' : A} {b b' : B} → Rel a b → Rel a' b' → Rel a' b → Rel a b'
open QPER public

qper-to-qper' : ∀ {l} {A B : Set l} → QPER A B → QPER'
Dom (qper-to-qper' {A = A} Q) = A
Cod (qper-to-qper' {B = B} Q) = B
Rel' (qper-to-qper' Q) = Rel Q
zzc' (qper-to-qper' Q) = zzc Q

qper'-to-qper : ∀ {l} → (Q : QPER' {l}) → QPER (Dom Q) (Cod Q)
Rel (qper'-to-qper Q) = Rel' Q
zzc (qper'-to-qper Q) = zzc' Q

-- Example: Definitional equality on a type

Q≡ : ∀ {l} → (A : Set l) → QPER A A
Rel (Q≡ A) = _≡_
zzc (Q≡ A) Eq.refl Eq.refl Eq.refl = Eq.refl




record QPERMor {l : Level} (X : QPER' {l}) (Y : QPER' {l}) : Set l where
  field
    qf : Dom X → Dom Y
    qf' : Cod X → Cod Y
    law : {a : Dom X} {a' : Cod X} → Rel' X a a' → Rel' Y (qf a) (qf' a')
open QPERMor public

QPERCCC : ∀ {l} → CCC {lo = lsuc l} {lm = l} (QPER' {l})

_↦_ QPERCCC X Y = QPERMor X Y

qf (id QPERCCC X) = λ x → x
qf' (id QPERCCC X) = λ x → x
law (id QPERCCC X) = λ x → x

qf ((QPERCCC ∘ G) F) = λ x → (qf G) ((qf F) x)
qf' ((QPERCCC ∘ G) F) = λ x → (qf' G) ((qf' F) x)
law ((QPERCCC ∘ G) F) = λ x → (law G) ((law F) x)

_≃_ QPERCCC {X} {Y} F G = ∀ (a : Dom X) → ∀ (a' : Cod X) → Rel' X a a' → Rel' Y (qf F a) (qf' G a')

≃-refl QPERCCC {X} {Y} {F} a a' = law F
≃-sym QPERCCC {X} {Y} {F} {G} hxy a a' Raa' = zzc' Y (law G Raa') (law F Raa') (hxy a a' Raa')
≃-trans QPERCCC {X} {Y} {F} {G} {H} hxy hyz a a' Raa' = zzc' Y (hxy a a' Raa') (hyz a a' Raa') (law G Raa')

ident QPERCCC F = (λ _ _ → law F) , (λ _ _ → law F)
assoc QPERCCC F G H _ _ Raa' = law H (law G (law F Raa'))

Dom (𝟘 QPERCCC) = 𝟘 TypeCCC
Cod (𝟘 QPERCCC) = 𝟘 TypeCCC
Rel' (𝟘 QPERCCC) _ _ = 𝟘 TypeCCC
zzc' (𝟘 QPERCCC) h _ _ = h

qf (𝟘-mor QPERCCC X) = λ a → (⊥-elim (Level.lower a))
qf' (𝟘-mor QPERCCC X) = λ a → (⊥-elim (Level.lower a))
law (𝟘-mor QPERCCC X) = λ a → (⊥-elim (Level.lower a))

𝟘-univ QPERCCC _ _ _ _ = λ a → (⊥-elim (Level.lower a))

Dom (𝟙 QPERCCC) = 𝟙 TypeCCC
Cod (𝟙 QPERCCC) = 𝟙 TypeCCC
Rel' (𝟙 QPERCCC) _ _ = 𝟙 TypeCCC
zzc' (𝟙 QPERCCC) _ _ _ = Level.lift tt

qf (𝟙-mor QPERCCC X) _ = Level.lift tt
qf' (𝟙-mor QPERCCC X) _ = Level.lift tt
law (𝟙-mor QPERCCC X) _ = Level.lift tt

𝟙-univ QPERCCC _ _ _ _ _ = Level.lift tt

Dom ((QPERCCC + X) Y) = Dom X ∨ Dom Y
Cod ((QPERCCC + X) Y) = Cod X ∨ Cod Y
Rel' ((QPERCCC + X) Y) (inj₁ a) (inj₁ b) = Rel' X a b
Rel' ((QPERCCC + X) Y) (inj₂ a) (inj₂ b) = Rel' Y a b
Rel' ((QPERCCC + X) Y) (inj₁ _) (inj₂ _) = 𝟘 TypeCCC
Rel' ((QPERCCC + X) Y) (inj₂ _) (inj₁ _) = 𝟘 TypeCCC
zzc' ((QPERCCC + X) Y) {inj₁ _} {inj₁ _} {inj₁ _} {inj₁ _} = zzc' X
zzc' ((QPERCCC + X) Y) {inj₂ _} {inj₂ _} {inj₂ _} {inj₂ _} = zzc' Y
zzc' ((QPERCCC + X) Y) {inj₁ _} {inj₂ _} {inj₁ _} {b'} _ _ = λ a → (⊥-elim (Level.lower a))
zzc' ((QPERCCC + X) Y) {inj₁ _} {inj₂ _} {inj₂ _} {b'} h = ⊥-elim (Level.lower h)

qf (i₁ QPERCCC) = inj₁
qf' (i₁ QPERCCC) = inj₁
law (i₁ QPERCCC) h = h

qf (i₂ QPERCCC) = inj₂
qf' (i₂ QPERCCC) = inj₂
law (i₂ QPERCCC) h = h

qf ([ QPERCCC , F ] G) (inj₁ a) = qf F a
qf ([ QPERCCC , F ] G) (inj₂ b) = qf G b
qf' ([ QPERCCC , F ] G) (inj₁ a') = qf' F a'
qf' ([ QPERCCC , F ] G) (inj₂ b') = qf' G b'
law ([ QPERCCC , F ] G) {inj₁ _} {inj₁ _} h = law F h
law ([ QPERCCC , F ] G) {inj₂ _} {inj₂ _} h = law G h

+-comm QPERCCC F G = (λ _ _ → law F) , (λ _ _ → law G)

+-univ QPERCCC {X} {Y} {Z} F G H (h₁ , h₂) (inj₁ a) (inj₁ a') Raa' = zzc' X (law H Raa') (law F Raa') (h₁ a a' Raa')
+-univ QPERCCC {X} {Y} {Z} F G H (h₁ , h₂) (inj₂ b) (inj₂ b') Rbb' = zzc' X (law H Rbb') (law G Rbb') (h₂ b b' Rbb')

Dom ((QPERCCC × X) Y) = Dom X ∧ Dom Y
Cod ((QPERCCC × X) Y) = Cod X ∧ Cod Y
Rel' ((QPERCCC × X) Y) (a , a') (b , b') = Rel' X a b ∧ Rel' Y a' b'
zzc' ((QPERCCC × X) Y) h₁ h₂ h₃ = zzc' X (proj₁ h₁) (proj₁ h₂) (proj₁ h₃) , zzc' Y (proj₂ h₁) (proj₂ h₂) (proj₂ h₃)

qf (π₁ QPERCCC) = proj₁
qf' (π₁ QPERCCC) = proj₁
law (π₁ QPERCCC) = proj₁

qf (π₂ QPERCCC) = proj₂
qf' (π₂ QPERCCC) = proj₂
law (π₂ QPERCCC) = proj₂

qf (< QPERCCC , F > G) a = qf F a , qf G a
qf' (< QPERCCC , F > G) a' = qf' F a' , qf' G a'
law (< QPERCCC , F > G) Raa' = law F Raa' , law G Raa'

×-comm QPERCCC F G = (λ _ _ → law F) , (λ _ _ → law G)

×-univ QPERCCC {X} {Y} {Z} F G H (h₁ , h₂) a a' Raa' = 
  (zzc' Y (proj₁ (law H Raa')) (law F Raa') (h₁ a a' Raa')) ,
  (zzc' Z (proj₂ (law H Raa')) (law G Raa') (h₂ a a' Raa'))

Dom ((QPERCCC ^ Y) X) = Dom X → Dom Y
Cod ((QPERCCC ^ Y) X) = Cod X → Cod Y
Rel' ((QPERCCC ^ Y) X) = λ qf g → (a : Dom X) (b : Cod X) → Rel' X a b → Rel' Y (qf a) (g b)
zzc' ((QPERCCC ^ Y) X) h₁ h₂ h₃ = λ a b h → zzc' Y (h₁ a b h) (h₂ a b h) (h₃ a b h)

qf (eval QPERCCC) (a , N) = a N
qf' (eval QPERCCC) (a' , N') = a' N'
law (eval QPERCCC) {a} {a'} (h₁ , h₂) = h₁ (proj₂ a) (proj₂ a') h₂

qf (curr QPERCCC F) a N = qf F (a , N)
qf' (curr QPERCCC F) a' N' = qf' F (a' , N')
law (curr QPERCCC F) Raa' _ _ RNN' = law F (Raa' , RNN')

^-comm QPERCCC F _ _ = law F 

^-univ QPERCCC {X} {Y} {Z} F G h a a' Raa' N N' RNN' =   
  zzc' Z (law G Raa' N N' RNN') (law F (Raa' , RNN')) (h (a , N) (a' , N') (Raa' , RNN')) 