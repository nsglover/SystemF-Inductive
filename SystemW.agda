module SystemW where

-- Type Universe Levels
open import Level using (Level) renaming (zero to lzero ; suc to lsuc)

-- Sigma Types
open import Data.Product hiding (_×_)

-- Natural Numbers
open import Data.Nat using (ℕ)
import Data.Nat.Properties as Nat

-- Function Types
open import Function.Base using (id)

-- Finite Types
open import Data.Fin.Base as Fin using (Fin ; zero ; suc ; _↑ˡ_ ; _↑ʳ_)

-- List Types
open import Data.List as List using (List ; [] ; [_] ; _∷_ ; _++_)
import Data.List.Properties as List

-- Equality Types
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)

-- Church Encoding
open import Encoding.Poly
open import Encoding.SystemF
open import Encoding.Church

-- Cartesian-Closed Categories
open import Category.Type
open import Category.QPER

-- N-Ary Functions
open import Util.N-Ary

-- Safe List Lookup
open import Util.Lookup



--------------------------
-------- INTERFACE -------
--------------------------

-- Polynomial type operators for defining inductive types

infixr 2 _+_
infixr 2 _×_

data PolyTypeOp {l : Level} : Set (lsuc l) where
  Con : (A : Set l) → QPER A A → PolyTypeOp {l}
  Var : PolyTypeOp {l}
  𝟘 : PolyTypeOp {l}
  𝟙 : PolyTypeOp {l}
  _+_ : PolyTypeOp {l} → PolyTypeOp {l} → PolyTypeOp {l}
  _×_ : PolyTypeOp {l} → PolyTypeOp {l} → PolyTypeOp {l}

-- The interface for inductive types in System F

record SystemWType {l : Level} : Set (lsuc l) where
  field
    -- The shape of the inductive type; μ-View {X} Y is isomorphic to (P[Y] → X) → X
    μ-View : {Set l} → Set l → Set l

    -- We can map views to views of other types
    μ-ViewMap : {X Y Z : Set l} → (Y → Z) → μ-View {X} Y → μ-View {X} Z

  -- The encoding of the inductive type as a type constructor that only uses preexisting types and arrows
  μ-Type : {Set l} → Set l
  μ-Type {X} = μ-View {X} X

  field
    -- The definition of equivalence at inductive types
    μ-≡ : (A B : Set l) → QPER A B → QPER (μ-Type {A}) (μ-Type {B})

    -- The introduction form for inductive types
    μ-Fold : ∀ {X} → μ-View {X} (μ-Type {X}) → μ-Type {X}

  -- The System F encoding of the inductive type
  μ-Type' : Set (lsuc l)
  μ-Type' = ∀ {X} → μ-Type {X}

  -- The standard equivalence QPER for the System F encoding of the inductive type
  μ-≡' : QPER μ-Type' μ-Type'
  Rel μ-≡' W₁ W₂ = (A B : Set l) → (Inv : QPER A B) → Rel (μ-≡ A B Inv) W₁ W₂
  zzc μ-≡' hab ha'b' ha'b A B Inv = zzc (μ-≡ A B Inv) (hab A B Inv) (ha'b' A B Inv) (ha'b A B Inv)

  
open SystemWType public

-- The inductive type interface generator

{-# TERMINATING #-}
μ : ∀ {l} → PolyTypeOp {l} → SystemWType {l}



--------------------------
----- IMPLEMENTATION -----
--------------------------

private
  combine : ∀ {l} →
    Σ[ Δ₁ ∈ List (Σ[ A ∈ Set l ] QPER A A) ] Poly (List.length Δ₁) → 
    Σ[ Δ₂ ∈ List (Σ[ A ∈ Set l ] QPER A A) ] Poly (List.length Δ₂) →
    ({n : ℕ} → Poly n → Poly n → Poly n) → 
    Σ[ Δ ∈ List (Σ[ A ∈ Set l ] QPER A A) ] Poly (List.length Δ)
  combine (Δ₁ , P') (Δ₂ , Q') F = 
    Δ₁ ++ Δ₂ , 
    (
      F
        (Eq.subst Poly (Eq.sym (List.length-++ Δ₁)) 
        (map-indices (λ i → i ↑ˡ List.length Δ₂) P')) 
        (Eq.subst Poly (Eq.trans (Nat.+-comm (List.length Δ₂) (List.length Δ₁)) (Eq.sym (List.length-++ Δ₁))) 
        (map-indices (λ i → Eq.subst Fin (Nat.+-comm (List.length Δ₁) (List.length Δ₂)) ((List.length Δ₁) ↑ʳ i)) Q'))
    )

  to-inner : ∀ {l} → PolyTypeOp {l} → Σ[ Δ ∈ List (Σ[ A ∈ Set l ] QPER {l} A A) ] Poly (List.length Δ)
  to-inner (Con A Q) = [ (A , Q) ] , Const zero
  to-inner Var = [] , Var
  to-inner 𝟘 = [] , Zero
  to-inner 𝟙 = [] , One
  to-inner (P + Q) = combine (to-inner P) (to-inner Q) Sum
  to-inner (P × Q) = combine (to-inner P) (to-inner Q) Prod

  μ-View (μ P) {X} Y =
    let (Δ , P') = to-inner P in
    let Δ' = λ i → proj₁ (lookup Δ i) in
    exp-eval {ℂ = TypeCCC} (church-rep P' Δ' Y (Const X))

  μ-ViewMap (μ P) f = 
    let (_ , P') = to-inner P in
    church-rep-map-all P' id f id id

  μ-≡ (μ P) A B Inv =
    let (Δ , P') = to-inner P in 
    let Δ' = λ i → qper-to-qper' (proj₂ (lookup Δ i)) in
    Eq.subst₂ QPER
      (church-rep-exp-eval-map-comm {ℂ = QPERCCC} {𝔻 = TypeCCC} Dom P' Eq.refl) 
      (church-rep-exp-eval-map-comm {ℂ = QPERCCC} {𝔻 = TypeCCC} Cod P' Eq.refl) 
      (qper'-to-qper (exp-eval {ℂ = QPERCCC} (church-rep P' Δ' (qper-to-qper' Inv) (Const (qper-to-qper' Inv)))))

  μ-Fold (μ P) C =
    let (_ , P') = to-inner P in
    church-rep-intro P' 
    (λ E → let F = λ C' → church-rep-elim P' C' E in church-rep-elim P' (μ-ViewMap (μ P) F C) E)
  