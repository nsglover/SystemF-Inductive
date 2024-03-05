module Encoding.Church where

-- Type Universe Levels
open import Level using (Level) renaming (zero to lzero ; suc to lsuc)

-- Sum Types
open import Data.Empty

-- Product Types
open import Data.Unit
open import Data.Product
open import Data.Product.Properties as Prod

-- Natural Numbers
open import Data.Nat using (ℕ ; zero ; suc ; _+_)

-- Finite Types
open import Data.Fin.Base hiding (_+_ ; _≤_ ; fold)

-- List Types
open import Data.List as List using (List ; [] ; [_] ; _∷_)
import Data.List.Properties as List

-- Equality Types
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)

-- Cartesian-Closed Categories
open import Category.CCC using (CCC) renaming (_^_ to C^)
open import Category.Type

-- Polynomials and Exponential Expressions
open import Encoding.Poly
open import Encoding.SystemF

-- N-Ary Functions
open import Util.N-Ary



private
  church-rep' : ∀ {l} {O : Set l} {n : ℕ} → Poly' n → (Fin n → O) → O → Exps O → Exps O → Exps O
  -- Nothing to simplify; just return T ^ (S ^ A)
  church-rep' (Const i) Δ _ S T = Exp T (Exp S (Const (Δ i)))
  -- Nothing to simplify; just return T ^ (S ^ X)
  church-rep' Var _ X S T = Exp T (Exp S (Const X))
  -- T ^ (S ^ 0) = T ^ 1 = T
  church-rep' Zero _ _ _ T = T
  -- T ^ (S ^ 1) = T ^ S
  church-rep' One _ _ S T = Exp T S
  -- T ^ (S  ^ (P[X] + Q[X])) = T ^ (S ^ P[X] × S ^ Q[X]) = (T ^ (S ^ Q[X])) ^ (S ^ P[X])
  church-rep' (Sum P Q) Δ X S T = church-rep' P Δ X S (church-rep' Q Δ X S T)
  -- T ^ (S ^ (A × Q[X])) = T ^ ((S ^ A) ^ Q[X])
  church-rep' (Prod-Const P i) Δ X S = church-rep' P Δ X (Exp S (Const (Δ i)))
  -- T ^ (S ^ (X × Q[X])) = T ^ ((S ^ X) ^ Q[X])
  church-rep' (Prod-Var P) Δ X S = church-rep' P Δ X (Exp S (Const X))

  church-rep-exp-map-comm' :
    {l l' : Level} {O : Set l} {O' : Set l'} {n : ℕ} {Δ : Fin n → O} {X : O} {S T : Exps O} → 
    (f : O → O') → (P : Poly' n) → 
    exp-map f (church-rep' P Δ X S T) ≡ church-rep' P (λ i → f (Δ i)) (f X) (exp-map f S) (exp-map f T)
  church-rep-exp-map-comm' f (Const i) = Eq.refl
  church-rep-exp-map-comm' f Var = Eq.refl
  church-rep-exp-map-comm' f Zero = Eq.refl
  church-rep-exp-map-comm' f One = Eq.refl
  church-rep-exp-map-comm' f (Sum P Q) = 
    Eq.trans (church-rep-exp-map-comm' _ P) (Eq.cong (church-rep' P _ _ _) (church-rep-exp-map-comm' _ Q))
  church-rep-exp-map-comm' f (Prod-Var P) = church-rep-exp-map-comm' _ P
  church-rep-exp-map-comm' f (Prod-Const P i) = church-rep-exp-map-comm' _ P

  eval : ∀ {l} → Exps (Set l) → (Set l)
  eval = exp-eval {ℂ = TypeCCC}

  church-rep-eliminator' : ∀ {l} {n : ℕ} → Poly' n → (Fin n → Set l) → Set l → Exps (Set l) → Σ[ k ∈ ℕ ] (Fin k → Set l)
  church-rep-eliminator' (Const i) Δ X S = 1 , λ _ → Δ i → eval S
  church-rep-eliminator' Var Δ X S = 1 , λ _ → X → eval S
  church-rep-eliminator' Zero Δ X S = 0 , λ ()
  church-rep-eliminator' One Δ X S = 1 , λ _ → eval S
  church-rep-eliminator' (Sum P Q) Δ X S = 
    let (kP , sigP) = church-rep-eliminator' P Δ X S in
    let (kQ , sigQ) = church-rep-eliminator' Q Δ X S in
    kP + kQ , Append sigP sigQ
  church-rep-eliminator' (Prod-Const P i) Δ X S = church-rep-eliminator' P Δ X (Exp S (Const (Δ i)))
  church-rep-eliminator' (Prod-Var P) Δ X S = church-rep-eliminator' P Δ X (Exp S (Const X))

  church-rep-intro' : 
    ∀ {l} {n : ℕ} {Δ : Fin n → Set l} {X : Set l} {S T : Exps (Set l)} → (P : Poly' n) →
    let (k , Sig) = church-rep-eliminator' P Δ X S in
    (((i : Fin k) → Sig i) → eval T) → eval (church-rep' P Δ X S T)
  church-rep-intro' (Const i) elim = λ s → elim (λ _ → s)
  church-rep-intro' Var elim = λ s → elim (λ _ → s)
  church-rep-intro' Zero elim = elim (λ ())
  church-rep-intro' One elim = λ s → elim (λ _ → s)
  church-rep-intro' (Sum P Q) elim = 
    church-rep-intro' P (λ argsP → church-rep-intro' Q (λ argsQ → elim (append argsP argsQ)))
  church-rep-intro' (Prod-Const P i) = church-rep-intro' P
  church-rep-intro' (Prod-Var P) = church-rep-intro' P

  church-rep-elim' :
    ∀ {l} {n : ℕ} {Δ : Fin n → Set l} {X : Set l} {S T : Exps (Set l)} → (P : Poly' n) →
    let (k , Sig) = church-rep-eliminator' P Δ X S in
    eval (church-rep' P Δ X S T) → ((i : Fin k) → Sig i) → eval T
  church-rep-elim' (Const i) C args = C (args zero)
  church-rep-elim' Var C args = C (args zero)
  church-rep-elim' Zero C _ = C
  church-rep-elim' One C args = C (args zero)
  church-rep-elim' (Sum P Q) C args =
    let (argsP , argsQ) = split args in
    let CQ = church-rep-elim' P C argsP in
    church-rep-elim' Q CQ argsQ
  church-rep-elim' (Prod-Const P _) = church-rep-elim' P
  church-rep-elim' (Prod-Var P) = church-rep-elim' P

  church-rep-map-all' : 
    ∀ {l l'} {n : ℕ} {Δ : Fin n → Set l} {Δ' : Fin n → Set l'} {X : Set l} {X' : Set l'} → 
    {S T : Exps (Set l)} {S' T' : Exps (Set l')} → (P : Poly' n) → 
    ({i : Fin n} → Δ i → Δ' i) → (X → X') → (eval S' → eval S) → (eval T → eval T') →
    eval (church-rep' P Δ X S T) → eval (church-rep' P Δ' X' S' T')
  church-rep-map-all' (Const _) fΔ _ fS fT C = λ h → fT (C (λ x → fS (h (fΔ x))))
  church-rep-map-all' Var _ fX fS fT C = λ h → fT (C (λ x → fS (h (fX x))))
  church-rep-map-all' Zero _ _ _ fT = fT
  church-rep-map-all' One _ _ fS fT C = λ x → fT (C (fS x))
  church-rep-map-all' (Sum P Q) fΔ fX fS fT = church-rep-map-all' P fΔ fX fS (church-rep-map-all' Q fΔ fX fS fT)
  church-rep-map-all' (Prod-Const P _) fΔ fX fS = church-rep-map-all' P fΔ fX (λ h x → fS (h (fΔ x)))
  church-rep-map-all' (Prod-Var P) fΔ fX fS = church-rep-map-all' P fΔ fX (λ h x → fS (h (fX x)))



-- TODO: Documentation

church-rep : ∀ {l} {O : Set l} {n : ℕ} → Poly n → (Fin n → O) → O → Exps O → Exps O
church-rep P Δ X T = church-rep' (poly-to-poly' P) Δ X T T

-- Church representation commutes with map

church-rep-exp-exp-map-comm :
  {l l' : Level} {O : Set l} {O' : Set l'} {n : ℕ} {Δ : Fin n → O} {X : O} {T : Exps O} → 
  (f : O → O') → (P : Poly n) → 
  exp-map f (church-rep P Δ X T) ≡ church-rep P (λ i → f (Δ i)) (f X) (exp-map f T)
church-rep-exp-exp-map-comm f P = church-rep-exp-map-comm' f (poly-to-poly' P)

church-rep-exp-eval-map-comm :
  {lo lm lo' lm' : Level} {O : Set lo} {O' : Set lo'} {ℂ : CCC {lm = lm} O} {𝔻 : CCC {lm = lm'} O'} →
  {n : ℕ} {Δ : Fin n → O} {X : O} {T : Exps O} → 
  (f : O → O') → (P : Poly n) → (∀ {A B : O} → f (C^ ℂ A B) ≡ C^ 𝔻 (f A) (f B)) →
  f (exp-eval {ℂ = ℂ} (church-rep P Δ X T)) ≡ exp-eval {ℂ = 𝔻} (church-rep P (λ i → f (Δ i)) (f X) (exp-map f T))
church-rep-exp-eval-map-comm {ℂ = ℂ} {𝔻 = 𝔻} f P h = Eq.trans 
  (exp-eval-map {ℂ = ℂ} {𝔻 = 𝔻} f h (church-rep P _ _ _))
  (Eq.cong exp-eval (church-rep-exp-exp-map-comm f P))

-- The list of things needed to specify how to get from P[X] to T

church-rep-eliminator : ∀ {l} {n : ℕ} → Poly n → (Fin n → Set l) → Set l → Exps (Set l) → Σ[ k ∈ ℕ ] (Fin k → Set l)
church-rep-eliminator P = church-rep-eliminator' (poly-to-poly' P)

-- If, assuming we know how to get from P[X] to T, we are able to get T, then we can introduce a church-rep.

church-rep-intro : 
  ∀ {l} {n : ℕ} {Δ : Fin n → Set l} {X : Set l} {T : Exps (Set l)} → (P : Poly n) →
  let (k , Sig) = church-rep-eliminator P Δ X T in
  (((i : Fin k) → Sig i) → eval T) → eval (church-rep P Δ X T)
church-rep-intro P = church-rep-intro' (poly-to-poly' P)

-- If we know how to get from P[X] to S, and we have a church-rep, we can get a T.

church-rep-elim :
  ∀ {l} {n : ℕ} {Δ : Fin n → Set l} {X : Set l} {T : Exps (Set l)} → (P : Poly n) →
  let (k , Sig) = church-rep-eliminator P Δ X T in
  eval (church-rep P Δ X T) → ((i : Fin k) → Sig i) → eval T
church-rep-elim P = church-rep-elim' (poly-to-poly' P)

-- We can map over all the arguments (the base T must be mapped both ways due to the opposing variance of the last two
-- arguments of church-rep') to church-rep.

church-rep-map-all :  
  ∀ {l l'} {n : ℕ} {Δ : Fin n → Set l} {Δ' : Fin n → Set l'} {X : Set l} {X' : Set l'} → 
  {T : Exps (Set l)} {T' : Exps (Set l')} → 
  (P : Poly n) → ({i : Fin n} → Δ i → Δ' i) → (X → X') → 
  (eval T → eval T') → (eval T' → eval T) →
  eval (church-rep P Δ X T) → eval (church-rep P Δ' X' T')
church-rep-map-all P fΔ fX fT fT' = church-rep-map-all' (poly-to-poly' P) fΔ fX fT' fT
  