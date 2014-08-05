open import Data.Empty
open import Data.Unit
open import Data.Bool
open import Data.Product
open import Data.Nat hiding ( _⊔_ )
open import Data.Fin hiding ( _+_ )
open import Function
open import Level renaming ( zero to lzero ; suc to lsuc )
open import Relation.Binary.PropositionalEquality
module IIR where

----------------------------------------------------------------------

sum : (n : ℕ) (f : Fin n → ℕ) → ℕ
sum zero f = zero
sum (suc n) f = f zero + sum n (f ∘ suc)

prod : (n : ℕ)(f : Fin n → ℕ) → ℕ
prod zero f = suc zero
prod (suc n) f = f zero * prod n (f ∘ suc)

----------------------------------------------------------------------

elimBool : ∀{ℓ} (P : Bool → Set ℓ)
  → P true → P false
  → (b : Bool) → P b
elimBool P pt pf true = pt
elimBool P pt pf false = pf

mutual
  data Lang : Bool → Set where
    Nat : ∀{b} → Lang b
    Sg Pi : ∀{b} (A : Lang b) (B : (elimBool (λ b → Set) {!⟦ b ∣ A ⟧!} {!!} b) → Lang b) → Lang b
  

  ⟦_∣_⟧ : (b : Bool) → Lang b → if b then Set else (Lift ℕ)
  ⟦ true ∣ Nat ⟧ = ℕ
  ⟦ true ∣ Sg A B ⟧ = Σ ⟦ true ∣ A ⟧ λ a → ⟦ true ∣ B a ⟧
  ⟦ true ∣ Pi A B ⟧ = (a : ⟦ true ∣ A ⟧) → ⟦ true ∣ B a ⟧
  ⟦ false ∣ Nat ⟧ = {!!}
  ⟦ false ∣ Sg A B ⟧ = {!!}
  ⟦ false ∣ Pi A B ⟧ = {!!}

----------------------------------------------------------------------

-- mutual
--   data Arith : Set where
--     Nat : ℕ → Arith
--     Sg : (A : Arith) (f : Fin (eval A) → Arith) → Arith
--     Pi : (A : Arith) (f : Fin (eval A) → Arith) → Arith

--   eval : Arith → ℕ
--   eval (Nat n) = n
--   eval (Sg A f) = sum (eval A) λ a → sum (toℕ a) λ b → eval (f (inject b))
--   eval (Pi A f) = prod (eval A) λ a → sum (toℕ a) λ b → eval (f (inject b))

-- sum-lt-5 : Arith
-- sum-lt-5 = Sg (Nat 5) λ a → Nat (toℕ a)

-- test-eval : eval sum-lt-5 ≡ 10
-- test-eval = refl

-- ----------------------------------------------------------------------
