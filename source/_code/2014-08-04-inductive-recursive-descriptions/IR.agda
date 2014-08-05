open import Data.Empty
open import Data.Unit
open import Data.Bool
open import Data.Product
open import Data.Nat hiding ( _⊔_ )
open import Data.Fin hiding ( _+_ )
open import Function
open import Relation.Binary.PropositionalEquality
module IR where

----------------------------------------------------------------------

mutual
  data Lang : Set where
    Nat : Lang
    Sg Pi : (A : Lang) (B : ⟦ A ⟧ → Lang) → Lang
  
  ⟦_⟧ : Lang → Set
  ⟦ Nat ⟧ = ℕ
  ⟦ Sg A B ⟧ = Σ ⟦ A ⟧ λ a → ⟦ B a ⟧
  ⟦ Pi A B ⟧ = (a : ⟦ A ⟧) → ⟦ B a ⟧

----------------------------------------------------------------------

sum : (n : ℕ) (f : Fin n → ℕ) → ℕ
sum zero f = zero
sum (suc n) f = f zero + sum n (f ∘ suc)

prod : (n : ℕ)(f : Fin n → ℕ) → ℕ
prod zero f = suc zero
prod (suc n) f = f zero * prod n (f ∘ suc)

mutual
  data Arith : Set where
    Nat : ℕ → Arith
    Sg : (A : Arith) (f : Fin (eval A) → Arith) → Arith
    Pi : (A : Arith) (f : Fin (eval A) → Arith) → Arith

  eval : Arith → ℕ
  eval (Nat n) = n
  eval (Sg A f) = sum (eval A) λ a → sum (toℕ a) λ b → eval (f (inject b))
  eval (Pi A f) = prod (eval A) λ a → sum (toℕ a) λ b → eval (f (inject b))

sum-lt-5 : Arith
sum-lt-5 = Sg (Nat 5) λ a → Nat (toℕ a)

test-eval : eval sum-lt-5 ≡ 10
test-eval = refl

----------------------------------------------------------------------
