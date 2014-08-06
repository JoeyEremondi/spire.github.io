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

data W (A : Set) (B : A → Set) : Set where
  sup : (a : A) (t : B a → W A B) → W A B

mutual
  data Lang : Set where
    Zero One Two : Lang
    Pair Fun Tree : (A : Lang) (B : ⟦ A ⟧ → Lang) → Lang
  
  ⟦_⟧ : Lang → Set
  ⟦ Zero ⟧ = ⊥
  ⟦ One ⟧ = ⊤
  ⟦ Two ⟧ = Bool
  ⟦ Pair A B ⟧ = Σ ⟦ A ⟧ λ a → ⟦ B a ⟧
  ⟦ Fun A B ⟧ = (a : ⟦ A ⟧) → ⟦ B a ⟧
  ⟦ Tree A B ⟧ = W ⟦ A ⟧ λ a → ⟦ B a ⟧

----------------------------------------------------------------------

sum : (n : ℕ) (f : Fin n → ℕ) → ℕ
sum zero f = zero
sum (suc n) f = f zero + sum n (f ∘ suc)

prod : (n : ℕ) (f : Fin n → ℕ) → ℕ
prod zero f = suc zero
prod (suc n) f = f zero * prod n (f ∘ suc)

mutual
  data Arith : Set where
    Num : ℕ → Arith
    Sum : (A : Arith) (f : Fin (eval A) → Arith) → Arith
    Prod : (A : Arith) (f : Fin (eval A) → Arith) → Arith

  eval : Arith → ℕ
  eval (Num n) = n
  eval (Sum A f) = sum (eval A) λ a → sum (toℕ a) λ b → eval (f (inject b))
  eval (Prod A f) = prod (eval A) λ a → sum (toℕ a) λ b → eval (f (inject b))

sum-lt-5 : Arith
sum-lt-5 = Sum (Num 5) λ a → Num (toℕ a)

test-eval : eval sum-lt-5 ≡ 10
test-eval = refl

----------------------------------------------------------------------
