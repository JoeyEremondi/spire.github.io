open import Data.Empty
open import Data.Unit
open import Data.Bool
open import Data.Product
open import Data.Nat hiding ( _⊔_ )
open import Data.Fin hiding ( _+_ )
open import Function
open import Relation.Binary.PropositionalEquality
open import Level renaming ( zero to lzero ; suc to lsuc)
module DescIR where

----------------------------------------------------------------------

data Desc ℓ {ℓ′} (O : Set ℓ′) : Set (lsuc ℓ ⊔ ℓ′)  where
  End : (o : O) → Desc ℓ O
  Rec : (B : O → Desc ℓ O) → Desc ℓ O
  Ref : (A : Set ℓ) (B : (o : A → O) → Desc ℓ O) → Desc ℓ O
  Arg : (A : Set ℓ) (B : A → Desc ℓ O) → Desc ℓ O

----------------------------------------------------------------------

data LangT : Set where
  NatT SgT PiT : LangT

LangD : Desc lzero (Set lzero)
LangD = Arg LangT λ
  { NatT → End ℕ
  ; SgT → Rec λ A → Ref A λ B → End (Σ A B)
  ; PiT → Rec λ A → Ref A λ B → End ((a : A) → B a)
  }

----------------------------------------------------------------------

sum : (n : ℕ) (f : Fin n → ℕ) → ℕ
sum zero f = zero
sum (suc n) f = f zero + sum n (f ∘ suc)

prod : (n : ℕ)(f : Fin n → ℕ) → ℕ
prod zero f = suc zero
prod (suc n) f = f zero * prod n (f ∘ suc)

data ArithT : Set where
  NatT SgT PiT : ArithT

ArithD : Desc lzero ℕ
ArithD = Arg ArithT λ
  { NatT → Arg ℕ λ n → End n
  ; SgT → Rec λ a → Ref (Fin a) λ f → End (sum a f)
  ; PiT → Rec λ a → Ref (Fin a) λ f → End (prod a f)
  }

----------------------------------------------------------------------

