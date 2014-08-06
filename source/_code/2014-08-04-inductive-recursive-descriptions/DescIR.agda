open import Data.Empty
open import Data.Unit
open import Data.Bool
open import Data.Product
open import Data.Nat hiding ( _⊔_ )
open import Data.Fin hiding ( _+_ ; lift )
open import Function
open import Relation.Binary.PropositionalEquality
open import Level renaming ( zero to lzero ; suc to lsuc)
module DescIR where

data W (A : Set) (B : A → Set) : Set where
  sup : (a : A) (t : B a → W A B) → W A B

----------------------------------------------------------------------

data Desc {ℓ} (O : Set ℓ) : Set (lsuc ℓ)  where
  End : (o : O) → Desc O
  Rec : (B : O → Desc O) → Desc O
  Ref : (A : Set ℓ) (B : (o : A → O) → Desc O) → Desc O
  Arg : (A : Set ℓ) (B : A → Desc O) → Desc O

----------------------------------------------------------------------

data LangT {ℓ} : Set ℓ where
  ZeroT OneT TwoT PairT FunT TreeT : LangT

LangD : Desc (Set lzero)
LangD = Arg LangT λ
  { ZeroT → End ⊥
  ; OneT → End ⊤
  ; TwoT → End Bool
  ; PairT → Rec λ A → Ref (Lift A) λ B → End (Σ A (B ∘ lift))
  ; FunT → Rec λ A → Ref (Lift A) λ B → End ((a : A) → B (lift a))
  ; TreeT → Rec λ A → Ref (Lift A) λ B → End (W A (B ∘ lift))
  }

----------------------------------------------------------------------

sum : (n : ℕ) (f : Fin n → ℕ) → ℕ
sum zero f = zero
sum (suc n) f = f zero + sum n (f ∘ suc)

prod : (n : ℕ) (f : Fin n → ℕ) → ℕ
prod zero f = suc zero
prod (suc n) f = f zero * prod n (f ∘ suc)

data ArithT {ℓ} : Set ℓ where
  NumT SumT ProdT : ArithT

ArithD : Desc ℕ
ArithD = Arg ArithT λ
  { NumT → Arg ℕ λ n → End n
  ; SumT → Rec λ a → Ref (Fin a) λ f → End (sum a f)
  ; ProdT → Rec λ a → Ref (Fin a) λ f → End (prod a f)
  }

----------------------------------------------------------------------
