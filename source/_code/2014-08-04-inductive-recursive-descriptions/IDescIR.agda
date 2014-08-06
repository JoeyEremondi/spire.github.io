open import Data.Empty
open import Data.Unit
open import Data.Bool
open import Data.Nat
open import Data.Sum
open import Data.Product
open import Function
open import Relation.Binary.PropositionalEquality
open import Level renaming ( zero to lzero ; suc to lsuc)
module IDescIR where

----------------------------------------------------------------------

data Desc {ℓ} (I : Set ℓ) (O : I → Set ℓ) : Set (lsuc ℓ) where
  End : (i : I) (o : O i) → Desc I O
  Rec : (i : I) (B : O i → Desc I O) → Desc I O
  Ref : (A : Set) (i : A → I) (B : (o : (a : A) → O (i a)) → Desc I O) → Desc I O
  Arg : (A : Set) (B : A → Desc I O) → Desc I O

----------------------------------------------------------------------

El : ∀{ℓ I O} (D : Desc I O) (X : I → Set ℓ) (Y : ∀{i} → X i → O i) (i : I) → Set ℓ
El (End j o) X Y i = j ≡ i
El (Rec j B) X Y i = Σ (X j) λ x → El (B (Y x)) X Y i
El (Ref A j B) X Y i = Σ ((a : A) → X (j a)) λ f → El (B (λ a → Y (f a))) X Y i
El (Arg A B) X Y i = Σ A λ a → El (B a) X Y i

----------------------------------------------------------------------

mutual
  data μ {ℓ I O} (D : Desc I O) (i : I) : Set ℓ where
    init : El D (μ D) (foldO D) i → μ D i

  foldO : ∀{ℓ} {I : Set ℓ} {O : I → Set ℓ} {i} (D : Desc I O) → μ D i → O i
  foldO D (init xs) = foldsO D D xs

  foldsO : ∀{ℓ} {I : Set ℓ} {O : I → Set ℓ} {i} (D E : Desc I O) → El D (μ E) (foldO E) i → O i
  foldsO (End j o) E refl = o
  foldsO (Rec j B) E (x , xs) = foldsO (B (foldO E x )) E xs
  foldsO (Ref A j B) E (f , xs) = foldsO (B (λ a → foldO E (f a))) E xs
  foldsO (Arg A B) E (a , xs) = foldsO (B a) E xs

----------------------------------------------------------------------

Hyps : ∀{ℓ I O} (D : Desc I O) (X : I → Set ℓ) (Y : ∀{i} → X i → O i) 
  (P : {i : I} → X i → Set ℓ) (i : I) (xs : El D X Y i) → Set ℓ
Hyps (End j o) X Y P i q = Lift ⊤
Hyps (Rec j D) X Y P i (x , xs) = Σ (P x) (λ _ → Hyps (D (Y x)) X Y P i xs)
Hyps (Ref A j D) X Y P i (f , xs) = Σ ((a : A) → P (f a)) (λ _ → Hyps (D (λ a → Y (f a))) X Y P i xs)
Hyps (Arg A B) X Y P i (a , xs) = Hyps (B a) X Y P i xs

----------------------------------------------------------------------

ind : ∀{ℓ I O} (D : Desc I O)
  (P : ∀{i} → μ D i → Set ℓ)
  (α : ∀{i} (xs : El D (μ D) (foldO D) i) (ihs : Hyps D (μ D) (foldO D) P i xs) → P (init xs))
  {i : I}
  (x : μ D i)
  → P x

hyps : ∀{ℓ I O} (D E : Desc I O)
  (P : ∀{i} → μ E i → Set ℓ)
  (α : ∀{i} (xs : El E (μ E) (foldO E) i) (ihs : Hyps E (μ E) (foldO E) P i xs) → P (init xs))
  {i : I} (xs : El D (μ E) (foldO E) i) → Hyps D (μ E) (foldO E) P i xs

ind D P α (init xs) = α xs (hyps D D P α xs)

hyps (End i o) E P α q = lift tt
hyps (Rec i B) E P α (x , xs) = ind E P α x , hyps (B (foldO E x)) E P α xs
hyps (Ref A i B) E P α (f , xs) = (λ a → ind E P α (f a)) , hyps (B (λ a → foldO E (f a))) E P α xs
hyps (Arg A B) E P α (a , xs) = hyps (B a) E P α xs

----------------------------------------------------------------------
