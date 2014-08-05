---
layout: post
title: "Inductive-Recursive Descriptions"
author: Larry Diehl
date: 2014-08-04 19:52:32 -0700
comments: false
published: false
categories: 
---

This post is about adapting descriptions, used to encode dependently typed
datatypes (including type families) originally in
[The Gentle Art of Levitation](http://gallium.inria.fr/~pdagand/papers/levitation.pdf),
to inductive-recursive types.

<!-- more -->

## Goals

There have been many encodings of [indexed] inductive-recursive types,
but as I developed Spire I came to desire an encoding that satisfied all
of the following criteria:

* __Is universe-polymorphic.__ Although it's not hard to add universe
levels, it is crucial for an actual language implementation. Nevertheless, most
papers (justifiably) abstain from cluttering their presentation with
universe levels.
* __Passes Agda's termination & positivity checkers.__
Many alternative encodings of IR types, especially the ones that
are
[directly inspired by algebraic semantics [Ghani & Hancock]](https://personal.cis.strath.ac.uk/neil.ghani/papers/ghani-mscs11.pdf)
suffer from being too general to pass Agda's termination or positivity
checkers.
* __Has description constructors that directly correspond to
constructor declaration arguments.__
Implementing a high-level language that translates to a canonical
kernel language is very difficult if the kernel language is too
different from the high-level language. For this reason I have chosen
to make the description (`Desc`) datatype enforce structure that is as
similar to a higher-level constructor telescope declaration as
possible. From the descriptions literature, this means extending the
[propositional encoding [McBride]](https://personal.cis.strath.ac.uk/conor.mcbride/pub/OAAO/Ornament.pdf)
rather than the (albeit more general)
[computational encoding [Dagand]](http://gallium.inria.fr/~pdagand/stuffs/thesis-2011-phd/thesis.pdf).
From the IR literature, this means staying away from the more semantic
encodings described by
[Ghani & Hancock](https://personal.cis.strath.ac.uk/neil.ghani/papers/ghani-mscs11.pdf),
as well as subtle differences from the original encoding by Dybjer and
Setzer encoding, as reviewed by
[Malatesta et. al.](https://personal.cis.strath.ac.uk/conor.mcbride/pub/SmallIR/SmallIR.pdf).
* __Has an induction principle.__
The induction principle for datatypes encoded in the description literature is
typically given, but I haven't seen the induction principle in my
limitive exposure to the IR literature.

## Non-Indexed Inductive-Recursive Descriptions

I'm going with descriptions for non-indexed IR types, and move to
indexed IR types in the subequent section. Additionally, I will mainly
focus on the definition of descriptions, and encoding types with
descriptions. The harder part is defining the fixpoint for encoded types
and the corresponding induction principle, which I briefly mention but
link to at the end of the post.

A common use of IR is to
model a dependently typed language. Below is the definition of an
example language. The datatype definition (`Lang`) is mutually defined
with an interpretation function whose domain is `Set`. Because the
codomain is `Set` (rather than some small type like `ℕ`), this makes
it a _large_ inductive-recursive definition.

```Haskell
mutual
  data Lang : Set where
    Nat : Lang
    Sg Pi : (A : Lang) (B : ⟦ A ⟧ → Lang) → Lang
  
  ⟦_⟧ : Lang → Set
  ⟦ Nat ⟧ = ℕ
  ⟦ Sg A B ⟧ = Σ ⟦ A ⟧ λ a → ⟦ B a ⟧
  ⟦ Pi A B ⟧ = (a : ⟦ A ⟧) → ⟦ B a ⟧
```

I will encode `Lang` using the following description datatype
(`Desc`). `Desc` is paramterized by a datatype `O`, which is the type
of the codomain of the IR interpretation function. 
It is easiest to think of the constructors of `Desc` as the pieces
used to form the telescope of a constructor type decleration, such as
`Nat` and `Sg` in `Lang`.

```
data Desc ℓ {ℓ′} (O : Set ℓ′) : Set (lsuc ℓ ⊔ ℓ′)  where
  End : (o : O) → Desc ℓ O
  Rec : (B : O → Desc ℓ O) → Desc ℓ O
  Ref : (A : Set ℓ) (B : (o : A → O) → Desc ℓ O) → Desc ℓ O
  Arg : (A : Set ℓ) (B : A → Desc ℓ O) → Desc ℓ O
```

`End` ends a constructor declaration, and specifies what the
mutually-defined IR interpretation function returns for the
constructor. `Rec` encodes a request for a recursive first-order
argument, and the remainder of the telescope may depend on the
interpretation function applied to this recursive argument. 
`Ref` encodes a request for a recursive function argument. To remain
strictly positive, `Ref` asks for the type of the domain of the
function argument, and the remainder of the telescope may depend on a
function from a value of the domain of the function to the
interpretation function applied to the result of the recusive function
that `Ref` encodes. 
`Arg` records an ordinary argument by requesting the type of the
argument, and the remainder of the telescope may depend on a value of
that type.

Below is the encoding of the the `Lang` datatype, and its
interpretation function, as a description.

```Haskell
data LangT : Set where
  NatT SgT PiT : LangT

LangD : Desc lzero (Set lzero)
LangD = Arg LangT λ
  { NatT → End ℕ
  ; SgT → Rec λ A → Ref A λ B → End (Σ A B)
  ; PiT → Rec λ A → Ref A λ B → End ((a : A) → B a)
  }
```

The `Nat` constructor takes no arguments, and its interpretation
function returns the `ℕ` type. The `Sg` constructor first takes a
recursive argument, so the rest of the telescope can depend on its
interpretation. Then, it takes a recursive function argument whose
domain is the interpretation of the first argument. Once again, the
remainder of the telescope may depend on the the _function_ from the
requested domain to the interpretation function result. Finally, the
constructor declaration ends by saying that the interpretation of
`Sg` as a whole is the sigma type (`Σ`) that we expect. The `Pi`
constructor is encoded almost exactly like `Sg`, except the
interpretation function returns a Π type.

Another standard example of a _small_ inductive-recursive definition
is an interpreter of an arithmetic language, as presented by
[Malatesta et. al.](https://personal.cis.strath.ac.uk/conor.mcbride/pub/SmallIR/SmallIR.pdf).
The idea is to express mathematical sums and products, where the
domain of the sum or product specifies the bound on the iteration. See
the paper for an in depth explanation, but below is the high-level
code for the `Arith` type.

```
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
```

Note the that it is a _small_ IR type because the codomain of the
interpretation function is a small type (`ℕ`). Below is the Desc encoding,
which is very similar to what Malatesta et. al. gives.

```
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
```


## Indexed Inductive-Recursive Descriptions


