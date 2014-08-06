---
layout: post
title: "Inductive-Recursive Descriptions"
author: Larry Diehl
date: 2014-08-04 19:52:32 -0700
comments: true
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
The induction principle for datatypes encoded in the IR literature is
typically given, but elimination principles are only sometimes given.
I also wanted a principle in the style of the description literature.

## Non-Indexed Inductive-Recursive Descriptions

I'm going to start with descriptions for non-indexed IR types, and move to
indexed IR types in the subsequent section. Additionally, I will mainly
focus on the definition of descriptions, and encoding types with
descriptions. The harder part is defining the fixpoint for encoded types
and the corresponding induction principle, which I briefly gloss over
at the end of the post. Additionally, all the code presented in this
post is linked to in the conclusion.

A common use of IR is to
model a dependently typed language. Below is the definition of an
example language. The datatype definition (`Lang`) is mutually defined
with an interpretation function whose domain is `Set`. Because the
codomain is `Set` (rather than some small type like `ℕ`), this makes
it a _large_ inductive-recursive definition.

```Haskell
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
```

I will encode `Lang` using the following description datatype
(`Desc`). `Desc` is parameterized by a datatype `O`, which is the type
of the codomain of the IR interpretation function. 
It is easiest to think of the constructors of `Desc` as the pieces
used to form the telescope of a constructor type declaration, such as
`Two` and `Pair` in `Lang`.

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
interpretation function applied to the result of the recursive function
that `Ref` encodes. 
`Arg` records an ordinary argument by requesting the type of the
argument, and the remainder of the telescope may depend on a value of
that type.

Below is the encoding of the the `Lang` datatype, and its
interpretation function, as a description.

```
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
```

The `Two` constructor takes no arguments, and its interpretation
function returns the `Bool` type, and the `Zero` and `One` cases are
similar. 
The `Pair` constructor first takes a
recursive argument, so the rest of the telescope can depend on its
interpretation. Then, it takes a recursive function argument whose
domain is the interpretation of the first argument. Once again, the
remainder of the telescope may depend on the the _function_ from the
requested domain to the interpretation function result. Finally, the
constructor declaration ends by saying that the interpretation of
`Pair` as a whole is the sigma type (`Σ`) that we expect. The `Fun`
and `Tree` constructors are encoded in the same way that `Pair` is.
Also, I sprinkle `Lift` and `lift` in the right places to make the
universe levels work out.

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
```

Note the that it is a _small_ IR type because the codomain of the
interpretation function is a small type (`ℕ`). Below is the Desc encoding,
which is very similar to what Malatesta et. al. give.

```
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
```


## Indexed Inductive-Recursive Descriptions

Both the `Lang` and `Arith` types had interpretations whose codomain
was some constant value (`Set` and `ℕ` respectively). More generally,
an inductive-recursive type may be indexed, and the codomain of the
interpretation function may also be a type family. For example, you can
imagine a type like `Type : ℕ → Set` where the index type is `I = ℕ`,
and an interpretation function `eval : (n : ℕ) → Type n → Fin n` where
the interpretation type is `O = Fin`.

Below is the description type `Desc` modified to be able to encode
indexed inductive-recursive definitions. It now takes an
index type (`(I : Set ℓ)`) as an additional parameter to the
(now dependent) interpretation type (`(O : I → Set ℓ)`).

```
data Desc {ℓ} (I : Set ℓ) (O : I → Set ℓ) : Set (lsuc ℓ) where
  End : (i : I) (o : O i) → Desc I O
  Rec : (i : I) (B : O i → Desc I O) → Desc I O
  Ref : (A : Set) (i : A → I) (B : (o : (a : A) → O (i a)) → Desc I O) → Desc I O
  Arg : (A : Set) (B : A → Desc I O) → Desc I O
```

The new `Desc` is a mixture of the old one (which is a slightly modified
Dybjer-Setzer IR type) , and the indexed description by
[McBride](https://personal.cis.strath.ac.uk/conor.mcbride/pub/OAAO/Ornament.pdf).
Recall that descriptions encode constructor argument telescopes. At
the end of a telescope (`End`), we must now specify what index the type is
at, as well as the (dependent) value that the interpretation function
returns for the constructor being defined. A recursive (`Rec`)
argument requires the index at for the requested recursive type, and
the remainder of the telescope of arguments may use the (dependent)
result of the interpretation function. A recursive function argument
(`Ref`) requires the type of the domain of the recursive argument, an
index value (`I`) assuming the requested argument (`A`), and the rest
of the constructor arguments telescope may depend on a _function_ from
the requested argument to the (dependent) interpretation function
call. Finally, requesting an ordinary argument (`Arg`) is just as
before. 

So far we have only looked at descriptions, but they are relatively
useless and easy to get wrong if you haven't defined the corresponding
fixpoint type (which interprets a description of a type as an actual
type). First let's look at `El`, which interprets a description as a
functor between indexed families of sets.

```
El : ∀{ℓ I O} (D : Desc I O) (X : I → Set ℓ) (Y : ∀{i} → X i → O i) (i : I) → Set ℓ
El (End j o) X Y i = j ≡ i
El (Rec j B) X Y i = Σ (X j) λ x → El (B (Y x)) X Y i
El (Ref A j B) X Y i = Σ ((a : A) → X (j a)) λ f → El (B (λ a → Y (f a))) X Y i
El (Arg A B) X Y i = Σ A λ a → El (B a) X Y i
```

`El` gets an additional argument (`Y`), representing the interpretation
function of the described datatype. To define `El`, we must use `Y` wherever
we need to get the description from the codomain (`B`) of a recursive
first-order (`Rec`) or higher-order (`Ref`) argument.

More interestingly, we can now define the fixpoint datatype `μ`.

```
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
```

I tried to define this a couple of years ago but stuck for some
reason. I tried once again a couple of days ago and arrived at this
definition. In the IR literature `El` is
[sometimes referred to](https://personal.cis.strath.ac.uk/neil.ghani/papers/ghani-mscs11.pdf) as
`⟦_⟧₀`, and a more general version of `foldsO` is referred to as
`⟦_⟧₁`. However, to get `foldO` to pass Agda's termination check we must inline a
mutually defined specialized version of `⟦_⟧₁`, namely `foldsO`. This
is basically the same trick used to get the elimination principle
`ind` to terminate by inlining `hyps`. I remember trying to reuse this
termination technique a couple
of years ago and failing, but anyhow there it is.

Finally, for the sake of completeness below is the adapted definition
of `Hyps` (a collection of inductive hypotheses), `ind` (the primitive
induction principle for described types), and `hyps` (a specialized
mapping function to collect inductive hypotheses).

```
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
```

## Conclusion

Well there it is, indexed inductive-recursive descriptions that
satisfy all of my goals stated at the beginning of the post! The
beginning of the post was background on non-indexed IR encoding.
However, the useful bit of the code to reuse is in the previous
section, which includes the universe-polymorphic, indexed,
inductive-recursive, constructor-esque descriptions, as well as their primitive
introduction and elimination rules.

The code used throughout the post is linked below:

* [Declared Non-Indexed IR](https://github.com/spire/spire.github.io/blob/source/source/_code/2014-08-04-inductive-recursive-descriptions/IR.agda)
* [Encoded Non-Indexed IR](https://github.com/spire/spire.github.io/blob/source/source/_code/2014-08-04-inductive-recursive-descriptions/DescIR.agda)
* [Encoded Indexed IR](https://github.com/spire/spire.github.io/blob/source/source/_code/2014-08-04-inductive-recursive-descriptions/IDescIR.agda)

If you want some homework, try inventing your own indexed
inductive-recursive type, and encode it both in Agda and as a
description. You can also borrow a type to encode from
[Dybjer & Setzer's paper on the topic](http://www.cse.chalmers.se/~peterd/papers/Indexed_IR.pdf).






