---
layout: post
title: "Modeling Elimination of Described Types"
author: Larry Diehl
date: 2014-01-14 09:50:12 -0800
comments: true
categories: 
---

Before jumping straight into implementing datatypes via descriptions,
it is convient to be able model some them in Agda (as done in
[The Gentle Art of Levitation](http://gallium.inria.fr/~pdagand/papers/levitation.pdf)
by Chapman et. al.
and subsequent papers). Everything in the surface language, such as
datatype declarations and pattern matching, is elaborated to terms of
the core type theory. It is desirable to have the ingredients of the
core type theory be as similar to their higher level counterparts as
possible, otherwise work on the canonical terms (such as embedding
back upwards, generic programming on core terms, and compilation of
core terms) becomes complex.

<!-- more -->

My desired features for a bare bones version 1 of Spire include:

* implicit arguments
* elaboration of datatype declarations to descriptions
* elaboration of pattern matching syntax to eliminators
* later superceded by elaboration to the "by" gadget from
[The view from the left](http://strictlypositive.org/view.ps.gz)  by McBride
* sugar for performing generic programming over descriptions
* formal metatheory for the canonical type theory
* universe levels

Rather than implementing this all at once, certain features are
gradually being added. However, it is still a good idea to have future
features in mind when implementing something, and the Agda model helps
with that. The process goes like this:

1. Write down the high-level notation that Agda supports natively (or
in a comment, for features that Agda does not support)
2. Manually perform the elaboration procedures on paper
3. Typecheck and study the resulting core type theory terms

Elaboration of a high level term can involve many steps that
individually are easy to follow, but produce a complex final term, and
it is worth considering alternative core type theory constructs to
produce simpler final terms. These sorts of before-and-after pictures,
and most concepts in this post, can be found in
[Pierre Dagand's thesis](http://gallium.inria.fr/~pdagand/stuffs/thesis-2011-phd/thesis.pdf).

## Note

All of the code from this post can be
[found in Spire](https://github.com/spire/spire/tree/b4f467da96d5de9050f58b41ac10fd9a73ac84df/formalization/agda/Spire/Examples).
Additionally, each code snippet contains a link to the specific file
in the **top right corner**.

## Pattern Matching

When first implementing the `Desc`ription technology, it will be
convenient to have a sufficiently complex example to typecheck. The
following standard sequence of types and functions suits this goal.

``` haskell Functions using Pattern Matching https://github.com/spire/spire/blob/b4f467da96d5de9050f58b41ac10fd9a73ac84df/formalization/agda/Spire/Examples/Standard.agda#L34-L52
data ℕ : Set where
  zero : ℕ
  suc : (n : ℕ) → ℕ

data Vec (A : Set) : ℕ → Set where
  nil : Vec A zero
  cons : (n : ℕ) (a : A) (xs : Vec A n) → Vec A (suc n)

add : ℕ → ℕ → ℕ
add zero n = n
add (suc m) n = suc (add m n)

mult : ℕ → ℕ → ℕ
mult zero n = zero
mult (suc m) n = add n (mult m n)

append : (A : Set) (m : ℕ) (xs : Vec A m) (n : ℕ) (ys : Vec A n) → Vec A (add m n)
append A .zero nil n ys = ys
append A .(suc m) (cons m x xs) n ys = cons (add m n) x (append A m xs n ys) 

concat : (A : Set) (m n : ℕ) (xss : Vec (Vec A m) n) → Vec A (mult n m)
concat A m .zero nil = nil
concat A m .(suc n) (cons n xs xss) = append A m xs (mult n m) (concat A m n xss)
```

This sequence of functions has the nice property that each function
builds upon the previous ones (either in its type, value, or both),
ending in the definition of `concat`. Furthemore, concat has
a moderatley complicated dependent type, but only eliminates type
families applied to a sequence of variables. Eliminating type families
applied to expressions built from constructors requires more clever motive synthesis
(via [Eliminating Dependent Pattern Matching](http://strictlypositive.org/goguen.pdf)
by Goguen et. al.) that we would like to ignore for this first pass.

## Eliminators

Translating these basic functions into eliminators is straightforward.
Because we only eliminate type families applied to a sequence
of variables, the branch functions supplied to the eliminator look like
pattern matching, and the whole definition is rather compact.

``` haskell Functions using Eliminators https://github.com/spire/spire/blob/b4f467da96d5de9050f58b41ac10fd9a73ac84df/formalization/agda/Spire/Examples/Standard.agda#L54-L76
add : ℕ → ℕ → ℕ
add = elimℕ (λ _ → ℕ → ℕ)
  (λ n → n)
  (λ m ih n → suc (ih n))

mult : ℕ → ℕ → ℕ
mult = elimℕ (λ _ → ℕ → ℕ)
  (λ n → zero)
  (λ m ih n → add n (ih n))

append : (A : Set) (m : ℕ) (xs : Vec A m) (n : ℕ) (ys : Vec A n) → Vec A (add m n)
append A = elimVec A (λ m xs → (n : ℕ) (ys : Vec A n) → Vec A (add m n))
  (λ n ys → ys)
  (λ m x xs ih n ys → cons (add m n) x (ih n ys))

concat : (A : Set) (m n : ℕ) (xss : Vec (Vec A m) n) → Vec A (mult n m)
concat A m = elimVec (Vec A m) (λ n xss → Vec A (mult n m))
  nil
  (λ n xs xss ih → append A m xs (mult n m) ih)
```

## Computational Descriptions

Now we will consider `Desc`riptions as they appear in
[Dagand's thesis](http://gallium.inria.fr/~pdagand/stuffs/thesis-2011-phd/thesis.pdf),
which are the core type theory analogue to surface language datatype
definitions. 

``` haskell Computational Description Datatypes https://github.com/spire/spire/blob/b4f467da96d5de9050f58b41ac10fd9a73ac84df/formalization/agda/Spire/Examples/ComputationalDesc.agda#L19-L20
data Desc (I : Set) : Set₁ where
  `⊤ : Desc I
  `X : (i : I) → Desc I
  `Σ `Π : (A : Set) (B : A → Desc I) → Desc I

El : (I : Set) (D : Desc I) (X : I → Set) → Set
El I `⊤ X = ⊤
El I (`X i) X = X i
El I (`Σ A B) X = Σ A (λ a → El I (B a) X)
El I (`Π A B) X = (a : A) → El I (B a) X

data μ (I : Set) (R : I → Desc I) (i : I) : Set where
  con : El I (R i) (μ I R) → μ I R i
```

A well known isomorphism exists between sums and dependent products
whose domain is some finite collection. To encode a type such as `ℕ`,
we can use a `Σ` whose domain is an index into an enumeration of the
contructor names `zero` and `suc`.

``` haskell Computational ℕ Declaration https://github.com/spire/spire/blob/b4f467da96d5de9050f58b41ac10fd9a73ac84df/formalization/agda/Spire/Examples/ComputationalDesc.agda#L57-L67
data ℕT : Set where `zero `suc : ℕT

ℕD : ⊤ → Desc ⊤
ℕD tt = `Σ ℕT λ
  { `zero → `⊤
  ; `suc → `X tt
  }

ℕ : ⊤ → Set
ℕ = μ ⊤ ℕD
```

If you've been reading carefully, you noticed that `μ` did not take a
`Desc`ription as an argument, but a function from the index to a
description. Certain type families can be defined computationally (as
functions from their index), as in
[Inductive Families Need Not Store Their Indices](http://eb.host.cs.st-andrews.ac.uk/writings/types2003.pdf)
by Brady et. al. Eliminating functions defined in this style leads to
particularly nice reduction behaviour, buying you free equations
thanks to definitional equality. `ℕ` was not indexed, but below is an
example of defining `Vec` as a computational description.

``` haskell Computational Vec Declaration https://github.com/spire/spire/blob/b4f467da96d5de9050f58b41ac10fd9a73ac84df/formalization/agda/Spire/Examples/ComputationalDesc.agda#L77-L82
data VecT : Set where `nil `cons : VecT

VecD : (A : Set) (n : ℕ tt) → Desc (ℕ tt)
VecD A zero = `⊤
VecD A (suc n) = `Σ A λ _ → `X n

Vec : (A : Set) (n : ℕ tt) → Set
Vec A n = μ (ℕ tt) (VecD A) n
```

Rather than using a standard eliminator on datatypes defined using
descriptions, the special `ind` elimination rule is used. An
eliminator has separate "branches" for each constructor of a datatype,
along with proofs of the motive being satisfied at recursive positions
in the costructor. Intead, `ind` has a single branch (called `pcon`
below) that bundles up all branches of a typical eliminator, along
with an `All` argument for all recursive motive proofs.

``` haskell ind Elimination Rule Type https://github.com/spire/spire/blob/b4f467da96d5de9050f58b41ac10fd9a73ac84df/formalization/agda/Spire/Examples/ComputationalDesc.agda#L30-L37
ind :
  (I : Set)
  (R : I → Desc I)
  (P : (i : I) → μ I R i → Set)
  (pcon : (i : I) (xs : El I (R i) (μ I R)) → All I (μ I R) (R i) xs P → P i (con xs))
  (i : I)
  (x : μ I R i)
  → P i x
```

Using this eliminator we can define our running example of function
definitions. Here we use `ind` rather than pattern matching. The
anonymous function argument represents sugared "{}" syntax from
Dagand thesis `Example 3.19`. Additionally, the arguments bound in each
constructor pattern match clause are desugared into projections on the
right hand side. We will see what the final desugared terms look like
later in this post.

``` haskell Computational Desc Functions https://github.com/spire/spire/blob/b4f467da96d5de9050f58b41ac10fd9a73ac84df/formalization/agda/Spire/Examples/ComputationalDesc.agda#L92-L124
add : ℕ tt → ℕ tt → ℕ tt
add = ind ⊤ ℕD (λ _ _ → ℕ tt → ℕ tt)
  (λ
    { tt (`zero , tt) tt n → n
    ; tt (`suc , m) ih n → suc (ih n)
    }
  )
  tt

mult : ℕ tt → ℕ tt → ℕ tt
mult = ind ⊤ ℕD (λ _ _ → ℕ tt → ℕ tt)
  (λ
    { tt (`zero , tt) tt n → zero
    ; tt (`suc , m) ih n → add n (ih n)
    }
  )
  tt

append : (A : Set) (m : ℕ tt) (xs : Vec A m) (n : ℕ tt) (ys : Vec A n) → Vec A (add m n) 
append A = ind (ℕ tt) (VecD A) (λ m xs → (n : ℕ tt) (ys : Vec A n) → Vec A (add m n))
  (λ
    { zero tt tt n ys → ys
    ; (suc m) (x , xs) ih n ys → cons A (add m n) x (ih n ys)
    }
  )

concat : (A : Set) (m n : ℕ tt) (xss : Vec (Vec A m) n) → Vec A (mult n m)
concat A m = ind (ℕ tt) (VecD (Vec A m)) (λ n xss → Vec A (mult n m))
  (λ
    { zero tt tt → nil A
    ; (suc n) (xs , xss) ih → append A m xs (mult n m) ih
    }
  )
```

Definitions using computational descriptions (like the ones above) are
nice because you can pattern match on the index (e.g. `ℕ`) and the
description for the type family (e.g. `Vec`) definitionally unfolds.
However, things get a bit clunkier once we wish to support named
constructor arguments. Notice that we defined `ℕ` with an enumeration
for the constructor arguments, but we did not do the same for `Vec`.
`Example 7.46` in Dagand shows how to elaborate `Vec` into a description
that has named constructor arguments. This involves first wrapping the
description in an `elim` constructor identify `Vec` as a type defined
by computation over its index. Then, the `zero` and `suc` branches
return `zero` and `suc` constructor tags respectively. In this case,
the constructors index into singleton enumerations, i.e. `elim` into
`[elim]`, `zero` into `[zero]`, and `suc` into `[suc]`. If we were
defining a type that had multiple constructors with the same index for
a particular index branch (i.e. `zero`) then the enumeration would not
be a singleton, but it would still only be sub-enumeration of the
total enumeration of constructors that we have in mind for the type.

In contrast,
the `ℕ` description tag constructors both belong to a more natural
enumeration, i.e. `zero` and `suc` index into `[zero, suc]`. Hence,
although functions like `append` and `concat` defined above over
computational description `Vec` look nice, once you add these
singleton tags and desugar everything, you get lots of eliminations
over singleton enumerations that are no longer as elegant.
Additionally, type families defined by computation over the index are
only a subclass of all possible type families. The remaining types
(and actually, all type families) can be alternatively defined by
constraining the index with a propositional equality proof. See Dagand
`Example 7.45` for how to define `Vec` this way. This type of definition
keeps the more natural enumeration of constructor tags. I will call
types defined this way "propositional descriptions".

## Propositional Descriptions

Although computational descriptions give you an additional way to
define types, in practice once you add named constructors and perform
elaboration of patterns to eliminators, I don't feel like they buy you
enough for the additional complexity. I am content with supporting
Agda-style propositionally defined datatypes exclusively. Given this
decision, we can make change the grammar of descriptions to more
closely resemble the surface language Agda-style datatype
declarations. I saw something like this alternative `Desc` definition
from the code accompanying a
[blog post](http://perso.ens-lyon.fr/guillaume.allais/?en/main/blog/read/syntax-binding-run-omega) 
by Guillaume Allais.

``` haskell Propositional Description Datatypes https://github.com/spire/spire/blob/b4f467da96d5de9050f58b41ac10fd9a73ac84df/formalization/agda/Spire/Examples/PropositionalDesc.agda#L38-L54
data Desc (I : Set) : Set₁ where
  `End : (i : I) → Desc I
  `Rec : (i : I) (D : Desc I) → Desc I
  `Arg : (A : Set) (B : A → Desc I) → Desc I
  `RecFun : (A : Set) (B : A → I) (D : Desc I) → Desc I

ISet : Set → Set₁
ISet I = I → Set

El : (I : Set) (D : Desc I) (X : ISet I) → ISet I
El I (`End j) X i = j ≡ i
El I (`Rec j D) X i = X j × El I D X i
El I (`Arg A B) X i = Σ A (λ a → El I (B a) X i)
El I (`RecFun A B D) X i = ((a : A) → X (B a)) × El I D X i

data μ (I : Set) (D : Desc I) (i : I) : Set where
  con : El I D (μ I D) i → μ I D i
```

This description grammar enforces descriptions to look like what we
are used to seeing in datatype declarations. For example,
`Rec/Arg/RecFun`, corresponding to the previous `X/Σ/Π` constructors,
take an extra
description argument at the end. Then `End`, formerly `⊤`, ends the
"constructor" with an index value. The interpretation function uses
this index value to ask for a propositionally equality proof, making
sure that the index of the constructor you produce matches the index
of the type you specified. This can be achieved in the previous `Desc`
grammar by ending a descriptions with `Σ (x ≡ y) λ _ → ⊤`, but here
that pattern is internalized. One pleasant consequence can be seen by
looking at the `μ` datatype. It no longer requires a function from the
index to a description, and now merely requires a description. Because
we no longer support computational described datatypes (instead
describing them all propositionally), our descriptions can be
first-order rather than higher-order. The more first-order your
descriptions are, the more
[fully generic programming](https://github.com/larrytheliquid/leveling-up)
you can do over them.

The `ℕ` datatype is declared pretty much the same as before. However,
`Vec` is now given with its constructor names, and the index of a
particular constructor is given at the end of the sequence of
constructor arguments. Compare this to the Agda data declaration at
the top the post and notice the similar structure.

``` haskell Propositional ℕ & Vec Declarations https://github.com/spire/spire/blob/b4f467da96d5de9050f58b41ac10fd9a73ac84df/formalization/agda/Spire/Examples/PropositionalDesc.agda#L97-L122
  data ℕT : Set where `zero `suc : ℕT
  data VecT : Set where `nil `cons : VecT

  ℕD : Desc ⊤
  ℕD = `Arg ℕT λ
    { `zero → `End tt
    ; `suc → `Rec tt (`End tt)
    }

  ℕ : ⊤ → Set
  ℕ = μ ⊤ ℕD

  VecD : (A : Set) → Desc (ℕ tt)
  VecD A = `Arg VecT λ
    { `nil  → `End zero
    ; `cons → `Arg (ℕ tt) λ n → `Arg A λ _ → `Rec n (`End (suc n))
    }

  Vec : (A : Set) (n : ℕ tt) → Set
  Vec A n = μ (ℕ tt) (VecD A) n
```

Our function definitions for `add` and `mult` are pretty much
unchanged, but `append` and `concat` have one significant difference.
Both `Vec` constructors do a dependent pattern match on a
propositional equality proof. However, this is once again a rather
simple dependent match that can just be elaborated to uses of
substitution. Specifically, this elaboration is the `solution` step of
`Lemma 16` in
[Eliminating Dependent Pattern Matching](http://strictlypositive.org/goguen.pdf).

``` haskell Propositional Desc Functions https://github.com/spire/spire/blob/b4f467da96d5de9050f58b41ac10fd9a73ac84df/formalization/agda/Spire/Examples/PropositionalDesc.agda#L132-L164
add : ℕ tt → ℕ tt → ℕ tt
add = ind ⊤ ℕD (λ _ _ → ℕ tt → ℕ tt)
  (λ
    { tt (`zero , q) tt n → n
    ; tt (`suc , m , q) (ih , tt) n → suc (ih n)
    }
  )
  tt

mult : ℕ tt → ℕ tt → ℕ tt
mult = ind ⊤ ℕD (λ _ _ → ℕ tt → ℕ tt)
  (λ
    { tt (`zero , q) tt n → zero
    ; tt (`suc , m , q) (ih , tt) n → add n (ih n)
    }
  )
  tt

append : (A : Set) (m : ℕ tt) (xs : Vec A m) (n : ℕ tt) (ys : Vec A n) → Vec A (add m n) 
append A = ind (ℕ tt) (VecD A) (λ m xs → (n : ℕ tt) (ys : Vec A n) → Vec A (add m n))
  (λ
    { .(con (`zero , refl)) (`nil , refl) ih n ys → ys
    ; .(con (`suc , m , refl)) (`cons , m , x , xs , refl) (ih , tt) n ys → cons A (add m n) x (ih n ys)
    }
  )

concat : (A : Set) (m n : ℕ tt) (xss : Vec (Vec A m) n) → Vec A (mult n m)
concat A m = ind (ℕ tt) (VecD (Vec A m)) (λ n xss → Vec A (mult n m))
  (λ
    { .(con (`zero , refl)) (`nil , refl) tt → nil A
    ; .(con (`suc , n , refl)) (`cons , n , xs , xss , refl) (ih , tt) → append A m xs (mult n m) ih
    }
  )
```

## Desugared Propositional Descriptions

I will now show the desugared final forms of the propositional
description code given so far. It is very important to studies these
terms carefully, as they are the terms of our canonical type theory
and will appear as types everywhere throughout our language (as types
are fully evaluated terms). 

The first bit of sugar we will get rid of has to do with the pattern
matching we have been performing on finite enumerations of tags
(representing constructor names). The enumeration `Enum` will be a
list of strings. `Tag` is an index into `Enum` (like `Fin` into `ℕ`).
`Cases` is a finite product of values in a type family indexed by each
`Tag` (like `Vec` with type family values indexed by `ℕ`). Finally,
`case` eliminates a tag by returning the value in `Cases` at that
position/name. I've renamed these contstructs, and their original
names in Dagand are `EnumU`, `EnumT`, `π`, and `switch` and can be
found in `Definition 2.49` and `Definition 2.52`.

``` haskell Enum & Tag https://github.com/spire/spire/blob/b4f467da96d5de9050f58b41ac10fd9a73ac84df/formalization/agda/Spire/Examples/PropositionalDesc.agda#L18-L34
Label : Set
Label = String

Enum : Set
Enum = List Label

data Tag : Enum → Set where
  here : ∀{l E} → Tag (l ∷ E)
  there : ∀{l E} → Tag E → Tag (l ∷ E)

Cases : (E : Enum) (P : Tag E → Set) → Set
Cases [] P = ⊤
Cases (l ∷ E) P = P here × Cases E λ t → P (there t)

case : (E : Enum) (P : Tag E → Set) (cs : Cases E P) (t : Tag E) → P t
case (l ∷ E) P (c , cs) here = c
case (l ∷ E) P (c , cs) (there t) = case E (λ t → P (there t)) cs t

caseD : (E : Enum) (I : Set) (cs : Cases E (λ _ → Desc I)) (t : Tag E) → Desc I
caseD E I cs t = case E (λ _ → Desc I) cs t
```

In the sugared version of descriptions for datatypes we match on a tag
and return a description for it. In the desugared version, we instead
eliminate a tag with the special `case` elimination rule.

``` haskell Desugared ℕ & Vec Declarations https://github.com/spire/spire/blob/b4f467da96d5de9050f58b41ac10fd9a73ac84df/formalization/agda/Spire/Examples/PropositionalDesc.agda#L170-L206
ℕT : Enum
ℕT = "zero" ∷ "suc" ∷ []

VecT : Enum
VecT = "nil" ∷ "cons" ∷ []

ℕC : Tag ℕT → Desc ⊤
ℕC = caseD ℕT ⊤
  ( `End tt
  , `Rec tt (`End tt)
  , tt
  )

ℕD : Desc ⊤
ℕD = `Arg (Tag ℕT) ℕC

ℕ : ⊤ → Set
ℕ = μ ⊤ ℕD

VecC : (A : Set) → Tag VecT → Desc (ℕ tt)
VecC A = caseD VecT (ℕ tt)
  ( `End zero
  , `Arg (ℕ tt) (λ n → `Arg A λ _ → `Rec n (`End (suc n)))
  , tt
  )

VecD : (A : Set) → Desc (ℕ tt)
VecD A = `Arg (Tag VecT) (VecC A)

Vec : (A : Set) (n : ℕ tt) → Set
Vec A n = μ (ℕ tt) (VecD A) n
```

Now brace yourself for the rather wordy desugared version of our
series of function definitions. The general pattern for these is that
we first use `ind` on the datatype being eliminated (like before),
then we use `case` to give a branch for each constructor. Because
`case` eliminates a tag out of the domain of a dependent pair,
we must use the
[convoy pattern](http://adam.chlipala.net/cpdt/html/MoreDep.html)
to have the codomain properly unfold. As mentioned before, "matching" on
our propositional equality proof is done by applying `subst`. Finally,
each argument to a constructor is referenced by its projection out of
the tuple of arguments you actually get out of the constructor.

``` haskell Desugared Desc Functions https://github.com/spire/spire/blob/b4f467da96d5de9050f58b41ac10fd9a73ac84df/formalization/agda/Spire/Examples/PropositionalDesc.agda#L218-L292
add : ℕ tt → ℕ tt → ℕ tt
add = ind ⊤ ℕD (λ _ _ → ℕ tt → ℕ tt)
  (λ u t,c → case ℕT
    (λ t → (c : El ⊤ (ℕC t) ℕ u)
           (ih : All ⊤ ℕD ℕ (λ u n → ℕ u → ℕ u) u (t , c))
           → ℕ u → ℕ u
    )
    ( (λ q ih n → n)
    , (λ m,q ih,tt n → suc (proj₁ ih,tt n))
    , tt
    )
    (proj₁ t,c)
    (proj₂ t,c)
  )
  tt

mult : ℕ tt → ℕ tt → ℕ tt
mult = ind ⊤ ℕD (λ _ _ → ℕ tt → ℕ tt)
  (λ u t,c → case ℕT
    (λ t → (c : El ⊤ (ℕC t) ℕ u)
           (ih : All ⊤ ℕD ℕ (λ u n → ℕ u → ℕ u) u (t , c))
           → ℕ u → ℕ u
    )
    ( (λ q ih n → zero)
    , (λ m,q ih,tt n → add n (proj₁ ih,tt n))
    , tt
    )
    (proj₁ t,c)
    (proj₂ t,c)
  )
  tt

append : (A : Set) (m : ℕ tt) (xs : Vec A m) (n : ℕ tt) (ys : Vec A n) → Vec A (add m n) 
append A = ind (ℕ tt) (VecD A) (λ m xs → (n : ℕ tt) (ys : Vec A n) → Vec A (add m n))
  (λ m t,c → case VecT
    (λ t → (c : El (ℕ tt) (VecC A t) (Vec A) m)
           (ih : All (ℕ tt) (VecD A) (Vec A) (λ m xs → (n : ℕ tt) (ys : Vec A n) → Vec A (add m n)) m (t , c))
           (n : ℕ tt) (ys : Vec A n) → Vec A (add m n)
    )
    ( (λ q ih n ys → subst (λ m → Vec A (add m n)) q ys)
    , (λ m',x,xs,q ih,tt n ys →
        let m' = proj₁ m',x,xs,q
            x = proj₁ (proj₂ m',x,xs,q)
            q = proj₂ (proj₂ (proj₂ m',x,xs,q))
            ih = proj₁ ih,tt
        in
        subst (λ m → Vec A (add m n)) q (cons A (add m' n) x (ih n ys))
      )
    , tt
    )
    (proj₁ t,c)
    (proj₂ t,c)
  )

concat : (A : Set) (m n : ℕ tt) (xss : Vec (Vec A m) n) → Vec A (mult n m)
concat A m = ind (ℕ tt) (VecD (Vec A m)) (λ n xss → Vec A (mult n m))
  (λ n t,c → case VecT
    (λ t → (c : El (ℕ tt) (VecC (Vec A m) t) (Vec (Vec A m)) n)
           (ih : All (ℕ tt) (VecD (Vec A m)) (Vec (Vec A m)) (λ n xss → Vec A (mult n m)) n (t , c))
           → Vec A (mult n m)
    )
    ( (λ q ih → subst (λ n → Vec A (mult n m)) q (nil A))
    , (λ n',xs,xss,q ih,tt →
        let n' = proj₁ n',xs,xss,q
            xs = proj₁ (proj₂ n',xs,xss,q)
            q = proj₂ (proj₂ (proj₂ n',xs,xss,q))
            ih = proj₁ ih,tt
        in
        subst (λ n → Vec A (mult n m)) q (append A m xs (mult n' m) ih)
      )
    , tt
    )
    (proj₁ t,c)
    (proj₂ t,c)
  )
```

Alternatively, rather than defining these functions with `ind`,
`case`, and `subst` directly, we could reuse our former definitions by
eliminators and intead define the eliminators in much the same way.

``` haskell Desugared Eliminators https://github.com/spire/spire/blob/b4f467da96d5de9050f58b41ac10fd9a73ac84df/formalization/agda/Spire/Examples/PropositionalDesc.agda#L298-L358
elimℕ : (P : (ℕ tt) → Set)
  (pzero : P zero)
  (psuc : (m : ℕ tt) → P m → P (suc m))
  (n : ℕ tt)
  → P n
elimℕ P pzero psuc = ind ⊤ ℕD (λ u n → P n)
  (λ u t,c → case ℕT
    (λ t → (c : El ⊤ (ℕC t) ℕ u)
           (ih : All ⊤ ℕD ℕ (λ u n → P n) u (t , c))
           → P (con (t , c))
    )
    ( (λ q ih →
        elimEq ⊤ tt (λ u q → P (con (here , q)))
          pzero
          u q
      )
    , (λ n,q ih,tt →
        elimEq ⊤ tt (λ u q → P (con (there here , proj₁ n,q , q)))
          (psuc (proj₁ n,q) (proj₁ ih,tt))
          u (proj₂ n,q)
      )
    , tt
    )
    (proj₁ t,c)
    (proj₂ t,c)
  )
  tt

elimVec : (A : Set) (P : (n : ℕ tt) → Vec A n → Set)
  (pnil : P zero (nil A))
  (pcons : (n : ℕ tt) (a : A) (xs : Vec A n) → P n xs → P (suc n) (cons A n a xs))
  (n : ℕ tt)
  (xs : Vec A n)
  → P n xs
elimVec A P pnil pcons = ind (ℕ tt) (VecD A) (λ n xs → P n xs)
  (λ n t,c → case VecT
    (λ t → (c : El (ℕ tt) (VecC A t) (Vec A) n)
           (ih : All (ℕ tt) (VecD A) (Vec A) (λ n xs → P n xs) n (t , c))
           → P n (con (t , c))
    )
    ( (λ q ih →
        elimEq (ℕ tt) zero (λ n q → P n (con (here , q)))
          pnil
          n q
      )
    , (λ n',x,xs,q ih,tt →
        let n' = proj₁ n',x,xs,q
            x = proj₁ (proj₂ n',x,xs,q)
            xs = proj₁ (proj₂ (proj₂ n',x,xs,q))
            q = proj₂ (proj₂ (proj₂ n',x,xs,q))
            ih = proj₁ ih,tt
        in
        elimEq (ℕ tt) (suc n') (λ n q → P n (con (there here , n' , x , xs , q)))
          (pcons n' x xs ih )
          n q
      )
    , tt
    )
    (proj₁ t,c)
    (proj₂ t,c)
  )
```

## An Avalanche of Canonical Terms

We have already seen how large the desugared code gets in the previous
section. Unfortunately, if you evaluate this code to canonical form it
gets much bigger! For example, the 
[canonical term](https://gist.github.com/larrytheliquid/8447251#file-propositionaldescinductionconcat-agda)
 for `concat` defined
using `ind` is *2,195* lines long! This is a huge term, considering
the
[surface language source](https://github.com/spire/spire/blob/b4f467da96d5de9050f58b41ac10fd9a73ac84df/formalization/agda/Spire/Examples/Standard.agda#L36-L50)
 for defining the types and values `add`, `mult`, `append`, and
 `concat` is *14* lines long (the line count above only accounts for
 the value of concat by itself).


Some negative consequences of large canonical terms include:

* Computational overhead type checking expressions against these
canonical types.
* Computational overhead embedding/pretty-printing these canonical
terms.
* Memory overhead in type checking and embedding/pretty-printing.
* Readability of canonical terms for developers while debugging.

Some of this explosion in size comes from using eliminators instead of
dependent pattern matching, where the motive must be supplied
explicitly. Some more comes from the fact that a `μ` representing a
type is applied to its description, which may be large, so anywhere
the type appears the whole description is duplicated.

I haven't thought that much about solutions to this large term problem
yet, but I can imagine a few. I don't want to perform implicit
argument search and unification in the canonical type theory because
it complicates it too much. However, the current canonical grammar is
already broken up into values and spines. This allows for some
bidirectional argument synthesis for values, but not for elimination
rules. Breaking up the grammar further would allow for synthesis of
arguments to elimination rules too, and the canonical type checker
would remain relatively simple. Here is a file that adds some implicit
arguments to the definitions presented thus far that I believe could
be synthesized. I didn't try that hard, so there is more room for
making things more implicit, but that at least takes the
[line count](https://gist.github.com/larrytheliquid/8447251#file-inferredpropositionaldescinductionconcat-agda)
down to *1,411*.

An interesting thing to notice is that the way elimination proceeds
when writing definitions with `ind`, `case`, and `subst` is rather
uniform. All definitions of datatypes can already be characterized as
codes of a universe called `tagDesc` in Dagand `Definition 4.23`.
Dagand programs over this universe to do generic programming. One form
of that would be a specialized `indcase` definition to use `ind`, then
`case`, then maybe `subst` too. Ideally, I would like a generic
`elim` function that computes the exact type signature expected from
standard eliminators from each description. This basically involves
additionally doing some currying/uncurrying to pack/unpack values out of the tuple
produced by the interpretation function for descriptions. As we have
seen, programming definitions using the interface exposed by
eliminators leads to
[pretty short code](https://github.com/spire/spire/blob/b4f467da96d5de9050f58b41ac10fd9a73ac84df/formalization/agda/Spire/Examples/Standard.agda#L56-L74).
The motive is still there and descriptions are still duplicated in
every occurrence of `μ`, but we need to win this war by winning many
battles. However, even if you programmed this generic `elim` function
within the language, the canonical term it produces would be just as
big. It may be necessary to add `elim` as a canonical term primitive
instead, and we may not even need the more general `ind` or `case` if
our language never produces code in the more general form where `ind`
or `case` would be necessary.

Another technique might be to avoid expanding definitions where
possible. For example, if you have a unique hash represent the
description for a type, then testing the equality of terms using the
same hash value would work. However, I would need to be careful to
evaluate that hash to a concrete term during type checking,
a form of lazy evaluation. Memoization of previously type-checked
terms, and equality comparisons, would help a lot too because there
are a lot of duplicated terms.

## Sums

Using a tag that indexes into an enumeration as the domain of a
dependent pair type is isomorphic to using a `Sum` type. This
alternative approach is taken by Bob Atkey in
[Foveran](https://github.com/bobatkey/foveran). Well, the isomorphism
is almost there. A tag for an enumeration lets you have named sums,
used because we care about the name of our constructors. There are a
variety of ways to accomplish this with sums, like making a new
sum-like type, or always making the first type of a sum be a 
labelled type
(see
[The view from the left](http://strictlypositive.org/view.ps.gz)
) and ending the chain of sums in `⊥` on the right. This would still
allow you to do generic programming, by having a list of tuples of
strings plus descriptions act as the universe of codes
(just like `tagDesc`), which gets interpreted as a description,
which gets interpreted as a sequence of sums of the form that I just
described. There are a number of pros and cons between the tag and sum
approach that I should study more closely, but I think a lot of the
duplication issues would come up in either case. 

## Later

That wraps up this week's blog post. I think a weekly schedule is good
for this kind of development blog, as it gives me enough time to come
up with material worth blogging about and enough time for interested
readers to keep up.


