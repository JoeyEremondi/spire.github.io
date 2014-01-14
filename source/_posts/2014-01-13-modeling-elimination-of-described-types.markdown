---
layout: post
title: "Modeling elimination of described types"
author: Larry Diehl
date: 2014-01-13 16:50:12 -0800
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
[found in Spire](https://github.com/spire/spire/tree/0e34d3e67b7c1c95ec233b1b5fb3101c535bb088/formalization/agda/Spire/Examples).
Additionally, each code snippet contains a link to the specific file
in the **top right corner**.

## Functions using Pattern Matching

When first implementing the `Desc`ription technology, it will be
convenient to have a sufficiently complex example to typecheck. The
following standard sequence of types and functions suits this goal.

``` haskell Functions using pattern matching https://github.com/spire/spire/blob/0e34d3e67b7c1c95ec233b1b5fb3101c535bb088/formalization/agda/Spire/Examples/Standard.agda#L34
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
families indexed by variables. Eliminating type families indexed by
constructors or functions requires more clever motive synthesis
(via [Eliminating Dependent Pattern Matching](http://strictlypositive.org/goguen.pdf)
by Goguen et. al.) that we would like to ignore for this first pass.

## Functions using Eliminators