---
layout: post
title: "An Unremarkable Type Checker"
author: Larry Diehl
date: 2014-01-05 15:03:57 -0800
comments: true
categories: 
---

Since becoming a PhD student at Portland State,
[I've](https://twitter.com/larrytheliquid) been occasionally
hacking on what is currently a rather
[boring type checker (by the name of Spire)](https://github.com/spire/spire), but  what I hope
to become a dependently typed language for experimenting with generic
programming. Development has been slow and sporadic, so for the new
year I'm going to try out this daily development blog. 

<!-- more -->

## Goals

My friend and colleague [Nathan](http://web.cecs.pdx.edu/~ntc2/) is
also hacking on it nowadays. The goals of the project are as follows:

* To help the implementors learn how a dependent type checker works.
* To end up with a platform for experimenting with dependently typed
  generic programming.
* To elaborate everything in the language to a core type theory.
* To formalize the type checker of the core type theory.

For the most part, this comes down to implementing selective pieces of
[Epigram](https://code.google.com/p/epigram/).
More specifically, we're following a lot of what
[Pierre Dagand](http://gallium.inria.fr/~pdagand/) has wonderfully described
in his
[thesis](http://gallium.inria.fr/~pdagand/stuffs/thesis-2011-phd/thesis.pdf). 

## Project Structure

I experimented with a few different project structures, and my
favorite ended up using a canonical type theory for the core along
with hereditary substitution. I learned about hereditary substitution
from a beautiful paper describing how to formalize termination of
evaluation for the STLC by
[Keller and Alternkirch](http://www.cs.nott.ac.uk/~txa/publ/msfp10.pdf).
The technique originally came out work on the metatheory of LF/Twelf.
[Martens and Crary](http://www.cs.cmu.edu/~cmartens/lfinlf.pdf) have a
nice modern paper on how to use this to formalize LF in LF.

In a canonical type theory your terms are grammatically enforced to be
in β-normal form. This has a number of desirable consequences, for
instance:

* Big-step semantics (evaluation) can go from expressions to canonical
  terms, ensuring that you did not forget to reduce any β-redex. 
* A type-checking function checks expressions against reduced
  types. If the reduced types are canonical terms, you don't need to
  check for and throw errors due to expressions containing redexes.
* Other algorithms, such as unification, also benefit from operating
  on canonical terms, especially if they are in spine form where the
  variable that eliminators are stuck on is easily accessible. For
  instance,
  [Adam Gundry](https://personal.cis.strath.ac.uk/adam.gundry/thesis/)
  implements his dependently typed unification this way.

Because so many algorithms in a dependently typed language take or
return redex-free terms, having a canonical type theory makes things
easier and less error prone. Canonical terms are no
longer closed under substitution, hence _hereditary substitution_
evaluates as it substitutes to remove redexes. 

I originally tried to implement canonical Spire in Agda, extending
Keller and Altenkirch's typed STLC terms to dependent types. In Twelf
the canonical type theory even makes termination of hereditary
substitution immediate. However, Twelf's termination argument does not
easily extend to dependent type theory with
large eliminations (functions that return types). Even if you turn off
the termination checker, getting the rest of the definitions to type
check is difficult because of the multitude of mutual definitions.
[Here is a file](https://github.com/spire/spire/blob/master/formalization/agda/Spire/Operational.agda)
that postulates the hereditary substitution function, but still
defines all the other semantic functions that would be used when
implementing hereditary substitution. Somewhere on my hard drive
exists a stuck attempt at defining substitution where I ran into
trouble with all the mutual definitions.

In any case, making the typed-syntax above pass type checking would
still leave the open problem of termination. Instead, Spire is
implemented in Haskell with untyped syntax and a partial (monadic)
hereditary substitution semantics. I'm working on trying to prove
termination of this untyped semantics in Agda, which is easier due to not
having so many mutual definitions, and many future blog posts will
cover my slow progress on that front.

## Where Were We?

Ah yes, so the project structure of Spire. The idea is to have a
surface syntax of high-level constructs and expressions that
elaborates to the closed core type theory. This idea is the hallmark of
Epigram. Examples of this include Conor McBride's work on
[compiling dependent pattern matching to eliminators](http://strictlypositive.org/goguen.pdf),
and Pierre Dagand's work on compiling
[data declarations to descriptions](http://gallium.inria.fr/~pdagand/stuffs/paper-2012-data-jfla/paper.pdf).
Dagand's
[thesis](http://gallium.inria.fr/~pdagand/stuffs/thesis-2011-phd/thesis.pdf)
describes this process well. A minor difference is that we are
elaborating to canonical terms rather than a core theory that includes
expressions. The metatheorem for soundness of elaboration described
by Dagand corresponds to type preservation: After elaboration of a
well-typed surface term, you get a well-typed core term. In the
eventually formalized Spire canonical type theory, this will be
proven. In the current Haskell version, this is
[dynamically checked](https://github.com/spire/spire/blob/f948548c4b5793fdc042989404f4aad49a5015cc/src/Spire/Pipeline.hs#L29)
rather than proven.

Spire is currently split into 3 languages. The top language called
[Surface](https://github.com/spire/spire/blob/f948548c4b5793fdc042989404f4aad49a5015cc/src/Spire/Surface/Types.hs)
is what the user programs in. Elaboration from surface proceeds to
[Expression](https://github.com/spire/spire/blob/f948548c4b5793fdc042989404f4aad49a5015cc/src/Spire/Expression/Types.hs).
Expressions are like surface terms, but contain a two-part bidirectional
syntax. Other syntactical elaborations (those that need not be type directed) will also be performed here
in the future. Nathan has been working on the implicit arguments front
of the project, and Spire currently supports wildcard arguments.
Elaboration from Syntax to Expression also removes wildcards and
introduces metavariables into the context. In the future Surface will
contain other high-level constructrs like data declarations and
pattern matching syntax. Eloboration proceeds from expressions to
[Canonical](https://github.com/spire/spire/blob/master/src/Spire/Canonical/Types.hs)
terms. This performs type checking, introduces and solves unification
problems, and removes β-redexes. To keep the canonical terms smaller,
we only require them to be checkable rather than
inferrable/synthesizable. Canonical terms can be checked
bidirectionally, as they are already grammatically split into Values
and neutrals/spines. This works so long as every eliminator only
eliminates something inferred and the rest of the arguments are
checkable. A counter-example of this is the `if`-statement helper in
Expression. Therein the types of the two branches need to be inferred
rather than checked, but `if` appears as a specialized `elimBool` in
the canonical theory (once we have full implicit argument support,
`if` can go away in expressions too, but this is a nice example of what
would break bidirectional canonical type checking). Finally,
there are embedding functions to go back up the chain of languages. Another
[metatheorem](https://github.com/spire/spire/blob/f948548c4b5793fdc042989404f4aad49a5015cc/src/Spire/Pipeline.hs#L30)
that appears as a dynamic check in Spire is: if you evaluate a
well-typed term to a canonical, then embed it back up to a surface
term and evaluate it again, you get back the same canonical term. This
becomes more important as the surface and canonical languages diverge
more. Embedding is used to pretty-print canonicals after evaluation,
for example in error messages. Although messing up embedding does not
affect consistency, as a practical matter it would confuse the user if
type errors contained the wrong terms due to embedding bugs! 

### Implicit Arguments

The implicit argument work by Nathan (I'll ask him if he wants to
describe it) was inspired by [Asperti et. al.'s Matita work](http://arxiv.org/abs/1202.4905)
and somewhat by
[Edwin Brady's Idris work](http://eb.host.cs.st-andrews.ac.uk/drafts/impldtp.pdf). It
relies on the higher-order unification algorithm and library by
[Gundry](https://github.com/adamgundry/type-inference), and currently
translates between Spire terms and Gundry terms.

### Substitution & Binding

With something like NbE in
[Lambda Pi](http://www.andres-loeh.de/LambdaPi/)
you get to inherit  binding
structure and substitution from the meta-language. In Spire binding must be implemented
directly, but thanks to the
[Unbound](http://hackage.haskell.org/package/unbound) library a lot of
this can be automated. We also added a
[monadic extension](https://github.com/spire/substM)
that makes it possible to
use Unbound for hereditary substitution, used like
[this](https://github.com/spire/spire/blob/f948548c4b5793fdc042989404f4aad49a5015cc/src/Spire/Canonical/Evaluator.hs#L23)
in Spire.

## Wrapping Up

My near term next steps are going to be adding `Desc`riptions and implementing Dagand's data
declaration elaboration work, as well as working on trying to
formalize termination of Spire's canonical theory. We're leaving
type-in-type in the Haskell code for now, as I'm
[comfortable enough](https://github.com/larrytheliquid/leveling-up)
with universe hierarchies now to add them later (famous last words).
That's it for now folks, see you tomorrow with the start of a nice new
term. Also, Nathan and I have started to idle in `#spire-lang` on
`freenode`, so feel free to idle alongside us.
