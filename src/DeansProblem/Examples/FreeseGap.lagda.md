---
layout: default
file: "src/DeansProblem/Examples/FreeseGap.lagda.md"
title: "DeansProblem.Examples.FreeseGap module"
date: "2026-10-27"
author: "the agda-lattices development team"
---

### The ends of Freese's box lie outside his link

This is the [DeansProblem.Examples.FreeseGap][] module of this repository.

[the paper]: https://arxiv.org/abs/YYMM.NNNNN

Section 9.3 of [the paper][] says that the gap of Freese's almost-proof does
not move inside `FL(3)`: the ends of the box of a labeled pattern are elements
of the trees of the bottom triple in the ambient lattice, which in general lie
outside every link.  Its example is Freese's own step: the generator `a₁` of
`FL(9)` lies below `a'` (`a₁≤a'`{.AgdaFunction}), it is the lower end of the
interval of `a'` in his generator box ([DeansProblem.Examples.FreeseBox][]),
and it lies outside the link `⟨a', b', c'⟩` (`a₁∉⟨a',b',c'⟩`{.AgdaFunction}).
The last is Corollary 2.4 (`generator-in-image`{.AgdaFunction}): a generator
in the sublattice that a family generates is equal to a member of the family,
and `a₁` is none of `a'`, `b'`, `c'` (`a₁≉`{.AgdaFunction}), which three
decisions of the polynomial Whitman procedure settle, on the notes'
simplification `a″`{.AgdaFunction} of `a'` and its images under the
permutation (`abc″`{.AgdaFunction} of [DeansProblem.Examples.FreeseStep][]).
The other half of the paragraph, the box of a generator inside a link read as
`FL(3)`, is `point-box-in-link`{.AgdaFunction} of
[DeansProblem.Truncation.Pattern][].

<!--
```agda
{-# OPTIONS --without-K --exact-split --safe #-}

module DeansProblem.Examples.FreeseGap where

-- Imports from the Agda Standard Library ---------------------------------------
open import Data.Fin.Base                          using ( Fin )
open import Data.Fin.Patterns                      using ( 0F ; 1F ; 2F )
open import Data.Fin.Properties                    using ( _≟_ )
open import Data.Product                           using ( _,_ ; proj₂ )
open import Relation.Nullary                       using ( ¬_ )
open import Relation.Nullary.Decidable.Core        using ( from-yes ; from-no )

-- Imports from the Agda Universal Algebra Library ------------------------------
open import Lattices.Free.Canonical.Basic          using ( ≈ʷ-sym ; ≈ʷ-trans )
open import DeansProblem.Chain.Condition           using ( ⟨_⟩ )
open import DeansProblem.Examples.FreeseStep       using ( a₁ ; a' ; a″ ; abc' ; abc″ ; a'≈a″ ; abc'≈abc″ )
open import Lattices.Free.Generation               using ( generator-in-image )
open import Lattices.Free.Whitman                  using ( _≤ʷ_ ; _≈ʷ_ ; ≤ʷ-trans )
open import Lattices.Free.Whitman.Polynomial       using ( module Decisionᵖ )
```
-->

```agda
open Decisionᵖ (_≟_ {9}) using ( _≤ᵖ?_ ; _≈ᵖ?_ )

-- The generator a₁ lies below a'.
a₁≤a' : a₁ ≤ʷ a'
a₁≤a' = ≤ʷ-trans (from-yes (a₁ ≤ᵖ? a″)) (proj₂ a'≈a″)

-- The generator a₁ is none of a', b', c'.
a₁≉ : ∀ i → ¬ (a₁ ≈ʷ abc' i)
a₁≉ 0F e = from-no (a₁ ≈ᵖ? abc″ 0F) (≈ʷ-trans e (abc'≈abc″ 0F))
a₁≉ 1F e = from-no (a₁ ≈ᵖ? abc″ 1F) (≈ʷ-trans e (abc'≈abc″ 1F))
a₁≉ 2F e = from-no (a₁ ≈ᵖ? abc″ 2F) (≈ʷ-trans e (abc'≈abc″ 2F))

-- Section 9.3: a₁ lies outside the link ⟨a', b', c'⟩ (Corollary 2.4).
a₁∉⟨a',b',c'⟩ : ¬ ⟨ abc' ⟩ a₁
a₁∉⟨a',b',c'⟩ (t , e) = let (i , e′) = generator-in-image abc' t (≈ʷ-sym e) in a₁≉ i e′
```

--------------------------------------

[DeansProblem.Examples.FreeseGap]: DeansProblem.Examples.FreeseGap.html
[DeansProblem.Examples.FreeseBox]: DeansProblem.Examples.FreeseBox.html
[DeansProblem.Examples.FreeseStep]: DeansProblem.Examples.FreeseStep.html
[DeansProblem.Truncation.Pattern]: DeansProblem.Truncation.Pattern.html
