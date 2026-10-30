---
layout: default
file: "src/DeansProblem/Examples/FreeseStep/Complexity.lagda.md"
title: "DeansProblem.Examples.FreeseStep.Complexity module"
date: "2026-10-27"
author: "the agda-lattices development team"
---

### The complexities of Freese's step

This is the [DeansProblem.Examples.FreeseStep.Complexity][] module of this repository.

In Freese's step ([DeansProblem.Examples.FreeseStep][]) the new generators
`a'`, `b'`, `c'` are not subterms of the old ones `a`, `b`, `c`; they are
more complex.  The complexity of an element of a free lattice is the depth of
its canonical form (`complexity`{.AgdaFunction} of
[Lattices.Free.Complexity][]), and here each old generator has complexity 3
and each new one complexity 4 (`old-complexity`{.AgdaFunction},
`new-complexity`{.AgdaFunction}).

The second part of this module concerns where `a'` sits in the canonical tree
of `a`.  The canonical joinands of `a` are `a₁` and three meets, and `ā₁` is
the join of the first three of them; so `ā₁` is not itself a canonical
joinand of `a` (`ā₁-not-canonical-joinand`{.AgdaFunction}).  What holds is
`ā₁ ≤ a' ≤ a` (`ā₁≤a'`{.AgdaFunction}, `a'≤a`{.AgdaFunction}), by Freese's
relations (1) and (2).

**Cost**.  `complexity`{.AgdaFunction} runs the canonicalization algorithm of
[Lattices.Free.Canonical.Algorithm][] on its argument, while the module is
checked.  On the defining terms that is costly: measured 2026-10-27 with
`+RTS -M6G -A128M`, a module deciding `complexity a ≡ 3` alone checks in
13.5 s at a peak of 1.8 GB, and one deciding `complexity a' ≡ 4` alone in
58 s at 3.6 GB, against 2.3 s and 0.85 GB for a module with the same imports
and no decision.  So the six complexities are evaluated on the smaller equal
terms of [DeansProblem.Examples.FreeseStep][], the canonical form `â` of `a`,
the notes' simplification `a″` of `a'`, and their images under the
permutation of the letters, and carried to the defining terms by
`complexity-resp`{.AgdaFunction} along `abc≈abĉ`{.AgdaFunction} and
`abc'≈abc″`{.AgdaFunction}; the six together cost about 2.1 s.  By
`--profile=modules` (2026-10-27) the module's own check takes 2.3 s, and
4.2 s at 1.0 GB with the loading of its imports, so it is not marked
`check-cost: heavy`.  The decision
that `ā₁` is none of the four canonical joinands of `a` runs on the canonical
form `âᶜ`{.AgdaFunction} that [DeansProblem.Examples.FreeseBox][] certifies,
through the table of [Lattices.Free.Whitman.Polynomial][].

<!--
```agda
{-# OPTIONS --without-K --exact-split --safe #-}

module DeansProblem.Examples.FreeseStep.Complexity where

-- Imports from the Agda Standard Library ---------------------------------------
open import Data.Fin.Patterns                      using ( 0F ; 1F ; 2F )
open import Data.Fin.Properties                    using ( _≟_ )
open import Data.List.Base                         using ( map )
open import Data.List.Relation.Unary.Any           using ( Any ; any? )
open import Relation.Binary.PropositionalEquality  using ( _≡_ ; refl ; trans )
open import Relation.Nullary                       using ( ¬_ )
open import Relation.Nullary.Decidable.Core        using ( from-no )

-- Imports from the agda-lattices library ---------------------------------------
open import Lattices.Free.Canonical.Basic          using ( ⌊_⌋ᴶ ; asListJ ; joinandsOf )
open import Lattices.Free.Canonical.Joinands       using ( canonicalJoinands ; joinands-≈ˡ ; ≈ˡ-sym
                                                         ; Any-resp-≈ˡ )
open import Lattices.Free.Complexity               using ( complexity ; complexity-resp )
open import Lattices.Free.Whitman                  using ( _≤ʷ_ ; _≈ʷ_ ; ≤∧ ; ∨̇-upperˡ ; ∧̇-lowerˡ
                                                         ; ≤ʷ-trans )
open import Lattices.Free.Whitman.Polynomial       using ( module Decisionᵖ )
open import DeansProblem.Examples.FreeseStep       using ( a ; a' ; ā₁ ; abc ; abc' ; abĉ
                                                         ; abc″ ; abc≈abĉ ; abc'≈abc″ ; relation-1ᵇ
                                                         ; relation-2ᶜ )
open import DeansProblem.Examples.FreeseBox        using ( âᶜ ; âᶜ-canonical ; âᶜ-sound )
```
-->

#### The complexities

`complexity`{.AgdaFunction} is evaluated on the working triples `abĉ` and
`abc″`, and carried to the defined ones.

```agda
-- The complexities of the working triples, computed.
working-old : ∀ i → complexity _≟_ (abĉ i) ≡ 3
working-old 0F = refl
working-old 1F = refl
working-old 2F = refl

working-new : ∀ i → complexity _≟_ (abc″ i) ≡ 4
working-new 0F = refl
working-new 1F = refl
working-new 2F = refl

-- Each of a, b, c has complexity 3.
old-complexity : ∀ i → complexity _≟_ (abc i) ≡ 3
old-complexity i = trans (complexity-resp _≟_ (abc≈abĉ i)) (working-old i)

-- Each of a', b', c' has complexity 4.
new-complexity : ∀ i → complexity _≟_ (abc' i) ≡ 4
new-complexity i = trans (complexity-resp _≟_ (abc'≈abc″ i)) (working-new i)
```

#### Where a' sits below a

The canonical joinands of `a` are those of its certified canonical form `âᶜ`,
up to order and equality (`joinands-≈ˡ`{.AgdaFunction} of
[Lattices.Free.Canonical.Joinands][]), and `ā₁` is none of those four
(decided).  `a' = a ∧ b̄₂₁ ∧ c̄₂₂` lies below `a`, and above `ā₁`, which lies
below `a` as its first joinand, below `b̄₂₁` by relation (1) and below
`c̄₂₂` by relation (2).

```agda
open Decisionᵖ (_≟_ {9}) using ( _≈ᵖ?_ )

-- ā₁ is not a canonical joinand of a.
ā₁-not-canonical-joinand : ¬ Any (ā₁ ≈ʷ_) (canonicalJoinands _≟_ a)
ā₁-not-canonical-joinand j =
  from-no (any? (ā₁ ≈ᵖ?_) (map ⌊_⌋ᴶ (asListJ (joinandsOf âᶜ))))
          (Any-resp-≈ˡ (≈ˡ-sym (joinands-≈ˡ _≟_ âᶜ âᶜ-canonical âᶜ-sound)) j)

-- a' lies below a.
a'≤a : a' ≤ʷ a
a'≤a = ≤ʷ-trans ∧̇-lowerˡ ∧̇-lowerˡ

-- ā₁ lies below a'.
ā₁≤a' : ā₁ ≤ʷ a'
ā₁≤a' = ≤∧ (≤∧ ∨̇-upperˡ relation-1ᵇ) relation-2ᶜ
```

--------------------------------------

[DeansProblem.Examples.FreeseStep.Complexity]: DeansProblem.Examples.FreeseStep.Complexity.html
[DeansProblem.Examples.FreeseBox]: DeansProblem.Examples.FreeseBox.html
[DeansProblem.Examples.FreeseStep]: DeansProblem.Examples.FreeseStep.html
[Lattices.Free.Canonical.Algorithm]: Lattices.Free.Canonical.Algorithm.html
[Lattices.Free.Canonical.Joinands]: Lattices.Free.Canonical.Joinands.html
[Lattices.Free.Complexity]: Lattices.Free.Complexity.html
[Lattices.Free.Whitman.Polynomial]: Lattices.Free.Whitman.Polynomial.html
