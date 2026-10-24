---
layout: default
file: "src/DeansProblem/Examples/Rigidity.lagda.md"
title: "DeansProblem.Examples.Rigidity module"
date: "2026-10-14"
author: "the agda-lattices development team"
---

### Worked example: rigidity for two self-embeddings of FL(3) with fixed free triples

This is the [DeansProblem.Examples.Rigidity][] module of the [agda-lattices][] library.

[the paper]: https://arxiv.org/abs/YYMM.NNNNN

[DeansProblem.Inflationary][] proves that a self-embedding `Θ₁ = (a, b, z)`
of `FL(3)` fixing `z`, with `x ≤ a`, `y ≰ a`, `y ≤ b`, `x ≰ b`, is *rigid* as
soon as the canonical tree of `a` or `b` has a meet node with `x` or `y` among
its meetands: nothing but the identity fixes `a`, `b` and `z`
(`rigid-class`{.AgdaFunction}).  This module applies the theorem twice.

+  To `θ₁ : x ↦ x ∨ (y ∧ z), y ↦ y ∨ (x ∧ z), z ↦ z` of
   [DeansProblem.Examples.FixedTriple][], whose rigidity that module proves by
   Whitman's rules directly: the node is `y ∧ z`, the meet joinand of
   `x ∨ (y ∧ z)` (`rigid′`{.AgdaFunction}).
+  To the self-embedding

      θ₂ : x ↦ (x ∨ (y ∧ (x ∨ z))) ∧ (x ∨ (z ∧ (x ∨ y))),
           y ↦ (y ∨ (x ∧ (y ∨ z))) ∧ (y ∨ (z ∧ (x ∨ y))),
           z ↦ z,

   found by one of the searches reported in Section 10 of [the paper][] (the
   only member of the class within complexity 4 whose images have no meet of
   generators as a node), which fixes the same free triple `m₁, m₂, m₃` as `θ₁`
   and so is a second `FixedSublattice`{.AgdaRecord} and coherent chain of
   length two
   (`fixed-triple₂`{.AgdaFunction}, `coherent₂′`{.AgdaFunction}); the node is
   `y ∧ (x ∨ z)`, a joinand of the first meetand of `θ₂ x`
   (`rigid₂`{.AgdaFunction}, `no-extension₂`{.AgdaFunction}).

<!--
```agda
{-# OPTIONS --without-K --exact-split --safe #-}

module DeansProblem.Examples.Rigidity where

-- Imports from the Agda Standard Library ---------------------------------------
open import Data.Empty                             using ( ⊥ )
open import Data.Fin.Base                          using ( Fin )
open import Data.Fin.Patterns                      using ( 0F ; 1F ; 2F )
open import Data.Fin.Properties                    using ( _≟_ )
open import Data.List.Base                         using ( allFin )
open import Data.List.Membership.Propositional.Properties
                                                   using ( ∈-allFin )
open import Data.List.Relation.Unary.Any           using ( here ; there )
open import Data.Sum.Base                          using ( inj₁ )
open import Relation.Binary.PropositionalEquality  using ( refl )
open import Relation.Nullary                       using ( ¬_ )
open import Relation.Nullary.Decidable.Core        using ( from-yes ; from-no )

-- Imports from the Agda Universal Algebra Library ------------------------------
open import DeansProblem.Examples.FixedTriple      using ( x ; y ; z ; θ₁ ; c ; Θ ; m-free )
open import Lattices.Free.Canonical.Basic          using ( ≈ʷ-sym ; ≈ʷ-trans )
open import DeansProblem.Coherent                  using ( FixedSublattice )
open import DeansProblem.Coherent.Finite           using ( Coherent ; fixed→coherent₂ )
open import Lattices.Free.Generation               using ( FreelyGenerates ; module Decide )
open import DeansProblem.Inflationary              using ( Node ; root ; joinand ; meetand ; rigid-class )
open import Lattices.Free.Substitution             using ( Sub ; _[_] ; []-cong )
open import Lattices.Free.Term                     using ( LatTerm ; ℊ ; _∧̇_ ; _∨̇_ )
open import Lattices.Free.Whitman                  using ( _≈ʷ_ ; module Decision )

open Decide (_≟_ {3}) (allFin 3) ∈-allFin (_≟_ {3}) using ( freelyGenerates? )
open Decision (_≟_ {3}) using ( _≤ʷ?_ ; _≈ʷ?_ )
```
-->

#### A term that is no generator

The nodes of `Node`{.AgdaDatatype} carry the proof that they are not
generators; three decisions supply it.

```agda
-- A term equal to no generator, by three decisions.
notGen : (t : LatTerm (Fin 3)) → ¬ (t ≈ʷ x) → ¬ (t ≈ʷ y) → ¬ (t ≈ʷ z) → ∀ v → ¬ (t ≈ʷ ℊ v)
notGen t p q r 0F = p
notGen t p q r 1F = q
notGen t p q r 2F = r
```

#### θ₁, again

```agda
-- The node y ∧ z of the tree of θ₁ x = x ∨ (y ∧ z).
y∧z-node : Node (θ₁ 0F) (y ∧̇ z)
y∧z-node = joinand root (there (here refl))
                   (notGen (y ∧̇ z) (from-no ((y ∧̇ z) ≈ʷ? x)) (from-no ((y ∧̇ z) ≈ʷ? y)) (from-no ((y ∧̇ z) ≈ʷ? z)))

-- Nothing but the identity fixes θ₁ x, θ₁ y and θ₁ z: the class theorem at θ₁.
rigid′ : (Φ : Sub (Fin 3) (Fin 3)) → FreelyGenerates Φ → (∀ i → θ₁ i [ Φ ] ≈ʷ θ₁ i) → ∀ v → Φ v ≈ʷ ℊ v
rigid′ Φ Φ-free fixes =
  rigid-class Φ Φ-free 2F (fixes 2F) (θ₁ 0F) (θ₁ 1F) (fixes 0F) (fixes 1F)
              (from-yes (x ≤ʷ? θ₁ 0F)) (from-no (y ≤ʷ? θ₁ 0F)) (from-yes (y ≤ʷ? θ₁ 1F)) (from-no (x ≤ʷ? θ₁ 1F))
              (inj₁ y∧z-node) (λ ()) (here refl)
```

#### A second member of the class

```agda
-- The self-embedding θ₂.
a₂ b₂ : LatTerm (Fin 3)
a₂ = (x ∨̇ (y ∧̇ (x ∨̇ z))) ∧̇ (x ∨̇ c)
b₂ = (y ∨̇ (x ∧̇ (y ∨̇ z))) ∧̇ (y ∨̇ c)

θ₂ : Sub (Fin 3) (Fin 3)
θ₂ 0F = a₂
θ₂ 1F = b₂
θ₂ 2F = z

-- It freely generates, and misses x.
θ₂-free : FreelyGenerates θ₂
θ₂-free = from-yes (freelyGenerates? θ₂)

x∉θ₂ : ∀ i → ¬ (x ≈ʷ θ₂ i)
x∉θ₂ 0F = from-no (x ≈ʷ? θ₂ 0F)
x∉θ₂ 1F = from-no (x ≈ʷ? θ₂ 1F)
x∉θ₂ 2F = from-no (x ≈ʷ? θ₂ 2F)

-- It fixes the free triple m₁, m₂, m₃ of θ₁.
θ₂-fixes : ∀ i → Θ i [ θ₂ ] ≈ʷ Θ i
θ₂-fixes 0F = from-yes (Θ 0F [ θ₂ ] ≈ʷ? Θ 0F)
θ₂-fixes 1F = from-yes (Θ 1F [ θ₂ ] ≈ʷ? Θ 1F)
θ₂-fixes 2F = from-yes (Θ 2F [ θ₂ ] ≈ʷ? Θ 2F)

-- A second positive answer to the fixed-sublattice question, and a coherent chain of length two.
fixed-triple₂ : FixedSublattice
fixed-triple₂ = record
  { θ         = θ₂
  ; θ-free    = θ₂-free
  ; missed    = 0F
  ; missed∉θ  = x∉θ₂
  ; Θ         = Θ
  ; Θ-free    = m-free
  ; fixes     = θ₂-fixes
  }

coherent₂′ : Coherent 2
coherent₂′ = fixed→coherent₂ fixed-triple₂
```

The tree of `θ₂ x` has the meet node `y ∧ (x ∨ z)`, with `y` a meetand, so
`θ₂` is rigid.

```agda
-- The node y ∧ (x ∨ z): a joinand of the meetand x ∨ (y ∧ (x ∨ z)) of a₂.
y∧[x∨z]-node : Node a₂ (y ∧̇ (x ∨̇ z))
y∧[x∨z]-node =
  joinand (meetand root (here refl)
                   (notGen (x ∨̇ (y ∧̇ (x ∨̇ z))) (from-no ((x ∨̇ (y ∧̇ (x ∨̇ z))) ≈ʷ? x))
                           (from-no ((x ∨̇ (y ∧̇ (x ∨̇ z))) ≈ʷ? y)) (from-no ((x ∨̇ (y ∧̇ (x ∨̇ z))) ≈ʷ? z))))
          (there (here refl))
          (notGen (y ∧̇ (x ∨̇ z)) (from-no ((y ∧̇ (x ∨̇ z)) ≈ʷ? x)) (from-no ((y ∧̇ (x ∨̇ z)) ≈ʷ? y))
                  (from-no ((y ∧̇ (x ∨̇ z)) ≈ʷ? z)))

-- Nothing but the identity fixes θ₂ x, θ₂ y and θ₂ z.
rigid₂ : (Φ : Sub (Fin 3) (Fin 3)) → FreelyGenerates Φ → (∀ i → θ₂ i [ Φ ] ≈ʷ θ₂ i) → ∀ v → Φ v ≈ʷ ℊ v
rigid₂ Φ Φ-free fixes =
  rigid-class Φ Φ-free 2F (fixes 2F) a₂ b₂ (fixes 0F) (fixes 1F)
              (from-yes (x ≤ʷ? a₂)) (from-no (y ≤ʷ? a₂)) (from-yes (y ≤ʷ? b₂)) (from-no (x ≤ʷ? b₂))
              (inj₁ y∧[x∨z]-node) (λ ()) (here refl)

-- So no proper self-embedding fixes θ₂(FL(3)) pointwise: the pair (Θ, θ₂) continues to no third link above.
no-extension₂ : (F : FixedSublattice) → (∀ i → FixedSublattice.Θ F i ≈ʷ θ₂ i) → ⊥
no-extension₂ F Θ≈θ₂ = missed∉θ missed (≈ʷ-sym (rigid₂ θ θ-free fixes-θ₂ missed))
  where
  open FixedSublattice F

  fixes-θ₂ : ∀ i → θ₂ i [ θ ] ≈ʷ θ₂ i
  fixes-θ₂ i = ≈ʷ-trans ([]-cong θ (≈ʷ-sym (Θ≈θ₂ i))) (≈ʷ-trans (fixes i) (Θ≈θ₂ i))
```
