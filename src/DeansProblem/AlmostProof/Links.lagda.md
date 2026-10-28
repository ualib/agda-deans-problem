---
layout: default
file: "src/DeansProblem/AlmostProof/Links.lagda.md"
title: "DeansProblem.AlmostProof.Links module"
date: "2026-10-27"
author: "the agda-lattices development team"
---

### At most one link in a strongly irredundant box: Theorem 9.2's last clause

This is the [DeansProblem.AlmostProof.Links][] module of the [agda-lattices][] library.

[the paper]: https://arxiv.org/abs/YYMM.NNNNN

Theorem 9.2 of [the paper][] ends: "at most one link of a chain lies in a
strongly irredundant box."  [DeansProblem.AlmostProof][] proves the theorem
for the two triples of a step (`no-step-in-irredundant-box`{.AgdaFunction}).
This module proves the last clause for any two links, by the sentence of the
paper's proof: two links in a strongly irredundant box agree at every index
(`box-agree`{.AgdaFunction}), so they generate the same sublattice, against the
strictness of the chain.

`box-agree`{.AgdaFunction} asks only that one triple lie in the sublattice the
other generates, and freeness enters nowhere.  So the clause is stated first for
any strictly ascending chain of 3-generated sublattices
(`StrictlyAscending`{.AgdaRecord} of [DeansProblem.Chain.Condition][]): for
`j < k`, the links `j` and `k` do not both lie in the box
(`no-two-links-in-box`{.AgdaFunction}), and so two links in one strongly
irredundant box are the same link (`at-most-one-link`{.AgdaFunction}).  Such
chains exist (Theorem 4.5, `ladder`{.AgdaFunction} of
[DeansProblem.Examples.ChainCondition][]), so the statement is not about an
empty type.  The form for a chain of free triples (`Chain`{.AgdaRecord} of
[DeansProblem.Chain][]) is the case `chain→strict`{.AgdaFunction}
(`at-most-one-linkᶜ`{.AgdaFunction}).  This module imports nothing that
refutes the existence of a chain, so the `Chain` form is proved by the
argument above and not by the absurdity of its hypothesis.

<!--
```agda
{-# OPTIONS --without-K --exact-split --safe #-}

module DeansProblem.AlmostProof.Links where

open import Agda.Primitive  using () renaming ( Set to Type )

-- Imports from the Agda Standard Library ---------------------------------------
open import Data.Empty                             using ( ⊥-elim )
open import Data.Fin.Base                          using ( Fin )
open import Data.Nat.Base                          using ( ℕ ; _<_ )
open import Data.Nat.Properties                    using ( <⇒≤ ; <-cmp )
open import Data.Product                           using ( _,_ ; proj₁ ; proj₂ )
open import Level                                  using ( Level )
open import Relation.Binary                        using ( Tri ; tri< ; tri≈ ; tri> )
open import Relation.Binary.PropositionalEquality  using ( _≡_ )
open import Relation.Nullary                       using ( ¬_ )
open import Relation.Unary                         using ( _⊆_ )

-- Imports from the Agda Universal Algebra Library ------------------------------
open import Lattices.Free.Canonical.Basic          using ( ≈ʷ-sym )
open import DeansProblem.AlmostProof               using ( InBox ; StronglyIrredundant ; box-agree )
open import DeansProblem.Chain                     using ( Chain ; module Chain )
open import DeansProblem.Chain.Condition           using ( ⟨_⟩ ; gen∈ ; gens⊆ ; StrictlyAscending
                                                         ; strict→ascending ; ascends-≤ ; chain→strict )
open import Lattices.Free.Substitution             using ( Sub )
open import Lattices.Free.Term                     using ( LatTerm ; ℊ )
open import Lattices.Free.Whitman                  using ( _≈ʷ_ )

private variable
  χ : Level
```
-->

#### Two links in one box

Fix a strictly ascending chain of 3-generated sublattices and a strongly
irredundant box.  For `j < k`, link `j` lies in the sublattice of link `k`, by
terms `q i` (`below`{.AgdaFunction}); if both lay in the box, the two triples
would agree at every index (`agree`{.AgdaFunction}), so link `k` would lie in
the sublattice of link `j`, and with it the link after `j`, against the proper
step at `j`.

```agda
module _ {X : Type χ} (c : StrictlyAscending 3 X) where
  open StrictlyAscending c

  -- For j < k, links j and k do not both lie in a strongly irredundant box.
  no-two-links-in-box : {lo hi : Fin 3 → LatTerm X} → StronglyIrredundant lo hi
                      → ∀ {j k} → j < k → InBox lo hi (links j) → ¬ InBox lo hi (links k)
  no-two-links-in-box {lo} {hi} si {j} {k} j<k boxj boxk =
    proj₂ (ascends j) (λ p → back (ascends-≤ (strict→ascending c) j<k p))
    where
    -- Link j lies in the sublattice of link k.
    below : ⟨ links j ⟩ ⊆ ⟨ links k ⟩
    below = ascends-≤ (strict→ascending c) (<⇒≤ j<k)

    -- The terms expressing link j in link k.
    q : Sub (Fin 3) (Fin 3)
    q i = proj₁ (below (gen∈ (links j) i))

    -- The two links agree at every index.
    agree : ∀ i → links j i ≈ʷ links k i
    agree i = box-agree q (λ i′ → ≈ʷ-sym (proj₂ (below (gen∈ (links j) i′)))) boxj boxk i (si i)

    -- So link k lies in the sublattice of link j.
    back : ⟨ links k ⟩ ⊆ ⟨ links j ⟩
    back = gens⊆ λ i → ℊ i , agree i

  -- Theorem 9.2, last clause: two links in one strongly irredundant box are the same link.
  at-most-one-link : {lo hi : Fin 3 → LatTerm X} → StronglyIrredundant lo hi
                   → ∀ {j k} → InBox lo hi (links j) → InBox lo hi (links k) → j ≡ k
  at-most-one-link si {j} {k} boxj boxk = compare (<-cmp j k)
    where
    -- By the order of j and k.
    compare : Tri (j < k) (j ≡ k) (k < j) → j ≡ k
    compare (tri< j<k _ _)  = ⊥-elim (no-two-links-in-box si j<k boxj boxk)
    compare (tri≈ _ j≡k _)  = j≡k
    compare (tri> _ _ k<j)  = ⊥-elim (no-two-links-in-box si k<j boxk boxj)
```

#### Chains of free triples

A chain of free triples is a strictly ascending chain whose links are its
triples (`chain→strict`{.AgdaFunction}), so the clause holds of it as stated
(`at-most-one-linkᶜ`{.AgdaFunction}).

```agda
-- Theorem 9.2, last clause, for a chain of free triples.
at-most-one-linkᶜ : {X : Type χ} (c : Chain X) {lo hi : Fin 3 → LatTerm X} → StronglyIrredundant lo hi
                  → ∀ {j k} → InBox lo hi (Chain.gens c j) → InBox lo hi (Chain.gens c k) → j ≡ k
at-most-one-linkᶜ c = at-most-one-link (chain→strict c)
```
