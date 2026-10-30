---
layout: default
file: "src/DeansProblem/Chain/TwoGenerated.lagda.md"
title: "DeansProblem.Chain.TwoGenerated module"
date: "2026-10-27"
author: "the agda-lattices development team"
---

### Two generators: the chain condition is trivial

This is the [DeansProblem.Chain.TwoGenerated][] module of this repository.

[the paper]: https://arxiv.org/abs/YYMM.NNNNN

Section 4.2 of [the paper][] asks whether every ascending chain of
3-generated sublattices of a free lattice stabilizes, and remarks: "For two
generators the question is trivial, since two elements generate a sublattice
of at most four elements."  This module proves both halves of the sentence.

**Four elements**.  Every lattice term in two variables `x`, `y` is equal in
`FL(2)` to one of `x`, `y`, `x ∧ y`, `x ∨ y` (`one-of-four`{.AgdaFunction}),
by induction on the term, since those four are closed under meets and joins
(`closed`{.AgdaFunction}, sixteen pairs for each operation, decided by
Whitman's procedure).  Substitution carries an equation of `FL(2)` to one of
`FL(X)`, so every element of the sublattice `⟨σ⟩` that two elements generate
is the value at `σ` of one of the four terms (`two-generate-four`{.AgdaFunction}).

**The chain condition for two generators** (`chainCondition₂`{.AgdaFunction}),
for generators with decidable equality.  Membership in a 2-generated
sublattice is then decidable (`member?`{.AgdaFunction}): an element is a member
exactly when it equals one of the four values.  So a proper step
`⟨σ⟩ ⊊ ⟨τ⟩` names a generator of `τ` outside `⟨σ⟩`
(`new-element`{.AgdaFunction}): if both generators of `τ` were members, the
whole of `⟨τ⟩` would lie in `⟨σ⟩`.  In a strictly ascending chain
`L₀ ⊊ L₁ ⊊ ⋯` of 2-generated sublattices, a member of `L₀` and the new
elements of the first four steps are five elements of `L₄`, pairwise unequal,
since the new element of step `k` lies outside `Lₖ`, which contains all the
earlier ones (`apart`{.AgdaFunction}).  Each equals one of the four values that
generate `L₄`, so by the pigeonhole principle two of them equal the same value,
and so each other.  So no strictly ascending chain of 2-generated sublattices
exists, and `n = 3` is the first case that is not trivial.

<!--
```agda
{-# OPTIONS --without-K --exact-split --safe #-}

module DeansProblem.Chain.TwoGenerated where

open import Agda.Primitive  using () renaming ( Set to Type )

-- Imports from the Agda Standard Library ---------------------------------------
open import Data.Empty                             using ( ⊥ ; ⊥-elim )
open import Data.Fin.Base                          using ( Fin ; toℕ )
open import Data.Fin.Patterns                      using ( 0F ; 1F ; 2F ; 3F )
open import Data.Fin.Properties                    using ( _≟_ ; any? ; all? ; pigeonhole ; toℕ<n )
open import Data.Nat.Base                          using ( ℕ ; zero ; suc ; _≤_ ; _<_ ; z≤n ; s≤s )
open import Data.Nat.Properties                    using ( n<1+n )
open import Data.Product                           using ( Σ-syntax ; _×_ ; _,_ ; proj₁ ; proj₂ )
open import Level                                  using ( Level )
open import Relation.Binary.Definitions            using ( DecidableEquality )
open import Relation.Binary.PropositionalEquality  using ( _≡_ ; refl ; sym ; subst )
open import Relation.Nullary                       using ( ¬_ ; Dec ; yes ; no )
open import Relation.Nullary.Decidable.Core        using ( from-yes ; map′ )
open import Relation.Unary                         using ( _⊆_ )

-- Imports from the Agda Universal Algebra Library ------------------------------
open import Lattices.Free.Canonical.Basic          using ( ≈ʷ-refl ; ≈ʷ-sym ; ≈ʷ-trans ; ∧̇-cong ; ∨̇-cong )
open import DeansProblem.Chain.Condition           using ( ⟨_⟩ ; ⟨⟩-resp ; gen∈ ; gens⊆ ; StrictlyAscending
                                                         ; ChainCondition ; strict→ascending ; ascends-≤ )
open import Lattices.Free.Substitution             using ( Sub ; _[_] ; []-cong )
open import Lattices.Free.Term                     using ( LatTerm ; ℊ ; _∧̇_ ; _∨̇_ )
open import Lattices.Free.Whitman                  using ( _≈ʷ_ ; module Decision )

private variable
  χ : Level
```
-->

#### Two elements generate at most four

```agda
-- The four elements that x and y generate, as terms over two generators.
four : Fin 4 → LatTerm (Fin 2)
four 0F = ℊ 0F
four 1F = ℊ 1F
four 2F = ℊ 0F ∧̇ ℊ 1F
four 3F = ℊ 0F ∨̇ ℊ 1F

open Decision (_≟_ {2}) using () renaming ( _≈ʷ?_ to _≈₂?_ )

-- The four are closed under meets and joins, by Whitman's procedure.
closed : (∀ i j → Σ[ k ∈ Fin 4 ] four i ∧̇ four j ≈ʷ four k)
       × (∀ i j → Σ[ k ∈ Fin 4 ] four i ∨̇ four j ≈ʷ four k)
closed = from-yes (all? (λ i → all? (λ j → any? (λ k → four i ∧̇ four j ≈₂? four k))))
       , from-yes (all? (λ i → all? (λ j → any? (λ k → four i ∨̇ four j ≈₂? four k))))

-- Every term over two generators is one of the four.
one-of-four : (t : LatTerm (Fin 2)) → Σ[ k ∈ Fin 4 ] t ≈ʷ four k
one-of-four (ℊ 0F)   = 0F , ≈ʷ-refl
one-of-four (ℊ 1F)   = 1F , ≈ʷ-refl
one-of-four (s ∧̇ t)  = let (i , s≈) = one-of-four s ; (j , t≈) = one-of-four t ; (k , e) = proj₁ closed i j
                       in k , ≈ʷ-trans (∧̇-cong s≈ t≈) e
one-of-four (s ∨̇ t)  = let (i , s≈) = one-of-four s ; (j , t≈) = one-of-four t ; (k , e) = proj₂ closed i j
                       in k , ≈ʷ-trans (∨̇-cong s≈ t≈) e

-- Two elements generate a sublattice of at most four elements.
two-generate-four : {X : Type χ} (σ : Sub (Fin 2) X) {w : LatTerm X} → ⟨ σ ⟩ w
                  → Σ[ k ∈ Fin 4 ] w ≈ʷ four k [ σ ]
two-generate-four σ (t , e) = let (k , t≈) = one-of-four t in k , ≈ʷ-trans (≈ʷ-sym e) ([]-cong σ t≈)
```

#### The chain condition for two generators

```agda
module _ {X : Type χ} (_≟ˣ_ : DecidableEquality X) where
  open Decision _≟ˣ_ using ( _≈ʷ?_ )

  -- Membership in a 2-generated sublattice is decidable.
  member? : (σ : Sub (Fin 2) X) (w : LatTerm X) → Dec (⟨ σ ⟩ w)
  member? σ w = map′ (λ (k , e) → four k , ≈ʷ-sym e) (two-generate-four σ) (any? (λ k → w ≈ʷ? four k [ σ ]))

  private
    -- The search for a generator of τ outside ⟨ σ ⟩, on the two membership decisions.
    search : {σ τ : Sub (Fin 2) X} → ¬ (⟨ τ ⟩ ⊆ ⟨ σ ⟩) → Dec (⟨ σ ⟩ (τ 0F)) → Dec (⟨ σ ⟩ (τ 1F))
           → Σ[ w ∈ LatTerm X ] ⟨ τ ⟩ w × ¬ ⟨ σ ⟩ w
    search {τ = τ} _  (no n)   _        = τ 0F , gen∈ τ 0F , n
    search {τ = τ} _  (yes _)  (no n)   = τ 1F , gen∈ τ 1F , n
    search         ⊉  (yes p)  (yes q)  = ⊥-elim (⊉ (gens⊆ λ { 0F → p ; 1F → q }))

  -- A proper step names a member of the upper sublattice outside the lower.
  new-element : {σ τ : Sub (Fin 2) X} → ¬ (⟨ τ ⟩ ⊆ ⟨ σ ⟩) → Σ[ w ∈ LatTerm X ] ⟨ τ ⟩ w × ¬ ⟨ σ ⟩ w
  new-element {σ} {τ} ⊉ = search ⊉ (member? σ (τ 0F)) (member? σ (τ 1F))
```

Fix a strictly ascending chain of 2-generated sublattices.  Its witnesses
(`witness`{.AgdaFunction}) are a member of the bottom link and, for each step,
the new element of the step: the `m`-th lies in link `m`
(`witness∈`{.AgdaFunction}), and the `(k + 1)`-st lies outside link `k`
(`witness∉`{.AgdaFunction}).  Witnesses at different places are unequal
(`apart`{.AgdaFunction}), and five of them in the fifth link contradict the
four values that generate it.

```agda
  module _ (c : StrictlyAscending 2 X) where
    open StrictlyAscending c

    private
      -- The new element of step k.
      new : ∀ k → Σ[ w ∈ LatTerm X ] ⟨ links (suc k) ⟩ w × ¬ ⟨ links k ⟩ w
      new k = new-element (proj₂ (ascends k))

    -- A member of the bottom link, then the new element of each step.
    witness : ℕ → LatTerm X
    witness zero     = links 0 0F
    witness (suc k)  = proj₁ (new k)

    -- The m-th witness lies in link m.
    witness∈ : ∀ m → ⟨ links m ⟩ (witness m)
    witness∈ zero     = gen∈ (links 0) 0F
    witness∈ (suc k)  = proj₁ (proj₂ (new k))

    -- Witnesses at different places are unequal.
    apart : ∀ {m m′} → m < m′ → ¬ (witness m ≈ʷ witness m′)
    apart {m} {suc k} (s≤s m≤k) e =
      proj₂ (proj₂ (new k)) (⟨⟩-resp (links k) (ascends-≤ (strict→ascending c) m≤k (witness∈ m)) e)

    -- Two generators: no strictly ascending chain of 2-generated sublattices.
    no-chain₂ : ⊥
    no-chain₂ =
      let (i , j , i<j , e) = pigeonhole (n<1+n 4) idx
      in apart i<j (≈ʷ-trans (proj₂ (at i)) (subst (λ k → four k [ links 4 ] ≈ʷ witness (toℕ j))
                                                    (sym e)
                                                    (≈ʷ-sym (proj₂ (at j)))))
      where
      -- The first five witnesses lie in link 4, and so equal values of the four terms.
      at : (i : Fin 5) → Σ[ k ∈ Fin 4 ] witness (toℕ i) ≈ʷ four k [ links 4 ]
      at i = two-generate-four (links 4)
               (ascends-≤ (strict→ascending c) (≤-pred (toℕ<n i)) (witness∈ (toℕ i)))
        where
        ≤-pred : ∀ {a} → a < 5 → a ≤ 4
        ≤-pred (s≤s a≤4) = a≤4

      idx : Fin 5 → Fin 4
      idx i = proj₁ (at i)

  -- The chain condition holds for 2-generated sublattices.
  chainCondition₂ : ChainCondition 2 X
  chainCondition₂ c = no-chain₂ c
```

--------------------------------------

[DeansProblem.Chain.TwoGenerated]: DeansProblem.Chain.TwoGenerated.html
