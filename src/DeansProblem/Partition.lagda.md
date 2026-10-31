---
layout: default
file: "src/DeansProblem/Partition.lagda.md"
title: "DeansProblem.Partition module"
date: "2026-10-14"
author: "the agda-lattices development team"
---

### The partition of a free lattice at a generator

This is the [DeansProblem.Partition][] module of this repository.

Fix a generator `z` of a free lattice `FL(X)` on finitely many generators, and
let `⋁others` be the join of the other generators.  Every element `w` of `FL(X)`
satisfies `w ≤ ⋁others` or `z ≤ w`, and never both
(`partition`{.AgdaFunction}, `partition-disjoint`{.AgdaFunction}): the free
lattice is the disjoint union of the ideal `(⋁others]` and the filter `[z)`.
This is the kernel of the homomorphism onto the two-element lattice that sends
`z` to `1` and every other generator to `0`, and the proof is an induction on
the term `w`: a generator is `z` or one of the others; a join with both joinands
below `⋁others` is below it, and otherwise a joinand is above `z`; a meet with a
meetand below `⋁others` is below it, and otherwise both meetands are above `z`.
Exclusivity is Whitman's rule 4: a generator below a join of generators is one
of them.  Dually `⋀others ≤ w` or `w ≤ z`, and never both
(`partitionᵈ`{.AgdaFunction}, `partitionᵈ-disjoint`{.AgdaFunction}).

The consequence this module is for: **an injective endomorphism of `FL(X)` that
fixes every generator but `z` fixes `z` too** (`fixes-last`{.AgdaFunction}),
and so is the identity (`fixes-all`{.AgdaFunction}).  For if `θ` fixes the
other generators, the join condition of Corollary 1.13 of [Freese, Ježek, and
Nation (1995)][] says `θ z ≰ ⋁others`, so `z ≤ θ z` by the partition, and the
meet condition says `⋀others ≰ θ z`, so `θ z ≤ z` by its dual.  Read for a free
generating triple of `FL(3)`: if `{ℊ x, ℊ y, r}` freely generates, then `r` is
the third generator; and a self-embedding of `FL(3)` that fixes two generators
is the identity (`fix-two-generators`{.AgdaFunction}).  So the fixed sublattice
of a proper self-embedding of `FL(3)` contains at most one generator, which is
one of the facts about the fixed-sublattice question of
[DeansProblem.Coherent][].

<!--
```agda
{-# OPTIONS --without-K --exact-split --safe #-}

module DeansProblem.Partition where

open import Agda.Primitive  using ( Setω ) renaming ( Set to Type )

-- Imports from the Agda Standard Library ---------------------------------------
open import Data.Empty                             using ( ⊥ ; ⊥-elim )
open import Data.Fin.Base                          using ( Fin )
open import Data.Fin.Patterns                      using ( 0F ; 1F ; 2F )
open import Data.List.Base                         using ( List ; [] ; _∷_ ; map )
open import Data.List.Membership.Propositional     using ( _∈_ ; find )
open import Data.List.Membership.Propositional.Properties
                                                   using ( ∈-map⁺ ; ∈-map⁻ )
open import Data.List.Relation.Unary.Any           using ( here ; there )
open import Data.Product                           using ( _,_ ; proj₁ ; proj₂ )
open import Data.Sum.Base                          using ( _⊎_ ; inj₁ ; inj₂ ; [_,_]′ )
open import Level                                  using ( Level )
open import Relation.Binary.PropositionalEquality  using ( _≡_ ; _≢_ ; refl ; sym ; subst )
open import Relation.Nullary                       using ( ¬_ )

-- Imports from the Agda Universal Algebra Library ------------------------------
open import Lattices.Free.Canonical.Basic          using ( ≈ʷ-refl ; ≈ʷ-sym ; ⋁⁺ ; ⋀⁺ ; ⋁⁺-upper ; ⋁⁺-least ; ⋀⁺-lower
                                                         ; ⋀⁺-greatest ; gen-⋁⁺-prime ; ⋀⁺-gen-below )
open import Lattices.Free.Generation               using ( FreelyGenerates )
open import Lattices.Free.Substitution             using ( Sub )
open import Lattices.Free.Term                     using ( LatTerm ; ℊ ; _∧̇_ ; _∨̇_ )
open import Lattices.Free.Whitman                  using ( _≤ʷ_ ; _≈ʷ_ ; ∨≤ ; ℊ≤ℊ ; ℊ≤ℊ-inv ; ≤∧ ; ≤∨ˡ
                                                         ; ≤∨ʳ ; ∧ˡ≤ ; ∧ʳ≤ ; ≤ʷ-trans )

private variable
  χ : Level
```
-->

#### The partition

The module `Partition`{.AgdaModule} takes the generator `z`, a nonempty list
`g ∷ gs` of generators, a proof that every generator is `z` or in the list, and
a proof that `z` is not.  Nothing requires decidable equality: the first proof
is the case split the induction needs at a generator, and the second gives
exclusivity.

```agda
module Partition {X : Type χ} (z : X) (g : X) (gs : List X)
                 (cover : ∀ v → v ≡ z ⊎ v ∈ g ∷ gs) (z∉ : ¬ (z ∈ g ∷ gs)) where

  -- The join and the meet of the generators other than z.
  ⋁others : LatTerm X
  ⋁others = ⋁⁺ (ℊ g) (map ℊ gs)

  ⋀others : LatTerm X
  ⋀others = ⋀⁺ (ℊ g) (map ℊ gs)

  -- Every element lies below the join of the others or above z.
  partition : (w : LatTerm X) → w ≤ʷ ⋁others ⊎ ℊ z ≤ʷ w
  partition (ℊ v)    = [ (λ v≡z → inj₂ (ℊ≤ℊ (sym v≡z))) , (λ v∈ → inj₁ (⋁⁺-upper (∈-map⁺ ℊ v∈))) ]′
                         (cover v)
  partition (s ∨̇ t)  = join (partition s) (partition t)
    where
    -- A join: both joinands below, or one above z.
    join : s ≤ʷ ⋁others ⊎ ℊ z ≤ʷ s → t ≤ʷ ⋁others ⊎ ℊ z ≤ʷ t → s ∨̇ t ≤ʷ ⋁others ⊎ ℊ z ≤ʷ s ∨̇ t
    join (inj₁ p)  (inj₁ q)  = inj₁ (∨≤ p q)
    join (inj₁ _)  (inj₂ q)  = inj₂ (≤∨ʳ q)
    join (inj₂ p)  _         = inj₂ (≤∨ˡ p)
  partition (s ∧̇ t)  = meet (partition s) (partition t)
    where
    -- A meet: one meetand below, or both above z.
    meet : s ≤ʷ ⋁others ⊎ ℊ z ≤ʷ s → t ≤ʷ ⋁others ⊎ ℊ z ≤ʷ t → s ∧̇ t ≤ʷ ⋁others ⊎ ℊ z ≤ʷ s ∧̇ t
    meet (inj₁ p)  _         = inj₁ (∧ˡ≤ p)
    meet (inj₂ _)  (inj₁ q)  = inj₁ (∧ʳ≤ q)
    meet (inj₂ p)  (inj₂ q)  = inj₂ (≤∧ p q)

  -- z is not below the join of the others.
  z≰⋁others : ¬ (ℊ z ≤ʷ ⋁others)
  z≰⋁others p =
    let (u , u∈ , z≤u) = find (gen-⋁⁺-prime p)
        (v , v∈ , u≡) = ∈-map⁻ ℊ u∈
    in z∉ (subst (_∈ g ∷ gs) (sym (ℊ≤ℊ-inv (subst (ℊ z ≤ʷ_) u≡ z≤u))) v∈)

  -- The two halves are disjoint.
  partition-disjoint : (w : LatTerm X) → w ≤ʷ ⋁others → ℊ z ≤ʷ w → ⊥
  partition-disjoint w p q = z≰⋁others (≤ʷ-trans q p)
```

The dual: every element lies above the meet of the others or below `z`, and not
both.

```agda
  -- Every element lies above the meet of the others or below z.
  partitionᵈ : (w : LatTerm X) → ⋀others ≤ʷ w ⊎ w ≤ʷ ℊ z
  partitionᵈ (ℊ v)    = [ (λ v≡z → inj₂ (ℊ≤ℊ v≡z)) , (λ v∈ → inj₁ (⋀⁺-lower (∈-map⁺ ℊ v∈))) ]′
                          (cover v)
  partitionᵈ (s ∨̇ t)  = join (partitionᵈ s) (partitionᵈ t)
    where
    -- A join: one joinand above, or both below z.
    join : ⋀others ≤ʷ s ⊎ s ≤ʷ ℊ z → ⋀others ≤ʷ t ⊎ t ≤ʷ ℊ z → ⋀others ≤ʷ s ∨̇ t ⊎ s ∨̇ t ≤ʷ ℊ z
    join (inj₁ p)  _         = inj₁ (≤∨ˡ p)
    join (inj₂ _)  (inj₁ q)  = inj₁ (≤∨ʳ q)
    join (inj₂ p)  (inj₂ q)  = inj₂ (∨≤ p q)
  partitionᵈ (s ∧̇ t)  = meet (partitionᵈ s) (partitionᵈ t)
    where
    -- A meet: both meetands above, or one below z.
    meet : ⋀others ≤ʷ s ⊎ s ≤ʷ ℊ z → ⋀others ≤ʷ t ⊎ t ≤ʷ ℊ z → ⋀others ≤ʷ s ∧̇ t ⊎ s ∧̇ t ≤ʷ ℊ z
    meet (inj₁ p)  (inj₁ q)  = inj₁ (≤∧ p q)
    meet (inj₁ _)  (inj₂ q)  = inj₂ (∧ʳ≤ q)
    meet (inj₂ p)  _         = inj₂ (∧ˡ≤ p)

  -- The meet of the others is not below z.
  ⋀others≰z : ¬ (⋀others ≤ʷ ℊ z)
  ⋀others≰z p =
    let (u , u∈ , u≤z) = find (⋀⁺-gen-below p)
        (v , v∈ , u≡) = ∈-map⁻ ℊ u∈
    in z∉ (subst (_∈ g ∷ gs) (ℊ≤ℊ-inv (subst (_≤ʷ ℊ z) u≡ u≤z)) v∈)

  -- The two halves are disjoint.
  partitionᵈ-disjoint : (w : LatTerm X) → ⋀others ≤ʷ w → w ≤ʷ ℊ z → ⊥
  partitionᵈ-disjoint w p q = ⋀others≰z (≤ʷ-trans p q)
```

#### An embedding fixing all generators but one

Let `θ` freely generate (equivalently, by Corollary 1.13, be injective) and fix
every generator in `g ∷ gs`.  The join of those generators lies below the join
of their images (`others≤`{.AgdaFunction}), so if `θ z` were below `⋁others` it
would be below the join of the images of the others, and the join condition
would put `z` among them; so `z ≤ θ z` by the partition.  Dually `θ z ≤ z`
(`fixes-last`{.AgdaFunction}), and `θ` fixes every generator
(`fixes-all`{.AgdaFunction}).

```agda
  module _ (θ : Sub X X) (θ-free : FreelyGenerates θ) (fix : ∀ {v} → v ∈ g ∷ gs → θ v ≈ʷ ℊ v) where
    private
      -- The join of the others lies below the join of their images; dually for meets.
      others≤ : ⋁others ≤ʷ ⋁⁺ (θ g) (map θ gs)
      others≤ = ⋁⁺-least λ u∈ →
        let (v , v∈ , u≡) = ∈-map⁻ ℊ u∈
        in subst (_≤ʷ ⋁⁺ (θ g) (map θ gs)) (sym u≡)
                 (≤ʷ-trans (proj₂ (fix v∈)) (⋁⁺-upper (∈-map⁺ θ v∈)))

      others≥ : ⋀⁺ (θ g) (map θ gs) ≤ʷ ⋀others
      others≥ = ⋀⁺-greatest λ u∈ →
        let (v , v∈ , u≡) = ∈-map⁻ ℊ u∈
        in subst (⋀⁺ (θ g) (map θ gs) ≤ʷ_) (sym u≡)
                 (≤ʷ-trans (⋀⁺-lower (∈-map⁺ θ v∈)) (proj₁ (fix v∈)))

    -- θ fixes z as well.
    fixes-last : θ z ≈ʷ ℊ z
    fixes-last =
      [ (λ p → ⊥-elim (z∉ (proj₂ θ-free {z} {g ∷ gs} (≤ʷ-trans others≥ p)))) , (λ q → q) ]′
        (partitionᵈ (θ z)) ,
      [ (λ p → ⊥-elim (z∉ (proj₁ θ-free {z} {g ∷ gs} (≤ʷ-trans p others≤)))) , (λ q → q) ]′
        (partition (θ z))

    -- So θ fixes every generator.
    fixes-all : ∀ v → θ v ≈ʷ ℊ v
    fixes-all v = [ (λ v≡z → subst (λ u → θ u ≈ʷ ℊ u) (sym v≡z) fixes-last) , fix ]′ (cover v)
```

#### In `FL(3)`

The partition of `FL(3)` at each generator `z` separates `z` from the other two
(`other`{.AgdaFunction}, `other'`{.AgdaFunction}; `cover₃`{.AgdaFunction},
`∉others₃`{.AgdaFunction}).  A self-embedding of `FL(3)` that fixes the two
generators other than `z` is the identity (`fixes-two`{.AgdaFunction}), and so
is one that fixes any two distinct generators
(`fix-two-generators`{.AgdaFunction}).  Read for a family `θ` with
`θ x = ℊ x` and `θ y = ℊ y`, the first says that `{ℊ x, ℊ y, r}` freely
generates only for `r ≈ʷ ℊ z`.

```agda
-- The two generators other than a given one.
other other' : Fin 3 → Fin 3
other 0F   = 1F
other 1F   = 0F
other 2F   = 0F
other' 0F  = 2F
other' 1F  = 2F
other' 2F  = 1F

-- Every generator is z or one of the other two.
cover₃ : ∀ z v → v ≡ z ⊎ v ∈ other z ∷ other' z ∷ []
cover₃ 0F 0F = inj₁ refl
cover₃ 0F 1F = inj₂ (here refl)
cover₃ 0F 2F = inj₂ (there (here refl))
cover₃ 1F 0F = inj₂ (here refl)
cover₃ 1F 1F = inj₁ refl
cover₃ 1F 2F = inj₂ (there (here refl))
cover₃ 2F 0F = inj₂ (here refl)
cover₃ 2F 1F = inj₂ (there (here refl))
cover₃ 2F 2F = inj₁ refl

-- z is not one of the other two.
∉others₃ : ∀ z → ¬ (z ∈ other z ∷ other' z ∷ [])
∉others₃ 0F (here ())
∉others₃ 0F (there (here ()))
∉others₃ 0F (there (there ()))
∉others₃ 1F (here ())
∉others₃ 1F (there (here ()))
∉others₃ 1F (there (there ()))
∉others₃ 2F (here ())
∉others₃ 2F (there (here ()))
∉others₃ 2F (there (there ()))

-- A self-embedding of FL(3) fixing the two generators other than z is the identity.
fixes-two : (θ : Sub (Fin 3) (Fin 3)) → FreelyGenerates θ → (z : Fin 3)
          → θ (other z) ≈ʷ ℊ (other z) → θ (other' z) ≈ʷ ℊ (other' z) → ∀ v → θ v ≈ʷ ℊ v
fixes-two θ θ-free z e e' = fixes-all θ θ-free fix
  where
  open Partition z (other z) (other' z ∷ []) (cover₃ z) (∉others₃ z)

  -- The hypothesis, read for the list of the other two.
  fix : ∀ {v} → v ∈ other z ∷ other' z ∷ [] → θ v ≈ʷ ℊ v
  fix (here refl)          = e
  fix (there (here refl))  = e'
  fix (there (there ()))

-- A self-embedding of FL(3) fixing two distinct generators is the identity.
fix-two-generators : (θ : Sub (Fin 3) (Fin 3)) → FreelyGenerates θ → {x y : Fin 3} → x ≢ y
                   → θ x ≈ʷ ℊ x → θ y ≈ʷ ℊ y → ∀ v → θ v ≈ʷ ℊ v
fix-two-generators θ θ-free {0F} {0F} x≢y _  _  = ⊥-elim (x≢y refl)
fix-two-generators θ θ-free {0F} {1F} _   ex ey = fixes-two θ θ-free 2F ex ey
fix-two-generators θ θ-free {0F} {2F} _   ex ey = fixes-two θ θ-free 1F ex ey
fix-two-generators θ θ-free {1F} {0F} _   ex ey = fixes-two θ θ-free 2F ey ex
fix-two-generators θ θ-free {1F} {1F} x≢y _  _  = ⊥-elim (x≢y refl)
fix-two-generators θ θ-free {1F} {2F} _   ex ey = fixes-two θ θ-free 0F ex ey
fix-two-generators θ θ-free {2F} {0F} _   ex ey = fixes-two θ θ-free 1F ey ex
fix-two-generators θ θ-free {2F} {1F} _   ex ey = fixes-two θ θ-free 0F ey ex
fix-two-generators θ θ-free {2F} {2F} x≢y _  _  = ⊥-elim (x≢y refl)
```

The two last clauses of the lemma, as the paper on Dean's problem states it
(Lemma 6.10), follow.  A proper self-embedding of `FL(3)`, one that misses a
generator, fixes at most one generator (`proper-fixes-one`{.AgdaFunction}):
fixing two, it would be the identity, and miss nothing.  And a triple
`(x, y, r)` of `FL(3)` is free only for `r = z`
(`xyr-free→z`{.AgdaFunction}): the self-embedding `x, y, z ↦ x, y, r`
(`xyr`{.AgdaFunction}) fixes `x` and `y`, so it is the identity.

```agda
-- A proper self-embedding of FL(3) fixes at most one generator.
proper-fixes-one : (θ : Sub (Fin 3) (Fin 3)) → FreelyGenerates θ → (m : Fin 3) → (∀ i → ¬ (ℊ m ≈ʷ θ i))
                 → {u v : Fin 3} → u ≢ v → θ u ≈ʷ ℊ u → θ v ≈ʷ ℊ v → ⊥
proper-fixes-one θ θ-free m missed u≢v eu ev = missed m (≈ʷ-sym (fix-two-generators θ θ-free u≢v eu ev m))

-- The triple (x, y, r) of FL(3), as a substitution.
xyr : LatTerm (Fin 3) → Sub (Fin 3) (Fin 3)
xyr r 0F = ℊ 0F
xyr r 1F = ℊ 1F
xyr r 2F = r

-- A triple (x, y, r) of FL(3) is free only for r = z.
xyr-free→z : (r : LatTerm (Fin 3)) → FreelyGenerates (xyr r) → r ≈ʷ ℊ 2F
xyr-free→z r r-free = fixes-two (xyr r) r-free 2F ≈ʷ-refl ≈ʷ-refl 2F
```

**Lemma 6.10** of the paper on Dean's problem, as one statement.  Its first
part: for `X` finite with at least two elements, given as a generator `z` and
the list `g ∷ gs` of the others, a self-embedding `θ` of `FL(X)` that fixes
every generator but `z` fixes `z` too.  Its other parts are the lemma's
consequences in `FL(3)`: a self-embedding that fixes two distinct generators is
the identity; a proper one, missing a generator `m`, fixes at most one; and a
triple `(x, y, r)` is free only for `r = z`.

```agda
-- Lemma 6.10: in FL(X), X finite with at least two elements, a self-embedding fixing every
-- generator but z fixes z; in FL(3), fixing two is the identity, a proper one fixes at most
-- one, and (x, y, r) is free only for r = z.
record Lemma-6·10 : Setω where
  field
    part-1 : ∀ {χ} {X : Type χ} (z g : X) (gs : List X)
             → (∀ v → v ≡ z ⊎ v ∈ g ∷ gs) → ¬ (z ∈ g ∷ gs)
             → (θ : Sub X X) → FreelyGenerates θ → (∀ {v} → v ∈ g ∷ gs → θ v ≈ʷ ℊ v)
             → θ z ≈ʷ ℊ z
    part-2 : (θ : Sub (Fin 3) (Fin 3)) → FreelyGenerates θ → {x y : Fin 3} → x ≢ y
             → θ x ≈ʷ ℊ x → θ y ≈ʷ ℊ y → ∀ v → θ v ≈ʷ ℊ v
    part-3 : (θ : Sub (Fin 3) (Fin 3)) → FreelyGenerates θ → (m : Fin 3) → (∀ i → ¬ (ℊ m ≈ʷ θ i))
             → {u v : Fin 3} → u ≢ v → θ u ≈ʷ ℊ u → θ v ≈ʷ ℊ v → ⊥
    part-4 : (r : LatTerm (Fin 3)) → FreelyGenerates (xyr r) → r ≈ʷ ℊ 2F

-- The proof of Lemma 6.10.
lemma-6·10 : Lemma-6·10
lemma-6·10 = record
  { part-1 = λ z g gs cover z∉ θ θ-free fix → Partition.fixes-last z g gs cover z∉ θ θ-free fix
  ; part-2 = fix-two-generators
  ; part-3 = proper-fixes-one
  ; part-4 = xyr-free→z
  }
```

--------------------------------------

[DeansProblem.Partition]: DeansProblem.Partition.html
[DeansProblem.Coherent]: DeansProblem.Coherent.html
