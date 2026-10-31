---
layout: default
file: "src/DeansProblem/Shape.lagda.md"
title: "DeansProblem.Shape module"
date: "2026-10-15"
author: "the agda-lattices development team"
---

### The shape of a self-embedding with a fixed free triple

This is the [DeansProblem.Shape][] module of this repository.

[the paper]: https://arxiv.org/abs/YYMM.NNNNN

Corollary E1 of [the paper][] (Section 7) says that a proper self-embedding
`Θ` of `FL(3)` with a fixed free triple fixes exactly one generator `z`.  Put
`x = other z` and `y = other' z`.  The join `x ∨ y` decreases under `Θ` and
the meet `x ∧ y` increases.  One of `Θ`, its square, its dual `Θᵟ`, and the
square of its dual, call it `Φ`, is inflationary, fixes all three pairwise
joins, and has the bounds `x ≤ Φ(x) ≤ (x ∨ y) ∧ (x ∨ z)` and
`y ≤ Φ(y) ≤ (x ∨ y) ∧ (y ∨ z)`.

```agda
{-# OPTIONS --without-K --exact-split --safe #-}

module DeansProblem.Shape where

open import Agda.Primitive                         using  () renaming ( Set to Type )
open import Data.Empty                             using  ( ⊥-elim )
open import Data.Fin.Base                          using  ( Fin )
open import Data.Fin.Patterns                      using  ( 0F ; 1F ; 2F )
open import Data.Fin.Properties                    using  ( _≟_ )
open import Data.List.Base                         using  ( [] ; _∷_ )
open import Data.List.Membership.Propositional     using  ( _∈_ )
open import Data.List.Relation.Unary.Any           using  ( here ; there )
open import Data.Nat.Base                          using  ( ℕ ; zero ; suc )
open import Data.Product                           using  ( Σ-syntax ; _×_ ; _,_
                                                          ; proj₁ ; proj₂ )
open import Data.Sum.Base                          using  ( _⊎_ ; inj₁ ; inj₂ ; [_,_]′ )
open import Function                               using  ( id )
open import Relation.Binary.PropositionalEquality  using  ( _≡_ ; _≢_ ; sym
                                                          ; trans ; subst )
open import Relation.Nullary                       using  ( ¬_ )
open import Relation.Nullary.Decidable.Core        using  ( Dec ; yes ; no )

open import Lattices.Free.Canonical.Basic          using  ( ≈ʷ-sym )
open import DeansProblem.Chain                     using  ( iter ; []-iter-suc
                                                          ; []-iter-sucʳ )
open import Lattices.Free.Duality                  using  ( dual-cong )
open import DeansProblem.Fixed                     using  ( iter-free ; fixed→image )
open import DeansProblem.FixedGenerator            using  ( dualˢ ; dual-free
                                                          ; fixes-generator
                                                          ; inflationary-power )
open import Lattices.Free.Generation               using  ( FreelyGenerates
                                                          ; freelyGenerates→injective )
open import DeansProblem.Inflationary              using  ( Inflationary
                                                          ; inflationary-term
                                                          ; fixes-join )
open import DeansProblem.Partition                 using  ( other ; other' ; cover₃
                                                          ; ∉others₃ ; module Partition
                                                          ; fix-two-generators )
open import Lattices.Free.Substitution             using  ( Sub ; _[_] ; []-ℊ ; []-mono
                                                          ; injective→reflects )
open import Lattices.Free.Term                     using  ( LatTerm ; ℊ ; _∨̇_ ; _∧̇_ )
open import Lattices.Free.Whitman                  using  ( _≤ʷ_ ; _≈ʷ_ ; ≤ʷ-refl
                                                          ; ∨≤ ; ≤∧ ; ≤ʷ-trans
                                                          ; ≤∨ʳ ; ∨̇-upperˡ
                                                          ; ∨̇-upperʳ ; ℊ≤ℊ-inv )
```

#### The statement

`Member`{.AgdaDatatype} names the four candidates of the corollary's "up to
duality, `Θ` or `Θ²`", and `member`{.AgdaFunction} reads each as a
substitution: `Θ`, `Θ²`, `Θᵟ` (`dualˢ`{.AgdaFunction} of
[DeansProblem.FixedGenerator][]) and `(Θᵟ)²`.  `InflationaryShape Φ z`
(`InflationaryShape`{.AgdaRecord}) is what the corollary says of the
inflationary candidate `Φ`: it is inflationary, fixes `z` and the three
pairwise joins, and satisfies the two upper bounds; the lower bounds
`x ≤ Φ(x)` and `y ≤ Φ(y)` are instances of inflation.  `Shape Θ`
(`Shape`{.AgdaRecord}) is the whole conclusion: the fixed generator, its
uniqueness, the two inequalities for `Θ` itself, and a candidate with its
`InflationaryShape`.  The names `x` and `y` are `other z` and `other' z` of
[DeansProblem.Partition][], the two generators other than `z` in a fixed
order; the statement is symmetric in them.

```agda
-- The finite choice of orientation and exponent in Corollary E1.
data Member : Type where
  original square dual-original dual-square : Member

-- Interpret the choice as one of precisely the four substitutions.
member : Sub (Fin 3) (Fin 3) → Member → Sub (Fin 3) (Fin 3)
member Θ original = Θ
member Θ square = iter Θ 2
member Θ dual-original = dualˢ Θ
member Θ dual-square = iter (dualˢ Θ) 2

-- The bounds and fixed joins for the inflationary member, at the same z.
record InflationaryShape (Φ : Sub (Fin 3) (Fin 3)) (z : Fin 3) : Type where
  field
    inflationary : Inflationary Φ
    fixes-z : Φ z ≈ʷ ℊ z
    fixes-xy : (ℊ (other z) ∨̇ ℊ (other' z)) [ Φ ] ≈ʷ ℊ (other z) ∨̇ ℊ (other' z)
    fixes-xz : (ℊ (other z) ∨̇ ℊ z) [ Φ ] ≈ʷ ℊ (other z) ∨̇ ℊ z
    fixes-yz : (ℊ (other' z) ∨̇ ℊ z) [ Φ ] ≈ʷ ℊ (other' z) ∨̇ ℊ z
    bound-x : Φ (other z) ≤ʷ (ℊ (other z) ∨̇ ℊ (other' z)) ∧̇ (ℊ (other z) ∨̇ ℊ z)
    bound-y : Φ (other' z) ≤ʷ (ℊ (other z) ∨̇ ℊ (other' z)) ∧̇ (ℊ (other' z) ∨̇ ℊ z)

-- The full conclusion, including uniqueness and both original inequalities.
record Shape (Θ : Sub (Fin 3) (Fin 3)) : Type where
  field
    fixed-generator : Fin 3
    generator-fixed : Θ fixed-generator ≈ʷ ℊ fixed-generator
    generator-unique : ∀ g → Θ g ≈ʷ ℊ g → g ≡ fixed-generator
    join-decreases :  (ℊ (other fixed-generator) ∨̇ ℊ (other' fixed-generator)) [ Θ ]
                      ≤ʷ ℊ (other fixed-generator) ∨̇ ℊ (other' fixed-generator)
    meet-increases :  ℊ (other fixed-generator) ∧̇ ℊ (other' fixed-generator)
                      ≤ʷ (ℊ (other fixed-generator) ∧̇ ℊ (other' fixed-generator)) [ Θ ]
    choice : Member
    member-shape : InflationaryShape (member Θ choice) fixed-generator
```

#### A fixed generator and a decreasing join

The partition lemma at the fixed generator puts the join of the other two
below itself: the other case contradicts order reflection.  Two fixed
generators would make the embedding the identity, contradicting the missed
generator.  The dual partition gives the meet inequality in the same way.

```agda
module _
  (Θ : Sub (Fin 3) (Fin 3))
  (Θ-free : FreelyGenerates Θ)
  (z : Fin 3)
  (fixz : Θ z ≈ʷ ℊ z)
  where
  open Partition z (other z) (other' z ∷ []) (cover₃ z) (∉others₃ z)

  -- The image of the join of the other two generators lies below that join.
  fixed-generator-join : (ℊ (other z) ∨̇ ℊ (other' z)) [ Θ ] ≤ʷ ℊ (other z) ∨̇ ℊ (other' z)

  fixed-generator-join = [ id , impossible ]′ (partition (⋁others [ Θ ]))
    where
    -- The other partition case would put z below the other generators.
    impossible : ℊ z ≤ʷ ⋁others [ Θ ] → ⋁others [ Θ ] ≤ʷ ⋁others
    impossible p = ⊥-elim (z≰⋁others (injective→reflects Θ
      (freelyGenerates→injective Θ Θ-free) (≤ʷ-trans (proj₁ fixz) p)))

  -- The image of the meet of the other two lies above that meet.
  fixed-generator-meet : ℊ (other z) ∧̇ ℊ (other' z)
                          ≤ʷ (ℊ (other z) ∧̇ ℊ (other' z)) [ Θ ]
  fixed-generator-meet = [ (λ p → p) , impossible ]′ (partitionᵈ (⋀others [ Θ ]))
    where
    -- The other dual partition case would put the meet below z.
    impossible : ⋀others [ Θ ] ≤ʷ ℊ z → ⋀others ≤ʷ ⋀others [ Θ ]
    impossible p = ⊥-elim (⋀others≰z (injective→reflects Θ
      (freelyGenerates→injective Θ Θ-free) (≤ʷ-trans p (proj₂ fixz))))

  -- Properness makes the fixed generator unique.
  fixed-generator-unique : (m : Fin 3) → (∀ i → ¬ (ℊ m ≈ʷ Θ i))
    → ∀ g → Θ g ≈ʷ ℊ g → g ≡ z

  fixed-generator-unique m m∉ g fixg = decide (g ≟ z)
    where
    -- A second fixed generator makes even the missed generator an image.
    decide : Dec (g ≡ z) → g ≡ z
    decide (yes e) = e
    decide (no g≢z) =
      ⊥-elim (m∉ m (≈ʷ-sym (fix-two-generators Θ Θ-free g≢z fixg fixz m)))
```

#### Collapsing a decreasing orbit

If `t [ Θ ] ≤ t`, every positive iterate lies below `t [ Θ ]`.  Thus an
inflationary positive power puts `t` below `t [ Θ ]`, making `t` fixed.
This uses `inflationary-power`{.AgdaFunction} directly; the descent to a join
or meet of two generators is already part of that theorem.

```agda
module _
  (Θ : Sub (Fin 3) (Fin 3))
  (t : LatTerm (Fin 3))
  (decreases : t [ Θ ] ≤ʷ t)
  where

  -- A decreasing orbit stays below its starting point.
  decreasing-iterate : (k : ℕ) → t [ iter Θ k ] ≤ʷ t
  decreasing-iterate zero = subst (_≤ʷ t) (sym ([]-ℊ t)) ≤ʷ-refl
  decreasing-iterate (suc k) = subst (_≤ʷ t) (sym ([]-iter-sucʳ t Θ k))
    (≤ʷ-trans ([]-mono Θ (decreasing-iterate k)) decreases)

  -- Every positive iterate lies below the first image.
  decreasing-positive : (k : ℕ) → t [ iter Θ (suc k) ] ≤ʷ t [ Θ ]
  decreasing-positive k = subst (_≤ʷ t [ Θ ]) (sym ([]-iter-sucʳ t Θ k))
    ([]-mono Θ (decreasing-iterate k))

  -- An inflationary positive power collapses the decreasing orbit.
  inflationary-power-fixes : (k : ℕ) → Inflationary (iter Θ (suc k)) → t [ Θ ] ≈ʷ t
  inflationary-power-fixes k inf = decreases ,
    ≤ʷ-trans (inflationary-term inf t) (decreasing-positive k)
```

#### The bounds for an inflationary member

For an inflationary embedding fixing `x ∨ y`, the image of `x` cannot lie
above `y`: it would then dominate `x ∨ y`, hence the image of `y`, and order
reflection would give `y ≤ x`.  The partition at `y` therefore puts that
image below `x ∨ z`.  The same argument with `x` and `y` exchanged gives
the other bound.  Together with the fixed generator these bounds fix the
remaining pairwise joins.

```agda
private
  -- The other two generators are distinct.
  others-distinct : ∀ z → other z ≢ other' z
  others-distinct 0F ()
  others-distinct 1F ()
  others-distinct 2F ()

  -- The partition at y, with its complementary join written x ∨ z.
  partition-y : (z : Fin 3) (t : LatTerm (Fin 3))
    → t ≤ʷ ℊ (other z) ∨̇ ℊ z ⊎ ℊ (other' z) ≤ʷ t

  partition-y 0F t = [ (λ p → inj₁ (≤ʷ-trans p (∨≤ ∨̇-upperʳ ∨̇-upperˡ))) , inj₂ ]′
    (Partition.partition 2F 0F (1F ∷ []) (cover₃ 2F) (∉others₃ 2F) t)
  partition-y 1F t = Partition.partition 2F 0F (1F ∷ []) (cover₃ 2F) (∉others₃ 2F) t
  partition-y 2F t = Partition.partition 1F 0F (2F ∷ []) (cover₃ 1F) (∉others₃ 1F) t

  -- The partition at x, with its complementary join written y ∨ z.
  partition-x : (z : Fin 3) (t : LatTerm (Fin 3))
    → t ≤ʷ ℊ (other' z) ∨̇ ℊ z ⊎ ℊ (other z) ≤ʷ t
  partition-x 0F t = [ (λ p → inj₁ (≤ʷ-trans p (∨≤ ∨̇-upperʳ ∨̇-upperˡ))) , inj₂ ]′
    (Partition.partition 1F 0F (2F ∷ []) (cover₃ 1F) (∉others₃ 1F) t)
  partition-x 1F t = [ (λ p → inj₁ (≤ʷ-trans p (∨≤ ∨̇-upperʳ ∨̇-upperˡ))) , inj₂ ]′
    (Partition.partition 0F 1F (2F ∷ []) (cover₃ 0F) (∉others₃ 0F) t)
  partition-x 2F t = Partition.partition 0F 1F (2F ∷ []) (cover₃ 0F) (∉others₃ 0F) t

module _
  (Φ : Sub (Fin 3) (Fin 3))
  (Φ-free : FreelyGenerates Φ)
  (z : Fin 3)
  (fixz : Φ z ≈ʷ ℊ z)
  (inf : Inflationary Φ)
  (fixxy : (ℊ (other z) ∨̇ ℊ (other' z)) [ Φ ] ≈ʷ ℊ (other z) ∨̇ ℊ (other' z))
  where

  private
    -- The other two generators, named for the bounds below.
    x y : Fin 3
    x = other z
    y = other' z

    -- Both images lie below the fixed join.
    x≤xy : Φ x ≤ʷ ℊ x ∨̇ ℊ y
    x≤xy = ≤ʷ-trans ∨̇-upperˡ (proj₁ fixxy)

    -- The second upper bound supplied by the fixed join.
    y≤xy : Φ y ≤ʷ ℊ x ∨̇ ℊ y
    y≤xy = ≤ʷ-trans ∨̇-upperʳ (proj₁ fixxy)

    -- y below Φ x would force y below x by order reflection.
    y≰Φx : ¬ (ℊ y ≤ʷ Φ x)
    y≰Φx p =  others-distinct z
              ( sym ( ℊ≤ℊ-inv ( injective→reflects Φ
                                ( freelyGenerates→injective Φ Φ-free )
                                ( ≤ʷ-trans y≤xy (∨≤ (inf x) p) ) ) ) )

    -- x below Φ y would force x below y.
    x≰Φy : ¬ (ℊ x ≤ʷ Φ y)
    x≰Φy p =  others-distinct z
              ( ℊ≤ℊ-inv ( injective→reflects Φ
                        ( freelyGenerates→injective Φ Φ-free )
                        ( ≤ʷ-trans x≤xy ( ∨≤ p (inf y) ) ) ) )

    -- Partition at y gives the remaining upper bound on Φ x.
    x≤xz : Φ x ≤ʷ ℊ x ∨̇ ℊ z
    x≤xz = [ (λ p → p) , (λ p → ⊥-elim (y≰Φx p)) ]′ (partition-y z (Φ x))

    -- Partition at x gives the remaining upper bound on Φ y.
    y≤yz : Φ y ≤ʷ ℊ y ∨̇ ℊ z
    y≤yz = [ (λ p → p) , (λ p → ⊥-elim (x≰Φy p)) ]′ (partition-x z (Φ y))

  -- Package the inflationary embedding, its three fixed joins and bounds.
  inflationary-shape : InflationaryShape Φ z
  inflationary-shape = record
    { inflationary = inf
    ; fixes-z = fixz
    ; fixes-xy = fixxy
    ; fixes-xz = ∨≤ x≤xz (≤∨ʳ (proj₁ fixz)) , inflationary-term inf (ℊ x ∨̇ ℊ z)
    ; fixes-yz = ∨≤ y≤yz (≤∨ʳ (proj₁ fixz)) , inflationary-term inf (ℊ y ∨̇ ℊ z)
    ; bound-x = ≤∧ x≤xy x≤xz
    ; bound-y = ≤∧ y≤xy y≤yz
    }
```

#### The embedding or its square

Lemma 1 gives either inflation at both other generators or a swap.  In the
swapped case substitution monotonicity makes the square inflationary.  Both
the fixed generator and the fixed join remain fixed under this square.

```agda
private
  -- Inflation at z and the other two generators covers all of Fin 3.
  inflationary-of : (Φ : Sub (Fin 3) (Fin 3)) (z : Fin 3)
    → ℊ (other z) ≤ʷ Φ (other z) → ℊ (other' z) ≤ʷ Φ (other' z)
    → ℊ z ≤ʷ Φ z → Inflationary Φ

  inflationary-of Φ z px py pz v =
    [ (λ e → subst (λ u → ℊ u ≤ʷ Φ u) (sym e) pz) , others ]′ (cover₃ z v)
    where
    -- Transport the two remaining inequalities along list membership.
    others : v ∈ other z ∷ other' z ∷ [] → ℊ v ≤ʷ Φ v
    others (here e) = subst (λ u → ℊ u ≤ʷ Φ u) (sym e) px
    others (there (here e)) = subst (λ u → ℊ u ≤ʷ Φ u) (sym e) py
    others (there (there ()))

  -- The square is two successive substitutions, including the final identity.
  square-equation : (Θ : Sub (Fin 3) (Fin 3)) (t : LatTerm (Fin 3))
    → t [ iter Θ 2 ] ≡ t [ Θ ] [ Θ ]
  square-equation Θ t = trans ([]-iter-suc t Θ 1)
    (trans ([]-iter-suc (t [ Θ ]) Θ 0) ([]-ℊ (t [ Θ ] [ Θ ])))

module _
  (Θ : Sub (Fin 3) (Fin 3))
  (Θ-free : FreelyGenerates Θ)
  (z : Fin 3)
  (fixz : Θ z ≈ʷ ℊ z)
  (fixxy : (ℊ (other z) ∨̇ ℊ (other' z)) [ Θ ] ≈ʷ ℊ (other z) ∨̇ ℊ (other' z))
  where
  private
    -- Name the other generators for the two cases of Lemma 1.
    x y : Fin 3
    x = other z
    y = other' z

    -- Either the embedding itself or its square has the required shape.
    finish : (ℊ x ≤ʷ Θ x × ℊ y ≤ʷ Θ y) ⊎ (ℊ x ≤ʷ Θ y × ℊ y ≤ʷ Θ x)
      → InflationaryShape Θ z ⊎ InflationaryShape (iter Θ 2) z

    finish (inj₁ (px , py)) = inj₁ (inflationary-shape Θ Θ-free z fixz
      (inflationary-of Θ z px py (proj₂ fixz)) fixxy)

    finish (inj₂ (px , py)) = inj₂ (inflationary-shape (iter Θ 2)
      (iter-free Θ Θ-free 2) z fixz² inf² fixxy²)
      where
      -- Fixed points stay fixed under the square.
      fixed-square : (t : LatTerm (Fin 3)) → t [ Θ ] ≈ʷ t → t [ iter Θ 2 ] ≈ʷ t
      fixed-square t e = fixed→image Θ (freelyGenerates→injective Θ Θ-free) t e 2

      -- In particular the same generator is fixed.
      fixz² : iter Θ 2 z ≈ʷ ℊ z
      fixz² = fixed-square (ℊ z) fixz

      -- The other generators' join is fixed too.
      fixxy² : (ℊ x ∨̇ ℊ y) [ iter Θ 2 ] ≈ʷ ℊ x ∨̇ ℊ y
      fixxy² = fixed-square (ℊ x ∨̇ ℊ y) fixxy

      -- Substitution of each swapped inequality gives inflation for the square.
      inf² : Inflationary (iter Θ 2)
      inf² = inflationary-of (iter Θ 2) z
        (subst (ℊ x ≤ʷ_) (sym (square-equation Θ (ℊ x))) (≤ʷ-trans px ([]-mono Θ py)))
        (subst (ℊ y ≤ʷ_) (sym (square-equation Θ (ℊ y))) (≤ʷ-trans py ([]-mono Θ px)))
        (proj₂ fixz²)

  -- A fixed join yields the full shape for exponent one or two.
  fixed-join-shape : InflationaryShape Θ z ⊎ InflationaryShape (iter Θ 2) z
  fixed-join-shape = finish (proj₁ (fixes-join Θ Θ-free z fixxy))
```

#### Corollary E1

Theorem E supplies the fixed generator.  The inflationary positive power
from its proof supplies the orientation.  In that orientation the collapse
lemma fixes the join; Lemma 1 reduces the exponent to one or two, and the
partition bounds finish the record.  No new Whitman decisions are needed:
the contradictions use the partition's disjointness and the distinctness
of the generators.

```agda
module _
  (Θ : Sub (Fin 3) (Fin 3))
  (Θ-free : FreelyGenerates Θ)
  (m : Fin 3)
  (m∉ : ∀ i → ¬ (ℊ m ≈ʷ Θ i))
  (τ : Sub (Fin 3) (Fin 3))
  (τ-free : FreelyGenerates τ)
  (τ-fixed : ∀ i → τ i [ Θ ] ≈ʷ τ i)
  where

  private
    -- The generator supplied by Theorem E.
    generator : Σ[ z ∈ Fin 3 ] Θ z ≈ʷ ℊ z
    generator = fixes-generator Θ Θ-free m m∉ τ τ-free τ-fixed

    -- Build the finite choice in a given orientation.
    oriented : (Φ : Sub (Fin 3) (Fin 3)) → FreelyGenerates Φ
      → (z : Fin 3) → Φ z ≈ʷ ℊ z
      → (Σ[ E ∈ ℕ ] Inflationary (iter Φ (suc E)))
      → InflationaryShape Φ z ⊎ InflationaryShape (iter Φ 2) z

    oriented Φ Φ-free z fixz (E , inf) = fixed-join-shape Φ Φ-free z fixz
      (inflationary-power-fixes Φ (ℊ (other z) ∨̇ ℊ (other' z))
        (fixed-generator-join Φ Φ-free z fixz) E inf)

    -- Keep the original generator while choosing the orientation and exponent.
    choose : (z : Fin 3) → Θ z ≈ʷ ℊ z
      →  (Σ[ E ∈ ℕ ] Inflationary (iter Θ (suc E)))
         ⊎ (Σ[ E ∈ ℕ ] Inflationary (iter (dualˢ Θ) (suc E)))
      →  Σ[ c ∈ Member ] InflationaryShape (member Θ c) z
    choose z fixz (inj₁ p) =
      [ (λ s → original , s) , (λ s → square , s) ]′ (oriented Θ Θ-free z fixz p)
    choose z fixz (inj₂ p) =
      [ (λ s → dual-original , s) , (λ s → dual-square , s) ]′
        (oriented (dualˢ Θ) (dual-free Θ Θ-free) z (dual-cong fixz) p)

  -- Corollary E1: the full shape of a proper embedding with a fixed free triple.
  shape : Shape Θ
  shape =
    let (z , fixz) = generator
        (c , shaped) = choose z fixz (inflationary-power Θ Θ-free m m∉ τ τ-free τ-fixed)
    in record
      { fixed-generator   = z
      ; generator-fixed   = fixz
      ; generator-unique  = fixed-generator-unique Θ Θ-free z fixz m m∉
      ; join-decreases    = fixed-generator-join Θ Θ-free z fixz
      ; meet-increases    = fixed-generator-meet Θ Θ-free z fixz
      ; choice            = c
      ; member-shape      = shaped
      }
```

**Corollary E1** of [the paper][], as one statement: a proper self-embedding
`Θ` of `FL(3)` with a fixed free triple `τ` has the shape `Shape Θ`: it fixes
exactly one generator, `z`; `Θ(x ∨ y) ≤ x ∨ y` and `Θ(x ∧ y) ≥ x ∧ y`; and,
up to duality, `Θ` or `Θ²` is inflationary, fixes `x ∨ y`, `x ∨ z` and
`y ∨ z`, and has `Θ(x) ≤ (x ∨ y) ∧ (x ∨ z)` and `Θ(y) ≤ (x ∨ y) ∧ (y ∨ z)`
(`InflationaryShape`{.AgdaRecord}, whose inflation gives `x ≤ Θ(x)` and
`y ≤ Θ(y)`).

```agda
-- Corollary E1: the shape of a proper self-embedding with a fixed free triple.
Corollary-E1 : Type
Corollary-E1 =  (Θ : Sub (Fin 3) (Fin 3)) → FreelyGenerates Θ → (m : Fin 3) → (∀ i → ¬ (ℊ m ≈ʷ Θ i))
                → (τ : Sub (Fin 3) (Fin 3)) → FreelyGenerates τ → (∀ i → τ i [ Θ ] ≈ʷ τ i)
                → Shape Θ

-- The proof of Corollary E1.
corollary-E1 : Corollary-E1
corollary-E1 = shape
```

--------------------------------------

[DeansProblem.Shape]: DeansProblem.Shape.html
[DeansProblem.FixedGenerator]: DeansProblem.FixedGenerator.html
[DeansProblem.Partition]: DeansProblem.Partition.html
