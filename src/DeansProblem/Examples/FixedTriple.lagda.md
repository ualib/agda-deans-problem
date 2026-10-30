---
layout: default
file: "src/DeansProblem/Examples/FixedTriple.lagda.md"
title: "DeansProblem.Examples.FixedTriple module"
date: "2026-10-14"
author: "the agda-lattices development team"
---

### Worked example: a proper self-embedding of FL(3) fixing a copy of FL(3)

This is the [DeansProblem.Examples.FixedTriple][] module of the [agda-lattices][] library.

The fixed-sublattice question of [DeansProblem.Coherent][] asks whether `FL(3)`
has an injective endomorphism `θ` that is not onto and whose fixed sublattice
contains a sublattice isomorphic to `FL(3)`.  It does.  Let `x`, `y`, `z` be the
free generators and

    θ₁ : x ↦ x ∨ (y ∧ z),    y ↦ y ∨ (x ∧ z),    z ↦ z.

`θ₁` freely generates a proper sublattice (`θ₁-free`{.AgdaFunction},
`x∉θ₁`{.AgdaFunction}; it misses `x`), and it fixes the three elements

    m₁ = x ∨ c,    m₂ = z ∨ ((x ∨ z) ∧ q),    m₃ = ((z ∨ (p ∧ q)) ∧ (x ∨ y)) ∨ y,

where `c = z ∧ (x ∨ y)`, `p = x ∨ c` and `q = y ∨ c`
(`θ₁-fixes`{.AgdaFunction}), and these three freely generate
(`m-free`{.AgdaFunction}).  So `θ₁` with `Θ = (m₁, m₂, m₃)` is a
`FixedSublattice`{.AgdaRecord} (`fixed-triple`{.AgdaFunction}), and the two
steps it yields form a chain of three copies of `FL(3)` inside `FL(3)`,

    ⟨m₁, m₂, m₃⟩ ⊊ θ₁(FL(3)) ⊊ FL(3),

a coherent chain of length two (`lower`{.AgdaFunction}, `upper`{.AgdaFunction};
as a `Coherent 2`{.AgdaRecord} of [DeansProblem.Coherent.Finite][],
`coherent₂`{.AgdaFunction}).  Every claim is decided in `FL(3)` by Whitman's
procedure: eight decisions, the two of free generation each comparing every
member with the join and with the meet of the other two (Corollary 1.13), on
terms with at most thirty generator occurrences, the largest being
`m₃ [ θ₁ ]` in `θ₁-fixes`{.AgdaFunction}.

Where the elements come from.  `θ₁` fixes `z`, so by the partition of `FL(3)` at
`z` ([DeansProblem.Partition][]) it preserves the ideal `(x ∨ y]` and the
filter `[z)`; it fixes `c = z ∧ (x ∨ y)`, `x ∨ y`, `x ∨ z` and `y ∨ z`, and it
fixes `p = x ∨ c` and `q = y ∨ c` because `θ₁(x) = x ∨ (y ∧ z)` and
`y ∧ z ≤ c`.  So its fixed sublattice contains the sublattice `⟨p, q, z⟩`, in
which `p ∧ z = q ∧ z = c`; that sublattice is infinite, and the three elements
above are among its free triples of least rank, found by a search over the
elements of `FL(3)` of complexity at most 4.  The fixed sublattice of Freese's
own self-embedding `x ↦ x ∨ (y ∧ z)`, cyclically
([DeansProblem.Examples.SelfEmbedding][]), is by contrast an eleven-element lattice
within the same bound, with no free triple.

<!--
```agda
{-# OPTIONS --without-K --exact-split --safe #-}

module DeansProblem.Examples.FixedTriple where

open import Agda.Primitive  using () renaming ( Set to Type )

-- Imports from the Agda Standard Library ---------------------------------------
open import Data.Fin.Base                          using ( Fin )
open import Data.Fin.Patterns                      using ( 0F ; 1F ; 2F )
open import Data.Fin.Properties                    using ( _≟_ )
open import Data.List.Base                         using ( allFin )
open import Data.List.Membership.Propositional.Properties
                                                   using ( ∈-allFin )
open import Data.Empty                             using ( ⊥ ; ⊥-elim )
open import Data.Nat.Base                          using ( z≤n ; s≤s )
open import Data.Product                           using ( Σ-syntax ; _×_ ; _,_ ; proj₁ ; proj₂ )
open import Data.Sum.Base                          using ( [_,_]′ )
open import Function                               using ( id )
open import Relation.Binary.PropositionalEquality  using ( _≡_ ; refl )
open import Relation.Nullary                       using ( ¬_ )
open import Relation.Unary                         using ( _⊂_ )
open import Relation.Nullary.Decidable.Core        using ( from-yes ; from-no )

-- Imports from the Agda Universal Algebra Library ------------------------------
open import Lattices.Free.Canonical.Basic          using ( ≈ʷ-refl ; ≈ʷ-sym ; ≈ʷ-trans )
open import DeansProblem.Chain                     using ( Step )
open import DeansProblem.Chain.Condition           using ( ⟨_⟩ ; step→⊂ )
open import DeansProblem.Coherent                  using ( FixedSublattice ; lower-step )
open import DeansProblem.Coherent.Finite           using ( Coherent ; fixed→coherent₂ )
open import Lattices.Free.Generation               using ( FreelyGenerates ; module Decide )
open import Lattices.Free.Substitution             using ( Sub ; _[_] ; []-cong )
open import Lattices.Free.Term                     using ( LatTerm ; ℊ ; _∧̇_ ; _∨̇_ )
open import Lattices.Free.Whitman                  using ( _≤ʷ_ ; _≈ʷ_ ; ≤ʷ-trans ; ∨≤-inv ; ℊ≤∨-inv
                                                         ; ≤∧-inv ; ∧≤ℊ-inv ; ∧≤∨-inv ; ℊ≤ℊ-inv
                                                         ; ∨̇-upperˡ ; module Decision )
```
-->

#### The self-embedding and the triple

```agda
-- The three generators of FL(3).
x y z : LatTerm (Fin 3)
x = ℊ 0F
y = ℊ 1F
z = ℊ 2F

-- The self-embedding θ₁: it fixes z and moves x and y up.
θ₁ : Sub (Fin 3) (Fin 3)
θ₁ 0F = x ∨̇ (y ∧̇ z)
θ₁ 1F = y ∨̇ (x ∧̇ z)
θ₁ 2F = z

-- Three elements θ₁ fixes, and the triple built from them.
c p q : LatTerm (Fin 3)
c = z ∧̇ (x ∨̇ y)
p = x ∨̇ c
q = y ∨̇ c

m₁ m₂ m₃ : LatTerm (Fin 3)
m₁ = p
m₂ = z ∨̇ ((x ∨̇ z) ∧̇ q)
m₃ = ((z ∨̇ (p ∧̇ q)) ∧̇ (x ∨̇ y)) ∨̇ y

-- The triple as a substitution.
Θ : Sub (Fin 3) (Fin 3)
Θ 0F = m₁
Θ 1F = m₂
Θ 2F = m₃
```

#### The decisions

```agda
open Decide (_≟_ {3}) (allFin 3) ∈-allFin (_≟_ {3}) using ( freelyGenerates? )
open Decision (_≟_ {3}) using ( _≈ʷ?_ )

-- θ₁ freely generates a copy of FL(3).
θ₁-free : FreelyGenerates θ₁
θ₁-free = from-yes (freelyGenerates? θ₁)

-- It misses x.
x∉θ₁ : ∀ i → ¬ (x ≈ʷ θ₁ i)
x∉θ₁ 0F = from-no (x ≈ʷ? θ₁ 0F)
x∉θ₁ 1F = from-no (x ≈ʷ? θ₁ 1F)
x∉θ₁ 2F = from-no (x ≈ʷ? θ₁ 2F)

-- The triple freely generates a copy of FL(3).
m-free : FreelyGenerates Θ
m-free = from-yes (freelyGenerates? Θ)

-- θ₁ fixes each member of the triple.
θ₁-fixes : ∀ i → Θ i [ θ₁ ] ≈ʷ Θ i
θ₁-fixes 0F = from-yes (m₁ [ θ₁ ] ≈ʷ? m₁)
θ₁-fixes 1F = from-yes (m₂ [ θ₁ ] ≈ʷ? m₂)
θ₁-fixes 2F = from-yes (m₃ [ θ₁ ] ≈ʷ? m₃)
```

#### The configuration, and the chain of length three

```agda
-- A positive answer to the fixed-sublattice question.
fixed-triple : FixedSublattice
fixed-triple = record
  { θ         = θ₁
  ; θ-free    = θ₁-free
  ; missed    = 0F
  ; missed∉θ  = x∉θ₁
  ; Θ         = Θ
  ; Θ-free    = m-free
  ; fixes     = θ₁-fixes
  }

-- The chain ⟨m₁, m₂, m₃⟩ ⊊ θ₁(FL(3)) ⊊ FL(3), as two steps.
lower upper : Step (Fin 3)
lower = lower-step fixed-triple
upper = FixedSublattice.upper-step fixed-triple

-- The same configuration as a coherent chain of length two: Θ₀ = (m₁, m₂, m₃), Θ₁ = θ₁.
coherent₂ : Coherent 2
coherent₂ = fixed→coherent₂ fixed-triple
```

#### The configuration does not extend upward

A coherent chain of length three, `Θ₀, Θ₁, Θ₂` with `Θ₁ ∘ Θ₀ = Θ₀` and
`Θ₂ ∘ Θ₁ = Θ₁`, would continue the pair `(Θ, θ₁)` with a proper self-embedding
`Θ₂` fixing `θ₁(FL(3))` pointwise, that is, fixing `x ∨ (y ∧ z)`, `y ∨ (x ∧ z)`
and `z`.  There is none: an endomorphism that fixes those three elements fixes
every generator (`rigid`{.AgdaFunction}), by Whitman's rules alone.  Write
`a`, `b`, `c` for the images of `x`, `y`, `z`; then `c = z`, and
`a ∨ (b ∧ c) = x ∨ (y ∧ z)`.  Since `x` is join prime, `x ≤ a` or `x ≤ b ∧ z`,
and the latter puts `x` below `z`; so `x ≤ a`, and likewise `y ≤ b`.  Whitman's
condition on `b ∧ z ≤ x ∨ (y ∧ z)` leaves four cases: `b ≤ x ∨ (y ∧ z)` puts `y`
below `x` or below `z`; `z ≤ x ∨ (y ∧ z)` puts `z` below `x` or below `y`;
`b ∧ z ≤ x` puts `y` or `z` below `x`; and `b ∧ z ≤ y ∧ z` gives `b ≤ y` or
`z ≤ y`.  So `b ≤ y`, and `b = y`; likewise `a = x`.  Hence no
`FixedSublattice`{.AgdaRecord} has `θ₁` as its fixed triple
(`no-extension`{.AgdaFunction}): the pair `(Θ, θ₁)` is a coherent chain of
length two that no third link continues.

```agda
-- Two generators of FL(3) that differ.
private
  0≢1 : ¬ (_≡_ {A = Fin 3} 0F 1F)
  0≢1 ()

  0≢2 : ¬ (_≡_ {A = Fin 3} 0F 2F)
  0≢2 ()

  1≢0 : ¬ (_≡_ {A = Fin 3} 1F 0F)
  1≢0 ()

  1≢2 : ¬ (_≡_ {A = Fin 3} 1F 2F)
  1≢2 ()

  2≢0 : ¬ (_≡_ {A = Fin 3} 2F 0F)
  2≢0 ()

  2≢1 : ¬ (_≡_ {A = Fin 3} 2F 1F)
  2≢1 ()

module _ (Θ : Sub (Fin 3) (Fin 3)) (fixes-θ₁ : ∀ i → θ₁ i [ Θ ] ≈ʷ θ₁ i) where
  private
    a b c₀ : LatTerm (Fin 3)
    a = Θ 0F
    b = Θ 1F
    c₀ = Θ 2F

    -- The image of z is z.
    c₀≈z : c₀ ≈ʷ z
    c₀≈z = fixes-θ₁ 2F

    -- A generator below the image of z is z.
    below-c₀ : ∀ {v} → ℊ v ≤ʷ c₀ → v ≡ 2F
    below-c₀ p = ℊ≤ℊ-inv (≤ʷ-trans p (proj₁ c₀≈z))

    -- x lies below a, and y below b: each is join prime, and neither lies below z.
    x≤a : x ≤ʷ a
    x≤a = [ id , (λ p → ⊥-elim (0≢2 (below-c₀ (proj₂ (≤∧-inv p))))) ]′
            (ℊ≤∨-inv (≤ʷ-trans ∨̇-upperˡ (proj₂ (fixes-θ₁ 0F))))

    y≤b : y ≤ʷ b
    y≤b = [ id , (λ p → ⊥-elim (1≢2 (below-c₀ (proj₂ (≤∧-inv p))))) ]′
            (ℊ≤∨-inv (≤ʷ-trans ∨̇-upperˡ (proj₂ (fixes-θ₁ 1F))))

    -- Whitman's condition on b ∧ c₀ ≤ x ∨ (y ∧ z): only b ≤ y survives.
    b≤y : b ≤ʷ y
    b≤y = [ [ (λ p → ⊥-elim ([ (λ q → 1≢0 (ℊ≤ℊ-inv q)) , (λ q → 1≢2 (ℊ≤ℊ-inv (proj₂ (≤∧-inv q)))) ]′
                                (ℊ≤∨-inv (≤ʷ-trans y≤b p))))
            , (λ p → ⊥-elim ([ (λ q → 2≢0 (ℊ≤ℊ-inv q)) , (λ q → 2≢1 (ℊ≤ℊ-inv (proj₁ (≤∧-inv q)))) ]′
                                (ℊ≤∨-inv (≤ʷ-trans (proj₂ c₀≈z) p)))) ]′
          , [ (λ p → ⊥-elim ([ (λ q → 1≢0 (ℊ≤ℊ-inv (≤ʷ-trans y≤b q)))
                              , (λ q → 2≢0 (ℊ≤ℊ-inv (≤ʷ-trans (proj₂ c₀≈z) q))) ]′ (∧≤ℊ-inv p)))
            , (λ p → [ id , (λ q → ⊥-elim (2≢1 (ℊ≤ℊ-inv (≤ʷ-trans (proj₂ c₀≈z) q)))) ]′
                        (∧≤ℊ-inv (proj₁ (≤∧-inv p)))) ]′ ]′
          (∧≤∨-inv (proj₂ (∨≤-inv (proj₁ (fixes-θ₁ 0F)))))

    -- And dually on a ∧ c₀ ≤ y ∨ (x ∧ z): only a ≤ x survives.
    a≤x : a ≤ʷ x
    a≤x = [ [ (λ p → ⊥-elim ([ (λ q → 0≢1 (ℊ≤ℊ-inv q)) , (λ q → 0≢2 (ℊ≤ℊ-inv (proj₂ (≤∧-inv q)))) ]′
                                (ℊ≤∨-inv (≤ʷ-trans x≤a p))))
            , (λ p → ⊥-elim ([ (λ q → 2≢1 (ℊ≤ℊ-inv q)) , (λ q → 2≢0 (ℊ≤ℊ-inv (proj₁ (≤∧-inv q)))) ]′
                                (ℊ≤∨-inv (≤ʷ-trans (proj₂ c₀≈z) p)))) ]′
          , [ (λ p → ⊥-elim ([ (λ q → 0≢1 (ℊ≤ℊ-inv (≤ʷ-trans x≤a q)))
                              , (λ q → 2≢1 (ℊ≤ℊ-inv (≤ʷ-trans (proj₂ c₀≈z) q))) ]′ (∧≤ℊ-inv p)))
            , (λ p → [ id , (λ q → ⊥-elim (2≢0 (ℊ≤ℊ-inv (≤ʷ-trans (proj₂ c₀≈z) q)))) ]′
                        (∧≤ℊ-inv (proj₁ (≤∧-inv p)))) ]′ ]′
          (∧≤∨-inv (proj₂ (∨≤-inv (proj₁ (fixes-θ₁ 1F)))))

  -- An endomorphism fixing θ₁(x), θ₁(y) and θ₁(z) fixes every generator.
  rigid : ∀ i → Θ i ≈ʷ ℊ i
  rigid 0F = a≤x , x≤a
  rigid 1F = b≤y , y≤b
  rigid 2F = c₀≈z

-- No proper self-embedding fixes θ₁(FL(3)) pointwise.
no-extension : (F : FixedSublattice) → (∀ i → FixedSublattice.Θ F i ≈ʷ θ₁ i) → ⊥
no-extension F Θ≈θ₁ = missed∉θ missed (≈ʷ-sym (rigid θ fixes-θ₁ missed))
  where
  open FixedSublattice F

  -- θ fixes θ₁(FL(3)) pointwise, since it fixes Θ, which is θ₁ up to equality.
  fixes-θ₁ : ∀ i → θ₁ i [ θ ] ≈ʷ θ₁ i
  fixes-θ₁ i = ≈ʷ-trans ([]-cong θ (≈ʷ-sym (Θ≈θ₁ i))) (≈ʷ-trans (fixes i) (Θ≈θ₁ i))
```

**Theorem D** of the paper, as one statement: the self-embedding `θ₁` of
`FL(3)` is proper, missing the generator `x`; it fixes `m₁`, `m₂` and `m₃`,
the members of the triple `Θ`; and these three freely generate.  So
`Θ₀ = Θ` and `Θ₁ = θ₁` form a coherent chain of length two, and
`⟨m₁, m₂, m₃⟩ ⊊ θ₁(FL(3)) ⊊ FL(3)`, where `FL(3)` is `⟨ ℊ ⟩`, the sublattice
the generators generate.

```agda
-- Theorem D: θ₁ is a proper self-embedding fixing the free triple (m₁, m₂, m₃), so the two form a
-- coherent chain of length two, and ⟨m₁, m₂, m₃⟩ ⊊ θ₁(FL(3)) ⊊ FL(3).
Theorem-D : Type
Theorem-D =  (FreelyGenerates θ₁ × (∀ i → ¬ (x ≈ʷ θ₁ i)))
           × (∀ i → Θ i [ θ₁ ] ≈ʷ Θ i)
           × FreelyGenerates Θ
           × (Σ[ C ∈ Coherent 2 ] Coherent.Θ C 0F ≡ Θ × Coherent.Θ C 1F ≡ θ₁)
           × ⟨ Θ ⟩ ⊂ ⟨ θ₁ ⟩ × ⟨ θ₁ ⟩ ⊂ ⟨ ℊ ⟩

-- The proof of Theorem D.
theorem-D : Theorem-D
theorem-D =  (θ₁-free , x∉θ₁) , θ₁-fixes , m-free , (coherent₂ , refl , refl)
           , step→⊂ lower , step→⊂ upper
```

**Proposition 6.9** of the paper, as one statement: an endomorphism `Φ` of
`FL(3)` that fixes `θ₁(x)`, `θ₁(y)` and `θ₁(z)` is the identity, with no
injectivity asked of `Φ`; hence no proper self-embedding `Θ₂` fixes
`θ₁(FL(3))` pointwise, and no coherent chain of length three has
`Θ₀ = (m₁, m₂, m₃)` and `Θ₁ = θ₁`, since its `Θ₂` would be such an embedding.

```agda
-- Proposition 6.9: nothing but the identity fixes θ₁(x), θ₁(y), θ₁(z); so nothing proper fixes
-- θ₁(FL(3)) pointwise, and the coherent chain of Theorem D extends to no third link.
Proposition-6·9 : Type
Proposition-6·9 =
    ((Φ : Sub (Fin 3) (Fin 3)) → (∀ i → θ₁ i [ Φ ] ≈ʷ θ₁ i) → ∀ i → Φ i ≈ʷ ℊ i)
  × ((Θ₂ : Sub (Fin 3) (Fin 3)) → FreelyGenerates Θ₂ → (g : Fin 3) → (∀ i → ¬ (ℊ g ≈ʷ Θ₂ i))
     → ¬ (∀ t → t [ θ₁ ] [ Θ₂ ] ≈ʷ t [ θ₁ ]))
  × ((C : Coherent 3) → (∀ i → Coherent.Θ C 0F i ≈ʷ Θ i) → (∀ i → Coherent.Θ C 1F i ≈ʷ θ₁ i) → ⊥)

-- The proof of Proposition 6.9.
proposition-6·9 : Proposition-6·9
proposition-6·9 =
    rigid
  , (λ Θ₂ Θ₂-free g g∉ fix → no-extension (record  { θ         = Θ₂
                                                   ; θ-free    = Θ₂-free
                                                   ; missed    = g
                                                   ; missed∉θ  = g∉
                                                   ; Θ         = θ₁
                                                   ; Θ-free    = θ₁-free
                                                   ; fixes     = λ i → fix (ℊ i)
                                                   })
                                          (λ i → ≈ʷ-refl))
  , third
  where
  -- The third link of such a chain fixes θ₁(x), θ₁(y), θ₁(z), so it is the identity.
  third : (C : Coherent 3) → (∀ i → Coherent.Θ C 0F i ≈ʷ Θ i) → (∀ i → Coherent.Θ C 1F i ≈ʷ θ₁ i) → ⊥
  third C _ Θ₁≈θ₁ = missed∉ 2F (missed 2F) (≈ʷ-sym (rigid Θ₂ fix (missed 2F)))
    where
    open Coherent C using ( missed ; missed∉ ; coherent )

    -- The third link.
    Θ₂ : Sub (Fin 3) (Fin 3)
    Θ₂ = Coherent.Θ C 2F

    -- Θ₂ fixes θ₁ x, θ₁ y and θ₁ z, through Θ₁.
    fix : ∀ i → θ₁ i [ Θ₂ ] ≈ʷ θ₁ i
    fix i = ≈ʷ-trans ([]-cong Θ₂ (≈ʷ-sym (Θ₁≈θ₁ i)))
                     (≈ʷ-trans (coherent (s≤s (s≤s z≤n)) i) (Θ₁≈θ₁ i))
```
