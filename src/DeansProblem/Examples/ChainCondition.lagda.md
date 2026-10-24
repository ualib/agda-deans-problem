---
layout: default
file: "src/DeansProblem/Examples/ChainCondition.lagda.md"
title: "DeansProblem.Examples.ChainCondition module"
date: "2026-10-16"
author: "the agda-lattices development team"
---

### The chain condition fails: a ladder in FL(3)

This is the [DeansProblem.Examples.ChainCondition][] module of the [agda-lattices][] library.

[DeansProblem.Chain.Condition][] asks whether every ascending chain of
3-generated sublattices of a free lattice stabilizes, the lattice analogue of
Takahasi's theorem for free groups.  The answer is no.  This module builds an
infinite strictly ascending chain of 3-generated sublattices of `FL(3)`
(`ladder`{.AgdaFunction}), so the chain condition fails in `FL(3)`
(`chain-condition-fails`{.AgdaFunction}), and in every free lattice with three
generators that a map back to `Fin 3` separates (`ladder-in`{.AgdaFunction}),
which is any `FL(X)` over three or more generators with decidable equality.
The links of the chain are not free, so Theorem H
(`no-copy-chain`{.AgdaFunction} of [DeansProblem.NoChain][]) is untouched:
each link has `x ∧ y` below its third generator, against the meet condition
of FJN Corollary 1.13 (argued here, not formalized).  The engine finds the
links finite, with 10, 12, 16, 18, 22, … elements, as far as it was run: the
first 24 links, of at most 78 elements, by `verify_ladder` in
`scripts/python/freelattices/chains.py`, run as
`python3 -m freelattices ladder --links 24`; its tests pin the first ten.
Finiteness is not proved.

**The ladder**.  Over elements `a`, `b` and `w` of a free lattice, put
`A₀ = a ∧ w`, `B₀ = b ∧ w`, `Aₖ₊₁ = w ∧ (a ∨ Bₖ)` and `Bₖ₊₁ = w ∧ (b ∨ Aₖ)`
(the module `Ladder`{.AgdaModule}).  The rungs lie below `w`, each side ascends,
and each rung of one side lies below the next rung of the other.  In `FL(3)`,
with generators `x`, `y`, `z`, take `a = x`, `b = y` and
`c = (x ∨ z) ∧ (y ∨ z)` for `w`, and write `Aₖ` and `Bₖ` for the rungs.  The
chain is

    ⟨x, y, A₀ ∨ B₀⟩ ⊊ ⟨x, y, A₁⟩ ⊊ ⟨x, y, A₁ ∨ B₁⟩ ⊊ ⟨x, y, A₂⟩ ⊊ ⋯,

the links `⟨x, y, Aₖ ∨ Bₖ⟩` and `⟨x, y, Aₖ₊₁⟩` interleaved
(`interleaved-chain`{.AgdaFunction}).

**Ascent, in any free lattice**.  Replacing the bound `c` by any `w` between
`Aₖ ∨ Bₖ` and `c` leaves the rungs up to `k` unchanged
(`stable`{.AgdaFunction}), by induction on the rung, since every operation in
them is monotone.  Both `Aₖ₊₁` and `Aₖ₊₁ ∨ Bₖ₊₁` lie between, so the term that
gives `Aₖ ∨ Bₖ` from `x`, `y` and `c` gives it from `x`, `y` and `Aₖ₊₁`, and the
term that gives `Aₖ₊₁` gives it from `x`, `y` and `Aₖ₊₁ ∨ Bₖ₊₁`
(`ascend-even`{.AgdaFunction}, `ascend-odd`{.AgdaFunction}).  Nothing about
`FL(3)` is used: in any lattice these links ascend.

**Strictness, in `FL(3)`**.  Seven non-inequalities among small terms are
decided by Whitman's procedure: `c ≰ x ∨ y`, `x ≰ y ∨ z`, `y ≰ x ∨ z`,
`x ∧ c ≰ y`, `y ∧ c ≰ x`, `x ≰ y` and `y ≰ x`.  With Whitman's condition and
the primality of generators they give, by induction on `k`, that the sides of
the ladder ascend strictly
(`A-strict`{.AgdaFunction}, `B-strict`{.AgdaFunction}), that
`Aₖ₊₁ ≰ Aₖ ∨ Bₖ` (`A'≰E`{.AgdaFunction}) and that `Bₖ₊₁ ≰ Aₖ₊₁`
(`B'≰A'`{.AgdaFunction}).  Then an invariant excludes the new generator from the
lower link.  Every element `s` of `⟨x, y, Aₖ ∨ Bₖ⟩` satisfies `s ≤ x ∨ y`, and
`Aₖ₊₁ ≤ s` only if `x ∨ Bₖ ≤ s` (`inv-A`{.AgdaFunction}): the generators satisfy
it, meets preserve it, and for a join `s ∨ t ≥ Aₖ₊₁ = c ∧ (x ∨ Bₖ)` Whitman's
condition leaves four cases, of which `c ≤ s ∨ t` is impossible since
`s ∨ t ≤ x ∨ y`, and the other three give `x ∨ Bₖ ≤ s ∨ t`.  If `Aₖ₊₁` were in
the link, then `x ∨ Bₖ ≤ Aₖ₊₁ ≤ c`, so `x ≤ c ≤ y ∨ z`, which is false
(`A'∉`{.AgdaFunction}).  The same argument with `x` and `y` exchanged keeps
`Bₖ₊₁` out of `⟨x, y, Aₖ₊₁⟩` (`inv-B`{.AgdaFunction}, `B'∉`{.AgdaFunction}),
and since `Bₖ₊₁` lies in `⟨x, y, Aₖ₊₁ ∨ Bₖ₊₁⟩`, so does that link's third
generator lie outside `⟨x, y, Aₖ₊₁⟩` (`E'∉`{.AgdaFunction}).

The chain was found by the engine's exact membership test, in the sublattice
`⟨x, y, c⟩`, which from its fourth round of closure on grows by three elements
a round where `FL(3)` explodes; the proof here is independent of the engine.

<!--
```agda
{-# OPTIONS --without-K --exact-split --safe #-}

module DeansProblem.Examples.ChainCondition where

open import Agda.Primitive  using () renaming ( Set to Type )

-- Imports from the Agda Standard Library ---------------------------------------
open import Data.Empty                             using ( ⊥-elim )
open import Data.Fin.Base                          using ( Fin )
open import Data.Fin.Patterns                      using ( 0F ; 1F ; 2F )
open import Data.Fin.Properties                    using ( _≟_ )
open import Data.Nat.Base                          using ( ℕ ; zero ; suc )
open import Data.Nat.Properties                    using ( ≤-refl )
open import Data.Product                           using ( _×_ ; _,_ ; proj₁ ; proj₂ )
open import Data.Sum.Base                          using ( inj₁ ; inj₂ )
open import Function                               using ( _∘_ )
open import Level                                  using ( Level )
open import Relation.Binary.PropositionalEquality  using ( _≡_ ; refl ; sym ; cong ; subst ; subst₂ )
open import Relation.Nullary                       using ( ¬_ )
open import Relation.Nullary.Decidable.Core        using ( from-no )
open import Relation.Unary                         using ( _⊆_ ; _⊂_ )

-- Imports from the Agda Universal Algebra Library ------------------------------
open import Lattices.Free.Canonical.Basic          using ( ≈ʷ-refl ; ≈ʷ-sym ; ≈ʷ-trans ; ∨̇-cong )
open import DeansProblem.Chain.Condition           using ( ⟨_⟩ ; gen∈ ; gens⊆ ; StrictlyAscending
                                                         ; ChainCondition ; Stabilizes
                                                         ; strict→ascending ; interleaved-chain
                                                         ; strict-⨟ )
open import Lattices.Free.Substitution             using ( Sub ; _[_] ; []-ℊ ; []-⨟ ; []-cong
                                                         ; []-congʳ ; subst-hom )
open import Lattices.Free.Term                     using ( LatTerm ; ℊ ; _∧̇_ ; _∨̇_ )
open import Lattices.Free.Whitman                  using ( _≤ʷ_ ; _≈ʷ_ ; ∨≤ ; ≤ʷ-refl ; ≤ʷ-trans
                                                         ; ≤∧ ; ≤∧-inv ; ≤∨ˡ ; ≤∨ʳ ; ∧ˡ≤ ; ∧ʳ≤
                                                         ; ∨≤-inv ; ℊ≤∨-inv ; ∧≤∨-inv
                                                         ; module Decision )
open import Setoid.Functions                       using ( IsInjective )

private variable
  χ υ : Level
  X : Type χ
```
-->

#### The ladder

Over any `a`, `b` and `w`, the two sides of the ladder are defined together
(`Ladder.A`{.AgdaFunction}, `Ladder.B`{.AgdaFunction}), and `E k` is the join
of the `k`-th rungs.  The rungs lie below `w`; each rung of one side lies below
the next rung of the other; and the sides ascend.

```agda
-- The formal join is monotone in both arguments.
∨̇-mono : {s t u v : LatTerm X} → s ≤ʷ u → t ≤ʷ v → s ∨̇ t ≤ʷ u ∨̇ v
∨̇-mono p q = ∨≤ (≤∨ˡ p) (≤∨ʳ q)

module Ladder {X : Type χ} (a b w : LatTerm X) where

  -- The two sides of the ladder over a, b and the bound w.
  A B : ℕ → LatTerm X
  A zero     = a ∧̇ w
  A (suc k)  = w ∧̇ (a ∨̇ B k)
  B zero     = b ∧̇ w
  B (suc k)  = w ∧̇ (b ∨̇ A k)

  -- The join of the k-th rungs.
  E : ℕ → LatTerm X
  E k = A k ∨̇ B k

  -- Every rung lies below the bound.
  A≤w : ∀ k → A k ≤ʷ w
  A≤w zero     = ∧ʳ≤ ≤ʷ-refl
  A≤w (suc k)  = ∧ˡ≤ ≤ʷ-refl

  -- Every rung lies below the bound.
  B≤w : ∀ k → B k ≤ʷ w
  B≤w zero     = ∧ʳ≤ ≤ʷ-refl
  B≤w (suc k)  = ∧ˡ≤ ≤ʷ-refl

  -- A rung of one side lies below the next rung of the other.
  B≤A : ∀ k → B k ≤ʷ A (suc k)
  B≤A k = ≤∧ (B≤w k) (≤∨ʳ ≤ʷ-refl)

  -- A rung of one side lies below the next rung of the other.
  A≤B : ∀ k → A k ≤ʷ B (suc k)
  A≤B k = ≤∧ (A≤w k) (≤∨ʳ ≤ʷ-refl)

  -- The sides ascend.
  A-mono : ∀ k → A k ≤ʷ A (suc k)
  B-mono : ∀ k → B k ≤ʷ B (suc k)
  A-mono zero     = ≤∧ (∧ʳ≤ ≤ʷ-refl) (∧ˡ≤ (≤∨ˡ ≤ʷ-refl))
  A-mono (suc k)  = ≤∧ (∧ˡ≤ ≤ʷ-refl) (∧ʳ≤ (∨̇-mono ≤ʷ-refl (B-mono k)))
  B-mono zero     = ≤∧ (∧ʳ≤ ≤ʷ-refl) (∧ˡ≤ (≤∨ˡ ≤ʷ-refl))
  B-mono (suc k)  = ≤∧ (∧ˡ≤ ≤ʷ-refl) (∧ʳ≤ (∨̇-mono ≤ʷ-refl (A-mono k)))

  -- The first rung of each side lies below every rung of it.
  A₀≤A : ∀ k → A zero ≤ʷ A k
  A₀≤A zero     = ≤ʷ-refl
  A₀≤A (suc k)  = ≤ʷ-trans (A₀≤A k) (A-mono k)

  -- The first rung of each side lies below every rung of it.
  B₀≤B : ∀ k → B zero ≤ʷ B k
  B₀≤B zero     = ≤ʷ-refl
  B₀≤B (suc k)  = ≤ʷ-trans (B₀≤B k) (B-mono k)
```

Substitution commutes with the construction (`ladder-[]`{.AgdaFunction}): the
rungs over `a`, `b`, `w`, substituted by `σ`, are the rungs over `a [ σ ]`,
`b [ σ ]`, `w [ σ ]`.  And between `Aₖ ∨ Bₖ` and `c`, any bound gives the same
rungs up to `k` as `c` does (`stable`{.AgdaFunction}).

```agda
module _ {X : Type χ} {Y : Type υ} (a b w : LatTerm X) (σ : Sub X Y) where
  private
    module L = Ladder a b w
    module M = Ladder (a [ σ ]) (b [ σ ]) (w [ σ ])

  -- Substitution commutes with the ladder.
  ladder-[] : ∀ k → L.A k [ σ ] ≡ M.A k × L.B k [ σ ] ≡ M.B k
  ladder-[] zero     = refl , refl
  ladder-[] (suc k)  = cong (λ v → w [ σ ] ∧̇ (a [ σ ] ∨̇ v)) (proj₂ (ladder-[] k))
                     , cong (λ v → w [ σ ] ∧̇ (b [ σ ] ∨̇ v)) (proj₁ (ladder-[] k))

module _ {X : Type χ} (a b c w : LatTerm X) where
  private
    module C = Ladder a b c
    module V = Ladder a b w

  -- Between the k-th rungs and c, the bound w gives the same rungs up to k.
  stable : ∀ k → C.A k ≤ʷ w → C.B k ≤ʷ w → w ≤ʷ c → V.A k ≈ʷ C.A k × V.B k ≈ʷ C.B k
  stable zero     hA hB w≤c = (≤∧ (∧ˡ≤ ≤ʷ-refl) (∧ʳ≤ w≤c) , ≤∧ (∧ˡ≤ ≤ʷ-refl) hA)
                            , (≤∧ (∧ˡ≤ ≤ʷ-refl) (∧ʳ≤ w≤c) , ≤∧ (∧ˡ≤ ≤ʷ-refl) hB)
  stable (suc k)  hA hB w≤c =
      (≤∧ (∧ˡ≤ w≤c) (∧ʳ≤ (∨̇-mono ≤ʷ-refl (proj₁ (proj₂ below))))
      , ≤∧ hA (∧ʳ≤ (∨̇-mono ≤ʷ-refl (proj₂ (proj₂ below)))))
    , (≤∧ (∧ˡ≤ w≤c) (∧ʳ≤ (∨̇-mono ≤ʷ-refl (proj₁ (proj₁ below))))
      , ≤∧ hB (∧ʳ≤ (∨̇-mono ≤ʷ-refl (proj₂ (proj₁ below)))))
    where
    -- The rungs up to k agree.
    below : V.A k ≈ʷ C.A k × V.B k ≈ʷ C.B k
    below = stable k (≤ʷ-trans (C.A-mono k) hA) (≤ʷ-trans (C.B-mono k) hB) w≤c
```

#### The links ascend, in any free lattice

The links are the triples `(a, b, w)` (`triple`{.AgdaFunction}), with
`w = Eₖ` and `w = Aₖ₊₁` in turn.  The witness terms are the rungs over the three
generators of `FL(3)`, the ladder `G` below, read through the upper link's
triple.

```agda
module Ascent {X : Type χ} (a b c : LatTerm X) where
  open Ladder a b c

  -- The family (a, b, w).
  triple : LatTerm X → Sub (Fin 3) X
  triple w 0F = a
  triple w 1F = b
  triple w 2F = w

  private
    -- The ladder over the generators, whose rungs are the witness terms.
    module G = Ladder {X = Fin 3} (ℊ 0F) (ℊ 1F) (ℊ 2F)

    -- The witness rungs, read through a triple, are the rungs over (a, b, w).
    rungs : ∀ w k → G.A k [ triple w ] ≡ Ladder.A a b w k × G.B k [ triple w ] ≡ Ladder.B a b w k
    rungs w = ladder-[] (ℊ 0F) (ℊ 1F) (ℊ 2F) (triple w)

    -- The k-th rungs are those over (a, b, A (k + 1)).
    even-rungs : ∀ k → Ladder.A a b (A (suc k)) k ≈ʷ A k × Ladder.B a b (A (suc k)) k ≈ʷ B k
    even-rungs k = stable a b c (A (suc k)) k (A-mono k) (B≤A k) (A≤w (suc k))

    -- The (k + 1)-st rungs are those over (a, b, E (k + 1)).
    odd-rungs : ∀ k → Ladder.A a b (E (suc k)) (suc k) ≈ʷ A (suc k)
                    × Ladder.B a b (E (suc k)) (suc k) ≈ʷ B (suc k)
    odd-rungs k = stable a b c (E (suc k)) (suc k) (≤∨ˡ ≤ʷ-refl) (≤∨ʳ ≤ʷ-refl)
                         (∨≤ (A≤w (suc k)) (B≤w (suc k)))

  -- The link of E k lies in the link of A (k + 1).
  ascend-even : ∀ k → ⟨ triple (E k) ⟩ ⊆ ⟨ triple (A (suc k)) ⟩
  ascend-even k = gens⊆ λ where
    0F → gen∈ (triple (A (suc k))) 0F
    1F → gen∈ (triple (A (suc k))) 1F
    2F → G.A k ∨̇ G.B k
       , subst₂ (λ u v → u ∨̇ v ≈ʷ E k) (sym (proj₁ (rungs (A (suc k)) k)))
                (sym (proj₂ (rungs (A (suc k)) k)))
                (∨̇-cong (proj₁ (even-rungs k)) (proj₂ (even-rungs k)))

  -- The link of A (k + 1) lies in the link of E (k + 1).
  ascend-odd : ∀ k → ⟨ triple (A (suc k)) ⟩ ⊆ ⟨ triple (E (suc k)) ⟩
  ascend-odd k = gens⊆ λ where
    0F → gen∈ (triple (E (suc k))) 0F
    1F → gen∈ (triple (E (suc k))) 1F
    2F → G.A (suc k) , subst (_≈ʷ A (suc k)) (sym (proj₁ (rungs (E (suc k)) (suc k))))
                             (proj₁ (odd-rungs k))

  -- B (k + 1) lies in the link of E (k + 1).
  B-in-odd : ∀ k → ⟨ triple (E (suc k)) ⟩ (B (suc k))
  B-in-odd k = G.B (suc k) , subst (_≈ʷ B (suc k)) (sym (proj₂ (rungs (E (suc k)) (suc k))))
                                   (proj₂ (odd-rungs k))
```

#### The ladder in FL(3)

In `FL(3)` the ladder is taken over `x`, `y` and `c = (x ∨ z) ∧ (y ∨ z)`.  The
base facts are decided by Whitman's procedure.

```agda
-- The generators of FL(3).
x y z : LatTerm (Fin 3)
x = ℊ 0F
y = ℊ 1F
z = ℊ 2F

-- The bound of the ladder.
c : LatTerm (Fin 3)
c = (x ∨̇ z) ∧̇ (y ∨̇ z)

open Ladder x y c
open Ascent x y c using ( triple ; ascend-even ; ascend-odd ; B-in-odd )
open Decision (_≟_ {3}) using ( _≤ʷ?_ )

-- c lies below neither generator's join with the other.
c≰x∨y : ¬ (c ≤ʷ x ∨̇ y)
c≰x∨y = from-no (c ≤ʷ? x ∨̇ y)

-- x lies below no join of the other two generators.
x≰y∨z : ¬ (x ≤ʷ y ∨̇ z)
x≰y∨z = from-no (x ≤ʷ? y ∨̇ z)

-- y lies below no join of the other two generators.
y≰x∨z : ¬ (y ≤ʷ x ∨̇ z)
y≰x∨z = from-no (y ≤ʷ? x ∨̇ z)

-- The first rungs: x ∧ c lies below no y, and y ∧ c lies below no x.
A₀≰y : ¬ (A zero ≤ʷ y)
A₀≰y = from-no (A zero ≤ʷ? y)

-- The first rungs: x ∧ c lies below no y, and y ∧ c lies below no x.
B₀≰x : ¬ (B zero ≤ʷ x)
B₀≰x = from-no (B zero ≤ʷ? x)

-- Distinct generators are incomparable.
x≰y : ¬ (x ≤ʷ y)
x≰y = from-no (x ≤ʷ? y)

-- Distinct generators are incomparable.
y≰x : ¬ (y ≤ʷ x)
y≰x = from-no (y ≤ʷ? x)

-- Neither x nor y lies below c.
x≰c : ¬ (x ≤ʷ c)
x≰c h = x≰y∨z (proj₂ (≤∧-inv h))

-- Neither x nor y lies below c.
y≰c : ¬ (y ≤ʷ c)
y≰c h = y≰x∨z (proj₁ (≤∧-inv h))
```

Every rung lies below `x ∨ y`, and so do the joins `x ∨ Bₖ` and `y ∨ Aₖ`.  The
rungs of the `A` side lie above `A₀`, hence not below `y`; after the first, they
lie above `B₀`, hence not below `x`; dually for the `B` side.

```agda
-- Every rung lies below x ∨ y.
A≤x∨y : ∀ k → A k ≤ʷ x ∨̇ y
B≤x∨y : ∀ k → B k ≤ʷ x ∨̇ y
A≤x∨y zero     = ∧ˡ≤ (≤∨ˡ ≤ʷ-refl)
A≤x∨y (suc k)  = ∧ʳ≤ (∨≤ (≤∨ˡ ≤ʷ-refl) (B≤x∨y k))
B≤x∨y zero     = ∧ˡ≤ (≤∨ʳ ≤ʷ-refl)
B≤x∨y (suc k)  = ∧ʳ≤ (∨≤ (≤∨ʳ ≤ʷ-refl) (A≤x∨y k))

-- The join x ∨ B k lies below x ∨ y.
xB≤ : ∀ k → x ∨̇ B k ≤ʷ x ∨̇ y
xB≤ k = ∨≤ (≤∨ˡ ≤ʷ-refl) (B≤x∨y k)

-- The join y ∨ A k lies below x ∨ y.
yA≤ : ∀ k → y ∨̇ A k ≤ʷ x ∨̇ y
yA≤ k = ∨≤ (≤∨ʳ ≤ʷ-refl) (A≤x∨y k)

-- No rung of the A side lies below y.
A≰y : ∀ k → ¬ (A k ≤ʷ y)
A≰y k h = A₀≰y (≤ʷ-trans (A₀≤A k) h)

-- No rung of the B side lies below x.
B≰x : ∀ k → ¬ (B k ≤ʷ x)
B≰x k h = B₀≰x (≤ʷ-trans (B₀≤B k) h)

-- No rung of the A side after the first lies below x.
A'≰x : ∀ k → ¬ (A (suc k) ≤ʷ x)
A'≰x k h = B₀≰x (≤ʷ-trans (≤ʷ-trans (B₀≤B k) (B≤A k)) h)

-- No rung of the B side after the first lies below y.
B'≰y : ∀ k → ¬ (B (suc k) ≤ʷ y)
B'≰y k h = A₀≰y (≤ʷ-trans (≤ʷ-trans (A₀≤A k) (A≤B k)) h)
```

A rung `Aₘ₊₁ = c ∧ (x ∨ Bₘ)` below `y ∨ Aₖ` lies below `Aₖ`, by Whitman's
condition: `c` is not below `y ∨ Aₖ ≤ x ∨ y`, nor is `x ∨ Bₘ` (it lies above
`x`, and `x` is below neither `y` nor `Aₖ ≤ c`), nor is the rung below `y`.
Dually for `Bₘ₊₁` below `x ∨ Bₖ` (`A≤y∨A`{.AgdaFunction},
`B≤x∨B`{.AgdaFunction}).  And a rung `Aₖ₊₂` below `x ∨ Bₖ` puts `Bₖ₊₁` there
too (`A''≤→B'≤`{.AgdaFunction}): of the four cases, `x ∨ Bₖ₊₁ ≤ x ∨ Bₖ` and
`Aₖ₊₂ ≤ Bₖ` both give it, since `Bₖ₊₁ ≤ Aₖ₊₂`.

```agda
-- An A rung below y ∨ A k lies below A k.
A≤y∨A : ∀ m k → A (suc m) ≤ʷ y ∨̇ A k → A (suc m) ≤ʷ A k
A≤y∨A m k h with ∧≤∨-inv h
... | inj₁ (inj₁ p) = ⊥-elim (c≰x∨y (≤ʷ-trans p (yA≤ k)))
... | inj₁ (inj₂ p) with ℊ≤∨-inv (proj₁ (∨≤-inv p))
...   | inj₁ q = ⊥-elim (x≰y q)
...   | inj₂ q = ⊥-elim (x≰c (≤ʷ-trans q (A≤w k)))
A≤y∨A m k h | inj₂ (inj₁ p) = ⊥-elim (A≰y (suc m) p)
A≤y∨A m k h | inj₂ (inj₂ p) = p

-- A B rung below x ∨ B k lies below B k.
B≤x∨B : ∀ m k → B (suc m) ≤ʷ x ∨̇ B k → B (suc m) ≤ʷ B k
B≤x∨B m k h with ∧≤∨-inv h
... | inj₁ (inj₁ p) = ⊥-elim (c≰x∨y (≤ʷ-trans p (xB≤ k)))
... | inj₁ (inj₂ p) with ℊ≤∨-inv (proj₁ (∨≤-inv p))
...   | inj₁ q = ⊥-elim (y≰x q)
...   | inj₂ q = ⊥-elim (y≰c (≤ʷ-trans q (B≤w k)))
B≤x∨B m k h | inj₂ (inj₁ p) = ⊥-elim (B≰x (suc m) p)
B≤x∨B m k h | inj₂ (inj₂ p) = p

-- If A (k + 2) lies below x ∨ B k, so does B (k + 1).
A''≤→B'≤ : ∀ k → A (suc (suc k)) ≤ʷ x ∨̇ B k → B (suc k) ≤ʷ x ∨̇ B k
A''≤→B'≤ k h with ∧≤∨-inv h
... | inj₁ (inj₁ p) = ⊥-elim (c≰x∨y (≤ʷ-trans p (xB≤ k)))
... | inj₁ (inj₂ p) = proj₂ (∨≤-inv p)
... | inj₂ (inj₁ p) = ⊥-elim (A'≰x (suc k) p)
... | inj₂ (inj₂ p) = ≤ʷ-trans (B≤A (suc k)) (≤ʷ-trans p (≤∨ʳ ≤ʷ-refl))

-- If B (k + 2) lies below y ∨ A k, so does A (k + 1).
B''≤→A'≤ : ∀ k → B (suc (suc k)) ≤ʷ y ∨̇ A k → A (suc k) ≤ʷ y ∨̇ A k
B''≤→A'≤ k h with ∧≤∨-inv h
... | inj₁ (inj₁ p) = ⊥-elim (c≰x∨y (≤ʷ-trans p (yA≤ k)))
... | inj₁ (inj₂ p) = proj₂ (∨≤-inv p)
... | inj₂ (inj₁ p) = ⊥-elim (B'≰y (suc k) p)
... | inj₂ (inj₂ p) = ≤ʷ-trans (A≤B (suc k)) (≤ʷ-trans p (≤∨ʳ ≤ʷ-refl))
```

So the sides ascend strictly (`A-strict`{.AgdaFunction},
`B-strict`{.AgdaFunction}), by induction on `k` with the sides exchanged at each
step: `Aₖ₊₂ ≤ Aₖ₊₁ = c ∧ (x ∨ Bₖ)` would give `Bₖ₊₁ ≤ x ∨ Bₖ`, hence
`Bₖ₊₁ ≤ Bₖ`.  The rest follows: `Aₖ₊₁ ≰ Bₖ` (`A'≰B`{.AgdaFunction}),
`Aₖ₊₁ ≰ Aₖ ∨ Bₖ` (`A'≰E`{.AgdaFunction}), and `Bₖ₊₁ ≰ Aₖ₊₁`
(`B'≰A'`{.AgdaFunction}).

```agda
-- The sides ascend strictly.
A-strict : ∀ k → ¬ (A (suc k) ≤ʷ A k)
B-strict : ∀ k → ¬ (B (suc k) ≤ʷ B k)
A-strict zero     h = A'≰x zero (proj₁ (≤∧-inv h))
A-strict (suc k)  h = B-strict k (B≤x∨B k k (A''≤→B'≤ k (proj₂ (≤∧-inv h))))
B-strict zero     h = B'≰y zero (proj₁ (≤∧-inv h))
B-strict (suc k)  h = A-strict k (A≤y∨A k k (B''≤→A'≤ k (proj₂ (≤∧-inv h))))

-- A (k + 1) does not lie below B k.
A'≰B : ∀ k → ¬ (A (suc k) ≤ʷ B k)
A'≰B zero     h = A≰y (suc zero) (proj₁ (≤∧-inv h))
A'≰B (suc k)  h =
  A-strict k (≤ʷ-trans (A-mono (suc k)) (A≤y∨A (suc k) k (proj₂ (≤∧-inv h))))

-- A (k + 1) does not lie below A k ∨ B k.
A'≰E : ∀ k → ¬ (A (suc k) ≤ʷ E k)
A'≰E k h with ∧≤∨-inv h
... | inj₁ (inj₁ p) = c≰x∨y (≤ʷ-trans p (∨≤ (A≤x∨y k) (B≤x∨y k)))
... | inj₁ (inj₂ p) with ℊ≤∨-inv (proj₁ (∨≤-inv p))
...   | inj₁ q = x≰c (≤ʷ-trans q (A≤w k))
...   | inj₂ q = x≰c (≤ʷ-trans q (B≤w k))
A'≰E k h | inj₂ (inj₁ p) = A-strict k p
A'≰E k h | inj₂ (inj₂ p) = A'≰B k p

-- B (k + 1) does not lie below A (k + 1).
B'≰A' : ∀ k → ¬ (B (suc k) ≤ʷ A (suc k))
B'≰A' k h = B-strict k (B≤x∨B k k (proj₂ (≤∧-inv h)))
```

#### The new generators lie outside the lower links

Every element of `⟨x, y, Eₖ⟩` lies below `x ∨ y`, and above `x ∨ Bₖ` whenever it
lies above `Aₖ₊₁` (`inv-A`{.AgdaFunction}); every element of `⟨x, y, Aₖ₊₁⟩`
lies below `x ∨ y`, and above `y ∨ Aₖ` whenever it lies above `Bₖ₊₁`
(`inv-B`{.AgdaFunction}).  Both by induction on the term, as described at the
top.

```agda
-- Every element of ⟨x, y, E k⟩ lies below x ∨ y, and above x ∨ B k if above A (k + 1).
inv-A : ∀ k (t : LatTerm (Fin 3))
      → t [ triple (E k) ] ≤ʷ x ∨̇ y × (A (suc k) ≤ʷ t [ triple (E k) ] → x ∨̇ B k ≤ʷ t [ triple (E k) ])
inv-A k (ℊ 0F)   = ≤∨ˡ ≤ʷ-refl , λ h → ⊥-elim (A'≰x k h)
inv-A k (ℊ 1F)   = ≤∨ʳ ≤ʷ-refl , λ h → ⊥-elim (A≰y (suc k) h)
inv-A k (ℊ 2F)   = ∨≤ (A≤x∨y k) (B≤x∨y k) , λ h → ⊥-elim (A'≰E k h)
inv-A k (s ∧̇ t)  = ∧ˡ≤ (proj₁ (inv-A k s))
                 , λ h → ≤∧ (proj₂ (inv-A k s) (proj₁ (≤∧-inv h)))
                            (proj₂ (inv-A k t) (proj₂ (≤∧-inv h)))
inv-A k (s ∨̇ t)  = ∨≤ (proj₁ (inv-A k s)) (proj₁ (inv-A k t)) , join
  where
  -- Whitman's condition for A (k + 1) below a join.
  join : A (suc k) ≤ʷ s [ triple (E k) ] ∨̇ t [ triple (E k) ]
       → x ∨̇ B k ≤ʷ s [ triple (E k) ] ∨̇ t [ triple (E k) ]
  join h with ∧≤∨-inv h
  ... | inj₁ (inj₁ p) = ⊥-elim (c≰x∨y (≤ʷ-trans p (∨≤ (proj₁ (inv-A k s)) (proj₁ (inv-A k t)))))
  ... | inj₁ (inj₂ p) = p
  ... | inj₂ (inj₁ p) = ≤ʷ-trans (proj₂ (inv-A k s) p) (≤∨ˡ ≤ʷ-refl)
  ... | inj₂ (inj₂ p) = ≤ʷ-trans (proj₂ (inv-A k t) p) (≤∨ʳ ≤ʷ-refl)

-- Every element of ⟨x, y, A (k + 1)⟩ lies below x ∨ y, and above y ∨ A k if above B (k + 1).
inv-B : ∀ k (t : LatTerm (Fin 3))
      → t [ triple (A (suc k)) ] ≤ʷ x ∨̇ y
      × (B (suc k) ≤ʷ t [ triple (A (suc k)) ] → y ∨̇ A k ≤ʷ t [ triple (A (suc k)) ])
inv-B k (ℊ 0F)   = ≤∨ˡ ≤ʷ-refl , λ h → ⊥-elim (B≰x (suc k) h)
inv-B k (ℊ 1F)   = ≤∨ʳ ≤ʷ-refl , λ h → ⊥-elim (B'≰y k h)
inv-B k (ℊ 2F)   = A≤x∨y (suc k) , λ h → ⊥-elim (B'≰A' k h)
inv-B k (s ∧̇ t)  = ∧ˡ≤ (proj₁ (inv-B k s))
                 , λ h → ≤∧ (proj₂ (inv-B k s) (proj₁ (≤∧-inv h)))
                            (proj₂ (inv-B k t) (proj₂ (≤∧-inv h)))
inv-B k (s ∨̇ t)  = ∨≤ (proj₁ (inv-B k s)) (proj₁ (inv-B k t)) , join
  where
  -- Whitman's condition for B (k + 1) below a join.
  join : B (suc k) ≤ʷ s [ triple (A (suc k)) ] ∨̇ t [ triple (A (suc k)) ]
       → y ∨̇ A k ≤ʷ s [ triple (A (suc k)) ] ∨̇ t [ triple (A (suc k)) ]
  join h with ∧≤∨-inv h
  ... | inj₁ (inj₁ p) = ⊥-elim (c≰x∨y (≤ʷ-trans p (∨≤ (proj₁ (inv-B k s)) (proj₁ (inv-B k t)))))
  ... | inj₁ (inj₂ p) = p
  ... | inj₂ (inj₁ p) = ≤ʷ-trans (proj₂ (inv-B k s) p) (≤∨ˡ ≤ʷ-refl)
  ... | inj₂ (inj₂ p) = ≤ʷ-trans (proj₂ (inv-B k t) p) (≤∨ʳ ≤ʷ-refl)
```

If `Aₖ₊₁` were `t [ triple (E k) ]`, the invariant would put `x ∨ Bₖ` below it,
so `x ≤ Aₖ₊₁ ≤ c` (`A'∉`{.AgdaFunction}); dually for `Bₖ₊₁`
(`B'∉`{.AgdaFunction}).  And if `Eₖ₊₁` lay in `⟨x, y, Aₖ₊₁⟩`, the whole link of
`Eₖ₊₁` would, `Bₖ₊₁` with it (`E'∉`{.AgdaFunction}).

```agda
-- A (k + 1) is not in ⟨x, y, E k⟩.
A'∉ : ∀ k → ¬ ⟨ triple (E k) ⟩ (A (suc k))
A'∉ k (t , e) =
  x≰c (≤ʷ-trans (proj₁ (∨≤-inv (≤ʷ-trans (proj₂ (inv-A k t) (proj₂ e)) (proj₁ e)))) (A≤w (suc k)))

-- B (k + 1) is not in ⟨x, y, A (k + 1)⟩.
B'∉ : ∀ k → ¬ ⟨ triple (A (suc k)) ⟩ (B (suc k))
B'∉ k (t , e) =
  y≰c (≤ʷ-trans (proj₁ (∨≤-inv (≤ʷ-trans (proj₂ (inv-B k t) (proj₂ e)) (proj₁ e)))) (B≤w (suc k)))

-- E (k + 1) is not in ⟨x, y, A (k + 1)⟩.
E'∉ : ∀ k → ¬ ⟨ triple (A (suc k)) ⟩ (E (suc k))
E'∉ k m = B'∉ k (gens⊆ members (B-in-odd k))
  where
  -- The generators of the link of E (k + 1) lie in the link of A (k + 1).
  members : ∀ i → ⟨ triple (A (suc k)) ⟩ (triple (E (suc k)) i)
  members 0F = gen∈ (triple (A (suc k))) 0F
  members 1F = gen∈ (triple (A (suc k))) 1F
  members 2F = m
```

#### The chain, and the failure of the chain condition

Each step is proper: the upper link's third generator is not in the lower link.
Interleaved, the steps are the strictly ascending chain
(`ladder`{.AgdaFunction}), so the chain condition for 3-generated sublattices of
`FL(3)` fails (`chain-condition-fails`{.AgdaFunction}), and the ladder, read as
an ascending chain, never stabilizes (`ladder-never-stabilizes`{.AgdaFunction}).

```agda
-- The step from E k to A (k + 1) is proper.
even-step : ∀ k → ⟨ triple (E k) ⟩ ⊂ ⟨ triple (A (suc k)) ⟩
even-step k = ascend-even k , λ h → A'∉ k (h (gen∈ (triple (A (suc k))) 2F))

-- The step from A (k + 1) to E (k + 1) is proper.
odd-step : ∀ k → ⟨ triple (A (suc k)) ⟩ ⊂ ⟨ triple (E (suc k)) ⟩
odd-step k = ascend-odd k , λ h → E'∉ k (h (gen∈ (triple (E (suc k))) 2F))

-- An infinite strictly ascending chain of 3-generated sublattices of FL(3).
ladder : StrictlyAscending 3 (Fin 3)
ladder = interleaved-chain (λ k → triple (E k)) (λ k → triple (A (suc k))) even-step odd-step

-- The chain condition for 3-generated sublattices fails in FL(3).
chain-condition-fails : ¬ ChainCondition 3 (Fin 3)
chain-condition-fails cc = cc ladder

-- The ladder, read as an ascending chain, never stabilizes.
ladder-never-stabilizes : ¬ Stabilizes (strict→ascending ladder)
ladder-never-stabilizes (N , st) = proj₂ (StrictlyAscending.ascends ladder N) (st N ≤-refl)
```

A free lattice `FL(X)` with three generators `f 0`, `f 1`, `f 2` and a map
`g : X → Fin 3` back with `g (f i) = i` contains a copy of `FL(3)`: substitution
by `ℊ ∘ f` is injective, since substitution by `ℊ ∘ g` undoes it.  So the ladder
moves to `FL(X)` (`ladder-in`{.AgdaFunction}, by `strict-⨟`{.AgdaFunction} of
[DeansProblem.Chain.Condition][]); any `X` with three distinct elements and
decidable equality has such `f` and `g`.

```agda
-- Substitution by ℊ ∘ f is injective when g undoes f.
renaming-injective : (f : Fin 3 → X) (g : X → Fin 3) → (∀ i → g (f i) ≡ i)
                   → IsInjective (proj₁ (subst-hom (ℊ ∘ f)))
renaming-injective f g gf {s} {t} e = ≈ʷ-trans (≈ʷ-sym (back s)) (≈ʷ-trans ([]-cong (ℊ ∘ g) e) (back t))
  where
  -- Renaming by f and then by g returns the term.
  back : ∀ u → u [ ℊ ∘ f ] [ ℊ ∘ g ] ≈ʷ u
  back u = subst₂ _≈ʷ_ ([]-⨟ u (ℊ ∘ f) (ℊ ∘ g)) ([]-ℊ u)
                  ([]-congʳ u (λ i → subst (λ j → ℊ (g (f i)) ≈ʷ ℊ j) (gf i) ≈ʷ-refl))

-- The ladder in any free lattice with three generators that a map back separates.
ladder-in : (f : Fin 3 → X) (g : X → Fin 3) → (∀ i → g (f i) ≡ i) → StrictlyAscending 3 X
ladder-in f g gf = strict-⨟ ladder (ℊ ∘ f) (renaming-injective f g gf)
```
