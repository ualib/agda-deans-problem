---
layout: default
file: "src/DeansProblem/Ladder.lagda.md"
title: "DeansProblem.Ladder module"
date: "2026-10-27"
author: "the agda-lattices development team"
---

### The ladder in any lattice: Lemma 4.4

This is the [DeansProblem.Ladder][] module of this repository.

[the paper]: https://arxiv.org/abs/YYMM.NNNNN

In any lattice, the *ladder* over elements `a`, `b` and a bound `w` is the
pair of sequences

    A₀ = a ∧ w,   B₀ = b ∧ w,   Aₖ₊₁ = w ∧ (a ∨ Bₖ),   Bₖ₊₁ = w ∧ (b ∨ Aₖ),

whose terms are its *rungs*.  Lemma 4.4 of [the paper][] says the following,
in any lattice:

1.  every rung lies below `w`;
2.  each side ascends, `Aₖ ≤ Aₖ₊₁` and `Bₖ ≤ Bₖ₊₁`;
3.  each rung lies below the next rung of the other side, `Bₖ ≤ Aₖ₊₁` and
    `Aₖ ≤ Bₖ₊₁`;
4.  if `Aₖ(w) ∨ Bₖ(w) ≤ v ≤ w`, then `Aⱼ(v) = Aⱼ(w)` and `Bⱼ(v) = Bⱼ(w)` for
    every `j ≤ k`, where `Aⱼ(v)` is the rung over `a`, `b` and the bound `v`.

The module `Ladder`{.AgdaModule} of [DeansProblem.Examples.ChainCondition][]
proves the four clauses in a free lattice, over lattice terms with Whitman's
order.  The first three are inequalities between terms, so they would transfer
from `FL(X)` to every lattice; the fourth is an implication between
inequalities, which does not transfer so.
This module proves all four in an arbitrary lattice, by the paper's proof,
which is lattice algebra and nothing more (`Rungs`{.AgdaModule} and
`stable`{.AgdaFunction}), with the meet order of `Lattice-Order`{.AgdaModule}.
Every rung is the value at `(a, b, w)` of a lattice term in three variables,
the same for every lattice (`rung-terms`{.AgdaFunction}): the rungs of the
ladder over the three generators.  [DeansProblem.Examples.ChainCondition][]
reads its own ladder as the case `FL(X)` of this one.

The fourth clause is proved first for a single index, under the hypotheses
`Aₖ(w) ≤ v`, `Bₖ(w) ≤ v` and `v ≤ w` (`stable-at`{.AgdaFunction}), by
induction on `k`: `A₀(v) = a ∧ v` lies below `a ∧ w`, and above it since
`a ∧ w ≤ v`; and if the rungs agree at `k`, then
`Aₖ₊₁(v) = v ∧ (a ∨ Bₖ(w))` lies below `w ∧ (a ∨ Bₖ(w)) = Aₖ₊₁(w)`, and above
it since `Aₖ₊₁(w)` lies below `v` and below `a ∨ Bₖ(w)`.  The hypotheses at `k`
give those at every `j ≤ k`, since the sides ascend, and so the clause as the
paper states it (`stable`{.AgdaFunction}).

<!--
```agda
{-# OPTIONS --without-K --exact-split --safe #-}

module DeansProblem.Ladder where

open import Agda.Primitive  using ( Setω ) renaming ( Set to Type )

-- Imports from the Agda Standard Library ---------------------------------------
open import Data.Fin.Base                          using ( Fin )
open import Data.Fin.Patterns                      using ( 0F ; 1F ; 2F )
open import Data.Nat.Base                          using ( ℕ ; zero ; suc ; z≤n ; s≤s )
                                                   renaming ( _≤_ to _≤ℕ_ )
open import Data.Product                           using ( _×_ ; _,_ ; proj₁ ; proj₂ )
open import Level                                  using ( Level )
open import Relation.Binary                        using ( Setoid )
open import Relation.Binary.PropositionalEquality  using ( _≡_ ; refl ; cong )

-- Imports from the Agda Universal Algebra Library ------------------------------
open import Classical.Properties.Lattice        using ( module Lattice-Order )
open import Classical.Structures.Lattice.Basic  using ( Lattice ; module Lattice-Op )
open import Lattices.Free.Term                  using ( LatTerm ; ℊ ; _∧̇_ ; _∨̇_ ; module Evaluation )
open import Setoid.Algebras.Basic               using ( 𝔻[_] ; 𝕌[_] )

private variable
  α ρ : Level
```
-->

#### The rungs and the first three clauses

The rungs as lattice terms over three generators come first
(`termA`{.AgdaFunction}, `termB`{.AgdaFunction}).  Then fix a lattice
`𝑳`{.AgdaBound}.  Meets and joins are monotone in both
arguments (`∧-mono`{.AgdaFunction}, `∨-mono`{.AgdaFunction}), from the bounds
that define them.

```agda
-- The ladder of lattice terms over the three generators.
termA termB : ℕ → LatTerm (Fin 3)
termA zero     = ℊ 0F ∧̇ ℊ 2F
termA (suc k)  = ℊ 2F ∧̇ (ℊ 0F ∨̇ termB k)
termB zero     = ℊ 1F ∧̇ ℊ 2F
termB (suc k)  = ℊ 2F ∧̇ (ℊ 1F ∨̇ termA k)

module _ (𝑳 : Lattice α ρ) where
  open Lattice-Op 𝑳          using ( _∧_ ; _∨_ )
  open Lattice-Order 𝑳       using ( _≤_ ; ≤-refl ; ≤-trans ; ≤-antisym ; ∧-greatest ; ∧-lowerˡ
                                   ; ∧-lowerʳ ; ∨-least ; ∨-upperˡ ; ∨-upperʳ )
  open Setoid 𝔻[ proj₁ 𝑳 ]   using ( _≈_ )
  open Evaluation 𝑳          using ( ⟦_⟧ )

  private
    L : Type α
    L = 𝕌[ proj₁ 𝑳 ]

  -- The meet is monotone in both arguments.
  ∧-mono : {s t u v : L} → s ≤ u → t ≤ v → s ∧ t ≤ u ∧ v
  ∧-mono p q = ∧-greatest (≤-trans ∧-lowerˡ p) (≤-trans ∧-lowerʳ q)

  -- The join is monotone in both arguments.
  ∨-mono : {s t u v : L} → s ≤ u → t ≤ v → s ∨ t ≤ u ∨ v
  ∨-mono p q = ∨-least (≤-trans p ∨-upperˡ) (≤-trans q ∨-upperʳ)
```

Over `a`, `b` and the bound `w`, the two sides are defined together
(`Rungs.A`{.AgdaFunction}, `Rungs.B`{.AgdaFunction}), and the first three
clauses of the lemma follow by the paper's argument: every rung is a meet with
`w` (`A≤w`{.AgdaFunction}, `B≤w`{.AgdaFunction}); a rung lies below the next
rung of the other side (`B≤A`{.AgdaFunction}, `A≤B`{.AgdaFunction}); and the
sides ascend by a joint induction (`A-mono`{.AgdaFunction},
`B-mono`{.AgdaFunction}), so a rung lies below every later rung of its side
(`A-mono-≤`{.AgdaFunction}, `B-mono-≤`{.AgdaFunction}).

```agda
  module Rungs (a b w : L) where

    -- The two sides of the ladder over a, b and the bound w.
    A B : ℕ → L
    A zero     = a ∧ w
    A (suc k)  = w ∧ (a ∨ B k)
    B zero     = b ∧ w
    B (suc k)  = w ∧ (b ∨ A k)

    -- Every rung lies below the bound.
    A≤w : ∀ k → A k ≤ w
    A≤w zero     = ∧-lowerʳ
    A≤w (suc k)  = ∧-lowerˡ

    -- Every rung lies below the bound.
    B≤w : ∀ k → B k ≤ w
    B≤w zero     = ∧-lowerʳ
    B≤w (suc k)  = ∧-lowerˡ

    -- A rung of one side lies below the next rung of the other.
    B≤A : ∀ k → B k ≤ A (suc k)
    B≤A k = ∧-greatest (B≤w k) ∨-upperʳ

    -- A rung of one side lies below the next rung of the other.
    A≤B : ∀ k → A k ≤ B (suc k)
    A≤B k = ∧-greatest (A≤w k) ∨-upperʳ

    -- The sides ascend.
    A-mono : ∀ k → A k ≤ A (suc k)
    B-mono : ∀ k → B k ≤ B (suc k)
    A-mono zero     = ∧-greatest ∧-lowerʳ (≤-trans ∧-lowerˡ ∨-upperˡ)
    A-mono (suc k)  = ∧-mono ≤-refl (∨-mono ≤-refl (B-mono k))
    B-mono zero     = ∧-greatest ∧-lowerʳ (≤-trans ∧-lowerˡ ∨-upperˡ)
    B-mono (suc k)  = ∧-mono ≤-refl (∨-mono ≤-refl (A-mono k))

    -- A rung lies below every later rung of its side.
    A-mono-≤ : ∀ {j k} → j ≤ℕ k → A j ≤ A k
    B-mono-≤ : ∀ {j k} → j ≤ℕ k → B j ≤ B k
    A-mono-≤ {zero}  {zero}   _          = ≤-refl
    A-mono-≤ {zero}  {suc k}  _          = ≤-trans (A-mono-≤ {zero} {k} z≤n) (A-mono k)
    A-mono-≤ {suc j} {suc k}  (s≤s j≤k)  = ∧-mono ≤-refl (∨-mono ≤-refl (B-mono-≤ j≤k))
    B-mono-≤ {zero}  {zero}   _          = ≤-refl
    B-mono-≤ {zero}  {suc k}  _          = ≤-trans (B-mono-≤ {zero} {k} z≤n) (B-mono k)
    B-mono-≤ {suc j} {suc k}  (s≤s j≤k)  = ∧-mono ≤-refl (∨-mono ≤-refl (A-mono-≤ j≤k))
```

#### The rungs are values of terms

The ladder over the three generators of `FL(3)`, written out as lattice terms
(`termA`{.AgdaFunction}, `termB`{.AgdaFunction}, above), evaluated at
`(a, b, w)`, is the ladder over `a`, `b` and `w` (`rung-terms`{.AgdaFunction}).

```agda
  -- The family (a, b, w).
  abw : L → L → L → Fin 3 → L
  abw a b w 0F = a
  abw a b w 1F = b
  abw a b w 2F = w

  -- The rungs are the values of the term ladder at (a, b, w).
  rung-terms : (a b w : L) → ∀ k → ⟦ termA k ⟧ (abw a b w) ≡ Rungs.A a b w k
                                  × ⟦ termB k ⟧ (abw a b w) ≡ Rungs.B a b w k
  rung-terms a b w zero     = refl , refl
  rung-terms a b w (suc k)  = cong (λ u → w ∧ (a ∨ u)) (proj₂ (rung-terms a b w k))
                            , cong (λ u → w ∧ (b ∨ u)) (proj₁ (rung-terms a b w k))
```

#### The fourth clause

Between the `k`-th rungs over `w` and `w` itself, a bound `v` gives the same
rungs up to `k` (`stable-at`{.AgdaFunction} at `k`, and `stable`{.AgdaFunction}
at every `j ≤ k`, which is Lemma 4.4's last clause as the paper states it).

```agda
  module _ (a b w v : L) where
    private
      module W = Rungs a b w
      module V = Rungs a b v

    -- Below v and v below w: the rungs at k over v are those over w.
    stable-at : ∀ k → W.A k ≤ v → W.B k ≤ v → v ≤ w → V.A k ≈ W.A k × V.B k ≈ W.B k
    stable-at zero     hA hB v≤w =
        ≤-antisym (∧-mono ≤-refl v≤w) (∧-greatest ∧-lowerˡ hA)
      , ≤-antisym (∧-mono ≤-refl v≤w) (∧-greatest ∧-lowerˡ hB)
    stable-at (suc k)  hA hB v≤w =
        ≤-antisym (∧-mono v≤w (∨-mono ≤-refl (≤-reflexive′ (proj₂ below))))
                  (∧-greatest hA (≤-trans ∧-lowerʳ (∨-mono ≤-refl (≤-reflexive′ (sym′ (proj₂ below))))))
      , ≤-antisym (∧-mono v≤w (∨-mono ≤-refl (≤-reflexive′ (proj₁ below))))
                  (∧-greatest hB (≤-trans ∧-lowerʳ (∨-mono ≤-refl (≤-reflexive′ (sym′ (proj₁ below))))))
      where
      open Setoid 𝔻[ proj₁ 𝑳 ] using () renaming ( sym to sym′ )
      open Lattice-Order 𝑳 using () renaming ( ≤-reflexive to ≤-reflexive′ )

      -- The rungs at k agree.
      below : V.A k ≈ W.A k × V.B k ≈ W.B k
      below = stable-at k (≤-trans (W.A-mono k) hA) (≤-trans (W.B-mono k) hB) v≤w

    -- Lemma 4.4, last clause: if A k ∨ B k ≤ v ≤ w, the rungs agree at every j ≤ k.
    stable : ∀ k → W.A k ∨ W.B k ≤ v → v ≤ w → ∀ j → j ≤ℕ k → V.A j ≈ W.A j × V.B j ≈ W.B j
    stable k E≤v v≤w j j≤k =
      stable-at j (≤-trans (W.A-mono-≤ j≤k) (≤-trans ∨-upperˡ E≤v))
                  (≤-trans (W.B-mono-≤ j≤k) (≤-trans ∨-upperʳ E≤v)) v≤w
```

**Lemma 4.4** as one statement, for every lattice and every `a`, `b` and
`w`: every rung lies below `w`; each side ascends; each rung lies below the
next rung of the other side; and if `Aₖ(w) ∨ Bₖ(w) ≤ v ≤ w`, then
`Aⱼ(v) = Aⱼ(w)` and `Bⱼ(v) = Bⱼ(w)` for every `j ≤ k`.  The rungs over the
bound `w` are `Rungs.A 𝑳 a b w`{.AgdaFunction} and
`Rungs.B 𝑳 a b w`{.AgdaFunction}.

```agda
-- Lemma 4.4: the rungs lie below the bound, ascend, interlace, and are stable.
Lemma-4·4 : Setω
Lemma-4·4 =
  ∀ {α ρ} (𝑳 : Lattice α ρ) (a b w : 𝕌[ proj₁ 𝑳 ])
  → let open Lattice-Op 𝑳 using ( _∨_ )
        open Lattice-Order 𝑳 using ( _≤_ )
        open Setoid 𝔻[ proj₁ 𝑳 ] using ( _≈_ )
        A = Rungs.A 𝑳 a b w
        B = Rungs.B 𝑳 a b w
    in  (∀ k → A k ≤ w × B k ≤ w)
      × (∀ k → A k ≤ A (suc k) × B k ≤ B (suc k))
      × (∀ k → B k ≤ A (suc k) × A k ≤ B (suc k))
      × (∀ v k → A k ∨ B k ≤ v → v ≤ w
         → ∀ j → j ≤ℕ k → Rungs.A 𝑳 a b v j ≈ A j × Rungs.B 𝑳 a b v j ≈ B j)

-- The proof of Lemma 4.4.
lemma-4·4 : Lemma-4·4
lemma-4·4 𝑳 a b w =
    (λ k → A≤w k , B≤w k)
  , (λ k → A-mono k , B-mono k)
  , (λ k → B≤A k , A≤B k)
  , (λ v → stable 𝑳 a b w v)
  where open Rungs 𝑳 a b w using ( A≤w ; B≤w ; A-mono ; B-mono ; B≤A ; A≤B )
```

--------------------------------------

[DeansProblem.Ladder]: DeansProblem.Ladder.html
[DeansProblem.Examples.ChainCondition]: DeansProblem.Examples.ChainCondition.html
