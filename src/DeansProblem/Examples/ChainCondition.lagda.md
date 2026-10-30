---
layout: default
file: "src/DeansProblem/Examples/ChainCondition.lagda.md"
title: "DeansProblem.Examples.ChainCondition module"
date: "2026-10-16"
author: "the agda-lattices development team"
---

### The chain condition fails: a ladder in FL(3)

This is the [DeansProblem.Examples.ChainCondition][] module of this repository.

[DeansProblem.Chain.Condition][] asks whether every ascending chain of
3-generated sublattices of a free lattice stabilizes, the lattice analogue of
Takahasi's theorem for free groups.  The answer is no.  This module builds an
infinite strictly ascending chain of 3-generated sublattices of `FL(3)`
(`ladder`{.AgdaFunction}), so the chain condition fails in `FL(3)`
(`chain-condition-fails`{.AgdaFunction}), and in every free lattice with three
distinct generators (`ladder-into`{.AgdaFunction}), with no decidable equality.
No link of the chain is a copy of `FL(3)` (`no-link-is-a-copy`{.AgdaFunction}),
so Theorem H (`no-copy-chain`{.AgdaFunction} of [DeansProblem.NoChain][]) is
untouched: each link has `x ∧ y` below its third generator, against the meet
condition of FJN Corollary 1.13, and an embedding of `FL(3)` onto the link
would make its generating triple free.  The links lie in the sublattice
`⟨x, y, c⟩`, which is infinite (`links⊆⟨x,y,c⟩`{.AgdaFunction},
`⟨x,y,c⟩-infinite`{.AgdaFunction}).  The engine finds the
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

**Ascent, in any free lattice**.  (Lemma 4.4 of the paper, of which the
following is the free-lattice form, holds in any lattice:
[DeansProblem.Ladder][], to which `ladder≡rungs`{.AgdaFunction} ties the
ladder here.)  Replacing the bound `c` by any `w` between
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

open import Agda.Primitive  using ( Setω ) renaming ( Set to Type )

-- Imports from the Agda Standard Library ---------------------------------------
open import Data.Empty                             using ( ⊥-elim )
open import Data.List.Base                         using ( List ; [] ; _∷_ )
open import Data.List.Relation.Unary.Any           using ( Any ; here ; there )
open import Data.Fin.Base                          using ( Fin )
open import Data.Fin.Patterns                      using ( 0F ; 1F ; 2F )
open import Data.Fin.Properties                    using ( _≟_ )
open import Data.Nat.Base                          using ( ℕ ; zero ; suc ; _*_ ; _<_ ; z≤n )
                                                   renaming ( _≤_ to _≤ℕ_ )
open import Data.Nat.Properties                    using ( ≤-refl ; <-cmp )
open import Data.Product                           using ( Σ-syntax ; _×_ ; _,_ ; proj₁ ; proj₂ )
open import Data.Sum.Base                          using ( inj₁ ; inj₂ )
open import Function                               using ( _∘_ ; _↣_ ; mk↣ )
open import Level                                  using ( Level )
open import Relation.Binary                        using ( Tri ; tri< ; tri≈ ; tri> )
open import Relation.Binary.PropositionalEquality  using ( _≡_ ; refl ; sym ; trans ; cong ; subst
                                                         ; subst₂ )
open import Relation.Nullary                       using ( ¬_ )
open import Relation.Nullary.Decidable.Core        using ( from-no )
open import Relation.Unary                         using ( _⊆_ ; _⊂_ ; _≐_ )

-- Imports from the Agda Universal Algebra Library ------------------------------
open import Lattices.Free.Canonical.Basic          using ( ≈ʷ-refl ; ≈ʷ-sym ; ≈ʷ-trans ; ∨̇-cong )
open import DeansProblem.Chain.Condition           using ( ⟨_⟩ ; gen∈ ; gens⊆ ; StrictlyAscending
                                                         ; ChainCondition ; Stabilizes
                                                         ; strict→ascending ; interleaved-chain
                                                         ; strict-⨟ ; interleave-all
                                                         ; interleave-even ; interleave-odd
                                                         ; copy≐→freelyGenerates )
open import DeansProblem.Chain.Copies              using ( copy )
open import DeansProblem.Ladder                    using ( module Rungs )
import DeansProblem.Ladder
open import Lattices.Free.Complexity               using ( pigeonhole-≈ )
open import Lattices.Free.Countable                using ( three-generators ; three-generators-free )
open import Lattices.Free.Generation               using ( freelyGenerates→injective )
open import Lattices.Free.Universal                using ( FL ; ≤ʷ→≤ ; ≤→≤ʷ )
open import Setoid.Subalgebras.Basic               using ( _IsSubalgebraOf_ )
open import Lattices.Free.Substitution             using ( Sub ; _[_] ; []-ℊ ; []-⨟ ; []-cong
                                                         ; []-congʳ ; []-mono ; subst-hom )
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

These are the free-lattice forms of Lemma 4.4 of the paper, which
[DeansProblem.Ladder][] proves in any lattice.  The ladder of terms is the
ladder of that module in the lattice `FL(X)`, term for term
(`ladder≡rungs`{.AgdaFunction}), so its clauses are instances of the general
ones: the last clause as the paper states it, for every `j ≤ k`
(`stable≤`{.AgdaFunction}), and the ascent of each side over any distance
(`A-mono-≤`{.AgdaFunction}), are read off the lattice forms through the
agreement of the lattice order of `FL(X)` with Whitman's
(`≤ʷ→≤`{.AgdaFunction}, `≤→≤ʷ`{.AgdaFunction}).

```agda
module _ {X : Type χ} (a b w : LatTerm X) where
  private
    module L = Ladder a b w
    module R = Rungs (FL X) a b w

  -- The ladder of terms is the ladder of Lemma 4.4 in the lattice FL(X).
  ladder≡rungs : ∀ k → L.A k ≡ R.A k × L.B k ≡ R.B k
  ladder≡rungs zero     = refl , refl
  ladder≡rungs (suc k)  = cong (λ v → w ∧̇ (a ∨̇ v)) (proj₂ (ladder≡rungs k))
                        , cong (λ v → w ∧̇ (b ∨̇ v)) (proj₁ (ladder≡rungs k))

  -- Each side ascends over any distance (Lemma 4.4 in FL(X)).
  A-mono-≤ : ∀ {j k} → j ≤ℕ k → L.A j ≤ʷ L.A k
  A-mono-≤ {j} {k} j≤k = subst₂ _≤ʷ_ (sym (proj₁ (ladder≡rungs j))) (sym (proj₁ (ladder≡rungs k)))
                                 (≤→≤ʷ (R.A-mono-≤ j≤k))

module _ {X : Type χ} (a b w v : LatTerm X) where
  private
    module W = Ladder a b w
    module V = Ladder a b v

  -- Lemma 4.4, last clause, in FL(X): if E k ≤ v ≤ w, the rungs agree at every j ≤ k.
  stable≤ : ∀ k → W.E k ≤ʷ v → v ≤ʷ w → ∀ j → j ≤ℕ k → V.A j ≈ʷ W.A j × V.B j ≈ʷ W.B j
  stable≤ k E≤v v≤w j j≤k =
      subst₂ _≈ʷ_ (sym (proj₁ (ladder≡rungs a b v j))) (sym (proj₁ (ladder≡rungs a b w j))) (proj₁ general)
    , subst₂ _≈ʷ_ (sym (proj₂ (ladder≡rungs a b v j))) (sym (proj₂ (ladder≡rungs a b w j))) (proj₂ general)
    where
    -- The rungs at k, as the lattice's rungs, lie below v.
    E≤v′ : Rungs.A (FL X) a b w k ∨̇ Rungs.B (FL X) a b w k ≤ʷ v
    E≤v′ = subst₂ (λ s t → s ∨̇ t ≤ʷ v) (proj₁ (ladder≡rungs a b w k)) (proj₂ (ladder≡rungs a b w k))
                  E≤v

    -- Lemma 4.4 in the lattice FL(X).
    general : Rungs.A (FL X) a b v j ≈ʷ Rungs.A (FL X) a b w j
            × Rungs.B (FL X) a b v j ≈ʷ Rungs.B (FL X) a b w j
    general = DeansProblem.Ladder.stable (FL X) a b w v k (≤ʷ→≤ E≤v′) (≤ʷ→≤ v≤w) j j≤k
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

#### No link is a copy of FL(3)

Every link is a triple `(x, y, w)` whose third member lies above `x ∧ y`
(`link-meet`{.AgdaFunction}), since `x ∧ y ≤ x ∧ c = A₀` and `A₀` lies below
every rung: so the triple fails the meet condition of Corollary 2.5 (FJN
Corollary 1.13), and does not freely generate.  The clause of Theorem 4.5 is
about the link, not only its generating triple, and it holds so stated: no
embedding of `FL(3)` has the link as its image
(`no-link-is-a-copy`{.AgdaFunction}).  For an embedding whose copy is the
link, the triple would freely generate, by
`copy≐→freelyGenerates`{.AgdaFunction} of [DeansProblem.Chain.Condition][]
(the images of the free generators are `x`, `y` and `w` in some order, by
Corollary 2.4), and the meet condition at the index of `w` would put that
index among the other two.

```agda
-- x ∧ y lies below the bound c.
x∧y≤c : x ∧̇ y ≤ʷ c
x∧y≤c = ≤∧ (∧ˡ≤ (≤∨ˡ ≤ʷ-refl)) (∧ʳ≤ (≤∨ˡ ≤ʷ-refl))

-- x ∧ y lies below every rung.
x∧y≤A : ∀ k → x ∧̇ y ≤ʷ A k
x∧y≤A k = ≤ʷ-trans (≤∧ (∧ˡ≤ ≤ʷ-refl) x∧y≤c) (A₀≤A k)

-- The third member of every link lies above the meet of the first two.
link-meet : ∀ n → StrictlyAscending.links ladder n 0F ∧̇ StrictlyAscending.links ladder n 1F
                  ≤ʷ StrictlyAscending.links ladder n 2F
link-meet = interleave-all (λ σ → σ 0F ∧̇ σ 1F ≤ʷ σ 2F)
                           (λ k → triple (E k)) (λ k → triple (A (suc k)))
                           (λ k → ≤ʷ-trans (x∧y≤A k) (≤∨ˡ ≤ʷ-refl)) (λ k → x∧y≤A (suc k))

-- A triple whose third member lies above the meet of the others generates no copy of FL(3).
meet-below→no-copy : (σ : Sub (Fin 3) X) → σ 0F ∧̇ σ 1F ≤ʷ σ 2F
                   → (e : proj₁ (FL (Fin 3)) IsSubalgebraOf proj₁ (FL X)) → ¬ (copy e ≐ ⟨ σ ⟩)
meet-below→no-copy σ p e e≐ = not-member (proj₂ (copy≐→freelyGenerates e σ e≐) {2F} {0F ∷ 1F ∷ []} p)
  where
  -- The index of the third member is neither of the other two.
  not-member : ¬ Any (2F ≡_) (0F ∷ 1F ∷ [])
  not-member (here ())
  not-member (there (here ()))
  not-member (there (there ()))

-- Theorem 4.5: no link of the ladder is a copy of FL(3).
no-link-is-a-copy : ∀ n (e : proj₁ (FL (Fin 3)) IsSubalgebraOf proj₁ (FL (Fin 3)))
                  → ¬ (copy e ≐ ⟨ StrictlyAscending.links ladder n ⟩)
no-link-is-a-copy n = meet-below→no-copy (StrictlyAscending.links ladder n) (link-meet n)
```

#### The sublattice ⟨x, y, c⟩

Computation 4.6 of the paper says that the search for the chain ran inside the
sublattice `⟨x, y, c⟩`, which contains every link and is therefore infinite.
Every rung is a member of it (`A∈`{.AgdaFunction}, `B∈`{.AgdaFunction}): the
term that names it is the ladder over the three generators of `FL(3)`, read
through `(x, y, c)`.  So the generators of every link are members, and every
link lies in it (`links⊆⟨x,y,c⟩`{.AgdaFunction}).  The rungs of the `A` side
are pairwise distinct (`A-injective`{.AgdaFunction}): for `j < k`,
`Aⱼ₊₁ ≤ Aₖ` by Lemma 4.4, so `Aₖ = Aⱼ` would give `Aⱼ₊₁ ≤ Aⱼ`, against
strictness.  So no finite list covers `⟨x, y, c⟩`
(`⟨x,y,c⟩-infinite`{.AgdaFunction}): the rungs would repeat, by the pigeonhole
principle for a sequence in a list (`pigeonhole-≈`{.AgdaFunction} of
[Lattices.Free.Complexity][]).

```agda
private
  -- The ladder over the generators, whose rungs name the rungs over (x, y, c).
  module G = Ladder {X = Fin 3} (ℊ 0F) (ℊ 1F) (ℊ 2F)

-- Every rung of the A side is a member of ⟨x, y, c⟩.
A∈ : ∀ k → ⟨ triple c ⟩ (A k)
A∈ k = G.A k , subst (_≈ʷ A k) (sym (proj₁ (ladder-[] (ℊ 0F) (ℊ 1F) (ℊ 2F) (triple c) k))) ≈ʷ-refl

-- Every rung of the B side is a member of ⟨x, y, c⟩.
B∈ : ∀ k → ⟨ triple c ⟩ (B k)
B∈ k = G.B k , subst (_≈ʷ B k) (sym (proj₂ (ladder-[] (ℊ 0F) (ℊ 1F) (ℊ 2F) (triple c) k))) ≈ʷ-refl

-- The sublattice ⟨x, y, w⟩ lies in ⟨x, y, c⟩ when w does.
triple⊆ : ∀ {w} → ⟨ triple c ⟩ w → ⟨ triple w ⟩ ⊆ ⟨ triple c ⟩
triple⊆ w∈ = gens⊆ λ where
  0F → gen∈ (triple c) 0F
  1F → gen∈ (triple c) 1F
  2F → w∈

-- ⟨x, y, c⟩ contains every link.
links⊆⟨x,y,c⟩ : ∀ n → ⟨ StrictlyAscending.links ladder n ⟩ ⊆ ⟨ triple c ⟩
links⊆⟨x,y,c⟩ = interleave-all (λ σ → ⟨ σ ⟩ ⊆ ⟨ triple c ⟩)
                               (λ k → triple (E k)) (λ k → triple (A (suc k)))
                               (λ k → triple⊆ (E∈ k)) (λ k → triple⊆ (A∈ (suc k)))
  where
  -- The join of the k-th rungs is a member.
  E∈ : ∀ k → ⟨ triple c ⟩ (E k)
  E∈ k = proj₁ (A∈ k) ∨̇ proj₁ (B∈ k) , ∨̇-cong (proj₂ (A∈ k)) (proj₂ (B∈ k))

-- A later rung of the A side never lies below an earlier one.
A-later≰ : ∀ {j k} → j < k → ¬ (A k ≤ʷ A j)
A-later≰ {j} j<k h = A-strict j (≤ʷ-trans (A-mono-≤ x y c j<k) h)

-- The rungs of the A side are pairwise distinct.
A-injective : ∀ {j k} → A j ≈ʷ A k → j ≡ k
A-injective {j} {k} e = compare (<-cmp j k)
  where
  -- By the order of j and k.
  compare : Tri (j < k) (j ≡ k) (k < j) → j ≡ k
  compare (tri< j<k _ _)  = ⊥-elim (A-later≰ j<k (proj₂ e))
  compare (tri≈ _ j≡k _)  = j≡k
  compare (tri> _ _ k<j)  = ⊥-elim (A-later≰ k<j (proj₁ e))

-- No finite list covers ⟨x, y, c⟩: it is infinite.
⟨x,y,c⟩-infinite : ¬ (Σ[ L ∈ List (LatTerm (Fin 3)) ] (∀ {w} → ⟨ triple c ⟩ w → Any (w ≈ʷ_) L))
⟨x,y,c⟩-infinite (L , covers) =
  let (j , k , j<k , e) = pigeonhole-≈ L A (λ k → covers (A∈ k)) in A-later≰ j<k (proj₂ e)
```

#### The bottom link's term recurs

After Theorem 4.5 the paper observes that what fails without freeness is not
the recurrence on which Theorem C rests: by Lemma 4.4 the term `t₀` that gives
`w₀ = A₀ ∨ B₀` from `(x, y, c)` gives it from `(x, y, wₙ)` for every `n`
(`t₀-recurs`{.AgdaFunction}), since every third generator `wₙ` lies between
`A₀ ∨ B₀` and `c`, and the rungs at `0` over such a bound are those over `c`
(`t₀-at`{.AgdaFunction}, by `stable≤`{.AgdaFunction}).

```agda
-- The join of the first rungs lies below every rung after the first.
E₀≤A' : ∀ k → E zero ≤ʷ A (suc k)
E₀≤A' k = ∨≤ (A₀≤A (suc k)) (≤ʷ-trans (B₀≤B k) (B≤A k))

-- The term t₀ gives w₀ from (x, y, w) for any w between A₀ ∨ B₀ and c.
t₀-at : ∀ w → E zero ≤ʷ w → w ≤ʷ c → (G.A zero ∨̇ G.B zero) [ triple w ] ≈ʷ E zero
t₀-at w E≤w w≤c = let (eA , eB) = stable≤ x y c w zero E≤w w≤c zero z≤n in ∨̇-cong eA eB

-- The term t₀ = A₀ ∨ B₀ over the generators gives w₀ from every link's generators.
t₀-recurs : ∀ n → (G.A zero ∨̇ G.B zero) [ StrictlyAscending.links ladder n ] ≈ʷ E zero
t₀-recurs = interleave-all (λ σ → (G.A zero ∨̇ G.B zero) [ σ ] ≈ʷ E zero)
                           (λ k → triple (E k)) (λ k → triple (A (suc k)))
                           (λ k → t₀-at (E k) (∨̇-mono (A₀≤A k) (B₀≤B k)) (∨≤ (A≤w k) (B≤w k)))
                           (λ k → t₀-at (A (suc k)) (E₀≤A' k) (A≤w (suc k)))
```

#### Every free lattice on three or more generators

The paper's last clause of Theorem 4.5 is for every free lattice on at least
three generators.  Three distinct generators of `FL(X)`, given by an injection
`Fin 3 ↣ X`, freely generate, with no decidable equality on `X`
(`three-generators-free`{.AgdaFunction} of [Lattices.Free.Countable][]), so
substitution by them is injective, and it carries the ladder to a strictly
ascending chain of 3-generated sublattices of `FL(X)`
(`ladder-into`{.AgdaFunction}, by `strict-⨟`{.AgdaFunction} of
[DeansProblem.Chain.Condition][]).  Its links are no copies of `FL(3)` either
(`ladder-into-no-copy`{.AgdaFunction}): substitution keeps the inequality
`x ∧ y ≤ w`.

The earlier form `ladder-in`{.AgdaFunction} takes a map `f : Fin 3 → X` with a
map back `g` that undoes it; such an `f` is an injection, and `ladder-in` is
now a use of `ladder-into`.  Substitution by `ℊ ∘ f` is injective when `g`
undoes it (`renaming-injective`{.AgdaFunction}), which is the earlier proof.

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

-- Theorem 4.5 in every free lattice with three distinct generators.
ladder-into : Fin 3 ↣ X → StrictlyAscending 3 X
ladder-into ι = strict-⨟ ladder (three-generators ι)
                         (freelyGenerates→injective (three-generators ι) (three-generators-free ι))

-- No link of the ladder in FL(X) is a copy of FL(3).
ladder-into-no-copy : (ι : Fin 3 ↣ X) → ∀ n (e : proj₁ (FL (Fin 3)) IsSubalgebraOf proj₁ (FL X))
                    → ¬ (copy e ≐ ⟨ StrictlyAscending.links (ladder-into ι) n ⟩)
ladder-into-no-copy ι n = meet-below→no-copy (StrictlyAscending.links (ladder-into ι) n)
                                             ([]-mono (three-generators ι) (link-meet n))

-- The ladder in any free lattice with three generators that a map back separates.
ladder-in : (f : Fin 3 → X) (g : X → Fin 3) → (∀ i → g (f i) ≡ i) → StrictlyAscending 3 X
ladder-in f g gf = ladder-into (mk↣ λ {i} {j} e → trans (sym (gf i)) (trans (cong g e) (gf j)))
```

**Theorem 4.5** of the paper, as one statement.  In `FL(3)`, with
`c = (x ∨ z) ∧ (y ∨ z)` (the paper's `d`) and `Aₖ`, `Bₖ` the rungs of the
ladder over `x`, `y` and `c`, the links `L₂ₖ = ⟨x, y, Aₖ ∨ Bₖ⟩` and
`L₂ₖ₊₁ = ⟨x, y, Aₖ₊₁⟩` form an infinite strictly ascending chain of 3-generated
sublattices, and none of them is a copy of `FL(3)`, the image of an embedding
of `FL(3)` (its first part); so every free lattice with three distinct
generators, `Fin 3 ↣ X`, contains an infinite strictly ascending chain of
3-generated sublattices (its second part).  Here `triple w` is the family
`(x, y, w)` and `E k` is `Aₖ ∨ Bₖ`.

```agda
-- Theorem 4.5: the ladder's links form an infinite strictly ascending chain of 3-generated
-- sublattices of FL(3), none a copy of FL(3); so every free lattice with three distinct
-- generators contains such a chain.
record Theorem-4·5 : Setω where
  field
    part-1 : Σ[ L ∈ StrictlyAscending 3 (Fin 3) ]
                (∀ k → StrictlyAscending.links L (2 * k) ≡ triple (E k))
              × (∀ k → StrictlyAscending.links L (suc (2 * k)) ≡ triple (A (suc k)))
              × (∀ n (e : proj₁ (FL (Fin 3)) IsSubalgebraOf proj₁ (FL (Fin 3)))
                 → ¬ (copy e ≐ ⟨ StrictlyAscending.links L n ⟩))
    part-2 : ∀ {χ} {X : Type χ} → Fin 3 ↣ X → StrictlyAscending 3 X

-- The proof of Theorem 4.5.
theorem-4·5 : Theorem-4·5
theorem-4·5 = record
  { part-1 =  ladder
             , interleave-even (λ k → triple (E k)) (λ k → triple (A (suc k)))
             , interleave-odd (λ k → triple (E k)) (λ k → triple (A (suc k)))
             , no-link-is-a-copy
  ; part-2 = ladder-into
  }
```

--------------------------------------

[DeansProblem.Examples.ChainCondition]: DeansProblem.Examples.ChainCondition.html
[DeansProblem.Chain.Condition]: DeansProblem.Chain.Condition.html
[DeansProblem.Ladder]: DeansProblem.Ladder.html
[DeansProblem.NoChain]: DeansProblem.NoChain.html
[Lattices.Free.Complexity]: Lattices.Free.Complexity.html
[Lattices.Free.Countable]: Lattices.Free.Countable.html
