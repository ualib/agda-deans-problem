---
layout: default
file: "src/DeansProblem/Pigeonhole.lagda.md"
title: "DeansProblem.Pigeonhole module"
date: "2026-10-27"
author: "the agda-lattices development team"
---

### The infinite pigeonhole principle, as an explicit hypothesis

This is the [DeansProblem.Pigeonhole][] module of this repository.

[the paper]: https://arxiv.org/abs/YYMM.NNNNN

The *infinite pigeonhole principle* says that a sequence `u : ℕ → Fin k` takes
some value `i` infinitely often: for every `m` there is `n ≥ m` with
`u n ≡ i`.  Classical logic proves it; Agda's constructive logic does not,
since already for `k = 2` it decides the limited principle of omniscience
(LPO), which the intuitionistic type theory Agda implements under `--safe`
does not prove (`pigeonhole→LPO`{.AgdaFunction}).  Three statements of
[the paper][] rest on it: the coherent form of Theorem C, Corollary 6.4 and
the recurrence of Remark 5.1 ([DeansProblem.Coherent.Infinite][]).  So the
principle is a record (`InfinitePigeonhole`{.AgdaRecord}) that each statement
using it takes as an explicit argument and names in its type, never a
postulate.  The record gives its witnesses as functions, a value `i` and, for
each `m`, an `n ≥ m`; those functions are all the choices the diagonal
argument of Theorem C makes, so no choice principle enters besides the
record.

The module derives the two forms that the transitions of a chain need, as
follows.

+  **Selections**.  A strictly increasing sequence of natural numbers
   represents an infinite set of indices, listed in increasing order; its
   first value is the least element.  The recurrences of a value, a function
   giving for each `m` an occurrence beyond `m`, are read off as such a
   sequence (`occurrences`{.AgdaFunction}).
+  **Tuples of terms covered by a finite list**.  A sequence of `n`-tuples of
   lattice terms, each entry equal to a member of a finite list `L`, is
   constant up to `_≈ʷ_`{.AgdaFunction} along some selection
   (`constant-along`{.AgdaFunction}).  Each tuple is colored by the code that
   `tuple-code`{.AgdaFunction} of [Lattices.Free.Complexity][] gives it, a
   position in `Fin (length L ^ n)` read off the proofs that its entries are
   covered; the principle gives a code taken infinitely often, and equal codes
   give equal tuples (`tuple-code-sound`{.AgdaFunction}), which is all the
   argument uses.  So any proofs of the covering will do, and no canonical
   representative is chosen.

<!--
```agda
{-# OPTIONS --without-K --exact-split --safe #-}

module DeansProblem.Pigeonhole where

open import Agda.Primitive  using () renaming ( Set to Type )

-- Imports from the Agda Standard Library ---------------------------------------
open import Data.Bool.Base                         using ( Bool ; true ; false ; _∨_ )
open import Data.Fin.Base                          using ( Fin ; zero ; suc )
open import Data.List.Base                         using ( List ; length )
open import Data.List.Relation.Unary.Any           using ( Any )
open import Data.Nat.Base                          using ( ℕ ; zero ; suc ; _≤_ ; _<_ ; _^_ ; z≤n )
open import Data.Nat.Properties                    using ( ≤-pred ; m≤n⇒m<n∨m≡n )
open import Data.Product                           using ( Σ-syntax ; _×_ ; _,_ ; proj₁ ; proj₂ )
open import Data.Sum.Base                          using ( _⊎_ ; inj₁ ; inj₂ ; [_,_]′ )
open import Function                               using ( _∘_ )
open import Level                                  using ( Level )
open import Relation.Binary.PropositionalEquality  using ( _≡_ ; refl ; sym ; trans ; subst )

-- Imports from the Agda Universal Algebra Library ------------------------------
open import Lattices.Free.Complexity               using ( tuple-code ; tuple-code-sound )
open import Lattices.Free.Term                     using ( LatTerm )
open import Lattices.Free.Whitman                  using ( _≈ʷ_ )

private variable
  ℓ χ : Level
  X : Type χ
```
-->

#### The principle

```agda
-- The infinite pigeonhole principle: a sequence in Fin k takes some value infinitely often.
record InfinitePigeonhole : Type where
  field
    pigeonhole : (k : ℕ) (u : ℕ → Fin k) → Σ[ i ∈ Fin k ] (∀ m → Σ[ n ∈ ℕ ] m ≤ n × u n ≡ i)
```

#### The principle decides LPO

LPO says that a binary sequence `α` has a `1` or is all `0`.  Color `n` by
whether `α` has a `1` among its first `n + 1` terms (`seen`{.AgdaFunction}).
If the color `1` recurs, some term is `1`.  If the color `0` recurs, then
for every `m` some `n ≥ m` has no `1` up to `n`, so `α m` is `0`.

```agda
private module _ (α : ℕ → Bool) where
  -- Whether α has a 1 among its first n + 1 terms.
  seen : ℕ → Bool
  seen zero     = α zero
  seen (suc n)  = seen n ∨ α (suc n)

  private
    -- A true join has a true side.
    ∨-true : (a b : Bool) → a ∨ b ≡ true → a ≡ true ⊎ b ≡ true
    ∨-true true   _  _  = inj₁ refl
    ∨-true false  b  e  = inj₂ e

    -- A false join has false sides.
    ∨-false : (a b : Bool) → a ∨ b ≡ false → a ≡ false × b ≡ false
    ∨-false false  b  e  = refl , e
    ∨-false true   _  ()

  -- A 1 seen up to n is a 1 of α.
  seen-true : ∀ n → seen n ≡ true → Σ[ i ∈ ℕ ] α i ≡ true
  seen-true zero     e = zero , e
  seen-true (suc n)  e = [ seen-true n , (λ a → suc n , a) ]′ (∨-true (seen n) (α (suc n)) e)

  -- No 1 seen up to n means every term up to n is 0.
  seen-false : ∀ n → seen n ≡ false → ∀ i → i ≤ n → α i ≡ false
  seen-false zero     e zero z≤n  = e
  seen-false (suc n)  e i i≤n     =
    [ (λ i<n → seen-false n (proj₁ f) i (≤-pred i<n))
    , (λ i≡n → subst (λ a → α a ≡ false) (sym i≡n) (proj₂ f)) ]′ (m≤n⇒m<n∨m≡n i≤n)
    where
    -- Neither the earlier terms nor the last one is a 1.
    f : seen n ≡ false × α (suc n) ≡ false
    f = ∨-false (seen n) (α (suc n)) e

private
  -- A binary digit as a color.
  bit : Bool → Fin 2
  bit false  = zero
  bit true   = suc zero

  -- The color 1 is the digit true, and the color 0 the digit false.
  bit-1 : ∀ b → bit b ≡ suc zero → b ≡ true
  bit-1 true   _ = refl
  bit-1 false  ()

  bit-0 : ∀ b → bit b ≡ zero → b ≡ false
  bit-0 false  _ = refl
  bit-0 true   ()

-- The principle decides LPO, so Agda's constructive logic cannot prove it.
pigeonhole→LPO : InfinitePigeonhole → (α : ℕ → Bool) → (Σ[ n ∈ ℕ ] α n ≡ true) ⊎ (∀ n → α n ≡ false)
pigeonhole→LPO P α = decide (InfinitePigeonhole.pigeonhole P 2 (bit ∘ seen α))
  where
  -- Read the recurring color.
  decide : Σ[ i ∈ Fin 2 ] (∀ m → Σ[ n ∈ ℕ ] m ≤ n × bit (seen α n) ≡ i)
         → (Σ[ n ∈ ℕ ] α n ≡ true) ⊎ (∀ n → α n ≡ false)
  decide (zero , rec)      = inj₂ λ m → let (n , m≤n , e) = rec m in seen-false α n (bit-0 (seen α n) e) m m≤n
  decide (suc zero , rec)  = inj₁ (let (n , _ , e) = rec 0 in seen-true α n (bit-1 (seen α n) e))
```

#### Selections

A *selection* is a strictly increasing sequence of natural numbers, given by
its consecutive steps `h t < h (suc t)`; it represents an infinite set of
indices, listed in increasing order, whose least element is its first value.
The occurrences of a recurring property, given as a function that finds one
beyond any `m`, form a selection (`occurrences`{.AgdaFunction}): the
occurrence it finds beyond `0`, then the one it finds beyond the successor of
each, and so on.

```agda
module _ {P : ℕ → Type ℓ} (rec : ∀ m → Σ[ n ∈ ℕ ] m ≤ n × P n) where
  -- The occurrences, in increasing order.
  occurrences : ℕ → ℕ
  occurrences zero     = proj₁ (rec zero)
  occurrences (suc t)  = proj₁ (rec (suc (occurrences t)))

  -- They form a selection.
  occurrences-increasing : ∀ t → occurrences t < occurrences (suc t)
  occurrences-increasing t = proj₁ (proj₂ (rec (suc (occurrences t))))

  -- The property holds at each of them.
  occurrences-hold : ∀ t → P (occurrences t)
  occurrences-hold zero     = proj₂ (proj₂ (rec zero))
  occurrences-hold (suc t)  = proj₂ (proj₂ (rec (suc (occurrences t))))
```

#### Tuples covered by a finite list

```agda
-- A sequence of n-tuples covered by a finite list is constant, up to ≈ʷ, along a selection.
constant-along : InfinitePigeonhole → (L : List (LatTerm X)) (n : ℕ) (u : ℕ → Fin n → LatTerm X)
               → (∀ k i → Any (u k i ≈ʷ_) L)
               → Σ[ h ∈ (ℕ → ℕ) ] (∀ t → h t < h (suc t)) × (∀ t i → u (h t) i ≈ʷ u (h 0) i)
constant-along P L n u cov =
  let (c , rec) = InfinitePigeonhole.pigeonhole P (length L ^ n) code
  in occurrences rec , occurrences-increasing rec
   , λ t → tuple-code-sound L n (u (occurrences rec t)) (u (occurrences rec 0))
                             (cov (occurrences rec t)) (cov (occurrences rec 0))
                             (trans (occurrences-hold rec t) (sym (occurrences-hold rec 0)))
  where
  -- The color of each tuple: its code in the list.
  code : ℕ → Fin (length L ^ n)
  code k = tuple-code L n (u k) (cov k)
```

--------------------------------------

[DeansProblem.Pigeonhole]: DeansProblem.Pigeonhole.html
[DeansProblem.Coherent.Infinite]: DeansProblem.Coherent.Infinite.html
[Lattices.Free.Complexity]: Lattices.Free.Complexity.html
