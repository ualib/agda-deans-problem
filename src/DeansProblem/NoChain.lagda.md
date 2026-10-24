---
layout: default
file: "src/DeansProblem/NoChain.lagda.md"
title: "DeansProblem.NoChain module"
date: "2026-10-14"
author: "the agda-lattices development team"
---

### No infinite ascending chain of copies of FL(3)

This is the [DeansProblem.NoChain][] module of the [agda-lattices][] library.

Theorem H says that no free lattice contains an infinite strictly ascending
chain of copies of `FL(3)`.  Here the ambient generators have decidable
equality, as required to compute their canonical forms and complexities.
There is no uniform bound on the complexities of the chain's links, and no
classical principle is used.  The theorem is proved for the record
`Chain`{.AgdaRecord} of [DeansProblem.Chain][] (`no-chain`{.AgdaFunction})
and then, through the equivalence of [DeansProblem.Chain.Copies][], for
chains of copies as the problem states them
(`no-copy-chain`{.AgdaFunction}).

The proof replaces the infinite pigeonhole principle by finite searches and
induction on the number of codes for the transitions from the bottom.
Within any increasing subsequence, a finite search escapes a chosen code:
otherwise two transitions from its base agree, giving the four links that
[DeansProblem.LengthThree][] forbids.  Iterating those searches gives a
subsequence omitting that code.  Removing one color from a finite set and
repeating cannot continue past the empty set.

<!--
```agda
{-# OPTIONS --without-K --exact-split --safe #-}

module DeansProblem.NoChain where

open import Agda.Primitive using () renaming ( Set to Type )
open import Data.Empty using ( ⊥ ; ⊥-elim )
open import Data.Fin.Base using ( Fin ; toℕ ; punchOut )
open import Data.Fin.Properties using ( punchOut-injective ; _≟_ ; ¬∀⟶∃¬ )
open import Data.List.Base using ( length ; allFin )
open import Data.List.Membership.Propositional.Properties using ( ∈-allFin )
open import Data.List.Relation.Unary.Any using ( Any )
open import Data.Nat.Base
  using ( ℕ ; zero ; suc ; _+_ ; _∸_ ; _^_ ; _<_ ; _≤_ ; s≤s )
open import Data.Nat.Properties
  using ( <-trans ; +-comm ; m≤n⇒∃[o]m+o≡n ; +-identityʳ
        ; ≤-refl ; ≤-trans ; <⇒≤ ; ∸-monoˡ-< ; n∸n≡0 ; m∸n+n≡m
        ; n<1+n ; m≤m+n ; m≤n+m ; +-monoˡ-< )
open import Data.Product using ( Σ-syntax ; _×_ ; _,_ ; proj₁ ; proj₂ )
open import Level using ( Level )
open import Relation.Binary.Definitions using ( DecidableEquality )
open import Relation.Binary.PropositionalEquality
  using ( _≡_ ; _≢_ ; sym ; trans ; cong ; subst )

open import DeansProblem.Chain using ( Chain )
open import DeansProblem.Chain.Copies using ( CopyChain ; copyChain→chain )
open import DeansProblem.Coherent using ( transition ; transition-bound′ ; bound )
open import DeansProblem.Coherent.Finite using ( four-links→coherent₃ )
open import Lattices.Free.Complexity
  using ( complexity ; module Bounded ; tuple-code ; tuple-code-sound
        ; finite-pigeonhole-≈ⁿ )
open import DeansProblem.LengthThree using ( no-coherent₃ )
open import Lattices.Free.Whitman using ( _≈ʷ_ )

private variable
  χ : Level
  X : Type χ
```
-->

#### Removing a color by finite searches

An increasing map of natural numbers selects a subsequence.  The property
`Escapes`{.AgdaFunction} supplies, in every such subsequence and beyond any
position, a value different from the value at a chosen position.  It is
stronger than the negation of recurrence: it supplies the next position.

```agda
-- Strictly increasing maps of the natural numbers.
Increasing : (ℕ → ℕ) → Type
Increasing h = ∀ {i j} → i < j → h i < h j

-- Consecutive strict increases give a strictly increasing map.
steps-increasing : (h : ℕ → ℕ) → (∀ k → h k < h (suc k)) → Increasing h
steps-increasing h step {i} {j} i<j =
  let (d , eq) = m≤n⇒∃[o]m+o≡n i<j
      -- Read the larger index as a positive offset from the smaller one.
      j≡ : j ≡ suc d + i
      j≡ = trans (sym eq) (cong suc (+-comm i d))
  in subst (λ k → h i < h k) (sym j≡) (offset i d)
  where
  -- Every positive offset increases the value.
  offset : ∀ k d → h k < h (suc d + k)
  offset k zero = step k
  offset k (suc d) = <-trans (offset k d) (step (suc d + k))

-- Every subsequence constructively escapes each of its values arbitrarily late.
Escapes : {n : ℕ} → (ℕ → Fin n) → Type
Escapes u = (h : ℕ → ℕ) → Increasing h → (j m : ℕ)
          → Σ[ k ∈ ℕ ] m < k × u (h j) ≢ u (h k)

-- A finite color set admits no sequence with this hereditary escape property.
finite-colors-exhausted : (n : ℕ) (u : ℕ → Fin n) → Escapes u → ⊥
finite-colors-exhausted zero u E = ⊥-elim (empty (u 0))
  where
  -- The empty color set has no first entry.
  empty : Fin 0 → ⊥
  empty ()
finite-colors-exhausted (suc n) u E =
  finite-colors-exhausted n reduced reduced-escapes
  where
  -- A finite search finds another value after any position.
  next : (m : ℕ) → Σ[ k ∈ ℕ ] m < k × u 0 ≢ u k
  next = E (λ k → k) (λ p → p) 0

  -- Iterate those searches to omit the first color.
  skip : ℕ → ℕ
  skip zero = proj₁ (next 0)
  skip (suc k) = proj₁ (next (skip k))

  -- Each search advances strictly.
  skip-step : ∀ k → skip k < skip (suc k)
  skip-step k = proj₁ (proj₂ (next (skip k)))

  -- The selected positions form a subsequence.
  skip-increasing : Increasing skip
  skip-increasing = steps-increasing skip skip-step

  -- The first color is absent from every selected position.
  skip-avoids : ∀ k → u 0 ≢ u (skip k)
  skip-avoids zero = proj₂ (proj₂ (next 0))
  skip-avoids (suc k) = proj₂ (proj₂ (next (skip k)))

  -- Delete the omitted color from the finite carrier.
  reduced : ℕ → Fin n
  reduced k = punchOut (skip-avoids k)

  -- Escaping is inherited by every subsequence of the reduced sequence.
  reduced-escapes : Escapes reduced
  reduced-escapes h inc j m =
    let (k , m<k , different) =
          E (λ t → skip (h t)) (λ p → skip-increasing (inc p)) j m
    in k , m<k , λ eq →
       different (punchOut-injective (skip-avoids (h j))
                                     (skip-avoids (h k)) eq)
```

#### The four-link obstruction at arbitrary indices

The four-link theorem uses positive offsets.  First express its obstruction
with those offsets, then with absolute indices.  Only the later link must
repeat the bottom transition at `j`; the earlier link need not do so.  The
existing theorem allows `j = 0` as well.

```agda
module _ (_≟ˣ_ : DecidableEquality X) (c : Chain X) where

  -- Two equal transitions from j cannot end at a later recurrence of its bottom value.
  no-repeated-offsets : (j e f : ℕ) → 0 < e → e < f
    → (∀ v → transition c 0 j v ≈ʷ transition c 0 (f + j) v)
    → (∀ v → transition c j e v ≈ʷ transition c j f v) → ⊥
  no-repeated-offsets j e f positive e<f E F =
    let (d₂ , eq₂) = m≤n⇒∃[o]m+o≡n positive
        (d₃ , eq₃) = m≤n⇒∃[o]m+o≡n e<f
        -- The first offset is positive.
        e≡ : e ≡ suc d₂
        e≡ = sym eq₂
        -- The later offset adds a further positive gap.
        f≡ : f ≡ suc d₃ + suc d₂
        f≡ = trans (sym eq₃)
                    (trans (cong suc (+-comm e d₃)) (cong (suc d₃ +_) e≡))
        -- The later bottom transition repeats the value at j.
        H₁ : ∀ v → transition c 0 j v
                  ≈ʷ transition c 0 (suc d₃ + suc d₂ + j) v
        H₁ v = subst (λ n → transition c 0 j v ≈ʷ transition c 0 (n + j) v)
                     f≡ (E v)
        -- The transitions from j agree, in the theorem's offset convention.
        H₂ : ∀ v → transition c (j + 0) (suc d₂) v
                  ≈ʷ transition c (j + 0) (suc d₃ + suc d₂) v
        H₂ v = subst (λ a → transition c a (suc d₂) v
                          ≈ʷ transition c a (suc d₃ + suc d₂) v)
                     (sym (+-identityʳ j))
                 (subst (λ n → transition c j (suc d₂) v ≈ʷ transition c j n v)
                        f≡ (subst (λ n → transition c j n v ≈ʷ transition c j f v)
                                  e≡ (F v)))
    in no-coherent₃ (four-links→coherent₃ _≟ˣ_ c 0 j d₂ d₃ H₁ H₂)

  -- The same obstruction in absolute indices, with subtraction justified by j < k < l.
  no-repeated-transitions : (j k l : ℕ) → j < k → k < l
    → (∀ v → transition c 0 j v ≈ʷ transition c 0 l v)
    → (∀ v → transition c j (k ∸ j) v ≈ʷ transition c j (l ∸ j) v) → ⊥
  no-repeated-transitions j k l j<k k<l E F =
    no-repeated-offsets j (k ∸ j) (l ∸ j)
      (subst (_< k ∸ j) (n∸n≡0 j) (∸-monoˡ-< j<k ≤-refl))
      (∸-monoˡ-< k<l (<⇒≤ j<k))
      (λ v → subst (λ n → transition c 0 j v ≈ʷ transition c 0 n v)
                    (sym (m∸n+n≡m (<⇒≤ (<-trans j<k k<l)))) (E v)) F
```

#### Finite bounds and finite escapes

For each base `j`, `generator-bound j` bounds the complexities of the three
generators at link `j`, and `code-count j`, which is
`length (bounded (generator-bound j)) ^ 3`, is the number of codes available
to the transitions from `j`, an upper bound for the number of their values.
Both depend on the chain; no bound is uniform.  With the four-link
obstruction, the finite pigeonhole rules out `code-count j + 1` later links
whose bottom code is the code at `j` (`recurrences-bounded`{.AgdaFunction}).
Inside any increasing subsequence, a finite search over that many positions
therefore finds a different code beyond any given position
(`chain-escapes`{.AgdaFunction}): the hereditary escape property.

```agda
module _ (_≟ˣ_ : DecidableEquality X) (c : Chain X) where
  open Chain c using ( gens )
  open Bounded (_≟_ {3}) (allFin 3) ∈-allFin
    using ( bounded ; bounded-complete )

  -- A common complexity bound for the generators at one link.
  generator-bound : ℕ → ℕ
  generator-bound j = proj₁ (bound 3 (λ v → complexity _≟ˣ_ (gens j v)))

  -- Each generator satisfies that common bound.
  generators-bounded : ∀ j v → complexity _≟ˣ_ (gens j v) ≤ generator-bound j
  generators-bounded j = proj₂ (bound 3 (λ v → complexity _≟ˣ_ (gens j v)))

  -- The number of codes for the transitions from j, a computable upper bound
  -- for the number of their values.
  code-count : ℕ → ℕ
  code-count j = length (bounded (generator-bound j)) ^ 3

  -- Every transition coordinate has a representative in the bounded list.
  transition-covered : ∀ j e v
                     → Any (transition c j e v ≈ʷ_) (bounded (generator-bound j))
  transition-covered j e v =
    bounded-complete (generator-bound j) (transition c j e v)
      (≤-trans (transition-bound′ _≟ˣ_ c j e v) (generators-bounded j v))

  -- Encode the transitions from the bottom in one fixed finite carrier.
  bottom-color : ℕ → Fin (code-count 0)
  bottom-color k = tuple-code (bounded (generator-bound 0)) 3 (transition c 0 k)
                              (transition-covered 0 k)

  -- A repeated color is a componentwise equivalent bottom transition.
  bottom-color-sound : ∀ {j k} → bottom-color j ≡ bottom-color k
                    → ∀ v → transition c 0 j v ≈ʷ transition c 0 k v
  bottom-color-sound {j} {k} =
    tuple-code-sound (bounded (generator-bound 0)) 3
                     (transition c 0 j) (transition c 0 k)
                     (transition-covered 0 j) (transition-covered 0 k)

  -- Too many later recurrences give the forbidden four links.
  recurrences-bounded : (j : ℕ) (links : Fin (suc (code-count j)) → ℕ)
    → (∀ i → j < links i)
    → (∀ {i k} → toℕ i < toℕ k → links i < links k)
    → (∀ i → bottom-color j ≡ bottom-color (links i)) → ⊥
  recurrences-bounded j links later inc same =
    let (i , k , i<k , E) =
          finite-pigeonhole-≈ⁿ (bounded (generator-bound j)) 3
            (n<1+n (code-count j))
            (λ i → transition c j (links i ∸ j))
            (λ i → transition-covered j (links i ∸ j))
    in no-repeated-transitions _≟ˣ_ c j (links i) (links k)
         (later i) (inc i<k) (bottom-color-sound {j} {links k} (same k)) E

  -- A bounded search escapes a chosen color inside any increasing subsequence.
  chain-escapes : Escapes bottom-color
  chain-escapes h inc j m =
    let (i , different) =
          ¬∀⟶∃¬ (suc (code-count (h j)))
            (λ i → bottom-color (h j) ≡ bottom-color (h (position i)))
            (λ i → bottom-color (h j) ≟ bottom-color (h (position i)))
            (recurrences-bounded (h j) (λ i → h (position i))
              (λ i → inc (after-base i))
              (λ p → inc (s≤s (+-monoˡ-< (j + m) p))))
    in position i , after-bound i , different
    where
    -- A finite window lying strictly after both j and m.
    position : Fin (suc (code-count (h j))) → ℕ
    position i = suc (toℕ i + (j + m))

    -- Every position in the window is after the chosen base.
    after-base : ∀ i → j < position i
    after-base i = s≤s (≤-trans (m≤m+n j m) (m≤n+m (j + m) (toℕ i)))

    -- Every position in the window is beyond the requested bound.
    after-bound : ∀ i → m < position i
    after-bound i = s≤s (≤-trans (m≤n+m m j) (m≤n+m (j + m) (toℕ i)))
```

#### Theorem H

Apply the finite-color induction to the codes of the transitions from the
bottom.  It uses only a finite pigeonhole at each selected base and
primitive recursion to iterate the finite searches: it selects no infinitely
recurring value, and it needs neither excluded middle nor a choice
principle.  The module is checked under `--safe`, so no postulate enters
either.

The hypothesis on `X` is decidable equality, not finiteness, and it is what
complexity costs: the canonical form of a term over `X`, and with it the
term's complexity, is computed by comparing generators.  It is also the
hypothesis of `no-chain-recurs`{.AgdaFunction}.  In classical mathematics
every set has decidable equality, so there the theorem covers every free
lattice `FL(X)`.

```agda
-- No free lattice over generators with decidable equality admits such a chain.
no-chain : (_≟ˣ_ : DecidableEquality X) → Chain X → ⊥
no-chain _≟ˣ_ c =
  finite-colors-exhausted (code-count _≟ˣ_ c 0) (bottom-color _≟ˣ_ c)
                        (chain-escapes _≟ˣ_ c)
```

#### Theorem H for chains of copies

A chain as the problem states it is a sequence of sublattices of `FL(X)`,
each isomorphic to `FL(3)`, each properly contained in the next.  In the
library's terms (the record `CopyChain`{.AgdaRecord} of
[DeansProblem.Chain.Copies][]) it is a sequence of embeddings
`FL(3) ≤ FL(X)`, injective homomorphisms in the sense of
[Setoid.Subalgebras.Basic][], whose images ascend strictly.  Such a chain
gives the record `Chain`{.AgdaRecord} (`copyChain→chain`{.AgdaFunction}),
with no hypothesis on `X`, so Theorem H as stated follows
(`no-copy-chain`{.AgdaFunction}).  Decidable equality on `X` remains its one
hypothesis, and it enters only through `no-chain`{.AgdaFunction}.

```agda
-- Theorem H: no free lattice over generators with decidable equality contains
-- an infinite strictly ascending chain of copies of FL(3).
no-copy-chain : (_≟ˣ_ : DecidableEquality X) → CopyChain X → ⊥
no-copy-chain _≟ˣ_ c = no-chain _≟ˣ_ (copyChain→chain c)
```
