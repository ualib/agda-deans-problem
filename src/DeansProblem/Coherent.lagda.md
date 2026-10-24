---
layout: default
file: "src/DeansProblem/Coherent.lagda.md"
title: "DeansProblem.Coherent module"
date: "2026-10-14"
author: "the agda-lattices development team"
---

### Coherent chains and the fixed-sublattice question

This is the [DeansProblem.Coherent][] module of the [agda-lattices][] library.

[the paper]: https://arxiv.org/abs/YYMM.NNNNN

A chain toward Dean's problem ([DeansProblem.Chain][]) is a sequence of freely
generating triples `gens k` in `FL(X)`, each expressed in the next by terms
`terms k` over three generators, with a generator of the next triple outside the
sublattice of the current one.  Composing the terms of consecutive steps gives
the *transition* from the `j`-th link to the `(e + j)`-th
(`transition`{.AgdaFunction}): the self-embedding `θ_{j,e+j}` of `FL(3)` that
reads the inclusion `Lⱼ ⊆ L_{e+j}` through the two isomorphisms with `FL(3)`.
This module proves the one-step form of the coherent-chain theorem: in any
chain, some transition `θ_{j,k}` with `j < k` is a proper self-embedding of
`FL(3)` that fixes a copy of `FL(3)` pointwise
(`chain→fixed-sublattice`{.AgdaFunction}).  The argument has three steps.

1.  **The transitions from the bottom are few**.  Each `θ_{0,k}` expresses
    `gens 0` in `gens k` (`gens≈transition`{.AgdaFunction}), and `gens k` is a
    lattice embedding, which never lowers complexity
    ([Lattices.Free.Complexity][]); so `complexity (θ_{0,k} i)` is at most
    `complexity (gens 0 i)` for every `k` (`transition-bound`{.AgdaFunction}).
    Only finitely many elements of `FL(3)` have bounded complexity, so two of
    the triples `(θ_{0,k} x, θ_{0,k} y, θ_{0,k} z)` agree
    (`transition-repeats`{.AgdaFunction}, by the pigeonhole principle for
    tuples): `θ_{0,j} = θ_{0,k}` for some `j < k`.
2.  **Transitions compose**.  `θ_{0,k} = θ_{j,k} ∘ θ_{0,j}`
    (`transition-⨟`{.AgdaFunction}), so the repeat says that `θ_{j,k}` fixes
    each `θ_{0,j} i`, hence every element of the sublattice `M = θ_{0,j}(FL(3))`
    (`fixes-⟨Θ⟩`{.AgdaFunction}).
3.  **Both are embeddings, and `θ_{j,k}` is not onto**.  A first factor of an
    injective composite is injective (`first-factor-injective`{.AgdaFunction}),
    and `gens 0 = gens j ∘ θ_{0,j}`, `gens j = gens k ∘ θ_{j,k}` up to equality;
    so `θ_{0,j}` and `θ_{j,k}` freely generate (Corollary 1.13 of [Freese, Ježek,
    and Nation (1995)][]).  The last step of the chain before `k` has a fresh
    generator, none of the terms `terms (k - 1) i`; since `θ_{j,k}` is
    `θ_{j,k-1}` followed by `terms (k - 1)`, Corollary 1.6
    (`generator-in-image`{.AgdaFunction}) puts that generator outside the image
    of `θ_{j,k}`.

The conclusion is packaged as a record (`FixedSublattice`{.AgdaRecord}): a
freely generating `θ : Sub (Fin 3) (Fin 3)` that misses a generator, and a
freely generating `Θ` with `Θ i [ θ ] ≈ʷ Θ i` for every `i`.  It is the
configuration of the **fixed-sublattice question**: does `FL(3)` have an
injective endomorphism that is not onto and fixes a sublattice isomorphic to
`FL(3)` pointwise?  By the theorem, a negative answer answers Dean's question
negatively.  A positive answer is a chain of length three inside `FL(3)`,
`M ⊊ θ(FL(3)) ⊊ FL(3)`, whose two steps the record also yields
(`lower-step`{.AgdaFunction}, `upper-step`{.AgdaFunction}): the upper one is
`θ(FL(3)) ⊊ FL(3)` with the missed generator as its fresh index, and the lower
one is `M ⊊ θ(FL(3))`, where `θ` expresses `Θ` in itself by `fixes`, and some
generator is none of the `Θ i`, because otherwise `θ` would fix every
generator and be onto (`Θ-misses`{.AgdaFunction}).

**The coherent form**, which stays in prose.  For a fixed `j` the transitions
`θ_{j,k}`, `k > j`, take finitely many values, by the same bound with `gens j`
in place of `gens 0`; so some value is taken on an infinite set of `k`.  A
diagonal argument (choose `k₀ = 0`, an infinite set `S₀` of indices on which
`θ_{0,k}` is constant, `k₁ = min S₀`, an infinite `S₁ ⊆ S₀` above `k₁` on
which `θ_{k₁,k}` is constant, and so on) passes to a subchain on which
`θ_{kᵢ,kⱼ} = Θᵢ` depends only on `i`, with `Θⱼ ∘ Θᵢ = Θᵢ` for `i < j`.  The
images `Mᵢ = Θᵢ(FL(3))` then form a strictly ascending chain of copies of
`FL(3)` inside `FL(3)`, each `Θⱼ` a non-surjective self-embedding fixing every
earlier `Mᵢ` pointwise; and conversely such a sequence is a chain for Dean's
problem.  So Dean's problem has a positive answer if and only if a coherent
chain exists, and the one-step theorem here is its first link.  This is the
coherent form of Theorem C of [the paper][], Section 6, which gives the
argument in full.

<!--
```agda
{-# OPTIONS --without-K --exact-split --safe #-}

module DeansProblem.Coherent where

open import Agda.Primitive  using () renaming ( Set to Type )

-- Imports from the Agda Standard Library ---------------------------------------
open import Data.Empty                             using ( ⊥-elim )
open import Data.Fin.Base                          using ( Fin ; zero ; suc )
open import Data.Fin.Properties                    using ( _≟_ ; any? ; all? ; ¬∀⟶∃¬ )
open import Data.List.Base                         using ( allFin )
open import Data.List.Membership.Propositional.Properties
                                                   using ( ∈-allFin )
open import Data.Nat.Base                          using ( ℕ ; zero ; suc ; _+_ ; _≤_ ; _<_ ; _⊔_ )
open import Data.Nat.Properties                    using ( ≤-trans ; ≤-reflexive ; +-comm ; +-identityʳ
                                                         ; m≤m⊔n ; m≤n⊔m ; m≤n⇒∃[o]m+o≡n )
open import Data.Product                           using ( Σ-syntax ; ∃ ; _×_ ; _,_ ; proj₁ ; proj₂ )
open import Function                               using ( _∘_ )
open import Level                                  using ( Level )
open import Relation.Binary.Definitions            using ( DecidableEquality )
open import Relation.Binary.PropositionalEquality  using ( _≡_ ; sym ; trans ; cong ; subst
                                                         ; subst₂ )
open import Relation.Nullary                       using ( ¬_ )
open import Relation.Nullary.Decidable.Core        using ( Dec ; yes ; no )

-- Imports from the Agda Universal Algebra Library ------------------------------
open import Lattices.Free.Canonical.Basic          using ( ≈ʷ-refl ; ≈ʷ-sym ; ≈ʷ-trans )
open import DeansProblem.Chain                     using ( Step ; Chain )
open import Lattices.Free.Complexity               using ( complexity ; complexity-resp
                                                         ; complexity-mono ; module Bounded
                                                         ; pigeonhole-≈ⁿ )
open import Lattices.Free.Generation               using ( FreelyGenerates
                                                         ; freelyGenerates→injective
                                                         ; injective→freelyGenerates
                                                         ; generator-in-image )
open import Lattices.Free.Substitution             using ( Sub ; _[_] ; _⨟_ ; []-ℊ ; []-⨟ ; []-cong
                                                         ; []-congʳ ; subst-hom )
open import Lattices.Free.Term                     using ( LatTerm ; ℊ )
open import Lattices.Free.Whitman                  using ( _≈ʷ_ ; module Decision )
open import Setoid.Functions                       using ( IsInjective )

private variable
  ι χ υ : Level
  I : Type ι
  X : Type χ
  Y : Type υ
```
-->

#### Two general facts

Finitely many natural numbers have a common bound (`bound`{.AgdaFunction}), and a
first factor of an injective composite of substitutions is injective
(`first-factor-injective`{.AgdaFunction}): if `ρ i ≈ʷ σ i [ τ ]` for every `i`,
then `s [ ρ ] ≈ʷ s [ σ ] [ τ ]` for every term `s`, so equal images under `σ`
have equal images under `ρ`.  The identity substitution freely generates
(`ℊ-free`{.AgdaFunction}), being injective.

```agda
-- A common bound for finitely many natural numbers.
bound : (n : ℕ) (f : Fin n → ℕ) → Σ[ C ∈ ℕ ] (∀ i → f i ≤ C)
bound zero     f = 0 , λ ()
bound (suc n)  f =
  let (C , b) = bound n (f ∘ suc)
  in f zero ⊔ C , λ { zero → m≤m⊔n _ _ ; (suc i) → ≤-trans (b i) (m≤n⊔m _ _) }

-- A first factor of an injective composite is injective.
first-factor-injective : (σ : Sub I X) (τ : Sub X Y) (ρ : Sub I Y) → (∀ i → ρ i ≈ʷ σ i [ τ ])
                       → IsInjective (proj₁ (subst-hom ρ)) → IsInjective (proj₁ (subst-hom σ))
first-factor-injective σ τ ρ e inj {s} {t} p =
  inj (≈ʷ-trans (through s) (≈ʷ-trans ([]-cong τ p) (≈ʷ-sym (through t))))
  where
  -- ρ is σ followed by τ, on every term.
  through : (w : LatTerm _) → w [ ρ ] ≈ʷ w [ σ ] [ τ ]
  through w = subst (w [ ρ ] ≈ʷ_) ([]-⨟ w σ τ) ([]-congʳ w e)

-- The identity substitution freely generates.
ℊ-free : FreelyGenerates (ℊ {X = X})
ℊ-free = injective→freelyGenerates ℊ λ {s} {t} e → subst₂ _≈ʷ_ ([]-ℊ s) ([]-ℊ t) e
```

#### The transitions of a chain

Fix a chain.  The transition from link `j` over `e` steps
(`transition j e`{.AgdaFunction}) is the identity for `e = 0`, and for `e + 1`
it is the transition over `e` steps followed by the terms of step `e + j`; so it
expresses `gens j` in `gens (e + j)` (`gens≈transition`{.AgdaFunction}), by
induction on `e` through `[]-congʳ`{.AgdaFunction} and `[]-⨟`{.AgdaFunction}.
Transitions compose: the transition from the bottom over `e + d` steps is the one
over `d` steps followed by the one from `d` over `e`
(`transition-⨟`{.AgdaFunction}), by induction on `e`.

```agda
module _ {X : Type χ} (c : Chain X) where
  open Chain c

  -- The terms expressing gens j in gens (e + j): the composite of e consecutive steps.
  transition : ℕ → ℕ → Sub (Fin 3) (Fin 3)
  transition j zero     = ℊ
  transition j (suc e)  = transition j e ⨟ terms (e + j)

  -- The transition expresses the earlier family in the later one.
  gens≈transition : ∀ j e i → gens j i ≈ʷ transition j e i [ gens (e + j) ]
  gens≈transition j zero     i = ≈ʷ-refl
  gens≈transition j (suc e)  i =
    ≈ʷ-trans (gens≈transition j e i)
      (subst (transition j e i [ gens (e + j) ] ≈ʷ_)
             ([]-⨟ (transition j e i) (terms (e + j)) (gens (suc (e + j))))
             ([]-congʳ (transition j e i) (gens≈ (e + j))))

  -- Transitions compose: from the bottom over e + d steps is over d steps, then from d over e.
  transition-⨟ : ∀ d e i → transition 0 (e + d) i ≡ transition 0 d i [ transition d e ]
  transition-⨟ d zero     i = sym ([]-ℊ (transition 0 d i))
  transition-⨟ d (suc e)  i =
    trans (cong (λ m → transition 0 (e + d) i [ terms m ]) (+-identityʳ (e + d)))
          (trans (cong (_[ terms (e + d) ]) (transition-⨟ d e i))
                 (sym ([]-⨟ (transition 0 d i) (transition d e) (terms (e + d)))))
```

#### Bounded complexity and a repeat

Complexity in `FL(3)` uses the decidable equality of `Fin 3`, and in `FL(X)` a
decidable equality of `X`.  The transition from any base `j` over `e` steps
has, on each generator, at most the complexity of the corresponding generator
at that base (`transition-bound′`{.AgdaFunction}): `gens j i` equals
`θ_{j,e+j} i [ gens (e + j) ]`, and `gens (e + j)` is an embedding
(`complexity-mono`{.AgdaFunction}).  The bound from the bottom is
`transition-bound`{.AgdaFunction}.  With a common bound
`C` for the three complexities, every triple `θ_{0,k}` lies in the finite list
`bounded C`{.AgdaFunction} coordinatewise, and the pigeonhole principle for
tuples gives two equal triples (`transition-repeats`{.AgdaFunction}).

```agda
module _ {X : Type χ} (_≟ˣ_ : DecidableEquality X) (c : Chain X) where
  open Chain c
  open Bounded (_≟_ {3}) (allFin 3) ∈-allFin using ( bounded ; bounded-complete )

  private
    -- The complexities in FL(3) and in FL(X).
    κ : LatTerm (Fin 3) → ℕ
    κ = complexity (_≟_ {3})

    κˣ : LatTerm X → ℕ
    κˣ = complexity _≟ˣ_

  -- The transitions from any link are bounded by its generators' complexities.
  transition-bound′ : ∀ j e i → κ (transition c j e i) ≤ κˣ (gens j i)
  transition-bound′ j e i =
    ≤-trans (complexity-mono _≟_ _≟ˣ_ (gens (e + j))
                             (freelyGenerates→injective (gens (e + j)) (gens-free (e + j)))
                             (transition c j e i))
            (≤-reflexive (sym (complexity-resp _≟ˣ_ (gens≈transition c j e i))))

  -- The transitions from the bottom have bounded complexity.
  transition-bound : ∀ k i → κ (transition c 0 k i) ≤ κˣ (gens 0 i)
  transition-bound = transition-bound′ 0

  -- Two transitions from the bottom agree on every generator.
  transition-repeats : Σ[ j ∈ ℕ ] Σ[ k ∈ ℕ ] j < k × (∀ i → transition c 0 j i ≈ʷ transition c 0 k i)
  transition-repeats =
    let (C , C-bound) = bound 3 (λ i → κˣ (gens 0 i))
    in pigeonhole-≈ⁿ (bounded C) 3 (transition c 0)
         (λ k i → bounded-complete C (transition c 0 k i) (≤-trans (transition-bound k i) (C-bound i)))
```

#### The fixed-sublattice configuration

A `FixedSublattice`{.AgdaRecord} is a proper self-embedding `θ` of `FL(3)` and
a copy `Θ(FL(3))` of `FL(3)` that it fixes pointwise.  Since `θ` fixes the
generators `Θ i`, it fixes every element of the sublattice they generate
(`fixes-⟨Θ⟩`{.AgdaFunction}), and the containment `θ(FL(3)) ⊊ FL(3)` is a step
with the identity as its upper family (`upper-step`{.AgdaFunction}).

```agda
-- A proper self-embedding of FL(3) fixing a copy of FL(3) pointwise.
record FixedSublattice : Type where
  field
    θ         : Sub (Fin 3) (Fin 3)
    θ-free    : FreelyGenerates θ
    missed    : Fin 3
    missed∉θ  : ∀ i → ¬ (ℊ missed ≈ʷ θ i)
    Θ         : Sub (Fin 3) (Fin 3)
    Θ-free    : FreelyGenerates Θ
    fixes     : ∀ i → Θ i [ θ ] ≈ʷ Θ i

  -- θ fixes every element of the sublattice Θ generates.
  fixes-⟨Θ⟩ : (t : LatTerm (Fin 3)) → t [ Θ ] [ θ ] ≈ʷ t [ Θ ]
  fixes-⟨Θ⟩ t = subst (_≈ʷ t [ Θ ]) ([]-⨟ t Θ θ) ([]-congʳ t fixes)

  -- The containment θ(FL(3)) ⊊ FL(3), as a step.
  upper-step : Step (Fin 3)
  upper-step = record
    { σ        = θ
    ; τ        = ℊ
    ; σ-free   = θ-free
    ; τ-free   = ℊ-free
    ; p        = θ
    ; σ≈p[τ]   = λ i → subst (θ i ≈ʷ_) (sym ([]-ℊ (θ i))) ≈ʷ-refl
    ; fresh    = missed
    ; fresh∉p  = missed∉θ
    }
```

The lower containment `Θ(FL(3)) ⊊ θ(FL(3))` is a step too
(`lower-step`{.AgdaFunction}).  Its terms are `Θ` itself, by `fixes`, and its
fresh generator is one that is none of the `Θ i`: if every generator `ℊ f` were
some `Θ i`, then `θ` would fix it, `θ f ≈ʷ ℊ f`, against the missed generator
(`Θ-misses`{.AgdaFunction}).  Which generator is missed is decided by Whitman's
procedure in `FL(3)`, one equation per pair of indices.

```agda
module _ (F : FixedSublattice) where
  open FixedSublattice F
  open Decision (_≟_ {3}) using ( _≈ʷ?_ )

  private
    -- If every generator is one of the Θ i, then θ fixes every generator.
    fixed-generator : (∀ f → ∃ λ i → ℊ f ≈ʷ Θ i) → ∀ f → θ f ≈ʷ ℊ f
    fixed-generator all f =
      let (i , e) = all f
      in ≈ʷ-trans ([]-cong θ e) (≈ʷ-trans (fixes i) (≈ʷ-sym e))

    -- The search, on the decision of whether every generator is some Θ i.
    search : Dec (∀ f → ∃ λ i → ℊ f ≈ʷ Θ i) → Σ[ f ∈ Fin 3 ] (∀ i → ¬ (ℊ f ≈ʷ Θ i))
    search (yes all)   = ⊥-elim (missed∉θ missed (≈ʷ-sym (fixed-generator all missed)))
    search (no ¬all)   =
      let (f , ¬∃) = ¬∀⟶∃¬ 3 _ (λ f → any? (λ i → ℊ f ≈ʷ? Θ i)) ¬all
      in f , λ i e → ¬∃ (i , e)

  -- Some generator of FL(3) is none of the Θ i.
  Θ-misses : Σ[ f ∈ Fin 3 ] (∀ i → ¬ (ℊ f ≈ʷ Θ i))
  Θ-misses = search (all? (λ f → any? (λ i → ℊ f ≈ʷ? Θ i)))

  -- The containment Θ(FL(3)) ⊊ θ(FL(3)), as a step.
  lower-step : Step (Fin 3)
  lower-step = record
    { σ        = Θ
    ; τ        = θ
    ; σ-free   = Θ-free
    ; τ-free   = θ-free
    ; p        = Θ
    ; σ≈p[τ]   = λ i → ≈ʷ-sym (fixes i)
    ; fresh    = proj₁ Θ-misses
    ; fresh∉p  = proj₂ Θ-misses
    }
```

#### The one-step theorem

From the repeat `θ_{0,j} = θ_{0,k}`, write `k = (o + 1) + j`.  Then `θ_{j,k}`,
the transition from `j` over `o + 1` steps, is the `θ` of the configuration and
`θ_{0,j}` its `Θ`: the composition law turns the repeat into
`Θ i [ θ ] ≈ʷ Θ i`; both freely generate, as first factors of the injective
`gens 0` and `gens j`; and the fresh generator of step `o + j`, the last step
before `k`, is none of the `θ i`, by Corollary 1.6 applied to the last factor
`terms (o + j)` of `θ`.

```agda
module _ {X : Type χ} (_≟ˣ_ : DecidableEquality X) (c : Chain X) where
  open Chain c

  -- Every chain has a transition that is a proper self-embedding fixing a copy of FL(3).
  chain→fixed-sublattice : FixedSublattice
  chain→fixed-sublattice =
    let (j , k , j<k , e) = transition-repeats _≟ˣ_ c
        (o , j+o≡k) = m≤n⇒∃[o]m+o≡n j<k
        k≡ : k ≡ suc o + j
        k≡ = trans (sym j+o≡k) (cong suc (+-comm j o))
    in record
      { θ         = transition c j (suc o)
      ; θ-free    = injective→freelyGenerates _
                      (first-factor-injective (transition c j (suc o)) (gens (suc o + j)) (gens j)
                                              (gens≈transition c j (suc o))
                                              (freelyGenerates→injective (gens j) (gens-free j)))
      ; missed    = fresh (o + j)
      ; missed∉θ  = λ i e' →
                      let (i' , e″) = generator-in-image (terms (o + j)) (transition c j o i) e'
                      in fresh∉ (o + j) i' e″
      ; Θ         = transition c 0 j
      ; Θ-free    = injective→freelyGenerates _
                      (first-factor-injective (transition c 0 j) (gens (j + 0)) (gens 0)
                                              (gens≈transition c 0 j)
                                              (freelyGenerates→injective (gens 0) (gens-free 0)))
      ; fixes     = λ i → subst (_≈ʷ transition c 0 j i)
                                (trans (cong (λ m → transition c 0 m i) k≡) (transition-⨟ c j (suc o) i))
                                (≈ʷ-sym (e i))
      }
```
