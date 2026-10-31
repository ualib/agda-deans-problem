---
layout: default
file: "src/DeansProblem/Chain/Limit.lagda.md"
title: "DeansProblem.Chain.Limit module"
date: "2026-10-30"
author: "the agda-lattices development team"
---

### Proposition 4.2: a chain and the direct limit of its self-embeddings

This is the [DeansProblem.Chain.Limit][] module of this repository.

[the paper]: https://arxiv.org/abs/YYMM.NNNNN

Definition 4.1 of [the paper][] fixes, for a chain `L₀ ⊊ L₁ ⊊ ⋯` of copies of
`FL(3)` in `FL(X)`, isomorphisms `φₖ : FL(3) → Lₖ`, and reads the inclusion
`Lₖ ⊆ Lₖ₊₁` as a self-embedding `θₖ = φₖ₊₁⁻¹ ∘ φₖ` of `FL(3)`.  Its
Proposition 4.2 says the following:

+  (a) the union `⋃ₖ Lₖ` is the direct limit of the sequence of maps
   `θₖ : FL(3) → FL(3)`, and it embeds in `FL(X)`;
+  (b) conversely, if `θₖ` are proper self-embeddings of `FL(3)` whose direct
   limit `L` embeds in `FL(X)` by `e`, the images `Lₖ = e(ιₖ(FL(3)))` of the
   canonical maps `ιₖ : FL(3) → L` form a chain.

This module proves both, from the direct limits of agda-lattices
([Lattices.DirectLimit][]) and its unions of chains of sublattices
([Lattices.DirectLimit.Union][]), and states the proposition as one type,
`Proposition-4·2`{.AgdaFunction}.  A chain is a `CopyChain`{.AgdaRecord} of
[DeansProblem.Chain.Copies][]: embeddings `φ k` of `FL(3)` in `FL(X)` whose
copies ascend strictly.  The module imports neither [DeansProblem.NoChain][]
nor [DeansProblem.LengthThree][], directly or through another module, so no
statement here holds because no chain exists.

**The self-embeddings of a chain**.  The library's `step`{.AgdaFunction}
factors each embedding through the next: `copy-θ k`{.AgdaFunction} sends `a`
to an element `b` with `φ (suc k)` at `b` equal to `φ k` at `a`, which exists
because the `k`-th copy lies in the next.  So `φₖ₊₁ ∘ θₖ = φₖ`
(`copy-θ-commutes`{.AgdaFunction}), and since `φₖ₊₁` is injective, any
homomorphisms of `FL(3)` with that property agree with these at every element
(`copy-θ-unique`{.AgdaFunction}): they are the `θₖ` of Definition 4.1.  Each
is injective (`copy-θ-injective`{.AgdaFunction}), and none is onto
(`copy-θ-not-onto`{.AgdaFunction}): if every `b` were `θₖ(a)` for some `a`,
every element `φₖ₊₁(b)` of the next copy would be `φₖ(a)`, in this one, which
strictness forbids.

**(a)**.  The union of the copies is a sublattice of `FL(X)`
(`copyUnion`{.AgdaFunction}).  The `φₖ` form a cocone over the `θₖ`, so they
induce an embedding of the direct limit `copyLimit`{.AgdaFunction} in `FL(X)`
(`copyLimit-embedding`{.AgdaFunction}), which sends `ιₖ(a)` to `φₖ(a)`
(`copyLimit-ι`{.AgdaFunction}) and whose image is the union
(`copyLimit-range`{.AgdaFunction}); so the union is isomorphic to the limit
(`copyUnion≅copyLimit`{.AgdaFunction}).  This is the proof in [the paper][]:
every element of the union lies in some `Lₖ`, and two elements of the limit
with one image in `FL(X)` are equal, because the `φₖ` are injective.

**(b)**.  Fix self-embeddings `θ k` of `FL(3)`, each injective and not onto,
and an embedding `e` of their direct limit in `FL(X)`.  The `k`-th embedding
of the chain is `e ∘ ιₖ` (`limit-φ`{.AgdaFunction}), injective because `ιₖ`
is.  Its copy lies in the next, since `ιₖ = ιₖ₊₁ ∘ θₖ`
(`limit-⊆`{.AgdaFunction}).  And the next does not lie in it
(`limit-⊉`{.AgdaFunction}): if it did, then for every `w` the element
`e(ιₖ₊₁(w))` would be `e(ιₖ(u))` for some `u`, so `ιₖ₊₁(w) = ιₖ(u)` since `e`
is injective, and so `w = θₖ(u)` (the library's
`ι∞-range-step`{.AgdaFunction}); then `θₖ` would be onto.  Strictness in a
`CopyChain`{.AgdaRecord} is the negation of the reverse containment, so the
negation of ontoness is all that (b) needs of properness; the proof in
[the paper][] names an element outside the image of `θₖ`, which asks more.

**The statement**.  In `Proposition-4·2`{.AgdaFunction}, "proper" is injective
and not onto, the Agda Universal Algebra Library's `IsInjective`{.AgdaFunction}
and `IsSurjective`{.AgdaFunction}.  Part (a) names the `θₖ` by the equation of
Definition 4.1, and says that the limit embeds in `FL(X)` by the map that the
`φₖ` induce; part (b) says that the chain's embeddings are `e ∘ ιₖ`, so that
its links are the images `e(ιₖ(FL(3)))`.  Neither part has a hypothesis that
the paper does not, and neither decides anything about `X`.

<!--
```agda
{-# OPTIONS --without-K --exact-split --safe #-}

module DeansProblem.Chain.Limit where

open import Agda.Primitive  using ( Setω ) renaming ( Set to Type )

-- Imports from the Agda Standard Library ---------------------------------------
open import Data.Fin.Base                          using ( Fin )
open import Data.Nat.Base                          using ( ℕ ; suc )
open import Data.Product                           using ( Σ-syntax ; _×_ ; _,_ ; proj₁ ; proj₂ )
open import Function                               using ( Func ; _∘_ )
open import Level                                  using ( Level ; 0ℓ )
open import Relation.Nullary                       using ( ¬_ )
open import Relation.Unary                         using ( _⊆_ ; _≐_ ; ⋃ )

-- Imports from the Agda Universal Algebra Library ------------------------------
open import Classical.Structures.Lattice.Basic     using ( Lattice )
open import Setoid.Functions                       using ( IsInjective ; IsSurjective ; IsInRange
                                                         ; IsInRange→IsInImage ; eq )
open import Setoid.Homomorphisms.Basic             using ( hom )
open import Setoid.Homomorphisms.Isomorphisms      using ( _≅_ )
open import Setoid.Subalgebras.Basic               using ( _≤_ )
open import Setoid.Subalgebras.Properties          using ( ≤-trans )

-- Imports from agda-lattices ---------------------------------------------------
open import Lattices.DirectLimit                   using ( DirectLimit ; ι∞ ; ι∞-cocone ; ι∞-embedding
                                                         ; ι∞-range-step ; limit-extend-embedding )
open import Lattices.DirectLimit.Union             using ( step ; step-commutes ; step-injective
                                                         ; rangeUnion ; rangeUnion≅limit )
open import Lattices.Free.Canonical.Basic          using ( ≈ʷ-refl ; ≈ʷ-sym ; ≈ʷ-trans )
open import Lattices.Free.Term                     using ( LatTerm )
open import Lattices.Free.Universal                using ( FL )
open import Lattices.Free.Whitman                  using ( _≈ʷ_ )

-- Imports from this development ------------------------------------------------
open import DeansProblem.Chain.Copies              using ( CopyChain ; copy ; copy-map )

open Func using ( cong ) renaming ( to to _⟨$⟩_ )

private variable
  χ : Level
```
-->

#### The constant sequence

Every stage of the sequences here is `FL(3)`.

```agda
-- FL(3) at every stage.
FL₃ : ℕ → Lattice 0ℓ 0ℓ
FL₃ _ = FL (Fin 3)
```

#### The self-embeddings of a chain

Fix a chain of copies.  Its `k`-th self-embedding `copy-θ k`{.AgdaFunction} is
the library's factor of `φ k` through `φ (suc k)`.

```agda
module _ {X : Type χ} (c : CopyChain X) where
  open CopyChain c

  -- Each copy lies in the next.
  copy-⊆ : (k : ℕ) → copy (φ k) ⊆ copy (φ (suc k))
  copy-⊆ k = ascends k .proj₁

  -- Definition 4.1's θₖ = φₖ₊₁⁻¹ ∘ φₖ, a self-embedding of FL(3).
  copy-θ : (k : ℕ) → hom (FL (Fin 3) .proj₁) (FL (Fin 3) .proj₁)
  copy-θ = step FL₃ (FL X) φ copy-⊆

  -- φₖ₊₁ ∘ θₖ = φₖ.
  copy-θ-commutes : (k : ℕ) (a : LatTerm (Fin 3))
    → copy-map c (suc k) (copy-θ k .proj₁ ⟨$⟩ a) ≈ʷ copy-map c k a
  copy-θ-commutes = step-commutes FL₃ (FL X) φ copy-⊆

  -- Any homomorphisms with that property agree with these at every element.
  copy-θ-unique : (θ : (k : ℕ) → hom (FL (Fin 3) .proj₁) (FL (Fin 3) .proj₁))
    → (∀ k a → copy-map c (suc k) (proj₁ (θ k) ⟨$⟩ a) ≈ʷ copy-map c k a)
    → ∀ k a → θ k .proj₁ ⟨$⟩ a ≈ʷ copy-θ k .proj₁ ⟨$⟩ a
  copy-θ-unique θ commutes k a =
    proj₂ (φ (suc k)) (≈ʷ-trans (commutes k a) (≈ʷ-sym (copy-θ-commutes k a)))

  -- Each θₖ is injective.
  copy-θ-injective : (k : ℕ) → IsInjective (proj₁ (copy-θ k))
  copy-θ-injective = step-injective FL₃ (FL X) φ copy-⊆
```

None is onto: if every `b` were `θₖ(a)`, the next copy would lie in this one.

```agda
  -- No θₖ is onto.
  copy-θ-not-onto : (k : ℕ) → ¬ IsSurjective (copy-θ k .proj₁)
  copy-θ-not-onto k onto = ascends k .proj₂ ⊇
    where
    -- Every element of the next copy is one of this copy.
    ⊇ : copy (φ (suc k)) ⊆ copy (φ k)
    ⊇ (b , e) with onto {b}
    ... | eq a b≈θa = a , ≈ʷ-trans  (≈ʷ-sym (copy-θ-commutes k a))
                                    (≈ʷ-trans  (cong (φ (suc k) .proj₁ .proj₁)
                                                     (≈ʷ-sym b≈θa))
                                               e)
```

#### Proposition 4.2(a)

The embeddings `φₖ` form a cocone of injective maps over the `θₖ`.  So the
union of the copies is a sublattice of `FL(X)`, carried by `⋃ₖ copy (φ k)`
(the library's `rangeUnion`{.AgdaFunction}), the direct limit of the `θₖ` is
`copyLimit`{.AgdaFunction}, and the embedding of the limit is the one the `φₖ`
induce, whose image is the union.  The library's
`rangeChainUnion≅stepLimit`{.AgdaFunction} says the same, of the limit of its
`step`{.AgdaFunction}; it is not used here, because its type spells the limit
through `step`{.AgdaFunction} and these types spell it through
`copy-θ`{.AgdaFunction}, and Agda matches the two spellings only by unfolding
both limits, at a cost of ten seconds.

```agda
  -- The embeddings of the chain as homomorphisms, and their injectivity.
  copy-hom : (k : ℕ) → hom (FL (Fin 3) .proj₁) (FL X .proj₁)
  copy-hom = proj₁ ∘ φ

  copy-injective : (k : ℕ) → IsInjective (copy-hom k .proj₁)
  copy-injective = proj₂ ∘ φ

  -- The union of the chain, a sublattice of FL(X).
  copyUnion : Lattice χ χ
  copyUnion = rangeUnion FL₃ copy-θ (FL X) copy-hom copy-θ-commutes copy-injective

  -- The direct limit of the θₖ.
  copyLimit : Lattice 0ℓ 0ℓ
  copyLimit = DirectLimit FL₃ copy-θ

  -- The limit embeds in FL(X).
  copyLimit-embedding : copyLimit .proj₁ ≤ FL X .proj₁
  copyLimit-embedding =
    limit-extend-embedding FL₃ copy-θ (FL X) copy-hom copy-θ-commutes copy-injective

  -- The embedding sends ιₖ(a) to φₖ(a).
  copyLimit-ι : (k : ℕ) (a : LatTerm (Fin 3))
    → copyLimit-embedding .proj₁ .proj₁ ⟨$⟩ (ι∞ FL₃ copy-θ k .proj₁ ⟨$⟩ a) ≈ʷ copy-map c k a
  copyLimit-ι k a = ≈ʷ-refl

  -- Its image is the union of the copies.
  copyLimit-range : IsInRange (copyLimit-embedding .proj₁ .proj₁) ≐ ⋃ ℕ (copy ∘ φ)
  copyLimit-range = (λ ((k , a) , e) → k , a , e) , (λ (k , a , e) → (k , a) , e)

  -- The union of the chain is the direct limit of the θₖ.
  copyUnion≅copyLimit : proj₁ copyUnion ≅ proj₁ copyLimit
  copyUnion≅copyLimit = rangeUnion≅limit FL₃ copy-θ (FL X) copy-hom copy-θ-commutes copy-injective
```

#### Proposition 4.2(b)

Fix self-embeddings `θ k` of `FL(3)`, injective and not onto, and an embedding
`e` of their direct limit in `FL(X)`.  The `k`-th embedding of the chain is
`e ∘ ιₖ`.

```agda
module _ {X : Type χ} (θ : (k : ℕ) → hom (FL (Fin 3) .proj₁) (FL (Fin 3) .proj₁))
         (proper : (k : ℕ) → IsInjective (θ k .proj₁) × ¬ IsSurjective (θ k .proj₁))
         (e : DirectLimit FL₃ θ .proj₁ ≤ FL X .proj₁) where

  -- Each θₖ is injective.
  limit-θ-injective : (k : ℕ) → IsInjective (proj₁ (θ k))
  limit-θ-injective = proj₁ ∘ proper

  -- The k-th embedding: e after the canonical map ιₖ.
  limit-φ : ℕ → FL (Fin 3) .proj₁ ≤ FL X .proj₁
  limit-φ k = ≤-trans (ι∞-embedding FL₃ θ limit-θ-injective k) e

  -- Each copy lies in the next, since ιₖ = ιₖ₊₁ ∘ θₖ.
  limit-⊆ : (k : ℕ) → copy (limit-φ k) ⊆ copy (limit-φ (suc k))
  limit-⊆ k (a , y≈) = θ k .proj₁ ⟨$⟩ a , ≈ʷ-trans ( cong  (e .proj₁ .proj₁)
                                                           (ι∞-cocone FL₃ θ k a) ) y≈
```

If the next copy lay in this one, every `w` would be in the image of `θₖ`.

```agda
  -- The next copy does not lie in this one, since θₖ is not onto.
  limit-⊉ : (k : ℕ) → ¬ (copy (limit-φ (suc k)) ⊆ copy (limit-φ k))
  limit-⊉ k ⊇ = proper k .proj₂ onto
    where
    -- Every w is θₖ(u) for some u.
    onto : IsSurjective (θ k .proj₁)
    onto {w} = let (u , eu) = ⊇ (w , ≈ʷ-refl) in
      IsInRange→IsInImage (ι∞-range-step FL₃ θ limit-θ-injective k (u , proj₂ e eu))

  -- The images e(ιₖ(FL(3))) form a chain.
  limit→copyChain : CopyChain X
  limit→copyChain = record
    { φ        = limit-φ
    ; ascends  = λ k → limit-⊆ k , limit-⊉ k
    }

  -- Its k-th embedding is e ∘ ιₖ.
  limit→copyChain-φ : (k : ℕ) (a : LatTerm (Fin 3))
    → copy-map limit→copyChain k a ≈ʷ e .proj₁ .proj₁ ⟨$⟩ (ι∞ FL₃ θ k .proj₁ ⟨$⟩ a)
  limit→copyChain-φ k a = ≈ʷ-refl
```

#### The statement

Proposition 4.2 is one definition whose type is its statement,
`Proposition-4·2`{.AgdaFunction}, and `proposition-4·2`{.AgdaFunction} its
proof.  It quantifies over the level of the generators, so it is a type in
`Setω`, and for each `X` it is the product of its two parts, (a) first.  It is
a definition, not a record with a field for each part, because the positivity
check of a record normalizes the types of its fields, which here unfolds the
construction of the limit, at a cost of two seconds.

```agda
-- Proposition 4.2:
--   (a) the union of a chain is the direct limit of the θₖ, and it embeds in FL(X);
--   (b) proper self-embeddings whose limit embeds in FL(X) by e give a chain,
--       the images e(ιₖ(FL(3))).
Proposition-4·2 : Setω
Proposition-4·2 = ∀ {χ} {X : Type χ}
  → ((c : CopyChain X)
     → Σ[ θ ∈ (∀ k → hom (FL (Fin 3) .proj₁) (FL (Fin 3) .proj₁)) ]
         (∀ k a → copy-map c (suc k) (θ k .proj₁ ⟨$⟩ a) ≈ʷ copy-map c k a)
       × (copyUnion c .proj₁ ≅ DirectLimit FL₃ θ .proj₁)
       × Σ[ e ∈ DirectLimit FL₃ θ .proj₁ ≤ FL X .proj₁ ]
           (∀ k a → e .proj₁ .proj₁ ⟨$⟩ (ι∞ FL₃ θ k .proj₁ ⟨$⟩ a) ≈ʷ copy-map c k a))
  × ((θ : ∀ k → hom (FL (Fin 3) .proj₁) (FL (Fin 3) .proj₁))
     → (∀ k → IsInjective (θ k .proj₁) × ¬ IsSurjective (θ k .proj₁))
     → (e : DirectLimit FL₃ θ .proj₁ ≤ FL X .proj₁)
     → Σ[ c ∈ CopyChain X ]
         (∀ k a → copy-map c k a ≈ʷ e .proj₁ .proj₁ ⟨$⟩ (ι∞ FL₃ θ k .proj₁ ⟨$⟩ a)))

-- The proof of Proposition 4.2.
proposition-4·2 : Proposition-4·2
proposition-4·2 =
    (λ c → copy-θ c , copy-θ-commutes c , copyUnion≅copyLimit c , copyLimit-embedding c , copyLimit-ι c)
  , (λ θ proper e → limit→copyChain θ proper e , limit→copyChain-φ θ proper e)
```

--------------------------------------

[DeansProblem.Chain.Limit]: DeansProblem.Chain.Limit.html
[DeansProblem.Chain.Copies]: DeansProblem.Chain.Copies.html
[DeansProblem.LengthThree]: DeansProblem.LengthThree.html
[DeansProblem.NoChain]: DeansProblem.NoChain.html
[Lattices.DirectLimit]: Lattices.DirectLimit.html
[Lattices.DirectLimit.Union]: Lattices.DirectLimit.Union.html
