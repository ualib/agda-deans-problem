---
layout: default
file: "src/DeansProblem/Chain/Copies.lagda.md"
title: "DeansProblem.Chain.Copies module"
date: "2026-10-15"
author: "the agda-lattices development team"
---

### Chains of copies of FL(3)

This is the [DeansProblem.Chain.Copies][] module of the [agda-lattices][] library.

[the paper]: https://arxiv.org/abs/YYMM.NNNNN

Dean's problem asks whether a free lattice `FL(X)` can contain an infinite
strictly ascending chain `L₀ ⊊ L₁ ⊊ L₂ ⊊ ⋯` of sublattices, each isomorphic to
`FL(3)`.  [DeansProblem.Chain][] records such a chain by its free generating
triples (`Chain`{.AgdaRecord}): the images of the three generators at each
link, the terms that express each triple in the next, and a fresh generator for
each step.  This module states the chain as the problem does, as a sequence of
copies of `FL(3)` in `FL(X)` (`CopyChain`{.AgdaRecord}), and proves the two
records equivalent: each gives the other, with no hypothesis on `X`
(`copyChain→chain`{.AgdaFunction} and `chain→copyChain`{.AgdaFunction}), and
the round trips return the same chain.  [DeansProblem.NoChain][] states
Theorem H for chains of copies as a corollary.

**A copy of `FL(3)` is the image of an embedding**.  A sublattice `L` of
`FL(X)` with an isomorphism `φ : FL(3) → L` gives an injective lattice
homomorphism `FL(3) → FL(X)`, `φ` followed by the inclusion, whose image is
`L`; and the image of an injective homomorphism `FL(3) → FL(X)` is a sublattice
of `FL(X)` isomorphic to `FL(3)`.  The library's subalgebra relation
`_≤_`{.AgdaFunction} of [Setoid.Subalgebras.Basic][] is exactly such an
embedding: an inhabitant of `FL(3) ≤ FL(X)` is a homomorphism together with a
proof that its underlying map is injective.  The copy that an embedding names
(`copy`{.AgdaFunction}) is its image, the predicate on `FL(X)` of being equal
to a value of the map (`IsInRange`{.AgdaFunction} of [Setoid.Functions][]).  So
a chain as Section 4 of [the paper][] defines it, sublattices `Lₖ` of `FL(X)`
with fixed isomorphisms `φₖ : FL(3) → Lₖ`, is a sequence of embeddings `φₖ`
whose copies ascend strictly, and that is the record `CopyChain`{.AgdaRecord}.

**Strictness**.  Strict containment is the standard library's
`_⊂_`{.AgdaFunction}: `P ⊂ Q` is `P ⊆ Q` together with `¬ (Q ⊆ P)`.  Given
`Lₖ ⊆ Lₖ₊₁`, the negation of the reverse containment is equivalent to
`Lₖ ≠ Lₖ₊₁`, the negation of the equality of the two sets
(`⊉⇔≠`{.AgdaFunction}), and it is the weakest constructive form of
strictness: it does not ask for an element of `Lₖ₊₁` outside `Lₖ`.  The
containment `Lₖ ⊆ Lₖ₊₁` is asked of every element, with its witness.  So the
record asks no more than the definition does.

<!--
```agda
{-# OPTIONS --without-K --exact-split --safe #-}

module DeansProblem.Chain.Copies where

open import Agda.Primitive  using () renaming ( Set to Type )

-- Imports from the Agda Standard Library ---------------------------------------
open import Data.Empty                             using ( ⊥-elim )
open import Data.Fin.Base                          using ( Fin )
open import Data.Fin.Properties                    using ( _≟_ ; any? ; all? ; ¬∀⟶∃¬ )
open import Data.Nat.Base                          using ( ℕ ; suc )
open import Data.Product                           using ( Σ-syntax ; _×_ ; _,_ ; proj₁ ; proj₂ )
open import Function                               using ( Func ; _∘_ ; _⇔_ ; mk⇔ )
open import Level                                  using ( Level ; _⊔_ )
open import Relation.Binary.PropositionalEquality  using ( _≡_ ; refl )
open import Relation.Nullary                       using ( ¬_ ; Dec ; yes ; no )
open import Relation.Unary                         using ( Pred ; _⊆_ ; _⊂_ ; _≐_ )

import Relation.Binary.Reasoning.Setoid as SetoidReasoning

-- Imports from the Agda Universal Algebra Library ------------------------------
open import Lattices.Free.Canonical.Basic          using ( ≈ʷ-refl ; ≈ʷ-sym ; ≈ʷ-trans )
open import DeansProblem.Chain                     using ( Chain ; module Chain ; ⟨σ⟩⊆⟨τ⟩
                                                         ; fresh∉⟨σ⟩ )
open import Lattices.Free.Generation               using ( FreelyGenerates ; freelyGenerates→≤
                                                         ; injective→freelyGenerates )
open import Lattices.Free.Substitution             using ( Sub ; _[_] ; _⨟_ ; []-⨟ ; []-cong
                                                         ; []-congʳ ; subst-hom ; restriction
                                                         ; hom-induced )
open import Lattices.Free.Term                     using ( LatTerm ; ℊ )
open import Lattices.Free.Universal                using ( FL ; FL-setoid )
open import Lattices.Free.Whitman                  using ( _≈ʷ_ ; module Decision )
open import Setoid.Functions                       using ( IsInjective ; IsInRange )
open import Setoid.Homomorphisms.Basic             using ( hom )
open import Setoid.Subalgebras.Basic               using ( _≤_ )

open Func using () renaming ( to to _⟨$⟩_ )

private variable
  ι χ ℓ₁ ℓ₂ : Level
  A : Type ι
  I : Type ι
  X : Type χ
```
-->

#### Copies and strictness

The copy that an embedding `FL(I) ≤ FL(X)` names is its image
(`copy`{.AgdaFunction}).  Given containment, not containing back is the same as
not being equal (`⊉⇔≠`{.AgdaFunction}), for predicates on any type.

```agda
-- The copy of FL(I) that an embedding names: its image, a predicate on FL(X).
copy : {I : Type ι} {X : Type χ} → proj₁ (FL I) ≤ proj₁ (FL X) → Pred (LatTerm X) (ι ⊔ χ)
copy e = IsInRange (proj₁ (proj₁ e))

-- Given P ⊆ Q, the negation of Q ⊆ P is the negation of P = Q.
⊉⇔≠ : {P : Pred A ℓ₁} {Q : Pred A ℓ₂} → P ⊆ Q → (¬ (Q ⊆ P)) ⇔ (¬ (P ≐ Q))
⊉⇔≠ P⊆Q = mk⇔ (λ Q⊈P P≐Q → Q⊈P (λ {x} → proj₂ P≐Q {x}))
               (λ P≠Q Q⊆P → P≠Q ((λ {x} → P⊆Q {x}) , λ {x} → Q⊆P {x}))
```

#### Chains of copies

A `CopyChain`{.AgdaRecord} is a sequence of embeddings `φ k` of `FL(3)` in
`FL(X)` whose copies ascend strictly.

```agda
-- An infinite strictly ascending chain of copies of FL(3) in FL(X).
record CopyChain (X : Type χ) : Type χ where
  field
    φ        : ℕ → proj₁ (FL (Fin 3)) ≤ proj₁ (FL X)
    ascends  : ∀ k → copy (φ k) ⊂ copy (φ (suc k))
```

#### Embeddings of free lattices are free triples

An injective homomorphism `h : FL(I) → FL(X)` agrees on every term with
substitution by its restriction to the generators (`hom-induced`{.AgdaFunction}),
so that substitution is injective too
(`restriction-injective`{.AgdaFunction}), and by Corollary 1.13 the
restriction freely generates (`≤→freelyGenerates`{.AgdaFunction}).  This is the
converse of `freelyGenerates→≤`{.AgdaFunction} of [Lattices.Free.Generation][].

```agda
-- An injective homomorphism out of FL(I) makes substitution by its restriction injective.
restriction-injective : (h : hom (proj₁ (FL I)) (proj₁ (FL X))) → IsInjective (proj₁ h)
                      → IsInjective (proj₁ (subst-hom (restriction h)))
restriction-injective h inj {s} {t} e =
  inj (≈ʷ-trans (hom-induced h s) (≈ʷ-trans e (≈ʷ-sym (hom-induced h t))))

-- The images of the generators under an embedding freely generate.
≤→freelyGenerates : (e : proj₁ (FL I) ≤ proj₁ (FL X)) → FreelyGenerates (restriction (proj₁ e))
≤→freelyGenerates (h , inj) = injective→freelyGenerates (restriction h) (restriction-injective h inj)
```

#### From copies to the record

Fix a chain of copies.  Its `k`-th triple is the restriction of `φ k` to the
generators (`copy-gens`{.AgdaFunction}), and `φ k` is substitution by it, up
to equality in `FL(X)` (`copy-φ≈`{.AgdaFunction}).  Containment at an element
`a` of `FL(3)` gives a term `b` with `φ (suc k)` at `b` equal to `φ k` at `a`
(`copy-lift`{.AgdaFunction}); at the generator `ℊ i`, that `b` is the `i`-th
term of the `k`-th step (`copy-terms`{.AgdaFunction}), and it expresses the
`k`-th triple in the next (`copy-gens≈`{.AgdaFunction}).

```agda
module _ (c : CopyChain X) where
  open CopyChain c
  open SetoidReasoning (FL-setoid X)

  -- The k-th embedding's underlying map.
  copy-map : ℕ → LatTerm (Fin 3) → LatTerm X
  copy-map k a = proj₁ (proj₁ (φ k)) ⟨$⟩ a

  -- The k-th triple: the images of the generators.
  copy-gens : ℕ → Sub (Fin 3) X
  copy-gens k = restriction (proj₁ (φ k))

  -- The k-th embedding is substitution by the k-th triple.
  copy-φ≈ : ∀ k a → copy-map k a ≈ʷ a [ copy-gens k ]
  copy-φ≈ k = hom-induced (proj₁ (φ k))

  -- Containment, element by element.
  copy-lift : ∀ k a → Σ[ b ∈ LatTerm (Fin 3) ] copy-map (suc k) b ≈ʷ copy-map k a
  copy-lift k a = proj₁ (ascends k) (a , ≈ʷ-refl)

  -- The terms of the k-th step: the generators of the k-th copy, named in the next.
  copy-terms : ℕ → Sub (Fin 3) (Fin 3)
  copy-terms k i = proj₁ (copy-lift k (ℊ i))

  -- The terms express each triple in the next.
  copy-gens≈ : ∀ k i → copy-gens k i ≈ʷ copy-terms k i [ copy-gens (suc k) ]
  copy-gens≈ k i = ≈ʷ-trans (≈ʷ-sym (proj₂ (copy-lift k (ℊ i)))) (copy-φ≈ (suc k) (copy-terms k i))
```

Suppose every generator `ℊ g` of `FL(3)` is equal to one of the terms,
`copy-terms k (i g)`.  Then the next copy lies in this one
(`covered→⊇`{.AgdaFunction}): for every term `b`, the element `a = b [ ℊ ∘ i ]`
has `φ k` at `a` equal to `φ (suc k)` at `b`, by the following computation.
Substitution by `ℊ ∘ i` and then by the `k`-th triple is substitution by the
triple's members `copy-gens k (i g)`; each is `copy-terms k (i g)` evaluated at
the next triple, and that term is `ℊ g`, so the member is the next triple's
`g`-th member.

```agda
  -- If every generator is one of the terms, the next copy lies in this one.
  covered→⊇ : ∀ k → (∀ g → Σ[ i ∈ Fin 3 ] ℊ g ≈ʷ copy-terms k i) → copy (φ (suc k)) ⊆ copy (φ k)
  covered→⊇ k covered {y} (b , e) = b [ ℊ ∘ idx ] , (begin
    copy-map k (b [ ℊ ∘ idx ])            ≈⟨ copy-φ≈ k (b [ ℊ ∘ idx ]) ⟩
    b [ ℊ ∘ idx ] [ copy-gens k ]         ≡⟨ []-⨟ b (ℊ ∘ idx) (copy-gens k) ⟨
    b [ (ℊ ∘ idx) ⨟ copy-gens k ]         ≈⟨ []-congʳ b member ⟩
    b [ copy-gens (suc k) ]               ≈⟨ copy-φ≈ (suc k) b ⟨
    copy-map (suc k) b                    ≈⟨ e ⟩
    y                                     ∎)
    where
    -- The index of the term equal to each generator.
    idx : Fin 3 → Fin 3
    idx g = proj₁ (covered g)

    -- Each member named through idx is the next triple's member.
    member : ∀ g → copy-gens k (idx g) ≈ʷ copy-gens (suc k) g
    member g = ≈ʷ-trans (copy-gens≈ k (idx g)) ([]-cong (copy-gens (suc k)) (≈ʷ-sym (proj₂ (covered g))))
```

So strictness makes some generator equal to none of the terms.  Which one is
decided by Whitman's procedure in `FL(3)`, at most three decisions for each
generator, and a finite search finds it (`copy-misses`{.AgdaFunction}), as
`Θ-misses`{.AgdaFunction} of [DeansProblem.Coherent][] does.  No decision on
`X` is made.  The chain of copies then gives the record
(`copyChain→chain`{.AgdaFunction}).

```agda
  open Decision (_≟_ {3}) using ( _≈ʷ?_ )

  private
    -- The search, on the decision of whether every generator is one of the terms.
    search : ∀ k → Dec (∀ g → Σ[ i ∈ Fin 3 ] ℊ g ≈ʷ copy-terms k i)
           → Σ[ g ∈ Fin 3 ] (∀ i → ¬ (ℊ g ≈ʷ copy-terms k i))
    search k (yes covered)  = ⊥-elim (proj₂ (ascends k) (covered→⊇ k covered))
    search k (no ¬covered)  =
      let (g , ¬∃) = ¬∀⟶∃¬ 3 _ (λ g → any? (λ i → ℊ g ≈ʷ? copy-terms k i)) ¬covered
      in g , λ i e → ¬∃ (i , e)

  -- Some generator of FL(3) is none of the terms of the k-th step.
  copy-misses : ∀ k → Σ[ g ∈ Fin 3 ] (∀ i → ¬ (ℊ g ≈ʷ copy-terms k i))
  copy-misses k = search k (all? (λ g → any? (λ i → ℊ g ≈ʷ? copy-terms k i)))

  -- A chain of copies gives the record of a chain.
  copyChain→chain : Chain X
  copyChain→chain = record
    { gens       = copy-gens
    ; gens-free  = λ k → ≤→freelyGenerates (φ k)
    ; terms      = copy-terms
    ; gens≈      = copy-gens≈
    ; fresh      = λ k → proj₁ (copy-misses k)
    ; fresh∉     = λ k → proj₂ (copy-misses k)
    }
```

#### From the record to copies

Conversely, fix a `Chain`{.AgdaRecord}.  Its `k`-th embedding is substitution
by the `k`-th triple, injective because the triple freely generates
(`freelyGenerates→≤`{.AgdaFunction}).  Its copy lies in the next
(`chain-⊆`{.AgdaFunction}): `a [ gens k ]` is equal to
`a [ terms k ] [ gens (suc k) ]` (`⟨σ⟩⊆⟨τ⟩`{.AgdaFunction} and
`[]-⨟`{.AgdaFunction}).  And the next copy does not lie in it
(`chain-⊉`{.AgdaFunction}): it contains the fresh generator's image
`gens (suc k) (fresh k)`, which is not in the `k`-th copy
(`fresh∉⟨σ⟩`{.AgdaFunction}).

```agda
module _ (c : Chain X) where
  open Chain c
  open SetoidReasoning (FL-setoid X)

  -- The k-th embedding: substitution by the k-th triple.
  chain-φ : ℕ → proj₁ (FL (Fin 3)) ≤ proj₁ (FL X)
  chain-φ k = freelyGenerates→≤ (gens k) (gens-free k)

  -- Each copy lies in the next.
  chain-⊆ : ∀ k → copy (chain-φ k) ⊆ copy (chain-φ (suc k))
  chain-⊆ k {y} (a , e) = a [ terms k ] , (begin
    a [ terms k ] [ gens (suc k) ]  ≡⟨ []-⨟ a (terms k) (gens (suc k)) ⟨
    a [ terms k ⨟ gens (suc k) ]    ≈⟨ ⟨σ⟩⊆⟨τ⟩ (step k) a ⟨
    a [ gens k ]                    ≈⟨ e ⟩
    y                               ∎)

  -- The next copy does not lie in this one.
  chain-⊉ : ∀ k → ¬ (copy (chain-φ (suc k)) ⊆ copy (chain-φ k))
  chain-⊉ k ⊇ = let (t , e) = ⊇ (ℊ (fresh k) , ≈ʷ-refl) in fresh∉⟨σ⟩ (step k) t e

  -- The record of a chain gives a chain of copies.
  chain→copyChain : CopyChain X
  chain→copyChain = record
    { φ        = chain-φ
    ; ascends  = λ k → chain-⊆ k , chain-⊉ k
    }
```

#### The round trips

A chain taken to copies and back has the same triples and the same terms, by
definition (`chain-round-trip`{.AgdaFunction}): the restriction of
substitution by a triple is the triple, and containment applied to a generator
returns the term the chain gave it.  Only the fresh index may change, since the
search returns the first generator it finds.  A chain of copies taken to the
record and back has the same copies (`copy-round-trip`{.AgdaFunction}), since
each embedding is substitution by its triple.  So the two records are two
encodings of one notion.

```agda
-- From a chain to copies and back: the same triples and the same terms.
chain-round-trip : (c : Chain X)
  → (∀ k i → Chain.gens (copyChain→chain (chain→copyChain c)) k i ≡ Chain.gens c k i)
  × (∀ k i → Chain.terms (copyChain→chain (chain→copyChain c)) k i ≡ Chain.terms c k i)
chain-round-trip c = (λ k i → refl) , (λ k i → refl)

-- From copies to a chain and back: the same copies.
copy-round-trip : (c : CopyChain X)
  → ∀ k → copy (CopyChain.φ (chain→copyChain (copyChain→chain c)) k) ≐ copy (CopyChain.φ c k)
copy-round-trip c k = (λ (a , e) → a , ≈ʷ-trans (copy-φ≈ c k a) e)
                    , (λ (a , e) → a , ≈ʷ-trans (≈ʷ-sym (copy-φ≈ c k a)) e)
```
