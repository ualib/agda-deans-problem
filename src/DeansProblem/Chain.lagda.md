---
layout: default
file: "src/DeansProblem/Chain.lagda.md"
title: "DeansProblem.Chain module"
date: "2026-10-13"
author: "the agda-lattices development team"
---

### Chains of free sublattices

This is the [DeansProblem.Chain][] module of this repository.

[the paper]: https://arxiv.org/abs/YYMM.NNNNN

R. A. Dean asked whether a free lattice can contain an infinite strictly
ascending chain of sublattices `L₀ ⊊ L₁ ⊊ L₂ ⊊ ⋯`, each isomorphic to `FL(3)`.
This module states the problem's data in Agda: a *step*, one proper containment
of a freely generated sublattice in another, and a *chain*, a sequence of steps
each beginning where the last ended.  It then proves that a self-similar step,
one that an injective endomorphism of the ambient free lattice carries to the
next, would give a chain, and it records in prose, with proofs, the
reformulation of Dean's problem through which the self-similar case arose.
[DeansProblem.SelfSimilar][] proves that no step is self-similar, so the
theorem here, though true, never applies; it is kept because it is the formal
content of the reformulation, and because its ingredients (free generation and
containment transfer along an injective substitution) serve any chain.

**Chains are sequences of self-embeddings**.  Fix a chain `L₀ ⊊ L₁ ⊊ ⋯` in
`FL(X)` with isomorphisms `φₖ : FL(3) → Lₖ`.  The inclusion `Lₖ ⊆ Lₖ₊₁`, read
through `φₖ` and `φₖ₊₁⁻¹`, is a lattice embedding `θₖ = φₖ₊₁⁻¹ ∘ φₖ` of
`FL(3)` into itself, and it is not onto, since `φₖ₊₁ ∘ θₖ = φₖ` has image `Lₖ`,
which is not all of `Lₖ₊₁`.  The union of the chain is a lattice `L`, the direct
limit of `FL(3) → FL(3) → ⋯` along the `θₖ`: the maps `φₖ` into `L` are
compatible with the `θₖ`, every element of `L` lies in some `Lₖ`, and two
elements identified in the limit are identified at some finite stage, which
injectivity forbids unless they are equal.  So a chain gives a sequence of
proper self-embeddings of `FL(3)` whose direct limit embeds in a free lattice.
Conversely, let `θ₀, θ₁, …` be injective, non-surjective lattice endomorphisms
of `FL(3)` whose direct limit `L` embeds in `FL(X)` by `e`.  The canonical maps
`ιₖ : FL(3) → L` are injective, because each `θₖ` is, and `ιₖ = ιₖ₊₁ ∘ θₖ`, so
the images `Lₖ = e(ιₖ(FL(3)))` are isomorphic to `FL(3)` and ascend; and the
containment `Lₖ ⊆ Lₖ₊₁` is proper, because an element of `FL(3)` outside the
image of `θₖ` is sent by the injective `e ∘ ιₖ₊₁` outside `Lₖ`.  So Dean's problem
is a question about sequences of self-embeddings of `FL(3)`, with the ambient
free lattice entering only through the limit.  Both directions are
Proposition 4.2 of [the paper][], proved in [DeansProblem.Chain.Limit][] from
the direct limits of agda-lattices; the records below speak of the chain
inside `FL(X)` directly.

**Steps**.  A step `⟨σ⟩ ⊊ ⟨τ⟩` (`Step`{.AgdaRecord}) is two families `σ` and `τ`
of three elements of `FL(X)`, each freely generating a copy of `FL(3)`
([Lattices.Free.Generation][]), with terms `p` over three generators that
express the members of `σ` in those of `τ` (`σ i = p i [ τ ]`), so that
`⟨σ⟩ ⊆ ⟨τ⟩`, and an index `fresh` whose generator `ℊ fresh` is none of the terms
`p i`.  The terms `p` are the self-embedding `θ` of the reformulation, and the
last condition says that `θ` is not onto; through Corollary 1.6 of [Freese, Ježek,
and Nation (1995)][] it says that `τ fresh` is not in `⟨σ⟩`
(`fresh∉⟨σ⟩`{.AgdaFunction}), so the containment is proper.  The condition is
decidable, one Whitman decision in `FL(3)` per term, which is how
[DeansProblem.Examples.FreeseStep][] proves Freese's step proper.

**Chains**.  A chain (`Chain`{.AgdaRecord}) is a sequence of families, indexed by
`ℕ`, each freely generating, with terms and a fresh index for each consecutive
pair, so that its `k`-th step (`Chain.step`{.AgdaFunction}) is a `Step`.

**The self-similar step**.  Let `Φ` be an injective substitution of `X` into
itself whose image of `σ` is `τ`.  Then `σ ⨟ Φᵏ`, the family `σ` moved by the
`k`-th iterate of `Φ`, freely generates for every `k`, because free generation
transfers along an injective substitution (`freelyGenerates-⨟`{.AgdaFunction}),
and the same terms `p` and the same fresh index make each family properly
contained in the next.  So a self-similar step gives a chain
(`selfSimilar→chain`{.AgdaFunction}), and Dean's problem would have a positive
answer.  [DeansProblem.SelfSimilar][] shows that the hypothesis is never met:
along such a chain the terms expressing `τ` in the families above it are the
iterates `pᵏ`, which have bounded complexity because an embedding never lowers
the complexity of an element; so they repeat, and a repeat makes `p` onto,
against the fresh index.

**The variant without freeness**.  Drop the requirement that the sublattices
be free: does every ascending chain of 3-generated sublattices of a free lattice
stabilize?  If it does, Dean's answer is no.  This is the lattice analogue of
Takahasi's theorem for free groups (Section 4 of [the paper][]);
[DeansProblem.Chain.Condition][] states it, and
[DeansProblem.Examples.ChainCondition][] shows that it fails.

<!--
```agda
{-# OPTIONS --without-K --exact-split --safe #-}

module DeansProblem.Chain where

open import Agda.Primitive  using ( Setω ) renaming ( Set to Type )

-- Imports from the Agda Standard Library ---------------------------------------
open import Data.Fin.Base                          using ( Fin )
open import Data.Nat.Base                          using ( ℕ ; zero ; suc ; _+_ )
open import Data.Product                           using ( Σ-syntax ; _,_ ; proj₁ )
open import Level                                  using ( Level )
open import Relation.Binary.PropositionalEquality  using ( _≡_ ; refl ; sym ; trans ; cong ; subst
                                                         ; subst₂ )
open import Relation.Nullary                       using ( ¬_ )

-- Imports from the Agda Universal Algebra Library ------------------------------
open import Lattices.Free.Canonical.Basic          using ( ≈ʷ-sym ; ≈ʷ-trans )
open import Lattices.Free.Generation
                                                   using ( FreelyGenerates
                                                         ; freelyGenerates→injective
                                                         ; injective→freelyGenerates
                                                         ; free-generator-in-image )
open import Lattices.Free.Substitution
                                                   using ( Sub ; _[_] ; _⨟_ ; []-ℊ ; []-⨟ ; []-cong
                                                         ; []-congʳ ; subst-hom ; ⨟-injective )
open import Lattices.Free.Term                     using ( LatTerm ; ℊ )
open import Lattices.Free.Whitman                  using ( _≈ʷ_ )
open import Setoid.Functions                       using ( IsInjective )

private variable
  ι χ υ ζ : Level
  I : Type ι
  X : Type χ
  Y : Type υ
  Z : Type ζ
```
-->

#### Iterated substitutions

The `k`-th iterate of a substitution `σ` of `X` into itself
(`iter`{.AgdaFunction}) is the identity substitution `ℊ` for `k = 0` and
`σ ⨟ iter σ k` for `k + 1`, so that applying `iter σ (suc k)` applies `σ` and
then `iter σ k` (`[]-iter-suc`{.AgdaFunction}, by `[]-⨟`{.AgdaFunction}).  The
other order holds too, up to `_≡_`{.AgdaDatatype}: applying `iter σ (suc k)`
applies `iter σ k` and then `σ` (`[]-iter-sucʳ`{.AgdaFunction}), by induction on
`k`; and iterates add (`[]-iter-+`{.AgdaFunction}).

```agda
-- The k-th iterate of a substitution.
iter : Sub X X → ℕ → Sub X X
iter σ zero     = ℊ
iter σ (suc k)  = σ ⨟ iter σ k

-- Applying the (k+1)-st iterate applies σ first.
[]-iter-suc : (t : LatTerm X) (σ : Sub X X) (k : ℕ) → t [ iter σ (suc k) ] ≡ t [ σ ] [ iter σ k ]
[]-iter-suc t σ k = []-⨟ t σ (iter σ k)

-- Applying the (k+1)-st iterate applies σ last.
[]-iter-sucʳ : (t : LatTerm X) (σ : Sub X X) (k : ℕ) → t [ iter σ (suc k) ] ≡ t [ iter σ k ] [ σ ]
[]-iter-sucʳ t σ zero     = trans ([]-iter-suc t σ zero) (trans ([]-ℊ (t [ σ ]))
                                  (cong (_[ σ ]) (sym ([]-ℊ t))))
[]-iter-sucʳ t σ (suc k)  = trans ([]-iter-suc t σ (suc k)) (trans ([]-iter-sucʳ (t [ σ ]) σ k)
                                  (cong (_[ σ ]) (sym ([]-iter-suc t σ k))))

-- Iterates add: the (m+n)-th iterate applies the m-th, then the n-th.
[]-iter-+ : (t : LatTerm X) (σ : Sub X X) (m n : ℕ)
          → t [ iter σ (m + n) ] ≡ t [ iter σ m ] [ iter σ n ]
[]-iter-+ t σ zero     n = cong (_[ iter σ n ]) (sym ([]-ℊ t))
[]-iter-+ t σ (suc m)  n = trans ([]-iter-suc t σ (m + n)) (trans ([]-iter-+ (t [ σ ]) σ m n)
                                 (cong (_[ iter σ n ]) (sym ([]-iter-suc t σ m))))
```

#### Injective substitutions

The composite of two substitutions whose induced homomorphisms are injective
induces an injective homomorphism (`⨟-injective`{.AgdaFunction} of
[Lattices.Free.Substitution][]), so every iterate of such a substitution does
(`iter-injective`{.AgdaFunction}).  A family that freely generates, moved
by an injective substitution, still freely generates
(`freelyGenerates-⨟`{.AgdaFunction}): by Corollary 1.13 both directions
(`freelyGenerates→injective`{.AgdaFunction} and
`injective→freelyGenerates`{.AgdaFunction}), free generation is injectivity, and
injectivity composes.

```agda
-- Every iterate of an injective substitution is injective.
iter-injective : (σ : Sub X X) → IsInjective (proj₁ (subst-hom σ))
               → (k : ℕ) → IsInjective (proj₁ (subst-hom (iter σ k)))
iter-injective σ inj zero     {s} {t} e = subst₂ _≈ʷ_ ([]-ℊ s) ([]-ℊ t) e
iter-injective σ inj (suc k)          = ⨟-injective σ (iter σ k) inj (iter-injective σ inj k)

-- Free generation transfers along an injective substitution.
freelyGenerates-⨟ : (σ : Sub I X) (ρ : Sub X Y) → FreelyGenerates σ
                  → IsInjective (proj₁ (subst-hom ρ)) → FreelyGenerates (σ ⨟ ρ)
freelyGenerates-⨟ σ ρ fg inj =
  injective→freelyGenerates (σ ⨟ ρ) (⨟-injective σ ρ (freelyGenerates→injective σ fg) inj)
```

#### Steps

A `Step`{.AgdaRecord} records one proper containment `⟨σ⟩ ⊊ ⟨τ⟩` of freely
generated copies of `FL(3)` in `FL(X)`, in the form described at the top of the
module.  The fields are kept plain, so that a later development (Freese's
truncation patterns, a chain condition) can read them directly.

```agda
-- One proper containment of freely generated copies of FL(3).
record Step (X : Type χ) : Type χ where
  field
    σ τ      : Sub (Fin 3) X
    σ-free   : FreelyGenerates σ
    τ-free   : FreelyGenerates τ
    p        : Sub (Fin 3) (Fin 3)
    σ≈p[τ]   : ∀ i → σ i ≈ʷ p i [ τ ]
    fresh    : Fin 3
    fresh∉p  : ∀ i → ¬ (ℊ fresh ≈ʷ p i)
```

Every element of `⟨σ⟩` lies in `⟨τ⟩`: the value of a term `t` at `σ` is the value
of `t [ p ]` at `τ` (`⟨σ⟩⊆⟨τ⟩`{.AgdaFunction}).  And `τ fresh` is not in `⟨σ⟩`
(`fresh∉⟨σ⟩`{.AgdaFunction}): if it were the value of `t` at `σ`, it would be the
value of `t` under `p ⨟ τ`, and Corollary 1.6, transported through the embedding
`τ` by `free-generator-in-image`{.AgdaFunction}, would make `ℊ fresh` one of the
terms `p i`.

```agda
module _ (s : Step X) where
  open Step s

  -- The lower sublattice lies in the upper one.
  ⟨σ⟩⊆⟨τ⟩ : (t : LatTerm (Fin 3)) → t [ σ ] ≈ʷ t [ p ⨟ τ ]
  ⟨σ⟩⊆⟨τ⟩ t = []-congʳ t σ≈p[τ]

  -- The fresh upper generator is not in the lower sublattice.
  fresh∉⟨σ⟩ : (t : LatTerm (Fin 3)) → ¬ (t [ σ ] ≈ʷ τ fresh)
  fresh∉⟨σ⟩ t e =
    let (i , e') = free-generator-in-image τ (freelyGenerates→injective τ τ-free) p t
                     (≈ʷ-trans (≈ʷ-sym e) (⟨σ⟩⊆⟨τ⟩ t))
    in fresh∉p i e'
```

#### Chains

A `Chain`{.AgdaRecord} is a sequence of freely generating families `gens k`,
with, for each `k`, the terms expressing `gens k` in `gens (suc k)` and a fresh
index.  Its `k`-th step is a `Step`{.AgdaRecord}
(`Chain.step`{.AgdaFunction}), so each containment is proper.

```agda
-- An infinite strictly ascending chain of freely generated copies of FL(3).
record Chain (X : Type χ) : Type χ where
  field
    gens       : ℕ → Sub (Fin 3) X
    gens-free  : ∀ k → FreelyGenerates (gens k)
    terms      : ℕ → Sub (Fin 3) (Fin 3)
    gens≈      : ∀ k i → gens k i ≈ʷ terms k i [ gens (suc k) ]
    fresh      : ℕ → Fin 3
    fresh∉     : ∀ k i → ¬ (ℊ (fresh k) ≈ʷ terms k i)

  -- The k-th step of the chain.
  step : ℕ → Step X
  step k = record
    { σ        = gens k
    ; τ        = gens (suc k)
    ; σ-free   = gens-free k
    ; τ-free   = gens-free (suc k)
    ; p        = terms k
    ; σ≈p[τ]   = gens≈ k
    ; fresh    = fresh k
    ; fresh∉p  = fresh∉ k
    }
```

#### The self-similar step gives a chain

Suppose `Φ` freely generates (equivalently, by Corollary 1.13, its induced
endomorphism of `FL(X)` is injective) and sends `σ` to `τ`: `σ i [ Φ ]` equals
`τ i` for each `i`.  The `k`-th family of the chain is `σ ⨟ iter Φ k`.  It freely
generates, by `freelyGenerates-⨟`{.AgdaFunction} and
`iter-injective`{.AgdaFunction}.  The `k`-th family is expressed in the next by
the step's own terms `p` (`self-similar-≈`{.AgdaFunction}): `σ i` is `p i [ τ ]`,
so `σ i [ Φᵏ ]` is `p i [ τ ] [ Φᵏ ]`, and `τ` is `σ ⨟ Φ`, so this is
`p i [ σ ⨟ Φ ] [ Φᵏ ]`, which is `p i [ σ ⨟ Φᵏ⁺¹ ]`.  And the step's fresh index
serves at every level.  So the chain is strictly ascending
(`selfSimilar→chain`{.AgdaFunction}).

```agda
module _ (s : Step X) (Φ : Sub X X) (Φ-free : FreelyGenerates Φ)
         (Φσ≈τ : ∀ i → Step.σ s i [ Φ ] ≈ʷ Step.τ s i) where
  open Step s

  -- The k-th family of the chain: σ moved by the k-th iterate of Φ.
  self-similar-gens : ℕ → Sub (Fin 3) X
  self-similar-gens k = σ ⨟ iter Φ k

  -- Each family freely generates.
  self-similar-free : ∀ k → FreelyGenerates (self-similar-gens k)
  self-similar-free k =
    freelyGenerates-⨟ σ (iter Φ k) σ-free (iter-injective Φ (freelyGenerates→injective Φ Φ-free) k)

  -- The next family, read through τ.
  self-similar-next : ∀ k i → self-similar-gens (suc k) i ≈ʷ τ i [ iter Φ k ]
  self-similar-next k i = subst (_≈ʷ τ i [ iter Φ k ]) (sym ([]-iter-suc (σ i) Φ k))
                                ([]-cong (iter Φ k) (Φσ≈τ i))

  -- Each family is expressed in the next by the step's terms.
  self-similar-≈ : ∀ k i → self-similar-gens k i ≈ʷ p i [ self-similar-gens (suc k) ]
  self-similar-≈ k i =
    ≈ʷ-trans ([]-cong (iter Φ k) (σ≈p[τ] i))
      (subst (_≈ʷ p i [ self-similar-gens (suc k) ]) ([]-⨟ (p i) τ (iter Φ k))
        ([]-congʳ (p i) (λ j → ≈ʷ-sym (self-similar-next k j))))

  -- A self-similar step gives an infinite strictly ascending chain.
  selfSimilar→chain : Chain X
  selfSimilar→chain = record
    { gens       = self-similar-gens
    ; gens-free  = self-similar-free
    ; terms      = λ _ → p
    ; gens≈      = self-similar-≈
    ; fresh      = λ _ → fresh
    ; fresh∉     = λ _ → fresh∉p
    }
```

**Proposition 4.3** of [the paper][] is this theorem: if an injective
endomorphism `Φ` of `FL(X)` sends the lower triple `σ` of a step to its upper
triple `τ`, coordinatewise, then the triples `Φᵏ(σ)`, `k ≥ 0`, form a chain.
Its type names the chain's triples, which the type of
`selfSimilar→chain`{.AgdaFunction} leaves to its definition: the `k`-th is
`σ i [ iter Φ k ]` at each index `i`.  An injective endomorphism of `FL(X)` is
a substitution `Φ : Sub X X` that freely generates, by Corollary 2.5.

```agda
-- Proposition 4.3: a self-similar step gives a chain, whose k-th triple is Φᵏ(σ).
Proposition-4·3 : Setω
Proposition-4·3 =  ∀ {χ} {X : Type χ} (s : Step X) (Φ : Sub X X) → FreelyGenerates Φ
                   → (∀ i → Step.σ s i [ Φ ] ≈ʷ Step.τ s i)
                   → Σ[ c ∈ Chain X ] (∀ k i → Chain.gens c k i ≡ Step.σ s i [ iter Φ k ])

-- The proof of Proposition 4.3.
proposition-4·3 : Proposition-4·3
proposition-4·3 s Φ Φ-free Φσ≈τ = selfSimilar→chain s Φ Φ-free Φσ≈τ , λ k i → refl
```

--------------------------------------

[DeansProblem.Chain]: DeansProblem.Chain.html
[DeansProblem.Chain.Condition]: DeansProblem.Chain.Condition.html
[DeansProblem.Chain.Limit]: DeansProblem.Chain.Limit.html
[DeansProblem.Examples.ChainCondition]: DeansProblem.Examples.ChainCondition.html
[DeansProblem.Examples.FreeseStep]: DeansProblem.Examples.FreeseStep.html
[DeansProblem.SelfSimilar]: DeansProblem.SelfSimilar.html
[Lattices.Free.Generation]: Lattices.Free.Generation.html
[Lattices.Free.Substitution]: Lattices.Free.Substitution.html
