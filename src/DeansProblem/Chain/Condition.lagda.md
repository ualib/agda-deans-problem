---
layout: default
file: "src/DeansProblem/Chain/Condition.lagda.md"
title: "DeansProblem.Chain.Condition module"
date: "2026-10-16"
author: "the agda-lattices development team"
---

### A chain condition for finitely generated sublattices of a free lattice

This is the [DeansProblem.Chain.Condition][] module of this repository.

[the paper]: https://arxiv.org/abs/YYMM.NNNNN

Takahasi proved that in a free group every ascending chain of subgroups of
bounded rank stabilizes (his note of 1950, recalled in his note of 1951;
Higman found it independently).  The lattice analogue asks the following:
does every ascending chain `L₀ ⊆ L₁ ⊆ L₂ ⊆ ⋯` of 3-generated sublattices of a
free lattice stabilize?  It is the variant without freeness of Section 4 of
[the paper][].  A positive answer would contain Theorem H
(`no-copy-chain`{.AgdaFunction} of
[DeansProblem.NoChain][]) as the case in which every link is a copy of
`FL(3)`; but the links may be finite (`N₅` is a 3-generated sublattice of
`FL(3)`) or infinite and not free, and the proof of Theorem H does not apply to
them.  This module states the question, proves that it contains Theorem H, and
proves the two theorems of [the paper][] that survive without freeness:
Theorem A for every finitely generated sublattice, and Corollary A3 for chains
of them.
The answer is no: [DeansProblem.Examples.ChainCondition][] builds an infinite
strictly ascending chain of 3-generated sublattices of `FL(3)` on the
interleaving and the transport of the last sections here.

**Generated sublattices**.  The sublattice `⟨ σ ⟩`{.AgdaFunction} of `FL(X)`
that a family `σ : Sub I X` generates is the set of values of terms at `σ`: an
element lies in it when some term `t` over `I` has `t [ σ ] ≈ʷ w`, and the
term is the witness.  One sublattice lies in another as soon as the generators
of the first do (`gens⊆`{.AgdaFunction}), which is the form in which
`Step`{.AgdaRecord} of [DeansProblem.Chain][] records a containment: a term
`p i` with `σ i ≈ʷ p i [ τ ]` for each generator.  The image of `⟨ σ ⟩` under
the endomorphism that a substitution `Φ` induces is `⟨ σ ⨟ Φ ⟩`
(`image⇔`{.AgdaFunction}), so `Φ(L)` is written `⟨ σ ⨟ Φ ⟩` below.

**Chains, stabilization, and the chain condition**.  An ascending chain of
`n`-generated sublattices (`Ascending n X`{.AgdaRecord}) is a sequence of
families `links k : Sub (Fin n) X` with `⟨ links k ⟩ ⊆ ⟨ links (suc k) ⟩`.  It
stabilizes (`Stabilizes`{.AgdaFunction}) if from some `N` on every link
contains the next.  A strictly ascending chain
(`StrictlyAscending n X`{.AgdaRecord}) has `⟨ links k ⟩ ⊂ ⟨ links (suc k) ⟩`,
the standard library's strict containment: containment, and the negation of
the reverse containment, as `CopyChain`{.AgdaRecord} of
[DeansProblem.Chain.Copies][] states strictness, which does not ask for an
element of the larger link outside the smaller.  The chain condition for
`n`-generated sublattices of `FL(X)` (`ChainCondition n X`{.AgdaFunction}) is
that no strictly ascending chain exists, the form of Theorem H.  The question
proper is that every ascending chain stabilizes; it implies the chain
condition (`stabilizes→chainCondition`{.AgdaFunction}), and classically the
two are equivalent, since a chain that never stabilizes has a strictly
ascending subsequence, chosen by excluded middle one proper step at a time.
For `n ≤ 2` the question is trivial, since two elements generate at most four
(`chainCondition₂`{.AgdaFunction} of [DeansProblem.Chain.TwoGenerated][]);
`n = 3` is the first case that is not, and since `FL(ω)` embeds in `FL(3)`,
`FL(3)` is the ambient lattice that matters.

**Chains of copies are chains**.  A `Chain`{.AgdaRecord} of free triples
(`gens k` freely generating, with terms and a fresh generator for each step)
is a strictly ascending chain of 3-generated sublattices
(`chain→strict`{.AgdaFunction}): the step's terms give the containment, as
`⟨σ⟩⊆⟨τ⟩`{.AgdaFunction} of [DeansProblem.Chain][] records, and its fresh
generator is a member of the upper link outside the lower
(`fresh∉⟨σ⟩`{.AgdaFunction}).  So the chain condition
for `3` and `X` excludes every `Chain X` and every `CopyChain X`
(`chainCondition→no-chain`{.AgdaFunction},
`chainCondition→no-copy-chain`{.AgdaFunction}): it would give Theorem H for
`X`, and Theorem H is the special case of it whose links are free.

**Theorem A for finitely generated sublattices**.  Let `X` have decidable
equality, `Φ` be an injective endomorphism of `FL(X)`, and `L = ⟨ σ ⟩` with
`σ = (g₁, …, gₙ)`, such that `L ⊆ Φ(L)`.  Then `Φ(L) ⊆ L`, so `Φ(L) = L`
(`generated-onto`{.AgdaFunction}).
[DeansProblem.SelfSimilar][] proves it for a free `L`
(`self-similar-onto`{.AgdaFunction}), running the orbit argument inside
`FL(n)` and carrying a repeat across the injective `τ`.  Without freeness the
repeat is taken in `L` itself, as follows.

1.  **The terms**.  Each `gᵢ` lies in `Φ(L)`, so `gᵢ ≈ θᵢ [ σ ⨟ Φ ]` for a term
    `θᵢ` over `n` generators (`θ`{.AgdaFunction}).  Write `θ` also for the
    endomorphism of `FL(n)` with `θ(xᵢ) = θᵢ`.  Then
    `w [ θ ] [ σ ] [ Φ ] ≈ w [ σ ]` for every term `w`
    (`turn`{.AgdaFunction}).
2.  **The orbit**.  Fix `j` and put `mₖ = θᵏ(xⱼ) [ σ ]`, an element of `L`
    (`orbit`{.AgdaFunction}), with `m₀ = gⱼ`.  By the first step,
    `Φ(mₖ₊₁) ≈ mₖ` (`back`{.AgdaFunction}), and so `Φᵈ(m_(d+k)) ≈ mₖ`
    (`back-by`{.AgdaFunction}).
3.  **Bounded complexity**.  An embedding never lowers complexity
    (`complexity-mono`{.AgdaFunction} of [Lattices.Free.Complexity][]), so
    `c(mₖ₊₁) ≤ c(Φ(mₖ₊₁)) = c(mₖ)`, and every `mₖ` has complexity at most
    `c(gⱼ)` (`orbit-bound`{.AgdaFunction}).
4.  **A repeat**.  Finitely many elements of `L` have complexity at most
    `c(gⱼ)`, so `mₐ ≈ m_b` with `a < b` (`orbit-repeats`{.AgdaFunction}).
5.  **The image of the generator is in `L`**.  Write `b = a + (1 + o)`.  Then
    `gⱼ ≈ m₀ ≈ Φᵃ(mₐ) ≈ Φᵃ(m_b) ≈ m_(1+o)`, by the second step twice, and so
    `Φ(gⱼ) ≈ Φ(m_(1+o)) ≈ mₒ`, which lies in `L` with the witness term
    `θᵒ(xⱼ)` (`image-gen`{.AgdaFunction}).  As the generators of `Φ(L)` lie
    in `L`, `Φ(L) ⊆ L` (`image⊆`{.AgdaFunction}).

Injectivity of `Φ` enters only at the third step, and the injectivity of `θ`,
which the free case derives, is not needed.  The finiteness at the fourth step
is the one place where the generators of the ambient lattice matter.  The
argument is written for any finite list that covers the elements of `L` of
bounded complexity (the module `Orbit`{.AgdaModule}), and such a list exists
whenever `X` has decidable equality (the module `Local`{.AgdaModule}): the
generators that `σ` uses, listed once each, give an embedding of `FL(r)` in
`FL(X)` whose image contains `L`, and the elements of `FL(r)` of bounded
complexity are finitely many.  Decidable equality is the hypothesis of
Theorem H too, and both theorems need it only to compute canonical forms.

**Corollary A3**.  If `⟨ σ ⟩ ⊆ ⟨ τ ⟩` and an injective `Φ` has
`⟨ τ ⟩ ⊆ Φ(⟨ σ ⟩)`, then `⟨ σ ⟩ ⊆ Φ(⟨ σ ⟩)`, so Theorem A gives
`Φ(⟨ σ ⟩) ⊆ ⟨ σ ⟩`, and `⟨ τ ⟩ ⊆ ⟨ σ ⟩` (`collapse`{.AgdaFunction}).  In a
strictly ascending chain, then, no injective endomorphism carries a link onto
a sublattice containing a later link (`no-onto-later`{.AgdaFunction}), and in
particular none carries a link onto a later link
(`no-image-later`{.AgdaFunction}): `⟨ links (suc j) ⟩ ⊆ ⟨ links k ⟩ ⊆ ⟨ links j ⟩`
would contradict the proper step at `j`.  So no strictly ascending chain of
finitely generated sublattices is generated by one embedding, even with a
period (`no-periodic-embedding`{.AgdaFunction}).  Freeness is used nowhere,
and the links need not share a number of generators: Corollary A3 as the
paper states it is for a chain of finitely generated sublattices whose `k`-th
link has any number of generators (`StrictlyAscendingᶠ`{.AgdaRecord},
`no-image-laterᶠ`{.AgdaFunction}), of which the chains of `n`-generated
sublattices are the case of constant rank.

**Copies of `FL(n)`**.  A sublattice generated by `n` elements that is the
image of an embedding of `FL(n)` is freely generated by those `n` elements
(`copy≐→freelyGenerates`{.AgdaFunction}): the images of the free generators
lie in every generating set (Corollary 2.4), so they are the `n` elements in
some order.  [DeansProblem.Examples.ChainCondition][] uses it to prove that no
link of its chain is a copy of `FL(3)`.

<!--
```agda
{-# OPTIONS --without-K --exact-split --safe #-}

module DeansProblem.Chain.Condition where

open import Agda.Primitive  using ( Setω ) renaming ( Set to Type )

-- Imports from the Agda Standard Library ---------------------------------------
open import Data.Empty                             using ( ⊥ ; ⊥-elim )
open import Data.Fin.Base                          using ( Fin ; zero ; suc ; punchOut )
open import Data.Fin.Properties                    using ( _≟_ ; any? ; pigeonhole ; punchOut-injective )
                                                   renaming ( <⇒≢ to <ᶠ⇒≢ )
open import Data.List.Base                         using ( List ; [] ; _∷_ ; _++_ ; allFin ; length
                                                         ; lookup ; deduplicate ; map )
open import Data.List.Membership.Propositional     using ( _∈_ )
open import Data.List.Membership.Propositional.Properties
                                                   using ( ∈-allFin ; ∈-++⁺ˡ ; ∈-++⁺ʳ ; ∈-++⁻
                                                         ; ∈-lookup ; ∈-deduplicate⁺ )
open import Data.List.Relation.Unary.AllPairs      using ( _∷_ )
open import Data.List.Relation.Unary.Any           using ( Any ; here ; index )
open import Data.List.Relation.Unary.Any.Properties
                                                   using ( map⁺ ; lookup-index )
open import Data.List.Relation.Unary.Unique.Propositional
                                                   using ( Unique )
open import Data.Nat.Base                          using ( ℕ ; zero ; suc ; _+_ ; _*_ ; _≤_ ; _<_ ; z≤n
                                                         ; s≤s )
open import Data.Nat.Properties                    using ( ≤-refl ; ≤-trans ; ≤-reflexive ; <⇒≤
                                                         ; +-comm ; +-suc ; +-identityʳ ; *-suc
                                                         ; m≤n⇒∃[o]m+o≡n ; n<1+n )
open import Data.Product                           using ( Σ-syntax ; _×_ ; _,_ ; proj₁ ; proj₂ )
open import Data.Sum                               using ( [_,_]′ )
open import Function                               using ( _∘_ ; _⇔_ ; mk⇔ )
open import Level                                  using ( Level ; _⊔_ )
open import Relation.Binary.Definitions            using ( DecidableEquality )
open import Relation.Binary.PropositionalEquality  using ( _≡_ ; _≢_ ; refl ; sym ; trans ; cong ; cong₂
                                                         ; subst ; subst₂ )
open import Relation.Nullary                       using ( ¬_ ; Dec ; yes ; no )
open import Relation.Unary                         using ( Pred ; _⊆_ ; _⊂_ ; _≐_ )

import Data.List.Relation.Unary.All as All
import Data.List.Relation.Unary.Any as Any

-- Imports from the Agda Universal Algebra Library ------------------------------
open import Lattices.Free.Canonical.Basic          using ( ≈ʷ-refl ; ≈ʷ-sym ; ≈ʷ-trans )
open import DeansProblem.Chain                     using ( Step ; module Step ; Chain ; module Chain ; fresh∉⟨σ⟩ ; iter
                                                         ; []-iter-suc ; []-iter-sucʳ )
open import DeansProblem.Chain.Copies              using ( CopyChain ; copyChain→chain ; copy
                                                         ; ≤→freelyGenerates )
open import Lattices.Free.Complexity               using ( complexity ; complexity-resp
                                                         ; complexity-mono ; module Bounded
                                                         ; pigeonhole-≈ )
open import Lattices.Free.Generation               using ( FreelyGenerates
                                                         ; freelyGenerates→injective
                                                         ; freelyGenerates-reindex
                                                         ; freelyGenerates-resp
                                                         ; free-generator-in-image )
open import Lattices.Free.Substitution             using ( Sub ; _[_] ; _⨟_ ; []-ℊ ; []-⨟ ; []-cong
                                                         ; []-congʳ ; subst-hom ; restriction
                                                         ; hom-induced )
open import Lattices.Free.Term                     using ( LatTerm ; ℊ ; _∧̇_ ; _∨̇_ )
open import Lattices.Free.Universal                using ( FL ; ℊ-injective )
open import Lattices.Free.Whitman                  using ( _≈ʷ_ )
open import Setoid.Functions                       using ( IsInjective )
open import Setoid.Subalgebras.Basic               using ( _IsSubalgebraOf_ )

private variable
  ι κ χ υ : Level
  I : Type ι
  J : Type κ
  X : Type χ
  Y : Type υ
  n : ℕ
```
-->

#### Generated sublattices

The sublattice that a family generates (`⟨_⟩`{.AgdaFunction}) is a predicate on
`FL(X)` that respects equality (`⟨⟩-resp`{.AgdaFunction}) and holds of each
member of the family (`gen∈`{.AgdaFunction}), with the generator itself as
witness.

```agda
private
  -- An equation of lattice terms read as an equality in the free lattice.
  ≡→≈ʷ : {s t : LatTerm X} → s ≡ t → s ≈ʷ t
  ≡→≈ʷ {s = s} e = subst (s ≈ʷ_) e ≈ʷ-refl

-- The sublattice of FL(X) that a family generates: the values of terms at it.
⟨_⟩ : {I : Type ι} {X : Type χ} → Sub I X → Pred (LatTerm X) (ι ⊔ χ)
⟨_⟩ {I = I} σ w = Σ[ t ∈ LatTerm I ] t [ σ ] ≈ʷ w

-- Membership respects equality in the free lattice.
⟨⟩-resp : (σ : Sub I X) {v w : LatTerm X} → ⟨ σ ⟩ v → v ≈ʷ w → ⟨ σ ⟩ w
⟨⟩-resp σ (t , e) e' = t , ≈ʷ-trans e e'

-- Each member of a family lies in the sublattice it generates.
gen∈ : (σ : Sub I X) (i : I) → ⟨ σ ⟩ (σ i)
gen∈ σ i = ℊ i , ≈ʷ-refl
```

A sublattice lies in another as soon as its generators do
(`gens⊆`{.AgdaFunction}): if each `σ i` is `p i [ τ ]`, the value of a term `t`
at `σ` is the value of `t [ p ]` at `τ`.  The converse is immediate, so
containment is containment of the generators (`⊆⇔gens`{.AgdaFunction}).

```agda
-- A sublattice lies in another as soon as its generators do.
gens⊆ : {σ : Sub I X} {τ : Sub J X} → (∀ i → ⟨ τ ⟩ (σ i)) → ⟨ σ ⟩ ⊆ ⟨ τ ⟩
gens⊆ {σ = σ} {τ} g (t , e) =
  t [ p ] , subst (_≈ʷ _) ([]-⨟ t p τ) (≈ʷ-trans ([]-congʳ t (λ i → proj₂ (g i))) e)
  where
  -- The term expressing each generator of σ in τ.
  p : Sub _ _
  p i = proj₁ (g i)

-- Containment is containment of the generators.
⊆⇔gens : {σ : Sub I X} {τ : Sub J X} → (⟨ σ ⟩ ⊆ ⟨ τ ⟩) ⇔ (∀ i → ⟨ τ ⟩ (σ i))
⊆⇔gens {σ = σ} = mk⇔ (λ h i → h (gen∈ σ i)) gens⊆
```

The endomorphism of `FL(X)` induced by a substitution `Φ` maps `⟨ σ ⟩` onto
`⟨ σ ⨟ Φ ⟩` (`image⇔`{.AgdaFunction}): the value of `t` at `σ ⨟ Φ` is the
image under `Φ` of the value of `t` at `σ`, and conversely.

```agda
-- The image of ⟨ σ ⟩ under substitution by Φ is ⟨ σ ⨟ Φ ⟩.
image⇔ : (σ : Sub I X) (Φ : Sub X Y) {w : LatTerm Y}
       → ⟨ σ ⨟ Φ ⟩ w ⇔ (Σ[ v ∈ LatTerm X ] ⟨ σ ⟩ v × v [ Φ ] ≈ʷ w)
image⇔ σ Φ = mk⇔ (λ (t , e) → t [ σ ] , (t , ≈ʷ-refl) , subst (_≈ʷ _) ([]-⨟ t σ Φ) e)
                 (λ (v , (t , e) , e') →
                    t , subst (_≈ʷ _) (sym ([]-⨟ t σ Φ)) (≈ʷ-trans ([]-cong Φ e) e'))
```

#### Chains and the chain condition

An ascending chain of `n`-generated sublattices of `FL(X)`
(`Ascending`{.AgdaRecord}) has each link inside the next, and so inside every
later one (`ascends-≤`{.AgdaFunction}), by induction on the distance.  It
stabilizes (`Stabilizes`{.AgdaFunction}) if from some `N` on every link
contains the next.

```agda
-- An ascending chain of n-generated sublattices of FL(X).
record Ascending (n : ℕ) (X : Type χ) : Type χ where
  field
    links    : ℕ → Sub (Fin n) X
    ascends  : ∀ k → ⟨ links k ⟩ ⊆ ⟨ links (suc k) ⟩

module _ (c : Ascending n X) where
  open Ascending c

  -- Each link lies in the link d places later.
  ascends-+ : ∀ j d → ⟨ links j ⟩ ⊆ ⟨ links (d + j) ⟩
  ascends-+ j zero     p = p
  ascends-+ j (suc d)  p = ascends (d + j) (ascends-+ j d p)

  -- Each link lies in every later one.
  ascends-≤ : ∀ {j k} → j ≤ k → ⟨ links j ⟩ ⊆ ⟨ links k ⟩
  ascends-≤ {j} {k} j≤k {w} p =
    let (d , j+d≡k) = m≤n⇒∃[o]m+o≡n j≤k
    in subst (λ i → ⟨ links i ⟩ w) (trans (+-comm d j) j+d≡k) (ascends-+ j d p)

-- A chain stabilizes if from some link on, every link contains the next.
Stabilizes : {X : Type χ} → Ascending n X → Type χ
Stabilizes c = Σ[ N ∈ ℕ ] (∀ k → N ≤ k → ⟨ links (suc k) ⟩ ⊆ ⟨ links k ⟩)
  where open Ascending c
```

A strictly ascending chain (`StrictlyAscending`{.AgdaRecord}) is ascending
(`strict→ascending`{.AgdaFunction}), and the chain condition
(`ChainCondition`{.AgdaFunction}) says there is none.  If every ascending chain
stabilizes, the chain condition holds (`stabilizes→chainCondition`{.AgdaFunction}):
a strictly ascending chain, read as an ascending one, would stabilize at some
`N`, and its step at `N` is proper.

```agda
-- A strictly ascending chain of n-generated sublattices of FL(X).
record StrictlyAscending (n : ℕ) (X : Type χ) : Type χ where
  field
    links    : ℕ → Sub (Fin n) X
    ascends  : ∀ k → ⟨ links k ⟩ ⊂ ⟨ links (suc k) ⟩

-- A strictly ascending chain is ascending.
strict→ascending : StrictlyAscending n X → Ascending n X
strict→ascending c = record
  { links    = StrictlyAscending.links c
  ; ascends  = λ k → proj₁ (StrictlyAscending.ascends c k)
  }

-- The chain condition for n-generated sublattices of FL(X): no strictly ascending chain.
ChainCondition : ℕ → Type χ → Type χ
ChainCondition n X = ¬ StrictlyAscending n X

-- If every ascending chain stabilizes, the chain condition holds.
stabilizes→chainCondition : ((c : Ascending n X) → Stabilizes c) → ChainCondition n X
stabilizes→chainCondition every c =
  let (N , st) = every (strict→ascending c)
  in proj₂ (StrictlyAscending.ascends c N) (st N ≤-refl)
```

#### Chains of copies of FL(3) are chains

A `Chain`{.AgdaRecord} of free triples is a strictly ascending chain of
3-generated sublattices (`chain→strict`{.AgdaFunction}): its `k`-th step's terms
put the generators of `gens k` in `⟨ gens (suc k) ⟩`, and its fresh generator,
a member of `⟨ gens (suc k) ⟩`, is not in `⟨ gens k ⟩`
(`fresh∉⟨σ⟩`{.AgdaFunction}); the same argument makes every step a strict
containment (`step→⊂`{.AgdaFunction}).  Through
`copyChain→chain`{.AgdaFunction}, so is a chain of copies
(`copyChain→strict`{.AgdaFunction}).  So the chain condition
for 3-generated sublattices of `FL(X)` excludes both, which is Theorem H for
`X` (`chainCondition→no-chain`{.AgdaFunction},
`chainCondition→no-copy-chain`{.AgdaFunction}).

```agda
-- A chain of free triples is a strictly ascending chain of 3-generated sublattices.
chain→strict : Chain X → StrictlyAscending 3 X
chain→strict c = record
  { links    = gens
  ; ascends  = λ k → gens⊆ (λ i → terms k i , ≈ʷ-sym (gens≈ k i))
                   , λ ⊇ → let (t , e) = ⊇ (gen∈ (gens (suc k)) (fresh k))
                           in fresh∉⟨σ⟩ (step k) t e
  }
  where open Chain c

-- A step is a strict containment of generated sublattices.
step→⊂ : (s : Step X) → ⟨ Step.σ s ⟩ ⊂ ⟨ Step.τ s ⟩
step→⊂ s =  gens⊆ (λ i → Step.p s i , ≈ʷ-sym (Step.σ≈p[τ] s i))
          , λ ⊇ → let (t , e) = ⊇ (gen∈ (Step.τ s) (Step.fresh s)) in fresh∉⟨σ⟩ s t e

-- A chain of copies of FL(3) is a strictly ascending chain of 3-generated sublattices.
copyChain→strict : CopyChain X → StrictlyAscending 3 X
copyChain→strict c = chain→strict (copyChain→chain c)

-- The chain condition for 3-generated sublattices excludes every chain of free triples.
chainCondition→no-chain : ChainCondition 3 X → ¬ Chain X
chainCondition→no-chain cc c = cc (chain→strict c)

-- The chain condition for 3-generated sublattices excludes every chain of copies of FL(3).
chainCondition→no-copy-chain : ChainCondition 3 X → ¬ CopyChain X
chainCondition→no-copy-chain cc c = cc (copyChain→strict c)
```

#### Theorem A: the orbit of a generator

Fix generators `X` with decidable equality, a family `σ` of `n` elements, an
injective substitution `Φ` of `X` into itself with `⟨ σ ⟩ ⊆ ⟨ σ ⨟ Φ ⟩`, and a
finite cover: for each bound `B`, a list of elements of `FL(X)` such that every
element of `⟨ σ ⟩` of complexity at most `B`, given as a value `t [ σ ]`, is
equal to a member.  The module `Orbit`{.AgdaModule} runs the argument at the
top of this module under these hypotheses.

```agda
module Orbit {X : Type χ} (_≟ˣ_ : DecidableEquality X) {n : ℕ} (σ : Sub (Fin n) X)
             (cover : (B : ℕ) → Σ[ L ∈ List (LatTerm X) ]
                        ((t : LatTerm (Fin n)) → complexity _≟ˣ_ (t [ σ ]) ≤ B
                                               → Any (t [ σ ] ≈ʷ_) L))
             (Φ : Sub X X) (Φ-inj : IsInjective (proj₁ (subst-hom Φ)))
             (σ⊆Φσ : ⟨ σ ⟩ ⊆ ⟨ σ ⨟ Φ ⟩) where

  private
    -- Complexity in FL(X).
    c : LatTerm X → ℕ
    c = complexity _≟ˣ_

  -- The terms expressing each generator in the image: σ i ≈ θ i [ σ ⨟ Φ ].
  θ : Sub (Fin n) (Fin n)
  θ i = proj₁ (σ⊆Φσ (gen∈ σ i))

  -- The defining equation of θ.
  θ≈ : ∀ i → θ i [ σ ⨟ Φ ] ≈ʷ σ i
  θ≈ i = proj₂ (σ⊆Φσ (gen∈ σ i))

  -- Applying θ, then σ, then Φ, is applying σ.
  turn : (w : LatTerm (Fin n)) → w [ θ ] [ σ ] [ Φ ] ≈ʷ w [ σ ]
  turn w = subst (_≈ʷ w [ σ ]) (trans ([]-⨟ w θ (σ ⨟ Φ)) ([]-⨟ (w [ θ ]) σ Φ)) ([]-congʳ w θ≈)

  -- The orbit of the j-th generator: θᵏ(xⱼ) evaluated at σ, an element of ⟨ σ ⟩.
  orbit : Fin n → ℕ → LatTerm X
  orbit j k = iter θ k j [ σ ]

  -- Φ steps the orbit back by one.
  back : ∀ j k → orbit j (suc k) [ Φ ] ≈ʷ orbit j k
  back j k = subst (λ v → v [ σ ] [ Φ ] ≈ʷ orbit j k) (sym ([]-iter-sucʳ (ℊ j) θ k))
                   (turn (iter θ k j))

  -- The d-th iterate of Φ steps the orbit back by d.
  back-by : ∀ j d k → orbit j (d + k) [ iter Φ d ] ≈ʷ orbit j k
  back-by j zero     k = ≡→≈ʷ ([]-ℊ (orbit j k))
  back-by j (suc d)  k = subst (_≈ʷ orbit j k) (sym ([]-iter-suc (orbit j (suc (d + k))) Φ d))
                               (≈ʷ-trans ([]-cong (iter Φ d) (back j (d + k))) (back-by j d k))
```

Along the orbit, complexity never rises above that of the generator
(`orbit-bound`{.AgdaFunction}): each element has at most the complexity of its
image under the embedding `Φ`, which is the element before it.  So the orbit
lies in the cover at the bound `c(gⱼ)`, and repeats
(`orbit-repeats`{.AgdaFunction}).

```agda
  -- The orbit has at most the complexity of the generator.
  orbit-bound : ∀ j k → c (orbit j k) ≤ c (σ j)
  orbit-bound j zero     = ≤-refl
  orbit-bound j (suc k)  =
    ≤-trans (complexity-mono _≟ˣ_ _≟ˣ_ Φ Φ-inj (orbit j (suc k)))
            (≤-trans (≤-reflexive (complexity-resp _≟ˣ_ (back j k))) (orbit-bound j k))

  -- The orbit repeats.
  orbit-repeats : ∀ j → Σ[ a ∈ ℕ ] Σ[ b ∈ ℕ ] a < b × orbit j a ≈ʷ orbit j b
  orbit-repeats j =
    let (L , covers) = cover (c (σ j))
    in pigeonhole-≈ L (orbit j) (λ k → covers (iter θ k j) (orbit-bound j k))
```

A repeat `mₐ ≈ m_b`, with `b = a + (1 + o)`, puts `gⱼ` at `m_(1+o)` (`gen≈`):
`gⱼ` is `m₀ ≈ Φᵃ(mₐ)`, and `Φᵃ(mₐ) ≈ Φᵃ(m_b) ≈ m_(1+o)`.  So `Φ(gⱼ)` is
`mₒ`, a member of `⟨ σ ⟩` (`image-gen`{.AgdaFunction}), and `Φ` maps
`⟨ σ ⟩` into itself (`image⊆`{.AgdaFunction}).

```agda
  -- The image under Φ of each generator lies in ⟨ σ ⟩.
  image-gen : ∀ j → ⟨ σ ⟩ (σ j [ Φ ])
  image-gen j = iter θ o j , ≈ʷ-sym (≈ʷ-trans ([]-cong Φ gen≈) (back j o))
    where
    a b o : ℕ
    a = proj₁ (orbit-repeats j)
    b = proj₁ (proj₂ (orbit-repeats j))
    o = proj₁ (m≤n⇒∃[o]m+o≡n (proj₁ (proj₂ (proj₂ (orbit-repeats j)))))

    -- The repeat.
    ma≈mb : orbit j a ≈ʷ orbit j b
    ma≈mb = proj₂ (proj₂ (proj₂ (orbit-repeats j)))

    -- b is a + (1 + o).
    b≡ : b ≡ a + suc o
    b≡ = trans (sym (proj₂ (m≤n⇒∃[o]m+o≡n (proj₁ (proj₂ (proj₂ (orbit-repeats j)))))))
               (sym (+-suc a o))

    -- The generator is the (1 + o)-th element of its orbit.
    gen≈ : σ j ≈ʷ orbit j (suc o)
    gen≈ =
      ≈ʷ-trans (≈ʷ-sym (subst (λ i → orbit j i [ iter Φ a ] ≈ʷ σ j) (+-identityʳ a) (back-by j a 0)))
        (≈ʷ-trans ([]-cong (iter Φ a) ma≈mb)
          (subst (λ i → orbit j i [ iter Φ a ] ≈ʷ orbit j (suc o)) (sym b≡) (back-by j a (suc o))))

  -- Φ maps ⟨ σ ⟩ into itself.
  image⊆ : ⟨ σ ⨟ Φ ⟩ ⊆ ⟨ σ ⟩
  image⊆ = gens⊆ image-gen
```

#### Finitely many generators suffice

A family `σ` of `n + 1` terms uses finitely many generators of `X`.  Listed
from left to right (`vars`{.AgdaFunction}, `varsᶠ`{.AgdaFunction}) and with
repetitions removed, they are a list `gens`{.AgdaFunction} of length `r`
without repetitions, and every generator occurring in a value `t [ σ ]` is
among them (`∈gens`{.AgdaFunction}).  Reading position `i` as the `i`-th of
them is a substitution `ν`{.AgdaFunction} from `Fin r` to `X`, and sending each
generator to its position (any position, for a generator not in the list) is a
substitution `ρ`{.AgdaFunction} back.  For a term whose generators are among
`gens`, localizing by `ρ` and reading back by `ν` returns the term
(`ρν`{.AgdaFunction}); and since the list has no repetitions, the position of
the `i`-th generator is `i` (`position-lookup`{.AgdaFunction}), so `ρ` undoes
`ν` (`νρ`{.AgdaFunction}) and `ν` is injective (`ν-inj`{.AgdaFunction}).

```agda
-- The generators occurring in a term, from left to right.
vars : LatTerm X → List X
vars (ℊ x)    = x ∷ []
vars (s ∧̇ t)  = vars s ++ vars t
vars (s ∨̇ t)  = vars s ++ vars t

-- The generators occurring in a family of n terms.
varsᶠ : (n : ℕ) → Sub (Fin n) X → List X
varsᶠ zero     σ = []
varsᶠ (suc n)  σ = vars (σ zero) ++ varsᶠ n (σ ∘ suc)

-- A generator of a member of the family occurs in the family.
∈varsᶠ : (σ : Sub (Fin n) X) (i : Fin n) {x : X} → x ∈ vars (σ i) → x ∈ varsᶠ n σ
∈varsᶠ σ zero     p = ∈-++⁺ˡ p
∈varsᶠ σ (suc i)  p = ∈-++⁺ʳ (vars (σ zero)) (∈varsᶠ (σ ∘ suc) i p)

-- A generator of a value t [ σ ] occurs in some member of σ.
vars-[] : (σ : Sub I X) (t : LatTerm I) {x : X} → x ∈ vars (t [ σ ]) → Σ[ i ∈ I ] x ∈ vars (σ i)
vars-[] σ (ℊ i)    p = i , p
vars-[] σ (s ∧̇ t)  p = [ vars-[] σ s , vars-[] σ t ]′ (∈-++⁻ (vars (s [ σ ])) p)
vars-[] σ (s ∨̇ t)  p = [ vars-[] σ s , vars-[] σ t ]′ (∈-++⁻ (vars (s [ σ ])) p)

-- The leftmost generator of a term.
first : LatTerm X → X
first (ℊ x)    = x
first (s ∧̇ _)  = first s
first (s ∨̇ _)  = first s

-- The leftmost generator occurs in the term.
first∈ : (t : LatTerm X) → first t ∈ vars t
first∈ (ℊ x)    = here refl
first∈ (s ∧̇ _)  = ∈-++⁺ˡ (first∈ s)
first∈ (s ∨̇ _)  = ∈-++⁺ˡ (first∈ s)

-- In a list without repetitions, lookup is injective.
lookup-injective : {xs : List X} → Unique xs → ∀ i j → lookup xs i ≡ lookup xs j → i ≡ j
lookup-injective (_ ∷ _)   zero     zero     _ = refl
lookup-injective (x≢ ∷ _)  zero     (suc j)  e = ⊥-elim (All.lookup x≢ (∈-lookup j) e)
lookup-injective (x≢ ∷ _)  (suc i)  zero     e = ⊥-elim (All.lookup x≢ (∈-lookup i) (sym e))
lookup-injective (_ ∷ u)   (suc i)  (suc j)  e = cong suc (lookup-injective u i j e)

-- There is no lattice term over no generators.
no-term : LatTerm (Fin 0) → ⊥
no-term (ℊ ())
no-term (s ∧̇ _)  = no-term s
no-term (s ∨̇ _)  = no-term s

module Local {X : Type χ} (_≟ˣ_ : DecidableEquality X) {n : ℕ} (σ : Sub (Fin (suc n)) X) where
  open import Data.List.Membership.DecPropositional _≟ˣ_ using ( _∈?_ )
  open import Data.List.Relation.Unary.Unique.DecPropositional.Properties _≟ˣ_
    using ( deduplicate-! )

  -- The generators σ uses, each once.
  gens : List X
  gens = deduplicate _≟ˣ_ (varsᶠ (suc n) σ)

  -- Their number.
  r : ℕ
  r = length gens

  -- Every generator of a value t [ σ ] is among them.
  ∈gens : (t : LatTerm (Fin (suc n))) {x : X} → x ∈ vars (t [ σ ]) → x ∈ gens
  ∈gens t p = let (i , q) = vars-[] σ t p in ∈-deduplicate⁺ _≟ˣ_ (∈varsᶠ σ i q)

  -- A default position, that of the leftmost generator of σ 0.
  default : Fin r
  default = index (∈gens (ℊ zero) (first∈ (σ zero)))

  -- The position a decision of membership finds, or the default.
  position : {x : X} → Dec (x ∈ gens) → Fin r
  position (yes p)  = index p
  position (no _)   = default

  -- A generator in the list sits at the position found for it.
  position-sound : {x : X} (d : Dec (x ∈ gens)) → x ∈ gens → lookup gens (position d) ≡ x
  position-sound (yes p)   _ = sym (lookup-index p)
  position-sound (no ∉gs)  p = ⊥-elim (∉gs p)

  -- The position found for the i-th generator is i.
  position-lookup : (i : Fin r) (d : Dec (lookup gens i ∈ gens)) → position d ≡ i
  position-lookup i (yes p)   =
    lookup-injective (deduplicate-! (varsᶠ (suc n) σ)) (index p) i (sym (lookup-index p))
  position-lookup i (no ∉gs)  = ⊥-elim (∉gs (∈-lookup i))

  -- Localization: each generator to its position.
  ρ : Sub X (Fin r)
  ρ x = ℊ (position (x ∈? gens))

  -- Reading back: each position to its generator.
  ν : Sub (Fin r) X
  ν i = ℊ (lookup gens i)

  -- Localizing a term over gens and reading it back returns it.
  ρν : (t : LatTerm X) → (∀ {x} → x ∈ vars t → x ∈ gens) → t [ ρ ] [ ν ] ≡ t
  ρν (ℊ x)    h = cong ℊ (position-sound (x ∈? gens) (h (here refl)))
  ρν (s ∧̇ t)  h = cong₂ _∧̇_ (ρν s (λ p → h (∈-++⁺ˡ p))) (ρν t (λ p → h (∈-++⁺ʳ (vars s) p)))
  ρν (s ∨̇ t)  h = cong₂ _∨̇_ (ρν s (λ p → h (∈-++⁺ˡ p))) (ρν t (λ p → h (∈-++⁺ʳ (vars s) p)))

  -- Reading back and localizing returns the term, up to equality.
  νρ : (s : LatTerm (Fin r)) → s [ ν ] [ ρ ] ≈ʷ s
  νρ s = subst₂ _≈ʷ_ ([]-⨟ s ν ρ) ([]-ℊ s)
                ([]-congʳ s (λ i → ≡→≈ʷ (cong ℊ (position-lookup i (lookup gens i ∈? gens)))))

  -- Reading back is injective.
  ν-inj : IsInjective (proj₁ (subst-hom ν))
  ν-inj {s} {t} e = ≈ʷ-trans (≈ʷ-sym (νρ s)) (≈ʷ-trans ([]-cong ρ e) (νρ t))
```

So an element `t [ σ ]` of complexity at most `B` is read back from its
localization `t [ σ ] [ ρ ]`, which by `ν-inj`{.AgdaFunction} and
`complexity-mono`{.AgdaFunction} has complexity at most `B` in `FL(r)`, and is
therefore equal to a member of `bounded B`{.AgdaFunction} of
[Lattices.Free.Complexity][].  The members of `bounded B`, read back, are the
cover that `Orbit`{.AgdaModule} asks for (`cover`{.AgdaFunction}).

```agda
  open Bounded (_≟_ {r}) (allFin r) ∈-allFin using ( bounded ; bounded-complete )

  -- The elements of FL(r) of complexity at most B, read back, cover those of ⟨ σ ⟩.
  cover : (B : ℕ) → Σ[ L ∈ List (LatTerm X) ]
            ((t : LatTerm (Fin (suc n))) → complexity _≟ˣ_ (t [ σ ]) ≤ B → Any (t [ σ ] ≈ʷ_) L)
  cover B = map (_[ ν ]) (bounded B) , covers
    where
    covers : (t : LatTerm (Fin (suc n))) → complexity _≟ˣ_ (t [ σ ]) ≤ B
           → Any (t [ σ ] ≈ʷ_) (map (_[ ν ]) (bounded B))
    covers t b = map⁺ (Any.map (λ e → subst (_≈ʷ _) round ([]-cong ν e))
                               (bounded-complete B (t [ σ ] [ ρ ]) local-bound))
      where
      -- The localization reads back to the element.
      round : t [ σ ] [ ρ ] [ ν ] ≡ t [ σ ]
      round = ρν (t [ σ ]) (∈gens t)

      -- The localization has complexity at most B.
      local-bound : complexity _≟_ (t [ σ ] [ ρ ]) ≤ B
      local-bound = ≤-trans (complexity-mono _≟_ _≟ˣ_ ν ν-inj (t [ σ ] [ ρ ]))
                            (subst (_≤ B) (cong (complexity _≟ˣ_) (sym round)) b)
```

#### Theorem A

For generators with decidable equality, `Orbit`{.AgdaModule} with the cover of
`Local`{.AgdaModule} proves Theorem A (`generated-onto`{.AgdaFunction}): an
injective `Φ` whose image of `⟨ σ ⟩` contains `⟨ σ ⟩` maps `⟨ σ ⟩` into itself,
and so onto itself (`generated-onto≐`{.AgdaFunction}).  A family of no terms
generates nothing, and the theorem holds of it trivially.  Decidable equality is
the hypothesis Theorem H has, and it enters for the same reason, to compute
canonical forms and so complexities.

```agda
-- Theorem A: an injective Φ whose image of ⟨ σ ⟩ contains ⟨ σ ⟩ maps ⟨ σ ⟩ into itself.
generated-onto : {X : Type χ} → DecidableEquality X → {n : ℕ} (σ : Sub (Fin n) X)
               → (Φ : Sub X X) → FreelyGenerates Φ → ⟨ σ ⟩ ⊆ ⟨ σ ⨟ Φ ⟩ → ⟨ σ ⨟ Φ ⟩ ⊆ ⟨ σ ⟩
generated-onto _≟ˣ_ {zero}   σ Φ Φ-free σ⊆Φσ (t , _) = ⊥-elim (no-term t)
generated-onto _≟ˣ_ {suc n}  σ Φ Φ-free σ⊆Φσ =
  Orbit.image⊆ _≟ˣ_ σ (Local.cover _≟ˣ_ σ) Φ (freelyGenerates→injective Φ Φ-free) σ⊆Φσ

-- Theorem A, as the paper states it: Φ(L) = L.
generated-onto≐ : {X : Type χ} → DecidableEquality X → {n : ℕ} (σ : Sub (Fin n) X)
                → (Φ : Sub X X) → FreelyGenerates Φ → ⟨ σ ⟩ ⊆ ⟨ σ ⨟ Φ ⟩ → ⟨ σ ⨟ Φ ⟩ ≐ ⟨ σ ⟩
generated-onto≐ _≟ˣ_ σ Φ Φ-free σ⊆Φσ = generated-onto _≟ˣ_ σ Φ Φ-free σ⊆Φσ , σ⊆Φσ
```

**Theorem A** of [the paper][], as one statement: for an injective
endomorphism `Φ` of `FL(X)`, a substitution that freely generates (Corollary
2.5), and a finitely generated sublattice `L = ⟨ σ ⟩`, if `L ⊆ Φ(L)` then
`Φ(L) = L`, where `Φ(L)` is `⟨ σ ⨟ Φ ⟩`, the sublattice the images `Φ(σ i)`
generate (`image⇔`{.AgdaFunction}).  The hypothesis beyond the paper's is
decidable equality on the generators, which the complexity of Theorem B
needs.

```agda
-- Theorem A: an injective endomorphism that maps a finitely generated sublattice L onto a
-- superset of L maps it onto L.
Theorem-A : Setω
Theorem-A =  ∀ {χ} {X : Type χ} → DecidableEquality X → {n : ℕ} (σ : Sub (Fin n) X)
             → (Φ : Sub X X) → FreelyGenerates Φ → ⟨ σ ⟩ ⊆ ⟨ σ ⨟ Φ ⟩ → ⟨ σ ⨟ Φ ⟩ ≐ ⟨ σ ⟩

-- The proof of Theorem A.
theorem-A : Theorem-A
theorem-A = generated-onto≐
```

#### Corollary A3

If `⟨ σ ⟩ ⊆ ⟨ τ ⟩` and an injective `Φ` maps `⟨ σ ⟩` onto a sublattice
containing `⟨ τ ⟩`, then `⟨ τ ⟩ ⊆ ⟨ σ ⟩` (`collapse`{.AgdaFunction}).  In a
strictly ascending chain this cannot happen for links `j < k`
(`no-onto-later`{.AgdaFunction}), and in particular no injective `Φ` carries
link `j` onto link `k` (`no-image-later`{.AgdaFunction}).

```agda
-- If ⟨ σ ⟩ ⊆ ⟨ τ ⟩ ⊆ Φ(⟨ σ ⟩) with Φ injective, then ⟨ τ ⟩ lies in ⟨ σ ⟩.
collapse : DecidableEquality X → (σ : Sub (Fin n) X) (τ : Sub J X) (Φ : Sub X X) → FreelyGenerates Φ
         → ⟨ σ ⟩ ⊆ ⟨ τ ⟩ → ⟨ τ ⟩ ⊆ ⟨ σ ⨟ Φ ⟩ → ⟨ τ ⟩ ⊆ ⟨ σ ⟩
collapse _≟ˣ_ σ τ Φ Φ-free σ⊆τ τ⊆Φσ p =
  generated-onto _≟ˣ_ σ Φ Φ-free (λ q → τ⊆Φσ (σ⊆τ q)) (τ⊆Φσ p)

module _ (_≟ˣ_ : DecidableEquality X) (c : StrictlyAscending n X) where
  open StrictlyAscending c

  private
    -- The chain, read as an ascending one.
    c′ : Ascending n X
    c′ = strict→ascending c

  -- Corollary A3: no injective Φ maps a link onto a sublattice containing a later link.
  no-onto-later : (Φ : Sub X X) → FreelyGenerates Φ → ∀ {j k} → j < k
                → ¬ (⟨ links k ⟩ ⊆ ⟨ links j ⨟ Φ ⟩)
  no-onto-later Φ Φ-free {j} {k} j<k k⊆ =
    proj₂ (ascends j) (λ p → collapse _≟ˣ_ (links j) (links k) Φ Φ-free (ascends-≤ c′ (<⇒≤ j<k)) k⊆
                                      (ascends-≤ c′ j<k p))

  -- In particular, no injective Φ carries a link onto a later link.
  no-image-later : (Φ : Sub X X) → FreelyGenerates Φ → ∀ {j k} → j < k
                 → ¬ (⟨ links j ⨟ Φ ⟩ ≐ ⟨ links k ⟩)
  no-image-later Φ Φ-free j<k e = no-onto-later Φ Φ-free j<k (proj₂ e)
```

#### Building and moving strictly ascending chains

A chain is often found in two kinds of steps, from links `e k` to links `o k`
and from `o k` to `e (k + 1)`.  Interleaving the two sequences
(`interleave`{.AgdaFunction}: `e 0, o 0, e 1, o 1, …`) gives one sequence, and
a relation that holds across both kinds of steps holds between consecutive
terms of it (`interleave-step`{.AgdaFunction}), by induction on the position
with the roles of the two sequences exchanged at each step.  So two families
of proper steps make a strictly ascending chain
(`interleaved-chain`{.AgdaFunction}), and a property of every term of both
sequences holds of every interleaved term (`interleave-all`{.AgdaFunction}).
The term at `2k` is `e k` and the term at `2k + 1` is `o k`
(`interleave-even`{.AgdaFunction}, `interleave-odd`{.AgdaFunction}).

```agda
-- Interleave two sequences: e 0, o 0, e 1, o 1, ….
interleave : {A : Type ι} → (ℕ → A) → (ℕ → A) → ℕ → A
interleave e o zero     = e zero
interleave e o (suc n)  = interleave o (λ k → e (suc k)) n

-- A relation across both kinds of steps holds between consecutive interleaved terms.
interleave-step : {A : Type ι} {ℓ : Level} (R : A → A → Type ℓ) (e o : ℕ → A)
                → (∀ k → R (e k) (o k)) → (∀ k → R (o k) (e (suc k)))
                → ∀ n → R (interleave e o n) (interleave e o (suc n))
interleave-step R e o eo oe zero     = eo zero
interleave-step R e o eo oe (suc n)  =
  interleave-step R o (λ k → e (suc k)) oe (λ k → eo (suc k)) n

-- A property of every term of both sequences holds of every interleaved term.
interleave-all : {A : Type ι} {ℓ : Level} (P : A → Type ℓ) (e o : ℕ → A)
               → (∀ k → P (e k)) → (∀ k → P (o k)) → ∀ n → P (interleave e o n)
interleave-all P e o pe po zero     = pe zero
interleave-all P e o pe po (suc n)  = interleave-all P o (λ k → e (suc k)) po (λ k → pe (suc k)) n

-- The interleaved term at 2k is e k, and the one at 2k + 1 is o k.
interleave-even : {A : Type ι} (e o : ℕ → A) (k : ℕ) → interleave e o (2 * k) ≡ e k
interleave-even e o zero     = refl
interleave-even e o (suc k)  = trans (cong (interleave e o) (*-suc 2 k))
                                     (interleave-even (λ k → e (suc k)) (λ k → o (suc k)) k)

interleave-odd : {A : Type ι} (e o : ℕ → A) (k : ℕ) → interleave e o (suc (2 * k)) ≡ o k
interleave-odd e o k = interleave-even o (λ k → e (suc k)) k

-- Two families of proper steps make a strictly ascending chain.
interleaved-chain : (e o : ℕ → Sub (Fin n) X)
                  → (∀ k → ⟨ e k ⟩ ⊂ ⟨ o k ⟩) → (∀ k → ⟨ o k ⟩ ⊂ ⟨ e (suc k) ⟩)
                  → StrictlyAscending n X
interleaved-chain e o eo oe = record
  { links    = interleave e o
  ; ascends  = interleave-step (λ σ τ → ⟨ σ ⟩ ⊂ ⟨ τ ⟩) e o eo oe
  }
```

An injective substitution `ι` of `X` into `Y` carries containments of generated
sublattices to containments (`⊆-⨟`{.AgdaFunction}) and reflects them
(`⊆-⨟⁻`{.AgdaFunction}): the value of a term at `σ ⨟ ι` is the image under `ι`
of its value at `σ`.  So it carries a strictly ascending chain of `FL(X)` to one
of `FL(Y)` (`strict-⨟`{.AgdaFunction}), and a chain found in `FL(3)` is a chain
in every free lattice that contains a copy of `FL(3)`.

```agda
-- An injective substitution carries containment of generated sublattices.
⊆-⨟ : {σ : Sub I X} {τ : Sub J X} (ι : Sub X Y) → ⟨ σ ⟩ ⊆ ⟨ τ ⟩ → ⟨ σ ⨟ ι ⟩ ⊆ ⟨ τ ⨟ ι ⟩
⊆-⨟ {σ = σ} {τ} ι h = gens⊆ λ i →
  let (t , e) = h (gen∈ σ i) in t , subst (_≈ʷ _) (sym ([]-⨟ t τ ι)) ([]-cong ι e)

-- An injective substitution reflects containment of generated sublattices.
⊆-⨟⁻ : {σ : Sub I X} {τ : Sub J X} (ι : Sub X Y) → IsInjective (proj₁ (subst-hom ι))
     → ⟨ σ ⨟ ι ⟩ ⊆ ⟨ τ ⨟ ι ⟩ → ⟨ σ ⟩ ⊆ ⟨ τ ⟩
⊆-⨟⁻ {σ = σ} {τ} ι inj h = gens⊆ λ i →
  let (t , e) = h (gen∈ (σ ⨟ ι) i) in t , inj (subst (_≈ʷ _) ([]-⨟ t τ ι) e)

-- A strictly ascending chain carried along an injective substitution.
strict-⨟ : StrictlyAscending n X → (ι : Sub X Y) → IsInjective (proj₁ (subst-hom ι))
         → StrictlyAscending n Y
strict-⨟ c ι inj = record
  { links    = λ k → links k ⨟ ι
  ; ascends  = λ k → ⊆-⨟ ι (proj₁ (ascends k)) , λ h → proj₂ (ascends k) (⊆-⨟⁻ ι inj h)
  }
  where open StrictlyAscending c
```

#### A copy of FL(n) generated by n elements is freely generated by them

An injective map of `Fin n` into itself reaches every element
(`fin-injective→onto`{.AgdaFunction}): if it missed `k`, it would map the
`n` indices into the `n - 1` others, and the pigeonhole principle would put
two indices at one place.

```agda
private
  -- The search for a preimage of k, on the decision of whether there is one.
  onto-search : {m : ℕ} (π : Fin (suc m) → Fin (suc m)) → (∀ {i j} → π i ≡ π j → i ≡ j)
              → (k : Fin (suc m)) → Dec (Σ[ i ∈ Fin (suc m) ] π i ≡ k) → Σ[ i ∈ Fin (suc m) ] π i ≡ k
  onto-search π inj k (yes found)  = found
  onto-search {m} π inj k (no none) =
    let (i , j , i<j , e) = pigeonhole (n<1+n m) (λ i → punchOut (miss i))
    in ⊥-elim (<ᶠ⇒≢ i<j (inj (punchOut-injective (miss i) (miss j) e)))
    where
    -- No index is sent to k.
    miss : ∀ i → k ≢ π i
    miss i e = none (i , sym e)

-- An injective map of Fin n into itself reaches every element.
fin-injective→onto : {n : ℕ} (π : Fin n → Fin n) → (∀ {i j} → π i ≡ π j → i ≡ j)
                   → ∀ k → Σ[ i ∈ Fin n ] π i ≡ k
fin-injective→onto {suc m} π inj k = onto-search π inj k (any? (λ i → π i ≟ k))
```

Let an embedding `e` of `FL(n)` in `FL(X)` have as its copy the sublattice
`⟨ σ ⟩` that `n` elements generate.  Then `σ` freely generates
(`copy≐→freelyGenerates`{.AgdaFunction}), by the argument of the paper's
Theorem 4.5.  Write `r` for the images of the generators of `FL(n)`, which
freely generate (`≤→freelyGenerates`{.AgdaFunction} of
[DeansProblem.Chain.Copies][]).  Each `σ j` lies in the copy, so
`σ j = ρ j [ r ]` for a term `ρ j`; each `r i` lies in `⟨ σ ⟩`, so it is the
value of a term at `σ`, hence at `ρ ⨟ r`, and Corollary 2.4
(`free-generator-in-image`{.AgdaFunction}) makes the generator `ℊ i` equal to
some `ρ (π i)`.  Distinct generators are unequal, so `π` is injective, hence
onto, and `σ k = r (π⁻¹ k)`: the family `σ` is `r` re-indexed by a bijection.

```agda
module _ {X : Type χ} {n : ℕ} (e : proj₁ (FL (Fin n)) IsSubalgebraOf proj₁ (FL X))
         (σ : Sub (Fin n) X) (e≐ : copy e ≐ ⟨ σ ⟩) where
  private
    -- The images of the generators, which freely generate.
    r : Sub (Fin n) X
    r = restriction (proj₁ e)

    r-inj : IsInjective (proj₁ (subst-hom r))
    r-inj = freelyGenerates→injective r (≤→freelyGenerates e)

    -- A term over the generators naming each σ j in the copy.
    ρ : Sub (Fin n) (Fin n)
    ρ j = proj₁ (proj₂ e≐ (gen∈ σ j))

    σ≈ρ : ∀ j → σ j ≈ʷ ρ j [ r ]
    σ≈ρ j = ≈ʷ-trans (≈ʷ-sym (proj₂ (proj₂ e≐ (gen∈ σ j)))) (hom-induced (proj₁ e) (ρ j))

    -- Each generator is one of the terms ρ (Corollary 2.4).
    hit : ∀ i → Σ[ j ∈ Fin n ] ℊ i ≈ʷ ρ j
    hit i = let (s , s≈) = proj₁ e≐ (ℊ i , hom-induced (proj₁ e) (ℊ i))
            in free-generator-in-image r r-inj ρ s
                 (≈ʷ-trans (≈ʷ-sym s≈) ([]-congʳ s σ≈ρ))

    π : Fin n → Fin n
    π i = proj₁ (hit i)

    π-inj : ∀ {i i'} → π i ≡ π i' → i ≡ i'
    π-inj {i} {i'} p =
      ℊ-injective (≈ʷ-trans (proj₂ (hit i))
                            (subst (λ j → ρ j ≈ʷ ℊ i') (sym p) (≈ʷ-sym (proj₂ (hit i')))))

    -- The inverse of π.
    π⁻ : Fin n → Fin n
    π⁻ k = proj₁ (fin-injective→onto π π-inj k)

    ππ⁻ : ∀ k → π (π⁻ k) ≡ k
    ππ⁻ k = proj₂ (fin-injective→onto π π-inj k)

    π⁻-inj : ∀ {k k'} → π⁻ k ≡ π⁻ k' → k ≡ k'
    π⁻-inj {k} {k'} p = trans (sym (ππ⁻ k)) (trans (cong π p) (ππ⁻ k'))

    -- σ is r re-indexed by π⁻.
    rπ⁻≈σ : ∀ k → r (π⁻ k) ≈ʷ σ k
    rπ⁻≈σ k = ≈ʷ-sym (≈ʷ-trans (σ≈ρ k) ([]-cong r (subst (λ j → ρ j ≈ʷ ℊ (π⁻ k)) (ππ⁻ k)
                                                         (≈ʷ-sym (proj₂ (hit (π⁻ k)))))))

  -- A copy of FL(n) generated by n elements is freely generated by them.
  copy≐→freelyGenerates : FreelyGenerates σ
  copy≐→freelyGenerates =
    freelyGenerates-resp rπ⁻≈σ (freelyGenerates-reindex r π⁻ π⁻-inj (≤→freelyGenerates e))
```

#### Corollary A3 for links with any numbers of generators

Corollary A3 of [the paper][] speaks of a chain of finitely generated
sublattices, with no common number of generators.  A strictly ascending chain
of finitely generated sublattices (`StrictlyAscendingᶠ`{.AgdaRecord}) has its
`k`-th link generated by `rank k` elements; a chain of `n`-generated
sublattices is one with constant rank (`strict→strictᶠ`{.AgdaFunction}).  Each
link lies in every later one (`ascendsᶠ-≤`{.AgdaFunction}), and Corollary A3
holds as the paper states it (`no-onto-laterᶠ`{.AgdaFunction},
`no-image-laterᶠ`{.AgdaFunction}), by `collapse`{.AgdaFunction} as before,
which never asked the two families to have the same number of members.

```agda
-- A strictly ascending chain of finitely generated sublattices of FL(X).
record StrictlyAscendingᶠ (X : Type χ) : Type χ where
  field
    rank     : ℕ → ℕ
    links    : (k : ℕ) → Sub (Fin (rank k)) X
    ascends  : ∀ k → ⟨ links k ⟩ ⊂ ⟨ links (suc k) ⟩

-- A chain of n-generated sublattices is one of finitely generated sublattices.
strict→strictᶠ : StrictlyAscending n X → StrictlyAscendingᶠ X
strict→strictᶠ {n = n} c = record
  { rank     = λ _ → n
  ; links    = StrictlyAscending.links c
  ; ascends  = StrictlyAscending.ascends c
  }

module _ (c : StrictlyAscendingᶠ X) where
  open StrictlyAscendingᶠ c

  -- Each link lies in the link d places later.
  ascendsᶠ-+ : ∀ j d → ⟨ links j ⟩ ⊆ ⟨ links (d + j) ⟩
  ascendsᶠ-+ j zero     p = p
  ascendsᶠ-+ j (suc d)  p = proj₁ (ascends (d + j)) (ascendsᶠ-+ j d p)

  -- Each link lies in every later one.
  ascendsᶠ-≤ : ∀ {j k} → j ≤ k → ⟨ links j ⟩ ⊆ ⟨ links k ⟩
  ascendsᶠ-≤ {j} {k} j≤k {w} p =
    let (d , j+d≡k) = m≤n⇒∃[o]m+o≡n j≤k
    in subst (λ i → ⟨ links i ⟩ w) (trans (+-comm d j) j+d≡k) (ascendsᶠ-+ j d p)

module _ (_≟ˣ_ : DecidableEquality X) (c : StrictlyAscendingᶠ X) where
  open StrictlyAscendingᶠ c

  -- Corollary A3: no injective Φ maps a link onto a sublattice containing a later link.
  no-onto-laterᶠ : (Φ : Sub X X) → FreelyGenerates Φ → ∀ {j k} → j < k
                 → ¬ (⟨ links k ⟩ ⊆ ⟨ links j ⨟ Φ ⟩)
  no-onto-laterᶠ Φ Φ-free {j} {k} j<k k⊆ =
    proj₂ (ascends j) (λ p → collapse _≟ˣ_ (links j) (links k) Φ Φ-free (ascendsᶠ-≤ c (<⇒≤ j<k)) k⊆
                                      (ascendsᶠ-≤ c j<k p))

  -- Corollary A3 as the paper states it: no injective Φ has Φ(L j) = L k with j < k.
  no-image-laterᶠ : (Φ : Sub X X) → FreelyGenerates Φ → ∀ {j k} → j < k
                  → ¬ (⟨ links j ⨟ Φ ⟩ ≐ ⟨ links k ⟩)
  no-image-laterᶠ Φ Φ-free j<k e = no-onto-laterᶠ Φ Φ-free j<k (proj₂ e)
```

The remark after Corollary A3 says first that no chain is generated by one
embedding, even with a period: no injective `Φ` has `Φ(Lₖ) = Lₖ₊ₚ` for every
`k`, with a period `p ≥ 1` (`no-periodic-embedding`{.AgdaFunction}).  This is
Corollary A3 at `k = 0`, and it needs neither freeness of the links nor a
common number of generators.  (The remark's second claim, that the maps `θₖ`
of Definition 4.1 are never the powers of one map, is about a chain of copies
of `FL(3)` and does not follow from Corollary A3; [DeansProblem.Chain.Powers][]
proves it from Lemma 6.1.)

```agda
  -- No injective Φ carries every link onto the link p + 1 places later.
  no-periodic-embedding : (Φ : Sub X X) → FreelyGenerates Φ → (p : ℕ)
                        → ¬ (∀ k → ⟨ links k ⨟ Φ ⟩ ≐ ⟨ links (suc p + k) ⟩)
  no-periodic-embedding Φ Φ-free p every = no-image-laterᶠ Φ Φ-free {0} {suc p + 0} (s≤s z≤n) (every 0)
```

**Corollary A3** of [the paper][], as one statement: in a chain
`L₀ ⊊ L₁ ⊊ ⋯` of finitely generated sublattices of `FL(X)`, the links of any
ranks (`StrictlyAscendingᶠ`{.AgdaRecord}), no injective endomorphism `Φ` has
`Φ(Lⱼ) = Lₖ` with `j < k`.  The hypothesis beyond the paper's is decidable
equality on the generators, through Theorem A.

```agda
-- Corollary A3: in a chain of finitely generated sublattices, no injective endomorphism
-- maps a link onto a later one.
Corollary-A3 : Setω
Corollary-A3 =  ∀ {χ} {X : Type χ} → DecidableEquality X → (c : StrictlyAscendingᶠ X)
                → (Φ : Sub X X) → FreelyGenerates Φ → ∀ {j k} → j < k
                → ¬ (⟨ StrictlyAscendingᶠ.links c j ⨟ Φ ⟩ ≐ ⟨ StrictlyAscendingᶠ.links c k ⟩)

-- The proof of Corollary A3.
corollary-A3 : Corollary-A3
corollary-A3 = no-image-laterᶠ
```

--------------------------------------

[DeansProblem.Chain.Condition]: DeansProblem.Chain.Condition.html
[DeansProblem.Chain]: DeansProblem.Chain.html
[DeansProblem.Chain.Copies]: DeansProblem.Chain.Copies.html
[DeansProblem.Chain.Powers]: DeansProblem.Chain.Powers.html
[DeansProblem.Chain.TwoGenerated]: DeansProblem.Chain.TwoGenerated.html
[DeansProblem.Examples.ChainCondition]: DeansProblem.Examples.ChainCondition.html
[DeansProblem.NoChain]: DeansProblem.NoChain.html
[DeansProblem.SelfSimilar]: DeansProblem.SelfSimilar.html
[Lattices.Free.Complexity]: Lattices.Free.Complexity.html
