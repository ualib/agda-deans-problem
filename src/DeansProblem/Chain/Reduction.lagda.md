---
layout: default
file: "src/DeansProblem/Chain/Reduction.lagda.md"
title: "DeansProblem.Chain.Reduction module"
date: "2026-10-30"
author: "the agda-lattices development team"
---

### The reduction to FL(3)

This is the [DeansProblem.Chain.Reduction][] module of this repository.

[the paper]: https://arxiv.org/abs/YYMM.NNNNN

Section 1.1(i) of [the paper][] says: "Whitman proved that `FL(ω)`, the free
lattice on countably many generators, embeds in `FL(3)` (FJN, Theorem 1.28).
Hence if one free lattice has such a chain then every `FL(X)` with `|X| ≥ 3`
does, and `FL(3)` is the only case; for `|X| ≤ 2` the free lattice is
finite."  This module proves the second sentence up to its semicolon, for
chains of copies of `FL(3)` (`CopyChain`{.AgdaRecord} of
[DeansProblem.Chain.Copies][]), with decidable equality on the generators of
the free lattice the chain starts in, and with three distinct generators of
the one it ends in, `Fin 3 ↣ X`, the constructive reading of `|X| ≥ 3`.  No
decision on `X` is made.  The clause after the semicolon is agda-lattices'
[Lattices.Free.Small][], which enumerates `FL(X)` for `X` with at most two
elements.  The module imports neither
[DeansProblem.NoChain][] nor [DeansProblem.LengthThree][], directly or
through another module, so no statement here holds because no chain exists.

**An embedding carries a chain of copies to a chain of copies**
(`embed-copyChain`{.AgdaFunction}).  If `h` embeds `FL(Y)` in `FL(Z)` and
the `φ k` are the embeddings of a chain in `FL(Y)`, the composites `h ∘ φ k`
are embeddings of `FL(3)` in `FL(Z)`.  Their copies ascend, since `h` carries
the containment of one copy in the next; and strictly, since `h` is
injective: if the image of the next copy lay in the image of this one, the
next copy would lie in this one.

**Renumbering the generators**.  A chain in `FL(Y)` uses only countably many
generators of `Y`, the ones occurring in its triples, and renaming them by
natural numbers gives a chain in `FL(ℕ)` (`renumber`{.AgdaFunction}).  The
renaming is computed link by link, through the record of a chain
(`Chain`{.AgdaRecord} of [DeansProblem.Chain][]).  The generators used by
links `0` to `k` form a list (`used k`{.AgdaFunction}), each list extending
the one before; link `k` numbers a generator by the position of its first
occurrence in that list (`number k`{.AgdaFunction}), which needs decidable
equality on `Y` and no other decision.  So each numbering extends the one
before on the generators it numbers (`number-extends`{.AgdaFunction}), and
reading the list at a generator's number returns the generator
(`name-number`{.AgdaFunction}).  The `k`-th triple of the renumbered chain is
the `k`-th triple renamed by link `k`'s numbering.  The terms and the fresh
indices of the chain are kept, since they live in `FL(3)`:

+  the terms still express each triple in the next, because links `k` and
   `k + 1` number the generators of link `k` alike, and renaming is a
   homomorphism (`gens′≈`{.AgdaFunction});
+  each renamed triple still freely generates, by Corollary 1.13 of
   [Freese, Ježek, and Nation (1995)][], because renaming back by the list
   recovers the triple (`rename-unrename`{.AgdaFunction}), so that
   substitution by the renamed triple is injective
   (`gens′-injective`{.AgdaFunction}).

**The reduction**.  A chain of copies in `FL(Y)` gives the record of a chain
(`copyChain→chain`{.AgdaFunction}), which renumbers to one in `FL(ℕ)` and
gives a chain of copies there (`copyChain→ℕ`{.AgdaFunction}).  Theorem 1.28
of [Freese, Ježek, and Nation (1995)][] embeds `FL(ℕ)` in `FL(3)`
(`countable-embedding`{.AgdaFunction} of [Lattices.Free.Countable][]), which
carries it to a chain in `FL(3)` (`copyChain→FL₃`{.AgdaFunction}).  Three
distinct generators of `X` freely generate, by Corollary 1.5, so
substitution by them embeds `FL(3)` in `FL(X)`
(`three-embedding`{.AgdaFunction}), which carries a chain in `FL(3)` to one
in `FL(X)` (`FL₃→copyChain`{.AgdaFunction}).  So a chain in one free lattice
gives one in every `FL(X)` with three distinct generators
(`reduction`{.AgdaFunction}); and in a free lattice over generators with
decidable equality, three of them distinct, a chain exists exactly when one
exists in `FL(3)` (`copyChain⇔FL₃`{.AgdaFunction}).

<!--
```agda
{-# OPTIONS --without-K --exact-split --safe #-}

module DeansProblem.Chain.Reduction where

open import Agda.Primitive  using () renaming ( Set to Type )

-- Imports from the Agda Standard Library ---------------------------------------
open import Data.Fin.Base                          using ( Fin )
open import Data.Fin.Patterns                      using ( 0F ; 1F ; 2F )
open import Data.List.Base                         using ( List ; [] ; _∷_ ; _++_ )
open import Data.List.Membership.Propositional     using ( _∈_ )
open import Data.List.Membership.Propositional.Properties
                                                   using ( ∈-++⁺ˡ ; ∈-++⁺ʳ )
open import Data.List.Relation.Unary.Any           using ( here ; tail )
open import Data.Nat.Base                          using ( ℕ ; zero ; suc )
open import Data.Product                           using ( _,_ ; proj₁ ; proj₂ )
open import Function                               using ( Func ; _⇔_ ; mk⇔ ; _↣_ )
open import Level                                  using ( Level )
open import Relation.Binary.Definitions            using ( DecidableEquality )
open import Relation.Binary.PropositionalEquality  using ( _≡_ ; refl ; sym ; trans ; cong ; cong₂ )
open import Relation.Nullary                       using ( ¬_ ; yes ; no )
open import Relation.Unary                         using ( _⊆_ )

import Relation.Binary.Reasoning.Setoid as SetoidReasoning

-- Imports from the Agda Universal Algebra Library ------------------------------
open import Setoid.Functions                       using ( IsInjective )
open import Setoid.Subalgebras.Basic               using ( _≤_ )
open import Setoid.Subalgebras.Properties          using ( ≤-trans )

-- Imports from agda-lattices ---------------------------------------------------
open import Lattices.Free.Canonical.Basic          using ( ≈ʷ-refl ; ≈ʷ-trans )
open import Lattices.Free.Countable                using ( countable-embedding ; three-generators
                                                         ; three-generators-free )
open import Lattices.Free.Extrema                  using ( generators ; generators-∷ )
open import Lattices.Free.Generation               using ( FreelyGenerates ; freelyGenerates→≤
                                                         ; freelyGenerates→injective
                                                         ; injective→freelyGenerates )
open import Lattices.Free.Substitution             using ( Sub ; _[_] ; _⨟_ ; []-ℊ ; []-⨟ ; []-cong
                                                         ; subst-hom )
open import Lattices.Free.Term                     using ( LatTerm ; ℊ ; _∧̇_ ; _∨̇_ )
open import Lattices.Free.Universal                using ( FL ; FL-setoid )
open import Lattices.Free.Whitman                  using ( _≈ʷ_ )

-- Imports from this development ------------------------------------------------
open import DeansProblem.Chain                     using ( Chain ; module Chain )
open import DeansProblem.Chain.Copies              using ( CopyChain ; copy ; copyChain→chain
                                                         ; chain→copyChain )

open Func using () renaming ( cong to func-cong )

private variable
  χ υ ζ : Level
  X : Type χ
  Z : Type ζ
```
-->

#### An embedding carries a chain of copies to a chain of copies

Fix an embedding `h` of `FL(Y)` in `FL(Z)` and a chain of copies in `FL(Y)`.
The `k`-th embedding of the new chain is `h ∘ φ k`.

```agda
module _ {Y : Type υ} (h : proj₁ (FL Y) ≤ proj₁ (FL Z)) (c : CopyChain Y) where
  open CopyChain c

  -- The k-th embedding, followed by h.
  embed-φ : ℕ → proj₁ (FL (Fin 3)) ≤ proj₁ (FL Z)
  embed-φ k = ≤-trans (φ k) h

  -- Each copy lies in the next: h carries the containment.
  embed-⊆ : (k : ℕ) → copy (embed-φ k) ⊆ copy (embed-φ (suc k))
  embed-⊆ k (a , ez) = let (b , eb) = proj₁ (ascends k) (a , ≈ʷ-refl) in
    b , ≈ʷ-trans (func-cong (proj₁ (proj₁ h)) eb) ez

  -- The next copy does not lie in this one, since h is injective.
  embed-⊉ : (k : ℕ) → ¬ (copy (embed-φ (suc k)) ⊆ copy (embed-φ k))
  embed-⊉ k ⊇ = proj₂ (ascends k) λ (b , ey) → let (a , ea) = ⊇ (b , ≈ʷ-refl) in
    a , ≈ʷ-trans (proj₂ h ea) ey

  -- The chain of copies in FL(Z).
  embed-copyChain : CopyChain Z
  embed-copyChain = record
    { φ        = embed-φ
    ; ascends  = λ k → embed-⊆ k , embed-⊉ k
    }
```

#### Positions in a list

With decidable equality, the position of the first occurrence of an element
in a list (`position`{.AgdaFunction}) does not change when the list is
extended (`position-++`{.AgdaFunction}), and reading the list at the position
of a member returns the member (`at-position`{.AgdaFunction}); past the end of
the list, `at`{.AgdaFunction} returns a default.

```agda
private
  -- The element at a position, or d past the end.
  at : {Y : Type υ} → Y → List Y → ℕ → Y
  at d []        n        = d
  at d (x ∷ xs)  zero     = x
  at d (x ∷ xs)  (suc n)  = at d xs n

  module _ {Y : Type υ} (_≟ʸ_ : DecidableEquality Y) where

    -- The position of the first occurrence of y in a list.
    position : List Y → Y → ℕ
    position []        y = zero
    position (x ∷ xs)  y with x ≟ʸ y
    ... | yes _ = zero
    ... | no  _ = suc (position xs y)

    -- Reading the list at the position of a member returns the member.
    at-position : (d : Y) (xs : List Y) {y : Y} → y ∈ xs → at d xs (position xs y) ≡ y
    at-position d (x ∷ xs) {y} y∈ with x ≟ʸ y
    ... | yes x≡y  = x≡y
    ... | no  x≢y  = at-position d xs (tail (λ y≡x → x≢y (sym y≡x)) y∈)

    -- A member keeps its position when the list is extended.
    position-++ : (xs ys : List Y) {y : Y} → y ∈ xs → position (xs ++ ys) y ≡ position xs y
    position-++ (x ∷ xs) ys {y} y∈ with x ≟ʸ y
    ... | yes _    = refl
    ... | no  x≢y  = cong suc (position-++ xs ys (tail (λ y≡x → x≢y (sym y≡x)) y∈))
```

#### The generators of a triple

Two substitutions that agree on the generators of a term give the same term
(`[]-agree`{.AgdaFunction}), by induction on the term.  The generators of a
triple are those of its three members (`triple-generators`{.AgdaFunction}).

```agda
  -- Substitutions that agree on the generators of a term agree on the term.
  []-agree : {Y : Type υ} (t : LatTerm Y) {σ τ : Sub Y Z}
    → (∀ {y} → y ∈ generators t → σ y ≡ τ y) → t [ σ ] ≡ t [ τ ]
  []-agree (ℊ y)    e = e (here refl)
  []-agree (s ∧̇ t)  e = cong₂ _∧̇_ ([]-agree s (λ p → e (∈-++⁺ˡ p)))
                                  ([]-agree t (λ p → e (∈-++⁺ʳ (generators s) p)))
  []-agree (s ∨̇ t)  e = cong₂ _∨̇_ ([]-agree s (λ p → e (∈-++⁺ˡ p)))
                                  ([]-agree t (λ p → e (∈-++⁺ʳ (generators s) p)))

  -- The generators of a triple, member by member, with repetitions.
  triple-generators : {Y : Type υ} → Sub (Fin 3) Y → List Y
  triple-generators σ = generators (σ 0F) ++ generators (σ 1F) ++ generators (σ 2F)

  -- A generator of a member is a generator of the triple.
  ∈-triple : {Y : Type υ} (σ : Sub (Fin 3) Y) (i : Fin 3) {y : Y}
    → y ∈ generators (σ i) → y ∈ triple-generators σ
  ∈-triple σ 0F p = ∈-++⁺ˡ p
  ∈-triple σ 1F p = ∈-++⁺ʳ (generators (σ 0F)) (∈-++⁺ˡ p)
  ∈-triple σ 2F p = ∈-++⁺ʳ (generators (σ 0F)) (∈-++⁺ʳ (generators (σ 1F)) p)
```

#### Renumbering a chain

Fix decidable equality on `Y` and a chain in `FL(Y)`.  The generators used by
links `0` to `k` are listed in the order of the links, member by member
(`used`{.AgdaFunction}); link `k` numbers a generator by its position in
`used k`, and names a number by reading `used k` there, with the first
generator of link `0` as the default (`number`{.AgdaFunction},
`name`{.AgdaFunction}).

```agda
module Renumber {Y : Type υ} (_≟ʸ_ : DecidableEquality Y) (c : Chain Y) where
  open Chain c

  -- The generators used by links 0 to k, in the order of first use, with repetitions.
  used : ℕ → List Y
  used zero     = triple-generators (gens zero)
  used (suc k)  = used k ++ triple-generators (gens (suc k))

  -- A generator of link k is used by link k.
  gens-used : (k : ℕ) (i : Fin 3) {y : Y} → y ∈ generators (gens k i) → y ∈ used k
  gens-used zero     i p = ∈-triple (gens zero) i p
  gens-used (suc k)  i p = ∈-++⁺ʳ (used k) (∈-triple (gens (suc k)) i p)

  -- Link k's number for each generator: its position in the list of those used.
  number : ℕ → Y → ℕ
  number k = position _≟ʸ_ (used k)

  -- Each numbering extends the one before.
  number-extends : (k : ℕ) {y : Y} → y ∈ used k → number (suc k) y ≡ number k y
  number-extends k = position-++ _≟ʸ_ (used k) (triple-generators (gens (suc k)))

  -- A generator of Y: the first of link 0's first member.
  y₀ : Y
  y₀ = proj₁ (generators-∷ (gens zero 0F))

  -- Link k's generator for each number: the list read there.
  name : ℕ → ℕ → Y
  name k = at y₀ (used k)

  -- Naming a generator's number returns the generator.
  name-number : (k : ℕ) {y : Y} → y ∈ used k → name k (number k y) ≡ y
  name-number k = at-position _≟ʸ_ y₀ (used k)
```

Renaming by link `k`'s numbering, `rename k`{.AgdaFunction}, and back by its
names, `unrename k`{.AgdaFunction}, are substitutions; on a member of link
`k` the two in turn are the identity, and the renamings of links `k` and
`k + 1` agree.

```agda
  -- Renaming by link k's numbering.
  rename : ℕ → Sub Y ℕ
  rename k y = ℊ (number k y)

  -- Renaming back by link k's names.
  unrename : ℕ → Sub ℕ Y
  unrename k n = ℊ (name k n)

  -- Renaming a member of link k and renaming back is the identity.
  rename-unrename : (k : ℕ) (i : Fin 3) → gens k i [ rename k ] [ unrename k ] ≡ gens k i
  rename-unrename k i = trans (sym ([]-⨟ (gens k i) (rename k) (unrename k)))
    (trans ([]-agree (gens k i) (λ p → cong ℊ (name-number k (gens-used k i p)))) ([]-ℊ (gens k i)))

  -- Links k and k + 1 rename a member of link k alike.
  rename-stable : (k : ℕ) (i : Fin 3) → gens k i [ rename k ] ≡ gens k i [ rename (suc k) ]
  rename-stable k i = []-agree (gens k i) (λ p → cong ℊ (sym (number-extends k (gens-used k i p))))
```

The `k`-th renamed triple is the `k`-th triple renamed by link `k`
(`gens′`{.AgdaFunction}).  The terms express it in the next renamed triple,
since that is the next triple renamed by link `k + 1`, which renames link `k`
as link `k` does.

```agda
  -- The k-th triple, renamed by link k.
  gens′ : ℕ → Sub (Fin 3) ℕ
  gens′ k = gens k ⨟ rename k

  -- The terms express each renamed triple in the next.
  gens′≈ : (k : ℕ) (i : Fin 3) → gens′ k i ≈ʷ terms k i [ gens′ (suc k) ]
  gens′≈ k i = begin
    gens k i [ rename k ]                          ≡⟨ rename-stable k i ⟩
    gens k i [ rename (suc k) ]                    ≈⟨ []-cong (rename (suc k)) (gens≈ k i) ⟩
    terms k i [ gens (suc k) ] [ rename (suc k) ]  ≡⟨ []-⨟ (terms k i) (gens (suc k)) (rename (suc k)) ⟨
    terms k i [ gens′ (suc k) ]                    ∎
    where open SetoidReasoning (FL-setoid ℕ)
```

Substitution by a renamed triple, followed by renaming back, is substitution
by the triple, which is injective since the triple freely generates; so
substitution by the renamed triple is injective, and by Corollary 1.13 the
renamed triple freely generates.

```agda
  -- Substitution by a renamed triple is injective.
  gens′-injective : (k : ℕ) → IsInjective (proj₁ (subst-hom (gens′ k)))
  gens′-injective k {s} {t} e = freelyGenerates→injective (gens k) (gens-free k) (begin
    s [ gens k ]                  ≡⟨ []-agree s (λ {i} _ → rename-unrename k i) ⟨
    s [ gens′ k ⨟ unrename k ]    ≡⟨ []-⨟ s (gens′ k) (unrename k) ⟩
    s [ gens′ k ] [ unrename k ]  ≈⟨ []-cong (unrename k) e ⟩
    t [ gens′ k ] [ unrename k ]  ≡⟨ []-⨟ t (gens′ k) (unrename k) ⟨
    t [ gens′ k ⨟ unrename k ]    ≡⟨ []-agree t (λ {i} _ → rename-unrename k i) ⟩
    t [ gens k ]                  ∎)
    where open SetoidReasoning (FL-setoid Y)

  -- Each renamed triple freely generates.
  gens′-free : (k : ℕ) → FreelyGenerates (gens′ k)
  gens′-free k = injective→freelyGenerates (gens′ k) (gens′-injective k)

  -- The renumbered chain, in FL(ℕ).
  renumbered : Chain ℕ
  renumbered = record
    { gens       = gens′
    ; gens-free  = gens′-free
    ; terms      = terms
    ; gens≈      = gens′≈
    ; fresh      = fresh
    ; fresh∉     = fresh∉
    }
```

#### The reduction

```agda
-- A chain in FL(Y), Y with decidable equality, gives one in FL(ℕ).
renumber : {Y : Type υ} → DecidableEquality Y → Chain Y → Chain ℕ
renumber _≟ʸ_ c = Renumber.renumbered _≟ʸ_ c

-- A chain of copies in FL(Y), Y with decidable equality, gives one in FL(ℕ).
copyChain→ℕ : {Y : Type υ} → DecidableEquality Y → CopyChain Y → CopyChain ℕ
copyChain→ℕ _≟ʸ_ c = chain→copyChain (renumber _≟ʸ_ (copyChain→chain c))

-- And one in FL(3), since FL(ℕ) embeds in FL(3) (FJN Theorem 1.28).
copyChain→FL₃ : {Y : Type υ} → DecidableEquality Y → CopyChain Y → CopyChain (Fin 3)
copyChain→FL₃ _≟ʸ_ c = embed-copyChain countable-embedding (copyChain→ℕ _≟ʸ_ c)

-- Three distinct generators of X embed FL(3) in FL(X) (FJN Corollaries 1.5 and 1.13).
three-embedding : Fin 3 ↣ X → proj₁ (FL (Fin 3)) ≤ proj₁ (FL X)
three-embedding x = freelyGenerates→≤ (three-generators x) (three-generators-free x)

-- A chain of copies in FL(3) gives one in FL(X) when X has three distinct elements.
FL₃→copyChain : Fin 3 ↣ X → CopyChain (Fin 3) → CopyChain X
FL₃→copyChain x = embed-copyChain (three-embedding x)

-- Section 1.1(i): a chain in one free lattice gives one in every FL(X) with |X| ≥ 3.
reduction : {Y : Type υ} → DecidableEquality Y → CopyChain Y → Fin 3 ↣ X → CopyChain X
reduction _≟ʸ_ c x = FL₃→copyChain x (copyChain→FL₃ _≟ʸ_ c)

-- FL(3) is the only case: with |Y| ≥ 3, a chain exists in FL(Y) exactly when one exists in FL(3).
copyChain⇔FL₃ : {Y : Type υ} → DecidableEquality Y → Fin 3 ↣ Y → CopyChain Y ⇔ CopyChain (Fin 3)
copyChain⇔FL₃ _≟ʸ_ y = mk⇔ (copyChain→FL₃ _≟ʸ_) (FL₃→copyChain y)
```

--------------------------------------

[DeansProblem.Chain.Reduction]: DeansProblem.Chain.Reduction.html
