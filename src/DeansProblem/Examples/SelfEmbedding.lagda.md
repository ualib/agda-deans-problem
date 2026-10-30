---
layout: default
file: "src/DeansProblem/Examples/SelfEmbedding.lagda.md"
title: "DeansProblem.Examples.SelfEmbedding module"
date: "2026-10-13"
author: "the agda-lattices development team"
---

### Worked example: Freese's step seen from inside

This is the [DeansProblem.Examples.SelfEmbedding][] module of this repository.

[the paper]: https://arxiv.org/abs/YYMM.NNNNN

In the free lattice `FL(3)` on generators `x`, `y`, `z`, the three elements

    x ∨ (y ∧ z),    y ∨ (z ∧ x),    z ∨ (x ∧ y)

freely generate a sublattice, which is therefore a copy of `FL(3)`, and the copy
is proper: it does not contain `x`.  So the substitution `θ`{.AgdaFunction} that
sends each generator to the corresponding element is a self-embedding of `FL(3)`
that is not onto.  This is Freese's step toward Dean's problem
([DeansProblem.Examples.FreeseStep][]) seen from inside the upper sublattice: there
`a = a' ∨ (b' ∧ c')` and symmetrically, so reading `⟨a', b', c'⟩` as `FL(3)`
through its free generators, the lower sublattice `⟨a, b, c⟩` is the image of
`θ`{.AgdaFunction}.  What the nine-generator setting adds is the ambient lattice
in which `a'` is not a subterm of `a`; here everything happens inside `FL(3)`,
the decisions are on terms with at most six generator occurrences, and the
module is cheap.

The module decides free generation (`θ-free`{.AgdaFunction}) and properness
(`x∉θ`{.AgdaFunction}), packages the containment as a
`Step`{.AgdaRecord} of [DeansProblem.Chain][] with the identity family above
(`inside`{.AgdaFunction}), and iterates it: `θᵏ⁺¹(FL(3)) ⊊ θᵏ(FL(3))` for every
`k` (`descending`{.AgdaFunction}), the descending chain of copies of `FL(3)` that
makes Dean's question about ascending chains the interesting one.  By
[DeansProblem.SelfSimilar][], no injective endomorphism of `FL(3)` turns this
descending chain around.

Last, the module proves Corollary 7.5 of [the paper][], in which `θ` is
written `ρ`: `θ` fixes exactly the eleven elements of `T₁₁`
(`θ-fixed⇔T₁₁`{.AgdaFunction}), so its fixed sublattice contains no free triple
(`θ-no-fixed-triple`{.AgdaFunction}).

<!--
```agda
{-# OPTIONS --without-K --exact-split --safe #-}

module DeansProblem.Examples.SelfEmbedding where

open import Agda.Primitive  using () renaming ( Set to Type )

-- Imports from the Agda Standard Library ---------------------------------------
open import Data.Fin.Base                          using ( Fin )
open import Data.Fin.Patterns                      using ( 0F ; 1F ; 2F )
open import Data.Fin.Properties                    using ( _≟_ )
open import Data.List.Base                         using ( allFin )
open import Data.List.Relation.Unary.All           using ( All ; all? ; lookup )
open import Data.List.Relation.Unary.Any           using ( Any )
open import Data.List.Membership.Propositional     using ( find )
open import Data.List.Membership.Propositional.Properties
                                                   using ( ∈-allFin )
open import Data.Nat.Base                          using ( ℕ ; suc )
open import Data.Product                           using ( _,_ ; proj₁ )
open import Function                               using ( _⇔_ ; mk⇔ )
open import Relation.Binary.PropositionalEquality  using ( sym ; subst )
open import Relation.Nullary                       using ( ¬_ )
open import Relation.Nullary.Decidable.Core        using ( from-yes ; from-no )

-- Imports from the Agda Universal Algebra Library ------------------------------
open import Lattices.Free.Canonical.Basic          using ( ≈ʷ-refl ; ≈ʷ-sym ; ≈ʷ-trans )
open import DeansProblem.FixedGenerator            using ( T₁₁ ; strict-fixed-in-T₁₁ ; moves→no-fixed-triple )
open import DeansProblem.Inflationary              using ( Inflationary )
open import DeansProblem.Chain                     using ( Step ; iter ; iter-injective
                                                         ; freelyGenerates-⨟ )
open import Lattices.Free.Generation
                                                   using ( FreelyGenerates
                                                         ; freelyGenerates→injective
                                                         ; generator-in-image ; module Decide )
open import Lattices.Free.Substitution             using ( Sub ; _[_] ; []-ℊ ; []-cong ; subst-hom )
open import Lattices.Free.Term                     using ( LatTerm ; ℊ ; _∧̇_ ; _∨̇_ )
open import Lattices.Free.Whitman                  using ( _≈ʷ_ ; module Decision )
open import Setoid.Functions                       using ( IsInjective )
```
-->

#### The self-embedding

The generators of `FL(3)` are `x`, `y`, `z`, and `θ`{.AgdaFunction} sends each to
its join with the meet of the other two, in cyclic order.

```agda
-- The three generators of FL(3).
x y z : LatTerm (Fin 3)
x = ℊ 0F
y = ℊ 1F
z = ℊ 2F

-- Freese's step, read inside the upper sublattice.
θ : Sub (Fin 3) (Fin 3)
θ 0F = x ∨̇ (y ∧̇ z)
θ 1F = y ∨̇ (z ∧̇ x)
θ 2F = z ∨̇ (x ∧̇ y)
```

#### Free generation and properness

`freelyGenerates?`{.AgdaFunction} decides Corollary 1.13's condition for
`θ`{.AgdaFunction} by six decisions of Whitman's procedure, and the identity
family `ℊ`{.AgdaInductiveConstructor} passes the same test
(`θ-free`{.AgdaFunction}, `ℊ-free`{.AgdaFunction}).  The generator `x` is none of
the three terms (`x∉θ`{.AgdaFunction}), each decided in `FL(3)`, so by
Corollary 1.6 (`generator-in-image`{.AgdaFunction}) it is not in the sublattice
`θ`{.AgdaFunction} generates (`x∉⟨θ⟩`{.AgdaFunction}).

```agda
open Decide (_≟_ {3}) (allFin 3) ∈-allFin (_≟_ {3}) using ( freelyGenerates? )
open Decision (_≟_ {3}) using ( _≤ʷ?_ ; _≈ʷ?_ )

-- θ freely generates a copy of FL(3).
θ-free : FreelyGenerates θ
θ-free = from-yes (freelyGenerates? θ)

-- So does the identity family.
ℊ-free : FreelyGenerates {I = Fin 3} ℊ
ℊ-free = from-yes (freelyGenerates? ℊ)

-- The generator x is none of the three terms.
x∉θ : ∀ i → ¬ (x ≈ʷ θ i)
x∉θ 0F = from-no (x ≈ʷ? θ 0F)
x∉θ 1F = from-no (x ≈ʷ? θ 1F)
x∉θ 2F = from-no (x ≈ʷ? θ 2F)

-- So x is not in the sublattice θ generates.
x∉⟨θ⟩ : (t : LatTerm (Fin 3)) → ¬ (t [ θ ] ≈ʷ x)
x∉⟨θ⟩ t e = let (i , e') = generator-in-image θ t (≈ʷ-sym e) in x∉θ i e'
```

#### The step and the descending chain

Inside `FL(3)` the containment `θ(FL(3)) ⊊ FL(3)` is a `Step`{.AgdaRecord} whose
upper family is the identity (`inside`{.AgdaFunction}): `θ i` is `θ i [ ℊ ]`
up to `_≡_`{.AgdaDatatype} (`[]-ℊ`{.AgdaFunction}), and the fresh index is that
of `x`.

```agda
-- Freese's step inside FL(3): θ(FL(3)) ⊊ FL(3).
inside : Step (Fin 3)
inside = record
  { σ        = θ
  ; τ        = ℊ
  ; σ-free   = θ-free
  ; τ-free   = ℊ-free
  ; p        = θ
  ; σ≈p[τ]   = λ i → subst (θ i ≈ʷ_) (sym ([]-ℊ (θ i))) ≈ʷ-refl
  ; fresh    = 0F
  ; fresh∉p  = x∉θ
  }
```

Iterating, `θᵏ⁺¹(FL(3)) ⊊ θᵏ(FL(3))` for every `k` (`descending`{.AgdaFunction}):
the family `iter θ (suc k)` is, by the definition of `iter`{.AgdaFunction}, the
family `θ`{.AgdaFunction} moved by `iter θ k`, so the terms `θ i` express it in
`iter θ k`, and both families freely generate because `θ`{.AgdaFunction} and its
iterates are injective (`freelyGenerates-⨟`{.AgdaFunction}).

```agda
-- The iterates of θ are injective.
θ-injective : (k : ℕ) → IsInjective (proj₁ (subst-hom (iter θ k)))
θ-injective = iter-injective θ (freelyGenerates→injective θ θ-free)

-- The descending chain FL(3) ⊋ θ(FL(3)) ⊋ θ²(FL(3)) ⊋ ⋯, one step at a time.
descending : ℕ → Step (Fin 3)
descending k = record
  { σ        = iter θ (suc k)
  ; τ        = iter θ k
  ; σ-free   = freelyGenerates-⨟ θ (iter θ k) θ-free (θ-injective k)
  ; τ-free   = freelyGenerates-⨟ ℊ (iter θ k) ℊ-free (θ-injective k)
  ; p        = θ
  ; σ≈p[τ]   = λ i → ≈ʷ-refl
  ; fresh    = 0F
  ; fresh∉p  = x∉θ
  }
```

#### Corollary 7.5: the fixed points of θ

`θ`{.AgdaFunction} is strictly inflationary: `x ≤ x ∨ (y ∧ z)`, and
`x ∨ (y ∧ z) ≠ x` since `y ∧ z ≰ x`, cyclically (`θ-inflationary`{.AgdaFunction},
`θ-moves`{.AgdaFunction}, six decisions).  So by Proposition 7.3
(`strict-fixed-in-T₁₁`{.AgdaFunction}) its fixed points lie in `T₁₁`.
Conversely it fixes each of the eleven (`θ-fixes-T₁₁`{.AgdaFunction}, eleven
decisions), and so every element equal to one of them.  Since `θ` is proper and
moves every generator, Theorem E leaves it no fixed free triple
(`θ-no-fixed-triple`{.AgdaFunction}).

```agda
-- θ is inflationary.
θ-inflationary : Inflationary θ
θ-inflationary 0F = from-yes (x ≤ʷ? θ 0F)
θ-inflationary 1F = from-yes (y ≤ʷ? θ 1F)
θ-inflationary 2F = from-yes (z ≤ʷ? θ 2F)

-- And strictly: it moves every generator.
θ-moves : ∀ g → ¬ (θ g ≈ʷ ℊ g)
θ-moves 0F = from-no (θ 0F ≈ʷ? x)
θ-moves 1F = from-no (θ 1F ≈ʷ? y)
θ-moves 2F = from-no (θ 2F ≈ʷ? z)

-- It fixes each of the eleven.
θ-fixes-T₁₁ : All (λ t → t [ θ ] ≈ʷ t) T₁₁
θ-fixes-T₁₁ = from-yes (all? (λ t → t [ θ ] ≈ʷ? t) T₁₁)

-- Corollary 7.5: θ fixes exactly the eleven elements of T₁₁.
θ-fixed⇔T₁₁ : (w : LatTerm (Fin 3)) → (w [ θ ] ≈ʷ w) ⇔ Any (w ≈ʷ_) T₁₁
θ-fixed⇔T₁₁ w = mk⇔ (strict-fixed-in-T₁₁ θ θ-free θ-inflationary θ-moves w) fixed
  where
  -- An element equal to a fixed point is fixed.
  fixed : Any (w ≈ʷ_) T₁₁ → w [ θ ] ≈ʷ w
  fixed p = let (t , t∈ , w≈t) = find p
            in ≈ʷ-trans ([]-cong θ w≈t) (≈ʷ-trans (lookup θ-fixes-T₁₁ t∈) (≈ʷ-sym w≈t))

-- So the fixed sublattice of θ contains no free triple.
θ-no-fixed-triple : (τ : Sub (Fin 3) (Fin 3)) → FreelyGenerates τ → ¬ (∀ i → τ i [ θ ] ≈ʷ τ i)
θ-no-fixed-triple τ τ-free τ-fixed = moves→no-fixed-triple θ θ-free 0F x∉θ τ τ-free τ-fixed θ-moves
```

**Corollary 7.5** of [the paper][], as one statement: Freese's
self-embedding `ρ`, here `θ`, fixes exactly the eleven elements of `T₁₁`, up
to equality in `FL(3)`.

```agda
-- Corollary 7.5: Freese's self-embedding fixes exactly the eleven elements of T₁₁.
Corollary-7·5 : Type
Corollary-7·5 = (w : LatTerm (Fin 3)) → (w [ θ ] ≈ʷ w) ⇔ Any (w ≈ʷ_) T₁₁

-- The proof of Corollary 7.5.
corollary-7·5 : Corollary-7·5
corollary-7·5 = θ-fixed⇔T₁₁
```

--------------------------------------

[DeansProblem.Examples.SelfEmbedding]: DeansProblem.Examples.SelfEmbedding.html
[DeansProblem.Chain]: DeansProblem.Chain.html
[DeansProblem.Examples.FreeseStep]: DeansProblem.Examples.FreeseStep.html
[DeansProblem.SelfSimilar]: DeansProblem.SelfSimilar.html
