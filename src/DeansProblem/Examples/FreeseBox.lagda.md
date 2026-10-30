---
layout: default
file: "src/DeansProblem/Examples/FreeseBox.lagda.md"
title: "DeansProblem.Examples.FreeseBox module"
date: "2026-10-13"
author: "the agda-lattices development team"
---

### Worked example: Freese's step, its box, and its terms

This is the [DeansProblem.Examples.FreeseBox][] module of this repository.

[the paper]: https://arxiv.org/abs/YYMM.NNNNN

[DeansProblem.AlmostProof][] isolates the gap in Freese's almost-proof as a
predicate on a box: the intervals that a recurring truncation pattern pins the
generators of the later links into must be strongly join and meet irredundant.
This module decides the predicate on Freese's own step
([DeansProblem.Examples.FreeseStep][]), with its bounds as his notes give them:

    a⁻ = ā₁ ∨ b̄₂ ∨ c̄₂,    a⁺ = a ∧ b̄₂₁ ∧ c̄₂₂,    b̄₂ = b̄₂₁ ∧ b̄₂₂,  c̄₂ = c̄₂₁ ∧ c̄₂₂,

and their images under the cyclic permutation `π`{.AgdaFunction}.  "In fact we
can choose any `a' ∈ a ∧ b̄₂₁ ∧ c̄₂₂/ā₁ ∨ b̄₂ ∨ c̄₂` and independently choose
similar `b'` and `c'`," and his `a'` is the top of the interval: `a⁺` is `a'`, by
definition.

**The verdict**: the box is strongly irredundant, and the reason is short.  It
lies inside the *generator box*

    [a₁, a₁ ∨ b₂₁ ∨ c₂₂],    [b₁, b₁ ∨ c₂₁ ∨ a₂₂],    [c₁, c₁ ∨ a₂₁ ∨ b₂₂],

whose ends are a generator of `FL(9)` and a join of three generators: `a₁ ≤ ā₁`
because `a₁` is a joinand of `ā₁`, and `a' ≤ a₁ ∨ b₂₁ ∨ c₂₂` by the notes' own
simplification `a' = a ∧ (a₁ ∨ b₂₁ ∨ c₂₂)`.  The generator box is strongly
irredundant on its face (`a₁ ≰ b₁ ∨ c₂₁ ∨ a₂₂ ∨ c₁ ∨ a₂₁ ∨ b₂₂`, a generator
below a join of other generators, and `b₁ ∧ c₁ ≰ a₁ ∨ b₂₁ ∨ c₂₂` dually), and a
narrower box inherits irredundance (`stronglyIrredundant-narrow`{.AgdaFunction}).
So Lemma 2 applies to Freese's step: `a'` is the only element of `⟨a', b', c'⟩`
in `[a⁻, a⁺]`, and symmetrically (`freese-pinned`{.AgdaFunction}); and no step in
`FL(9)` has both of its triples in the generator box
(`no-step-in-generator-box`{.AgdaFunction}).

**Freese's terms occur in at most one link**.  More is true, and certified.  Let
`τ` be any triple that freely generates and expresses Freese's base by his terms,
`a = τ x ∨ (τ y ∧ τ z)` and cyclically, as `(a', b', c')` does.  Then `τ` lies in
the generator box (`freese-terms-in-box`{.AgdaFunction}), whatever the rest of its
truncation pattern.  The lower ends hold because `a₁` is join prime and not below
`b`.  The upper ends come from the truncation theorem of
[DeansProblem.Truncation][], applied to the canonical forms of `a`, `b` and `c`,
written out and certified canonical by the decision of
[Lattices.Free.Canonical.Recognition][]: the meet child `z ∧ x` of the term
`y ∨ (z ∧ x)` is matched with a meet joinand of the canonical form of `b`, all of
whose meetands are cut above `τ z` or above `τ x`; the generators below those two
rule out two of the three meet joinands, and the third has the meetand
`b₂₁ ∨ c₂₂ ∨ a₁`, which then lies above `τ x`.  Hence two such triples, one in the
other's sublattice, are equal (`freese-terms-once`{.AgdaFunction}), and no step
has both of its triples express `(a, b, c)` by Freese's terms
(`no-step-with-freese-terms`{.AgdaFunction}).  In a chain whose first link is
Freese's base, the term expressing the base in a later link (the transition
`θ_{0,k}` of Section 6 of [the paper][], of which some value recurs) is
Freese's for at most one link.  So Freese's step is not a witness of the gap:
an infinite chain over his base must recur in other terms.

**Cost**.  The module checks in about 2 s, measured with `--profile=modules`
against built interfaces (2026-10-13); it is not heavy.  The decisions on
Freese's own terms are few and run on the checked-equal canonical form `â` of
[DeansProblem.Examples.FreeseStep][]: the two that put `b̄₂` and `c̄₂` below `a`
(Freese's footnote: "Looking at Figure 1 we see that `a ≥ a' ≥ b₂`.  Defining
`a = a₁ ∨ (a₂₁ ∧ a₂₂)`, as we did above, does not guar[a]ntee this will hold.  In
fact the first solution to (1)–(4) does not satisfy this but the second one does.
This was lucky."), and the equation between `â` and its canonical term.  The
three canonicity decisions make 540 Whitman decisions each (at a node with `n`
children, `n(n - 1)` for the antichain, both directions per pair, and one per
meetand of a meet child for condition 4), almost all between generators and
joins of generators.

<!--
```agda
{-# OPTIONS --without-K --exact-split --safe #-}

module DeansProblem.Examples.FreeseBox where

open import Agda.Primitive  using () renaming ( Set to Type )

-- Imports from the Agda Standard Library ---------------------------------------
open import Data.Empty                             using ( ⊥ ; ⊥-elim )
open import Data.Fin.Base                          using ( Fin )
open import Data.Fin.Patterns                      using ( 0F ; 1F ; 2F ; 3F ; 4F ; 5F ; 6F
                                                         ; 7F ; 8F )
open import Data.Fin.Properties                    using ( _≟_ )
open import Data.List.Base                         using ( List ; [] ; _∷_ ; map )
open import Data.List.Membership.Propositional     using ( _∈_ )
open import Data.List.Relation.Unary.Any           using ( Any ; here ; there )
open import Data.Product                           using ( Σ-syntax ; _×_ ; _,_ ; proj₁ ; proj₂ )
open import Data.Sum.Base                          using ( _⊎_ ; inj₁ ; inj₂ )
open import Function                               using ( _∘_ )
open import Relation.Binary.PropositionalEquality  using ( _≡_ ; refl ; sym ; cong₂ ; subst )
open import Relation.Nullary                       using ( ¬_ )
open import Relation.Nullary.Decidable.Core        using ( from-yes ; from-no )

-- Imports from the Agda Universal Algebra Library ------------------------------
open import DeansProblem.Examples.FreeseStep
  using  ( a₁ ; a₂₁ ; a₂₂ ; b₁ ; b₂₁ ; b₂₂ ; c₁ ; c₂₁ ; c₂₂ ; π ; ā₁ ; ā₂₁ ; ā₂₂ ; b̄₂₁ ; b̄₂₂
         ; c̄₂₁ ; c̄₂₂ ; a ; b ; c ; a' ; abc ; abc' ; abc-free ; abc'-free ; abc≈ ; ρ ; x∉ρ
         ; â ; a≈â ; a'≈a″ ; relation-1ᵇ ; relation-2ᶜ ; relation-3ᵇ ; relation-4ᶜ )
open import DeansProblem.AlmostProof
  using  ( InBox ; StronglyIrredundant ; stronglyIrredundant-narrow ; lemma-2ᶠ ; box-agree
         ; no-step-in-irredundant-box ; module DecideBox )
open import Lattices.Free.Canonical.Basic
  using  ( CTerm ; genᶜ ; joinᶜ ; meetᶜ ; CJand ; jgen ; jmeet ; CMand ; mgen ; mjoin ; ⌊_⌋
         ; ⌊_⌋ᴶ ; ⌊_⌋ᴹ ; ⋁ᴶ ; ⋀ᴹ ; ≈ʷ-refl ; ≈ʷ-sym ; ≈ʷ-trans ; IsCanonical ; asListJ
         ; joinandsOf )
open import Lattices.Free.Canonical.Recognition    using ( module Recognize )
open import DeansProblem.Chain                     using ( Step )
open import Lattices.Free.Generation               using ( FreelyGenerates ; freelyGenerates→injective )
open import Lattices.Free.Substitution             using ( Sub ; _[_] ; subst-hom ; []-mono ; []-cong
                                                         ; []-congʳ )
open import Lattices.Free.Term                     using ( LatTerm ; ℊ ; _∧̇_ ; _∨̇_ )
open import DeansProblem.Truncation                using ( module Truncates ; truncation )
open import Lattices.Free.Whitman
  using  ( _≤ʷ_ ; _≈ʷ_ ; ∨≤ ; ≤∧ ; ≤ʷ-refl ; ≤ʷ-trans ; ∨̇-upperˡ ; ∧̇-lowerˡ ; ∧̇-lowerʳ
         ; ℊ≤∨-inv ; module Decision )
open import Setoid.Functions                       using ( IsInjective )
```
-->

#### The two boxes

Freese's box (`lo`{.AgdaFunction}, `hi`{.AgdaFunction}) is defined at the first
index as in the notes and at the others by `π`{.AgdaFunction}, so that its upper
ends are `a'`, `b'` and `c'` by definition.  The generator box
(`loᵍ`{.AgdaFunction}, `hiᵍ`{.AgdaFunction}) has a generator at each lower end
and a join of three generators at each upper end.

```agda
-- Freese's grouped meets.
ā₂ b̄₂ c̄₂ : LatTerm (Fin 9)
ā₂ = ā₂₁ ∧̇ ā₂₂
b̄₂ = b̄₂₁ ∧̇ b̄₂₂
c̄₂ = c̄₂₁ ∧̇ c̄₂₂

-- Freese's box: [ā₁ ∨ b̄₂ ∨ c̄₂ , a ∧ b̄₂₁ ∧ c̄₂₂] and its images under π.
lo hi : Fin 3 → LatTerm (Fin 9)
lo 0F = ā₁ ∨̇ b̄₂ ∨̇ c̄₂
lo 1F = lo 0F [ π ]
lo 2F = lo 0F [ π ] [ π ]
hi 0F = a ∧̇ b̄₂₁ ∧̇ c̄₂₂
hi 1F = hi 0F [ π ]
hi 2F = hi 0F [ π ] [ π ]

-- The generator box: [a₁ , a₁ ∨ b₂₁ ∨ c₂₂] and its images under π.
loᵍ hiᵍ : Fin 3 → LatTerm (Fin 9)
loᵍ 0F = a₁
loᵍ 1F = b₁
loᵍ 2F = c₁
hiᵍ 0F = a₁ ∨̇ b₂₁ ∨̇ c₂₂
hiᵍ 1F = b₁ ∨̇ c₂₁ ∨̇ a₂₂
hiᵍ 2F = c₁ ∨̇ a₂₁ ∨̇ b₂₂
```

#### The generator box is strongly irredundant

Six decisions of Whitman's procedure, each between a generator and a join of
generators or dually (`generator-box-irredundant`{.AgdaFunction}).

```agda
open DecideBox (_≟_ {9})  using ( stronglyIrredundant? )
open Decision (_≟_ {9})   using ( _≤ʷ?_ ; _≈ʷ?_ )

generator-box-irredundant : StronglyIrredundant loᵍ hiᵍ
generator-box-irredundant = from-yes (stronglyIrredundant? loᵍ hiᵍ)
```

#### Freese's box lies inside it, and so is strongly irredundant

At the first index, `a₁ ≤ ā₁ ≤ ā₁ ∨ b̄₂ ∨ c̄₂`, since `ā₁ = a₁ ∨ ⋯`, and
`a' = a″ ≤ a₁ ∨ b₂₁ ∨ c₂₂`, since `a″ = â ∧ (a₁ ∨ b₂₁ ∨ c₂₂)`; the other indices
are the images under `π`{.AgdaFunction}, which preserves the order
(`[]-mono`{.AgdaFunction}).  Narrowing keeps strong irredundance
(`freese-box-irredundant`{.AgdaFunction}).

```agda
-- The generator box is wider than Freese's.
loᵍ≤lo : ∀ j → loᵍ j ≤ʷ lo j
loᵍ≤lo 0F = from-yes (a₁ ≤ʷ? lo 0F)
loᵍ≤lo 1F = []-mono π (loᵍ≤lo 0F)
loᵍ≤lo 2F = []-mono π ([]-mono π (loᵍ≤lo 0F))

hi≤hiᵍ : ∀ j → hi j ≤ʷ hiᵍ j
hi≤hiᵍ 0F = ≤ʷ-trans (proj₁ a'≈a″) ∧̇-lowerʳ
hi≤hiᵍ 1F = []-mono π (hi≤hiᵍ 0F)
hi≤hiᵍ 2F = []-mono π ([]-mono π (hi≤hiᵍ 0F))

-- Freese's box is strongly irredundant.
freese-box-irredundant : StronglyIrredundant lo hi
freese-box-irredundant = stronglyIrredundant-narrow loᵍ≤lo hi≤hiᵍ generator-box-irredundant
```

#### Freese's step lies in his box

The upper ends are `a'`, `b'`, `c'` themselves.  For the lower end at the first
index, `ā₁ ≤ a'` follows from relations (1) and (2) of the notes
(`relation-1ᵇ`{.AgdaFunction}, `relation-2ᶜ`{.AgdaFunction}), since `ā₁` is a
joinand of `a`; `b̄₂ ≤ b̄₂₁` and `c̄₂ ≤ c̄₂₂` are meets; `b̄₂ ≤ c̄₂₂` and
`c̄₂ ≤ b̄₂₁` are relations (3) and (4) (`relation-4ᶜ`{.AgdaFunction},
`relation-3ᵇ`{.AgdaFunction}); and `b̄₂ ≤ a` and `c̄₂ ≤ a` are Freese's lucky
footnote, decided on the canonical form `â` (`b̄₂≤a`{.AgdaFunction},
`c̄₂≤a`{.AgdaFunction}).

```agda
-- Freese's footnote: b̄₂ and c̄₂ lie below a.
b̄₂≤a : b̄₂ ≤ʷ a
b̄₂≤a = ≤ʷ-trans (from-yes (b̄₂ ≤ʷ? â)) (proj₂ a≈â)

c̄₂≤a : c̄₂ ≤ʷ a
c̄₂≤a = ≤ʷ-trans (from-yes (c̄₂ ≤ʷ? â)) (proj₂ a≈â)

-- The lower end at the first index lies below a'.
lo≤a' : lo 0F ≤ʷ a'
lo≤a' = ∨≤ (∨≤ (≤∧ (≤∧ ∨̇-upperˡ relation-1ᵇ) relation-2ᶜ)
               (≤∧ (≤∧ b̄₂≤a ∧̇-lowerˡ) relation-4ᶜ))
           (≤∧ (≤∧ c̄₂≤a relation-3ᵇ) ∧̇-lowerʳ)

-- Freese's step lies in his box, and so in the generator box.
freese-in-box : InBox lo hi abc'
freese-in-box 0F = lo≤a' , ≤ʷ-refl
freese-in-box 1F = []-mono π lo≤a' , ≤ʷ-refl
freese-in-box 2F = []-mono π ([]-mono π lo≤a') , ≤ʷ-refl

freese-in-generator-box : InBox loᵍ hiᵍ abc'
freese-in-generator-box j = ≤ʷ-trans (loᵍ≤lo j) (proj₁ (freese-in-box j))
                          , ≤ʷ-trans (proj₂ (freese-in-box j)) (hi≤hiᵍ j)
```

#### Lemma 2 on Freese's step

`a'` is the only element of `⟨a', b', c'⟩` in `[a⁻, a⁺]`, and symmetrically
(`freese-pinned`{.AgdaFunction}).  The generator box holds the two triples of no
step in `FL(9)` (`no-step-in-generator-box`{.AgdaFunction}).  Freese's step is a
`Step`{.AgdaRecord} of [DeansProblem.Chain][] (`freese-step`{.AgdaFunction}),
from the facts of [DeansProblem.Examples.FreeseStep][], and no triple of the
generator box whose sublattice contains `⟨a', b', c'⟩` differs from
`(a', b', c')` (`above-freese`{.AgdaFunction}): a chain cannot continue Freese's
step inside the generator box.

```agda
-- Lemma 2 for Freese's step.
freese-pinned : (i : Fin 3) (t : LatTerm (Fin 3)) → lo i ≤ʷ t [ abc' ] → t [ abc' ] ≤ʷ hi i
              → t [ abc' ] ≈ʷ abc' i
freese-pinned = lemma-2ᶠ abc' freese-box-irredundant freese-in-box

-- No step has both triples in the generator box.
no-step-in-generator-box : (s : Step (Fin 9)) → InBox loᵍ hiᵍ (Step.σ s) → ¬ InBox loᵍ hiᵍ (Step.τ s)
no-step-in-generator-box s = no-step-in-irredundant-box s generator-box-irredundant

-- Freese's step, as a step.
freese-step : Step (Fin 9)
freese-step = record
  { σ        = abc
  ; τ        = abc'
  ; σ-free   = abc-free
  ; τ-free   = abc'-free
  ; p        = ρ
  ; σ≈p[τ]   = abc≈
  ; fresh    = 0F
  ; fresh∉p  = x∉ρ
  }

-- A triple of the generator box above Freese's is Freese's.
above-freese : (τ' : Sub (Fin 3) (Fin 9)) (q : Sub (Fin 3) (Fin 3)) → (∀ j → abc' j ≈ʷ q j [ τ' ])
             → InBox loᵍ hiᵍ τ' → ∀ i → abc' i ≈ʷ τ' i
above-freese τ' q abc'≈ box' i =
  box-agree q abc'≈ freese-in-generator-box box' i (generator-box-irredundant i)
```

#### The canonical forms of a, b and c, certified

The rest of the module reads the truncation of the canonical forms of `a`, `b`
and `c` by Freese's terms `ρ`{.AgdaFunction}, so it needs those canonical forms
as canonical terms, certified.  `âᶜ`{.AgdaFunction} is the canonical form `â`
of [DeansProblem.Examples.FreeseStep][] written as a canonical term, its meetands
joins of generators (`gens`{.AgdaFunction}), the generators numbered as there
(`a₁` is `0F`, `a₂₁` is `1F`, through `c₂₂`, which is `8F`).  The canonical
forms of `b` and `c` are its images under the renaming `πᵍ`{.AgdaFunction} of
the generators that `π`{.AgdaFunction} performs (`renᶜ`{.AgdaFunction}, which
commutes with the embedding: `⌊renᶜ⌋`{.AgdaFunction}).  The three are canonical,
by the decision of Theorem 1.18's conditions
(`isCanonical?`{.AgdaFunction} of [Lattices.Free.Canonical.Recognition][]), and
represent `a`, `b` and `c` (`âᶜ-sound`{.AgdaFunction}, `bᶜ-sound`{.AgdaFunction},
`cᶜ-sound`{.AgdaFunction}).  The canonical forms of Freese's terms are
`ρᶜ`{.AgdaFunction}, canonical by the same decision in `FL(3)`.

```agda
open Recognize (_≟_ {9}) using ( isCanonical? )
open Recognize (_≟_ {3}) using () renaming ( isCanonical? to isCanonical₃? )

-- Renaming the generators of a canonical term.
module _ {X Y : Type} (f : X → Y) where
  renᶜ   : CTerm X → CTerm Y
  renᴶ   : CJand X → CJand Y
  renᴹ   : CMand X → CMand Y
  renᴶs  : List (CJand X) → List (CJand Y)
  renᴹs  : List (CMand X) → List (CMand Y)

  renᶜ (genᶜ x)      = genᶜ (f x)
  renᶜ (joinᶜ h t)   = joinᶜ (renᴶ h) (renᴶs t)
  renᶜ (meetᶜ h t)   = meetᶜ (renᴹ h) (renᴹs t)
  renᴶ (jgen x)      = jgen (f x)
  renᴶ (jmeet h t)   = jmeet (renᴹ h) (renᴹs t)
  renᴹ (mgen x)      = mgen (f x)
  renᴹ (mjoin h t)   = mjoin (renᴶ h) (renᴶs t)
  renᴶs []           = []
  renᴶs (a ∷ as)     = renᴶ a ∷ renᴶs as
  renᴹs []           = []
  renᴹs (a ∷ as)     = renᴹ a ∷ renᴹs as

  -- Renaming commutes with the embedding.
  ⌊renᶜ⌋  : (C : CTerm X) → ⌊ renᶜ C ⌋ ≡ ⌊ C ⌋ [ ℊ ∘ f ]
  ⌊renᴶ⌋  : (a : CJand X) → ⌊ renᴶ a ⌋ᴶ ≡ ⌊ a ⌋ᴶ [ ℊ ∘ f ]
  ⌊renᴹ⌋  : (a : CMand X) → ⌊ renᴹ a ⌋ᴹ ≡ ⌊ a ⌋ᴹ [ ℊ ∘ f ]
  ⋁ᴶ-ren  : (h : CJand X) (t : List (CJand X)) → ⋁ᴶ (renᴶ h) (renᴶs t) ≡ ⋁ᴶ h t [ ℊ ∘ f ]
  ⋀ᴹ-ren  : (h : CMand X) (t : List (CMand X)) → ⋀ᴹ (renᴹ h) (renᴹs t) ≡ ⋀ᴹ h t [ ℊ ∘ f ]

  ⌊renᶜ⌋ (genᶜ x)     = refl
  ⌊renᶜ⌋ (joinᶜ h t)  = ⋁ᴶ-ren h t
  ⌊renᶜ⌋ (meetᶜ h t)  = ⋀ᴹ-ren h t
  ⌊renᴶ⌋ (jgen x)     = refl
  ⌊renᴶ⌋ (jmeet h t)  = ⋀ᴹ-ren h t
  ⌊renᴹ⌋ (mgen x)     = refl
  ⌊renᴹ⌋ (mjoin h t)  = ⋁ᴶ-ren h t
  ⋁ᴶ-ren h []         = ⌊renᴶ⌋ h
  ⋁ᴶ-ren h (a ∷ as)   = cong₂ _∨̇_ (⌊renᴶ⌋ h) (⋁ᴶ-ren a as)
  ⋀ᴹ-ren h []         = ⌊renᴹ⌋ h
  ⋀ᴹ-ren h (a ∷ as)   = cong₂ _∧̇_ (⌊renᴹ⌋ h) (⋀ᴹ-ren a as)

-- The renaming of the generators that π performs.
πᵍ : Fin 9 → Fin 9
πᵍ 0F = 3F
πᵍ 1F = 4F
πᵍ 2F = 5F
πᵍ 3F = 6F
πᵍ 4F = 7F
πᵍ 5F = 8F
πᵍ 6F = 0F
πᵍ 7F = 1F
πᵍ 8F = 2F

π≈ : ∀ x → ℊ (πᵍ x) ≈ʷ π x
π≈ 0F = ≈ʷ-refl
π≈ 1F = ≈ʷ-refl
π≈ 2F = ≈ʷ-refl
π≈ 3F = ≈ʷ-refl
π≈ 4F = ≈ʷ-refl
π≈ 5F = ≈ʷ-refl
π≈ 6F = ≈ʷ-refl
π≈ 7F = ≈ʷ-refl
π≈ 8F = ≈ʷ-refl

-- A meetand that is a join of generators.
gens : Fin 9 → List (Fin 9) → CMand (Fin 9)
gens g gs = mjoin (jgen g) (map jgen gs)

-- The canonical forms of a, b and c.
âᶜ bᶜ cᶜ : CTerm (Fin 9)
âᶜ = joinᶜ (jgen 0F)
  ( jmeet (gens 0F (4F ∷ 8F ∷ [])) ( gens 6F (1F ∷ 5F ∷ []) ∷ gens 0F (3F ∷ 2F ∷ 4F ∷ 7F ∷ [])
                                   ∷ gens 3F (6F ∷ 2F ∷ 5F ∷ 7F ∷ []) ∷ gens 0F (3F ∷ 6F ∷ 1F ∷ 4F ∷ 7F ∷ [])
                                   ∷ gens 0F (3F ∷ 6F ∷ 2F ∷ 5F ∷ 8F ∷ []) ∷ [] )
  ∷ jmeet (gens 0F (4F ∷ 8F ∷ [])) ( gens 3F (2F ∷ 7F ∷ []) ∷ gens 0F (6F ∷ 1F ∷ 5F ∷ 8F ∷ [])
                                   ∷ gens 3F (6F ∷ 1F ∷ 5F ∷ 7F ∷ []) ∷ gens 0F (3F ∷ 6F ∷ 1F ∷ 4F ∷ 7F ∷ [])
                                   ∷ gens 0F (3F ∷ 6F ∷ 2F ∷ 5F ∷ 8F ∷ []) ∷ [] )
  ∷ jmeet (gens 1F (5F ∷ 6F ∷ [])) ( gens 0F (1F ∷ 4F ∷ 6F ∷ 8F ∷ []) ∷ gens 0F (1F ∷ 3F ∷ 4F ∷ 6F ∷ 7F ∷ [])
                                   ∷ gens 2F (3F ∷ 7F ∷ []) ∷ gens 0F (2F ∷ 3F ∷ 4F ∷ 8F ∷ [])
                                   ∷ gens 0F (2F ∷ 3F ∷ 5F ∷ 6F ∷ 8F ∷ []) ∷ [] )
  ∷ [] )
bᶜ = renᶜ πᵍ âᶜ
cᶜ = renᶜ πᵍ bᶜ

-- They are canonical.
âᶜ-canonical : IsCanonical âᶜ
âᶜ-canonical = from-yes (isCanonical? âᶜ)

bᶜ-canonical : IsCanonical bᶜ
bᶜ-canonical = from-yes (isCanonical? bᶜ)

cᶜ-canonical : IsCanonical cᶜ
cᶜ-canonical = from-yes (isCanonical? cᶜ)

-- They represent a, b and c.
âᶜ-sound : ⌊ âᶜ ⌋ ≈ʷ a
âᶜ-sound = ≈ʷ-trans (from-yes (⌊ âᶜ ⌋ ≈ʷ? â)) (≈ʷ-sym a≈â)

ren-sound : {C : CTerm (Fin 9)} {w : LatTerm (Fin 9)} → ⌊ C ⌋ ≈ʷ w → ⌊ renᶜ πᵍ C ⌋ ≈ʷ w [ π ]
ren-sound {C} e = subst (_≈ʷ _) (sym (⌊renᶜ⌋ πᵍ C)) (≈ʷ-trans ([]-congʳ ⌊ C ⌋ π≈) ([]-cong π e))

bᶜ-sound : ⌊ bᶜ ⌋ ≈ʷ b
bᶜ-sound = ren-sound {C = âᶜ} âᶜ-sound

cᶜ-sound : ⌊ cᶜ ⌋ ≈ʷ c
cᶜ-sound = ren-sound {C = bᶜ} bᶜ-sound

-- The canonical forms of Freese's terms x ∨ (y ∧ z), y ∨ (z ∧ x), z ∨ (x ∧ y).
ρᶜ : Fin 3 → CTerm (Fin 3)
ρᶜ 0F = joinᶜ (jgen 0F) (jmeet (mgen 1F) (mgen 2F ∷ []) ∷ [])
ρᶜ 1F = joinᶜ (jgen 1F) (jmeet (mgen 2F) (mgen 0F ∷ []) ∷ [])
ρᶜ 2F = joinᶜ (jgen 2F) (jmeet (mgen 0F) (mgen 1F ∷ []) ∷ [])

ρᶜ-canonical : ∀ i → IsCanonical (ρᶜ i)
ρᶜ-canonical 0F = from-yes (isCanonical₃? (ρᶜ 0F))
ρᶜ-canonical 1F = from-yes (isCanonical₃? (ρᶜ 1F))
ρᶜ-canonical 2F = from-yes (isCanonical₃? (ρᶜ 2F))
```

#### Every triple that expresses a, b, c by Freese's terms lies in the generator box

Let `τ` be any triple whose induced homomorphism is injective, with
`(a, b, c) = ρ [ τ ]`: `a = τ x ∨ (τ y ∧ τ z)`, cyclically.  Then `τ` lies in the
generator box (`freese-terms-in-box`{.AgdaFunction}).

The lower ends need only that generators are join prime.  The generator `a₁`
lies below `a = τ x ∨ (τ y ∧ τ z)`, so below `τ x` or below `τ y ∧ τ z`; in the
second case it lies below `τ y`, which lies below `b = τ y ∨ (τ z ∧ τ x)`, and
`a₁ ≰ b` (`a₁≰b`{.AgdaFunction}).  So `a₁ ≤ τ x` (`a₁≤τx`{.AgdaFunction}), and
cyclically.

The upper ends come from the truncation ([DeansProblem.Truncation][]).  The term
`y ∨ (z ∧ x)` truncates the canonical form `bᶜ` of `b` (`trunc-b`{.AgdaFunction}),
so its meet child `z ∧ x` is matched with a meet joinand of `bᶜ`, every meetand
of which is cut, above `τ z` or above `τ x` (`zx-cut`{.AgdaFunction}).  The first
two meet joinands of `bᶜ` have the meetand `b₁ ∨ c₂₁ ∨ a₂₂`, which lies above
neither `c₁ ≤ τ z` nor `a₁ ≤ τ x`; so `z ∧ x` is matched with the third, whose
first meetand is `b₂₁ ∨ c₂₂ ∨ a₁`, which is not above `c₁`; so it lies above `τ x`
(`τx≤`{.AgdaFunction}).  The other two coordinates are the same reading of the
trees of `c` and `a`.

```agda
-- The generators a₁, b₁, c₁ lie below a, b, c and not below b, c, a.
a₁≤a : a₁ ≤ʷ a
a₁≤a = from-yes (a₁ ≤ʷ? a)

b₁≤b : b₁ ≤ʷ b
b₁≤b = []-mono π a₁≤a

c₁≤c : c₁ ≤ʷ c
c₁≤c = []-mono π b₁≤b

a₁≰b : ¬ (a₁ ≤ʷ b)
a₁≰b p = from-no (a₁ ≤ʷ? ⌊ bᶜ ⌋) (≤ʷ-trans p (proj₂ bᶜ-sound))

b₁≰c : ¬ (b₁ ≤ʷ c)
b₁≰c p = from-no (b₁ ≤ʷ? ⌊ cᶜ ⌋) (≤ʷ-trans p (proj₂ cᶜ-sound))

c₁≰a : ¬ (c₁ ≤ʷ a)
c₁≰a p = from-no (c₁ ≤ʷ? ⌊ âᶜ ⌋) (≤ʷ-trans p (proj₂ âᶜ-sound))

module _ (τ : Sub (Fin 3) (Fin 9)) (inj : IsInjective (proj₁ (subst-hom τ)))
         (abc≈ρ : ∀ i → abc i ≈ʷ ρ i [ τ ]) where
  open Truncates τ

  -- The lower ends: join primality of the generators.
  a₁≤τx : a₁ ≤ʷ τ 0F
  a₁≤τx with ℊ≤∨-inv (≤ʷ-trans a₁≤a (proj₁ (abc≈ρ 0F)))
  ... | inj₁ p  = p
  ... | inj₂ q  = ⊥-elim (a₁≰b (≤ʷ-trans q (≤ʷ-trans ∧̇-lowerˡ (≤ʷ-trans ∨̇-upperˡ (proj₂ (abc≈ρ 1F))))))

  b₁≤τy : b₁ ≤ʷ τ 1F
  b₁≤τy with ℊ≤∨-inv (≤ʷ-trans b₁≤b (proj₁ (abc≈ρ 1F)))
  ... | inj₁ p  = p
  ... | inj₂ q  = ⊥-elim (b₁≰c (≤ʷ-trans q (≤ʷ-trans ∧̇-lowerˡ (≤ʷ-trans ∨̇-upperˡ (proj₂ (abc≈ρ 2F))))))

  c₁≤τz : c₁ ≤ʷ τ 2F
  c₁≤τz with ℊ≤∨-inv (≤ʷ-trans c₁≤c (proj₁ (abc≈ρ 2F)))
  ... | inj₁ p  = p
  ... | inj₂ q  = ⊥-elim (c₁≰a (≤ʷ-trans q (≤ʷ-trans ∧̇-lowerˡ (≤ʷ-trans ∨̇-upperˡ (proj₂ (abc≈ρ 0F))))))

  -- The truncations of the canonical forms of a, b and c by Freese's terms.
  trunc-a : ρᶜ 0F ⊑ âᶜ
  trunc-a = truncation τ inj (ρᶜ 0F) âᶜ (ρᶜ-canonical 0F) âᶜ-canonical
                       (≈ʷ-trans (≈ʷ-sym (abc≈ρ 0F)) (≈ʷ-sym âᶜ-sound))

  trunc-b : ρᶜ 1F ⊑ bᶜ
  trunc-b = truncation τ inj (ρᶜ 1F) bᶜ (ρᶜ-canonical 1F) bᶜ-canonical
                       (≈ʷ-trans (≈ʷ-sym (abc≈ρ 1F)) (≈ʷ-sym bᶜ-sound))

  trunc-c : ρᶜ 2F ⊑ cᶜ
  trunc-c = truncation τ inj (ρᶜ 2F) cᶜ (ρᶜ-canonical 2F) cᶜ-canonical
                       (≈ʷ-trans (≈ʷ-sym (abc≈ρ 2F)) (≈ʷ-sym cᶜ-sound))

  -- A cut child of a node matched with a meet of two generators lies above one of them.
  cut-of-two : {i j : Fin 3} {v : CMand (Fin 9)}
             → Any (_⊑ᴹ v) (mgen i ∷ mgen j ∷ [])
               ⊎ (Σ[ k ∈ Fin 3 ] mgen k ∈ mgen i ∷ mgen j ∷ [] × τ k ≤ʷ ⌊ v ⌋ᴹ)
             → τ i ≤ʷ ⌊ v ⌋ᴹ ⊎ τ j ≤ʷ ⌊ v ⌋ᴹ
  cut-of-two (inj₁ (here ()))
  cut-of-two (inj₁ (there (here ())))
  cut-of-two (inj₂ (_ , here refl , le))          = inj₁ le
  cut-of-two (inj₂ (_ , there (here refl) , le))  = inj₂ le

  -- A meetand above neither generator below the two members is above neither member.
  neither : {i j : Fin 3} {g h u : LatTerm (Fin 9)} → g ≤ʷ τ i → h ≤ʷ τ j
          → ¬ (g ≤ʷ u) → ¬ (h ≤ʷ u) → τ i ≤ʷ u ⊎ τ j ≤ʷ u → ⊥
  neither g≤ _  g≰ _  (inj₁ p) = g≰ (≤ʷ-trans g≤ p)
  neither _  h≤ _  h≰ (inj₂ p) = h≰ (≤ʷ-trans h≤ p)

  -- A meetand not above the generator below the first member is above the second.
  second : {i j : Fin 3} {g u : LatTerm (Fin 9)} → g ≤ʷ τ i → ¬ (g ≤ʷ u) → τ i ≤ʷ u ⊎ τ j ≤ʷ u
         → τ j ≤ʷ u
  second g≤ g≰ (inj₁ p) = ⊥-elim (g≰ (≤ʷ-trans g≤ p))
  second _  _  (inj₂ p) = p
```

The three readings follow the same plan.  The term's meet child is matched with
one of the joinands of the canonical form; the generator joinand is impossible
(nothing truncates a generator child), so it is one of the three meet joinands;
the first two have a first meetand above neither of the generators below the
two members, which the cut forbids; the third has a first meetand above only the
generator below the member the coordinate is about, so that member lies below
it, and it lies below the upper end of the generator box.

```agda
  -- The upper end at x, from the tree of b, whose matched node z ∧ x has the meetands z and x.
  τx≤ : τ 0F ≤ʷ hiᵍ 0F
  τx≤ = from-tree trunc-b
    where
    v₁ v₃ : LatTerm (Fin 9)
    v₁ = ⌊ gens 3F (7F ∷ 2F ∷ []) ⌋ᴹ
    v₃ = ⌊ gens 4F (8F ∷ 0F ∷ []) ⌋ᴹ

    from-match : Any (jmeet (mgen 2F) (mgen 0F ∷ []) ⊑ᴶ_) (asListJ (joinandsOf bᶜ)) → τ 0F ≤ʷ hiᵍ 0F
    from-match (here ())
    from-match (there (here (jmeet⊑ (meet⊑ _ _ cut)))) =
      ⊥-elim (neither {u = v₁} c₁≤τz a₁≤τx (from-no (c₁ ≤ʷ? v₁)) (from-no (a₁ ≤ʷ? v₁))
                      (cut-of-two (cut (here refl))))
    from-match (there (there (here (jmeet⊑ (meet⊑ _ _ cut))))) =
      ⊥-elim (neither {u = v₁} c₁≤τz a₁≤τx (from-no (c₁ ≤ʷ? v₁)) (from-no (a₁ ≤ʷ? v₁))
                      (cut-of-two (cut (here refl))))
    from-match (there (there (there (here (jmeet⊑ (meet⊑ _ _ cut)))))) =
      ≤ʷ-trans (second {u = v₃} c₁≤τz (from-no (c₁ ≤ʷ? v₃)) (cut-of-two (cut (here refl))))
               (from-yes (v₃ ≤ʷ? hiᵍ 0F))
    from-match (there (there (there (there ()))))

    from-tree : ρᶜ 1F ⊑ bᶜ → τ 0F ≤ʷ hiᵍ 0F
    from-tree (join⊑ _ matched _) = from-match (matched (there (here refl)))

  -- The upper end at y, from the tree of c, whose matched node x ∧ y has the meetands x and y.
  τy≤ : τ 1F ≤ʷ hiᵍ 1F
  τy≤ = from-tree trunc-c
    where
    v₁ v₃ : LatTerm (Fin 9)
    v₁ = ⌊ gens 6F (1F ∷ 5F ∷ []) ⌋ᴹ
    v₃ = ⌊ gens 7F (2F ∷ 3F ∷ []) ⌋ᴹ

    from-match : Any (jmeet (mgen 0F) (mgen 1F ∷ []) ⊑ᴶ_) (asListJ (joinandsOf cᶜ)) → τ 1F ≤ʷ hiᵍ 1F
    from-match (here ())
    from-match (there (here (jmeet⊑ (meet⊑ _ _ cut)))) =
      ⊥-elim (neither {u = v₁} a₁≤τx b₁≤τy (from-no (a₁ ≤ʷ? v₁)) (from-no (b₁ ≤ʷ? v₁))
                      (cut-of-two (cut (here refl))))
    from-match (there (there (here (jmeet⊑ (meet⊑ _ _ cut))))) =
      ⊥-elim (neither {u = v₁} a₁≤τx b₁≤τy (from-no (a₁ ≤ʷ? v₁)) (from-no (b₁ ≤ʷ? v₁))
                      (cut-of-two (cut (here refl))))
    from-match (there (there (there (here (jmeet⊑ (meet⊑ _ _ cut)))))) =
      ≤ʷ-trans (second {u = v₃} a₁≤τx (from-no (a₁ ≤ʷ? v₃)) (cut-of-two (cut (here refl))))
               (from-yes (v₃ ≤ʷ? hiᵍ 1F))
    from-match (there (there (there (there ()))))

    from-tree : ρᶜ 2F ⊑ cᶜ → τ 1F ≤ʷ hiᵍ 1F
    from-tree (join⊑ _ matched _) = from-match (matched (there (here refl)))

  -- The upper end at z, from the tree of a, whose matched node y ∧ z has the meetands y and z.
  τz≤ : τ 2F ≤ʷ hiᵍ 2F
  τz≤ = from-tree trunc-a
    where
    v₁ v₃ : LatTerm (Fin 9)
    v₁ = ⌊ gens 0F (4F ∷ 8F ∷ []) ⌋ᴹ
    v₃ = ⌊ gens 1F (5F ∷ 6F ∷ []) ⌋ᴹ

    from-match : Any (jmeet (mgen 1F) (mgen 2F ∷ []) ⊑ᴶ_) (asListJ (joinandsOf âᶜ)) → τ 2F ≤ʷ hiᵍ 2F
    from-match (here ())
    from-match (there (here (jmeet⊑ (meet⊑ _ _ cut)))) =
      ⊥-elim (neither {u = v₁} b₁≤τy c₁≤τz (from-no (b₁ ≤ʷ? v₁)) (from-no (c₁ ≤ʷ? v₁))
                      (cut-of-two (cut (here refl))))
    from-match (there (there (here (jmeet⊑ (meet⊑ _ _ cut))))) =
      ⊥-elim (neither {u = v₁} b₁≤τy c₁≤τz (from-no (b₁ ≤ʷ? v₁)) (from-no (c₁ ≤ʷ? v₁))
                      (cut-of-two (cut (here refl))))
    from-match (there (there (there (here (jmeet⊑ (meet⊑ _ _ cut)))))) =
      ≤ʷ-trans (second {u = v₃} b₁≤τy (from-no (b₁ ≤ʷ? v₃)) (cut-of-two (cut (here refl))))
               (from-yes (v₃ ≤ʷ? hiᵍ 2F))
    from-match (there (there (there (there ()))))

    from-tree : ρᶜ 0F ⊑ âᶜ → τ 2F ≤ʷ hiᵍ 2F
    from-tree (join⊑ _ matched _) = from-match (matched (there (here refl)))

  -- Every triple expressing a, b, c by Freese's terms lies in the generator box.
  freese-terms-in-box : InBox loᵍ hiᵍ τ
  freese-terms-in-box 0F = a₁≤τx , τx≤
  freese-terms-in-box 1F = b₁≤τy , τy≤
  freese-terms-in-box 2F = c₁≤τz , τz≤
```

#### Freese's terms occur in at most one link

So two triples that both express `(a, b, c)` by Freese's terms, the first in the
sublattice of the second, are equal (`freese-terms-once`{.AgdaFunction}), and no
step has both of its triples express `(a, b, c)` by Freese's terms
(`no-step-with-freese-terms`{.AgdaFunction}).  In the language of Section 6 of
[the paper][]: in a chain whose first link is `⟨a, b, c⟩`, the term
`θ_{0,k}` expressing the first link in the `k`-th is `x ∨ (y ∧ z)`, cyclically,
for at most one `k`.  The finiteness theorem says that some term recurs; this
one cannot.

```agda
-- Two triples expressing a, b, c by Freese's terms, one inside the other's sublattice, are equal.
freese-terms-once : (τ₁ τ₂ : Sub (Fin 3) (Fin 9)) → FreelyGenerates τ₁ → FreelyGenerates τ₂
                  → (∀ i → abc i ≈ʷ ρ i [ τ₁ ]) → (∀ i → abc i ≈ʷ ρ i [ τ₂ ])
                  → (q : Sub (Fin 3) (Fin 3)) → (∀ j → τ₁ j ≈ʷ q j [ τ₂ ]) → ∀ i → τ₁ i ≈ʷ τ₂ i
freese-terms-once τ₁ τ₂ free₁ free₂ e₁ e₂ q τ₁≈ i =
  box-agree q τ₁≈ (freese-terms-in-box τ₁ (freelyGenerates→injective τ₁ free₁) e₁)
                  (freese-terms-in-box τ₂ (freelyGenerates→injective τ₂ free₂) e₂)
            i (generator-box-irredundant i)

-- No step has both of its triples express a, b, c by Freese's terms.
no-step-with-freese-terms : (s : Step (Fin 9)) → (∀ i → abc i ≈ʷ ρ i [ Step.σ s ])
                          → ¬ (∀ i → abc i ≈ʷ ρ i [ Step.τ s ])
no-step-with-freese-terms s eσ eτ =
  no-step-in-irredundant-box s generator-box-irredundant
    (freese-terms-in-box (Step.σ s) (freelyGenerates→injective (Step.σ s) (Step.σ-free s)) eσ)
    (freese-terms-in-box (Step.τ s) (freelyGenerates→injective (Step.τ s) (Step.τ-free s)) eτ)
```

--------------------------------------

[DeansProblem.Examples.FreeseBox]: DeansProblem.Examples.FreeseBox.html
[DeansProblem.AlmostProof]: DeansProblem.AlmostProof.html
[DeansProblem.Chain]: DeansProblem.Chain.html
[DeansProblem.Examples.FreeseStep]: DeansProblem.Examples.FreeseStep.html
[DeansProblem.Truncation]: DeansProblem.Truncation.html
[Lattices.Free.Canonical.Recognition]: Lattices.Free.Canonical.Recognition.html
