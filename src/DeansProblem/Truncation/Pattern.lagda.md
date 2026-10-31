---
layout: default
file: "src/DeansProblem/Truncation/Pattern.lagda.md"
title: "DeansProblem.Truncation.Pattern module"
date: "2026-10-27"
author: "the agda-lattices development team"
---

### Labeled patterns: finitely many for a fixed tree

This is the [DeansProblem.Truncation.Pattern][] module of this repository.

[the paper]: https://arxiv.org/abs/YYMM.NNNNN

Let `τ` be a family of elements of `FL(Y)` indexed by `I`, `p` a term over
`I` with canonical form `C`, and `D` the canonical form of `p [ τ ]`.  The
truncation theorem of [the paper][] (Theorem 9.1, `truncation`{.AgdaFunction}
of [DeansProblem.Truncation][]) says that `C` truncates `D` through `τ`.  A
*labeled pattern* is the data the relation `C ⊑ D`{.AgdaDatatype} records:
which node of `D` each node of `C` names, and at each cut which member `τ i`
sits between the node and its child.  Section 9.2 of the paper adds: "For a
fixed term `p` there are finitely many labeled patterns."

**The quantifier**.  So worded the claim is false.  Take `p = x ∨ y` and, for
each `n`, the family `τₙ` sending `x` to the join `g₀ ∨ ⋯ ∨ gₙ` of distinct
generators of `FL(Y)` and `y`, `z` to two further generators (a free triple).
Then `D` is the canonical join `g₀ ∨ ⋯ ∨ gₙ ∨ h` with `n + 2` children, all of
them cuts, so the patterns of `p` differ for every `n`.  Freese's claim is about
his chain's fixed bottom triple, so about a fixed `D`: there the meet children
of `C` match distinct children of `D`, and each node of `C` has at most `|I|`
generator children, so for `I` finite there are finitely many labeled patterns.
This module states that form.

**Labeled patterns as a type**.  A pattern on `D`
(`Pattern D`{.AgdaDatatype}) is read off the nodes of `D` that `C` names: at a
node where `C` is a generator `i` it is the label `i` (`pgen`{.AgdaInductiveConstructor});
at a join node of `D` that a join of `C` names
(`pjoin`{.AgdaInductiveConstructor}) it lists, for every child of `D`, either
the pattern of the child of `C` that matches it (a meet child, named by
`pjmeet`{.AgdaInductiveConstructor}) or the label `i` of the cut it is; and
dually at a meet node (`pmeet`{.AgdaInductiveConstructor},
`pmjoin`{.AgdaInductiveConstructor}).  The labeled pattern of a truncation is
this data (`patternOf`{.AgdaFunction}), which forgets the proofs and keeps the
choices: the matched children of `D` are the images of the meet children of
`C`, recursively, so the pattern records which node of `D` each node of `C`
names, and the labels record the cuts.

**Finitely many for a fixed `D`** (`Enumerate`{.AgdaModule}).  Given a list of
the indices `I`, every pattern on `D` is a member of an explicit list
`patterns D`{.AgdaFunction} (`patterns-complete`{.AgdaFunction}), built by
recursion on `D`: a label at the node, or, at a join node, one choice per
child, each a pattern of the child or a label.  So the labeled patterns of all
truncations of a fixed `D`, through all families `τ` and all terms `p`, lie in
one finite list: Freese's "finitely many possible truncations even counting the
labelling", with the quantifier where his argument puts it.

**The box of a pattern** (`Bound`{.AgdaDatatype}).  At a cut of a join node,
the cut child lies below `τ i`, and `τ i` below the node; at a cut of a meet
node, dually; at a node where `C` is the generator `i`, `τ i` is the node.  So
each cut gives an interval `[l, u]` for one `τ i`, read off the pattern alone,
and every truncation with that pattern puts `τ i` in it
(`bound-sound`{.AgdaFunction}): every link with the pattern lies in the box of
the pattern, which is the use Section 9.3 makes of it.

**The box inside `FL(3)`** (Section 9.3).  Read inside a link as `FL(3)`, the
labeled pattern of the terms is the *identity pattern* of their trees
(`idPattern`{.AgdaFunction}): every child of a node is matched, except a
generator child `x`, which is a cut labeled `x`, its own cut child.  The box of
a generator `x` that occurs in the tree both as a joinand
(`JoinGen`{.AgdaDatatype}) and as a meetand (`MeetGen`{.AgdaDatatype}) is then
the point `[x, x]` (`idPattern-joinGen`{.AgdaFunction},
`idPattern-meetGen`{.AgdaFunction}), and any family with that pattern sends
`x` to `x` (`point-box`{.AgdaFunction}).

<!--
```agda
{-# OPTIONS --without-K --exact-split --safe #-}

module DeansProblem.Truncation.Pattern where

open import Agda.Primitive  using () renaming ( Set to Type )

-- Imports from the Agda Standard Library ---------------------------------------
open import Data.List.Base                         using ( List ; [] ; _∷_ ; map ; _++_
                                                         ; cartesianProductWith )
open import Data.List.Membership.Propositional     using ( _∈_ ; lose )
open import Data.List.Membership.Propositional.Properties
                                                   using ( ∈-map⁺ ; ∈-++⁺ˡ ; ∈-++⁺ʳ
                                                         ; ∈-cartesianProductWith⁺ )
open import Data.List.Relation.Unary.All           using ( All ; [] ; _∷_ )
open import Data.List.Relation.Unary.Any           using ( Any ; here ; there )
open import Data.Product                           using ( Σ-syntax ; _×_ ; _,_ ; proj₁ ; proj₂ )
open import Data.Sum.Base                          using ( _⊎_ ; inj₁ ; inj₂ )
open import Data.Sum.Properties                    using ( inj₁-injective )
open import Data.Unit.Polymorphic                  using ( ⊤ ; tt )
open import Function                               using ( _∘_ )
open import Level                                  using ( Level ; _⊔_ )
open import Relation.Binary.PropositionalEquality  using ( _≡_ ; refl ; sym ; trans ; cong ; cong₂ ; subst )

import Data.List.Relation.Unary.All as All

-- Imports from the Agda Universal Algebra Library ------------------------------
open import Lattices.Free.Canonical.Basic          using ( CTerm ; genᶜ ; joinᶜ ; meetᶜ ; CJand ; jgen
                                                         ; jmeet ; CMand ; mgen ; mjoin ; ⌊_⌋ ; ⌊_⌋ᴶ
                                                         ; ⌊_⌋ᴹ ; ⋁ᴶ ; ⋀ᴹ )
open import DeansProblem.Truncation                using ( module Truncates ; ≡→≈ʷ )
open import Lattices.Free.Substitution             using ( Sub ; _[_] ; []-ℊ )
open import Lattices.Free.Term                     using ( LatTerm ; ℊ )
open import Lattices.Free.Whitman                  using ( _≤ʷ_ ; _≈ʷ_ ; ≤ʷ-refl )

private variable
  ι υ ℓ : Level
  A : Type ℓ
```
-->

#### Labeled patterns

A pattern on `D` over labels `I` is defined together with the patterns of the
children of joins and meets, as described at the top.

```agda
module _ (I : Type ι) {Y : Type υ} where
  data Pattern   : CTerm Y → Type (ι ⊔ υ)
  data Patternᴶ  : CJand Y → Type (ι ⊔ υ)
  data Patternᴹ  : CMand Y → Type (ι ⊔ υ)

  data Pattern where
    -- C is the generator i, whose image is the node.
    pgen   : {D : CTerm Y} → I → Pattern D
    -- A join of C names the join D: each child of D is matched or cut at a label.
    pjoin  : {h : CJand Y} {t : List (CJand Y)} → All (λ d → Patternᴶ d ⊎ I) (h ∷ t) → Pattern (joinᶜ h t)
    -- A meet of C names the meet D, dually.
    pmeet  : {h : CMand Y} {t : List (CMand Y)} → All (λ d → Patternᴹ d ⊎ I) (h ∷ t) → Pattern (meetᶜ h t)

  data Patternᴶ where
    -- A meet child of C matches the meet child of D.
    pjmeet : {mh : CMand Y} {mt : List (CMand Y)} → Pattern (meetᶜ mh mt) → Patternᴶ (jmeet mh mt)

  data Patternᴹ where
    -- A join child of C matches the join child of D.
    pmjoin : {jh : CJand Y} {jt : List (CJand Y)} → Pattern (joinᶜ jh jt) → Patternᴹ (mjoin jh jt)
```

#### The labeled pattern of a truncation

A family of choices, one for each member of a list, is collected into an
`All`{.AgdaDatatype} (`collect`{.AgdaFunction}), and looking a member up returns
its choice (`lookup-collect`{.AgdaFunction}).  The labeled pattern of a
truncation (`patternOf`{.AgdaFunction}) keeps, for each child of a node of `D`,
the pattern of the child of `C` that matches it, or the label of its cut.

```agda
-- One choice for each member of a list, collected.
collect : {R : A → Type ℓ} {ys : List A} → (∀ {d} → d ∈ ys → R d) → All R ys
collect {ys = []}      f = []
collect {ys = _ ∷ _}   f = f (here refl) ∷ collect (λ d∈ → f (there d∈))

-- Looking a member up in a collection returns its choice.
lookup-collect : {R : A → Type ℓ} {ys : List A} (f : ∀ {d} → d ∈ ys → R d) {d : A} (d∈ : d ∈ ys)
               → All.lookup (collect f) d∈ ≡ f d∈
lookup-collect f (here refl)  = refl
lookup-collect f (there d∈)   = lookup-collect (λ x∈ → f (there x∈)) d∈

module _ {I : Type ι} {Y : Type υ} (τ : Sub I Y) where
  open Truncates τ

  -- The labeled pattern of a truncation, of a matched child of a join, and of a meet.
  patternOf  : {C : CTerm I} {D : CTerm Y} → C ⊑ D → Pattern I D
  patternᴶ   : {c : CJand I} {d : CJand Y} → c ⊑ᴶ d → Patternᴶ I d
  patternᴹ   : {c : CMand I} {d : CMand Y} → c ⊑ᴹ d → Patternᴹ I d
  anyᴶ       : {d : CJand Y} {cs : List (CJand I)} → Any (_⊑ᴶ d) cs → Patternᴶ I d
  anyᴹ       : {d : CMand Y} {cs : List (CMand I)} → Any (_⊑ᴹ d) cs → Patternᴹ I d
  childᴶ     : {d : CJand Y} {cs : List (CJand I)}
             → Any (_⊑ᴶ d) cs ⊎ (Σ[ i ∈ I ] jgen i ∈ cs × ⌊ d ⌋ᴶ ≤ʷ τ i) → Patternᴶ I d ⊎ I
  childᴹ     : {d : CMand Y} {cs : List (CMand I)}
             → Any (_⊑ᴹ d) cs ⊎ (Σ[ i ∈ I ] mgen i ∈ cs × τ i ≤ʷ ⌊ d ⌋ᴹ) → Patternᴹ I d ⊎ I

  patternOf (gen⊑ {i = i} _)        = pgen i
  patternOf (join⊑ _ _ covered)     = pjoin (collect λ d∈ → childᴶ (covered d∈))
  patternOf (meet⊑ _ _ covered)     = pmeet (collect λ d∈ → childᴹ (covered d∈))
  patternᴶ (jmeet⊑ q)               = pjmeet (patternOf q)
  patternᴹ (mjoin⊑ q)               = pmjoin (patternOf q)
  anyᴶ (here q)                     = patternᴶ q
  anyᴶ (there a)                    = anyᴶ a
  anyᴹ (here q)                     = patternᴹ q
  anyᴹ (there a)                    = anyᴹ a
  childᴶ (inj₁ a)                   = inj₁ (anyᴶ a)
  childᴶ (inj₂ (i , _))             = inj₂ i
  childᴹ (inj₁ a)                   = inj₁ (anyᴹ a)
  childᴹ (inj₂ (i , _))             = inj₂ i
```

#### Finitely many patterns on a fixed tree

Fix a list `enum` of the labels with every label a member.  The patterns on `D`
(`patterns`{.AgdaFunction}) are the labels at the node, and at a join node
every row of choices for its children (`rowsᴶ⁺`{.AgdaFunction}), a choice for
a child being a pattern of it or a label (`choicesᴶ`{.AgdaFunction}); dually at
a meet node.  The recursion takes a node's children apart before it rebuilds
the node, as the truncation theorem's does, so that every call is on a
subterm.  Every pattern is a member (`patterns-complete`{.AgdaFunction}), by
the same recursion on the pattern.

```agda
module Enumerate {I : Type ι} {Y : Type υ} (enum : List I) (enum-complete : ∀ i → i ∈ enum) where
  -- The patterns that are a label at the node.
  labels : {D : CTerm Y} → List (Pattern I D)
  labels = map pgen enum

  patterns   : (D : CTerm Y) → List (Pattern I D)
  patternsᴶ  : (h : CJand Y) (t : List (CJand Y)) → List (Pattern I (joinᶜ h t))
  patternsᴹ  : (h : CMand Y) (t : List (CMand Y)) → List (Pattern I (meetᶜ h t))
  choicesᴶ   : (d : CJand Y) → List (Patternᴶ I d ⊎ I)
  choicesᴹ   : (d : CMand Y) → List (Patternᴹ I d ⊎ I)
  rowsᴶ      : (ds : List (CJand Y)) → List (All (λ d → Patternᴶ I d ⊎ I) ds)
  rowsᴶ⁺     : (h : CJand Y) (t : List (CJand Y)) → List (All (λ d → Patternᴶ I d ⊎ I) (h ∷ t))
  rowsᴹ      : (ds : List (CMand Y)) → List (All (λ d → Patternᴹ I d ⊎ I) ds)
  rowsᴹ⁺     : (h : CMand Y) (t : List (CMand Y)) → List (All (λ d → Patternᴹ I d ⊎ I) (h ∷ t))

  patterns (genᶜ _)              = labels
  patterns (joinᶜ h t)           = patternsᴶ h t
  patterns (meetᶜ h t)           = patternsᴹ h t
  patternsᴶ h t                  = labels ++ map pjoin (rowsᴶ⁺ h t)
  patternsᴹ h t                  = labels ++ map pmeet (rowsᴹ⁺ h t)
  choicesᴶ (jgen _)              = map inj₂ enum
  choicesᴶ (jmeet mh mt)         = map (inj₁ ∘ pjmeet) (patternsᴹ mh mt) ++ map inj₂ enum
  choicesᴹ (mgen _)              = map inj₂ enum
  choicesᴹ (mjoin jh jt)         = map (inj₁ ∘ pmjoin) (patternsᴶ jh jt) ++ map inj₂ enum
  rowsᴶ []                       = [] ∷ []
  rowsᴶ (d ∷ ds)                 = rowsᴶ⁺ d ds
  rowsᴶ⁺ h t                     = cartesianProductWith _∷_ (choicesᴶ h) (rowsᴶ t)
  rowsᴹ []                       = [] ∷ []
  rowsᴹ (d ∷ ds)                 = rowsᴹ⁺ d ds
  rowsᴹ⁺ h t                     = cartesianProductWith _∷_ (choicesᴹ h) (rowsᴹ t)
```

```agda
  -- Every pattern on D is in the list.
  patterns-complete  : {D : CTerm Y} (P : Pattern I D) → P ∈ patterns D
  choiceᴶ-complete   : {d : CJand Y} (x : Patternᴶ I d ⊎ I) → x ∈ choicesᴶ d
  choiceᴹ-complete   : {d : CMand Y} (x : Patternᴹ I d ⊎ I) → x ∈ choicesᴹ d
  rowᴶ-complete      : {ds : List (CJand Y)} (r : All (λ d → Patternᴶ I d ⊎ I) ds) → r ∈ rowsᴶ ds
  rowᴹ-complete      : {ds : List (CMand Y)} (r : All (λ d → Patternᴹ I d ⊎ I) ds) → r ∈ rowsᴹ ds

  patterns-complete {genᶜ _}     (pgen i)   = ∈-map⁺ pgen (enum-complete i)
  patterns-complete {joinᶜ _ _}  (pgen i)   = ∈-++⁺ˡ (∈-map⁺ pgen (enum-complete i))
  patterns-complete {meetᶜ _ _}  (pgen i)   = ∈-++⁺ˡ (∈-map⁺ pgen (enum-complete i))
  patterns-complete              (pjoin r)  = ∈-++⁺ʳ labels (∈-map⁺ pjoin (rowᴶ-complete r))
  patterns-complete              (pmeet r)  = ∈-++⁺ʳ labels (∈-map⁺ pmeet (rowᴹ-complete r))
  choiceᴶ-complete {jgen _}       (inj₂ i)           = ∈-map⁺ inj₂ (enum-complete i)
  choiceᴶ-complete {jmeet mh mt}  (inj₂ i)           = ∈-++⁺ʳ (map (inj₁ ∘ pjmeet) (patternsᴹ mh mt))
                                                              (∈-map⁺ inj₂ (enum-complete i))
  choiceᴶ-complete                (inj₁ (pjmeet P))  = ∈-++⁺ˡ (∈-map⁺ (inj₁ ∘ pjmeet) (patterns-complete P))
  choiceᴹ-complete {mgen _}       (inj₂ i)           = ∈-map⁺ inj₂ (enum-complete i)
  choiceᴹ-complete {mjoin jh jt}  (inj₂ i)           = ∈-++⁺ʳ (map (inj₁ ∘ pmjoin) (patternsᴶ jh jt))
                                                              (∈-map⁺ inj₂ (enum-complete i))
  choiceᴹ-complete                (inj₁ (pmjoin P))  = ∈-++⁺ˡ (∈-map⁺ (inj₁ ∘ pmjoin) (patterns-complete P))
  rowᴶ-complete []        = here refl
  rowᴶ-complete (x ∷ r)   = ∈-cartesianProductWith⁺ _∷_ (choiceᴶ-complete x) (rowᴶ-complete r)
  rowᴹ-complete []        = here refl
  rowᴹ-complete (x ∷ r)   = ∈-cartesianProductWith⁺ _∷_ (choiceᴹ-complete x) (rowᴹ-complete r)

  -- Section 9.2: the labeled patterns of all truncations of a fixed D lie in one finite list.
  finitely-many-patterns : (τ : Sub I Y) {C : CTerm I} {D : CTerm Y} (r : Truncates._⊑_ τ C D)
                         → patternOf τ r ∈ patterns D
  finitely-many-patterns τ r = patterns-complete (patternOf τ r)
```

#### The box of a pattern

`Bound P i l u`{.AgdaDatatype} says that the pattern `P` puts `τ i` in the
interval `[l, u]`: at a node labeled `i` (`at-gen`{.AgdaInductiveConstructor}),
at a cut labeled `i` of a join node or a meet node
(`cutᴶ`{.AgdaInductiveConstructor}, `cutᴹ`{.AgdaInductiveConstructor}), or
inside a matched child (`inᴶ`{.AgdaInductiveConstructor},
`inᴹ`{.AgdaInductiveConstructor}).  The intervals depend on the pattern alone,
and every truncation with the pattern puts `τ i` in each of them
(`bound-sound`{.AgdaFunction}).

```agda
module _ {I : Type ι} {Y : Type υ} where
  -- The pattern P puts τ i in the interval [l, u].
  data Bound : {D : CTerm Y} → Pattern I D → I → LatTerm Y → LatTerm Y → Type (ι ⊔ υ) where
    at-gen : {D : CTerm Y} {i : I} → Bound (pgen {D = D} i) i ⌊ D ⌋ ⌊ D ⌋
    cutᴶ   : {h : CJand Y} {t : List (CJand Y)} {r : All (λ d → Patternᴶ I d ⊎ I) (h ∷ t)} {d : CJand Y}
             {i : I} (d∈ : d ∈ h ∷ t) → All.lookup r d∈ ≡ inj₂ i → Bound (pjoin r) i ⌊ d ⌋ᴶ (⋁ᴶ h t)
    cutᴹ   : {h : CMand Y} {t : List (CMand Y)} {r : All (λ d → Patternᴹ I d ⊎ I) (h ∷ t)} {d : CMand Y}
             {i : I} (d∈ : d ∈ h ∷ t) → All.lookup r d∈ ≡ inj₂ i → Bound (pmeet r) i (⋀ᴹ h t) ⌊ d ⌋ᴹ
    inᴶ    : {h : CJand Y} {t : List (CJand Y)} {r : All (λ d → Patternᴶ I d ⊎ I) (h ∷ t)}
             {mh : CMand Y} {mt : List (CMand Y)} {P : Pattern I (meetᶜ mh mt)} {i : I} {l u : LatTerm Y}
             (d∈ : jmeet mh mt ∈ h ∷ t) → All.lookup r d∈ ≡ inj₁ (pjmeet P) → Bound P i l u
           → Bound (pjoin r) i l u
    inᴹ    : {h : CMand Y} {t : List (CMand Y)} {r : All (λ d → Patternᴹ I d ⊎ I) (h ∷ t)}
             {jh : CJand Y} {jt : List (CJand Y)} {P : Pattern I (joinᶜ jh jt)} {i : I} {l u : LatTerm Y}
             (d∈ : mjoin jh jt ∈ h ∷ t) → All.lookup r d∈ ≡ inj₁ (pmjoin P) → Bound P i l u
           → Bound (pmeet r) i l u

module _ {I : Type ι} {Y : Type υ} (τ : Sub I Y) where
  open Truncates τ

  -- Every truncation with a pattern puts τ i in each interval of the pattern.
  bound-sound   : {C : CTerm I} {D : CTerm Y} (r : C ⊑ D) {i : I} {l u : LatTerm Y}
                → Bound (patternOf τ r) i l u → l ≤ʷ τ i × τ i ≤ʷ u
  cut-soundᴶ    : {h : CJand I} {t : List (CJand I)} {h' : CJand Y} {t' : List (CJand Y)} {d : CJand Y}
                  {i : I} → ⋁ᴶ h t [ τ ] ≈ʷ ⋁ᴶ h' t'
                → (x : Any (_⊑ᴶ d) (h ∷ t) ⊎ (Σ[ j ∈ I ] jgen j ∈ h ∷ t × ⌊ d ⌋ᴶ ≤ʷ τ j))
                → childᴶ τ x ≡ inj₂ i → ⌊ d ⌋ᴶ ≤ʷ τ i × τ i ≤ʷ ⋁ᴶ h' t'
  cut-soundᴹ    : {h : CMand I} {t : List (CMand I)} {h' : CMand Y} {t' : List (CMand Y)} {d : CMand Y}
                  {i : I} → ⋀ᴹ h t [ τ ] ≈ʷ ⋀ᴹ h' t'
                → (x : Any (_⊑ᴹ d) (h ∷ t) ⊎ (Σ[ j ∈ I ] mgen j ∈ h ∷ t × τ j ≤ʷ ⌊ d ⌋ᴹ))
                → childᴹ τ x ≡ inj₂ i → ⋀ᴹ h' t' ≤ʷ τ i × τ i ≤ʷ ⌊ d ⌋ᴹ
  any-soundᴶ    : {cs : List (CJand I)} {mh : CMand Y} {mt : List (CMand Y)} {P : Pattern I (meetᶜ mh mt)}
                  {i : I} {l u : LatTerm Y} (a : Any (_⊑ᴶ jmeet mh mt) cs)
                → anyᴶ τ a ≡ pjmeet P → Bound P i l u → l ≤ʷ τ i × τ i ≤ʷ u
  any-soundᴹ    : {cs : List (CMand I)} {jh : CJand Y} {jt : List (CJand Y)} {P : Pattern I (joinᶜ jh jt)}
                  {i : I} {l u : LatTerm Y} (a : Any (_⊑ᴹ mjoin jh jt) cs)
                → anyᴹ τ a ≡ pmjoin P → Bound P i l u → l ≤ʷ τ i × τ i ≤ʷ u
  in-soundᴶ     : {cs : List (CJand I)} {mh : CMand Y} {mt : List (CMand Y)} {P : Pattern I (meetᶜ mh mt)}
                  {i : I} {l u : LatTerm Y}
                  (x : Any (_⊑ᴶ jmeet mh mt) cs ⊎ (Σ[ j ∈ I ] jgen j ∈ cs × ⋀ᴹ mh mt ≤ʷ τ j))
                → childᴶ τ x ≡ inj₁ (pjmeet P) → Bound P i l u → l ≤ʷ τ i × τ i ≤ʷ u
  in-soundᴹ     : {cs : List (CMand I)} {jh : CJand Y} {jt : List (CJand Y)} {P : Pattern I (joinᶜ jh jt)}
                  {i : I} {l u : LatTerm Y}
                  (x : Any (_⊑ᴹ mjoin jh jt) cs ⊎ (Σ[ j ∈ I ] mgen j ∈ cs × τ j ≤ʷ ⋁ᴶ jh jt))
                → childᴹ τ x ≡ inj₁ (pmjoin P) → Bound P i l u → l ≤ʷ τ i × τ i ≤ʷ u

  bound-sound (gen⊑ e)          at-gen          = proj₂ e , proj₁ e
  bound-sound (join⊑ {h' = h'} {t' = t'} e _ cov) (cutᴶ d∈ eq)    =
    cut-soundᴶ {h' = h'} {t' = t'} e (cov d∈) (trans (sym (lookup-collect (λ x∈ → childᴶ τ (cov x∈)) d∈)) eq)
  bound-sound (join⊑ {h' = h'} {t' = t'} e _ cov) (inᴶ d∈ eq b)   =
    in-soundᴶ (cov d∈) (trans (sym (lookup-collect (λ x∈ → childᴶ τ (cov x∈)) d∈)) eq) b
  bound-sound (meet⊑ {h' = h'} {t' = t'} e _ cov) (cutᴹ d∈ eq)    =
    cut-soundᴹ {h' = h'} {t' = t'} e (cov d∈) (trans (sym (lookup-collect (λ x∈ → childᴹ τ (cov x∈)) d∈)) eq)
  bound-sound (meet⊑ {h' = h'} {t' = t'} e _ cov) (inᴹ d∈ eq b)   =
    in-soundᴹ (cov d∈) (trans (sym (lookup-collect (λ x∈ → childᴹ τ (cov x∈)) d∈)) eq) b
  cut-soundᴶ {h' = h'} {t' = t'} e (inj₂ (i , i∈ , d≤)) refl = d≤ , cut-belowᴶ {h' = h'} {t' = t'} e i∈
  cut-soundᴹ {h' = h'} {t' = t'} e (inj₂ (i , i∈ , ≤d)) refl = cut-aboveᴹ {h' = h'} {t' = t'} e i∈ , ≤d
  any-soundᴶ (here (jmeet⊑ q)) refl b = bound-sound q b
  any-soundᴶ (there a)         eq   b = any-soundᴶ a eq b
  any-soundᴹ (here (mjoin⊑ q)) refl b = bound-sound q b
  any-soundᴹ (there a)         eq   b = any-soundᴹ a eq b
  in-soundᴶ (inj₁ a) eq b = any-soundᴶ a (inj₁-injective eq) b
  in-soundᴹ (inj₁ a) eq b = any-soundᴹ a (inj₁-injective eq) b
```

#### The box inside FL(3)

Over labels `Y` themselves, the identity pattern of a tree
(`idPattern`{.AgdaFunction}) matches every child of every node except a
generator child `y`, which is a cut labeled `y`: it is the pattern of the
tree read inside a link as `FL(3)`, whose cut children are the generators
themselves.  A generator occurs in the tree as a joinand
(`JoinGen`{.AgdaDatatype}) when it is a child of a join node, and as a meetand
(`MeetGen`{.AgdaDatatype}) when it is a child of a meet node, at any depth.

```agda
module _ {Y : Type υ} where
  idPattern   : (D : CTerm Y) → Pattern Y D
  idPatternᴶ  : (h : CJand Y) (t : List (CJand Y)) → Pattern Y (joinᶜ h t)
  idPatternᴹ  : (h : CMand Y) (t : List (CMand Y)) → Pattern Y (meetᶜ h t)
  idChildᴶ    : (d : CJand Y) → Patternᴶ Y d ⊎ Y
  idChildᴹ    : (d : CMand Y) → Patternᴹ Y d ⊎ Y
  idRowᴶ      : (ds : List (CJand Y)) → All (λ d → Patternᴶ Y d ⊎ Y) ds
  idRowᴹ      : (ds : List (CMand Y)) → All (λ d → Patternᴹ Y d ⊎ Y) ds

  idPattern (genᶜ y)        = pgen y
  idPattern (joinᶜ h t)     = idPatternᴶ h t
  idPattern (meetᶜ h t)     = idPatternᴹ h t
  idPatternᴶ h t            = pjoin (idChildᴶ h ∷ idRowᴶ t)
  idPatternᴹ h t            = pmeet (idChildᴹ h ∷ idRowᴹ t)
  idChildᴶ (jgen y)         = inj₂ y
  idChildᴶ (jmeet mh mt)    = inj₁ (pjmeet (idPatternᴹ mh mt))
  idChildᴹ (mgen y)         = inj₂ y
  idChildᴹ (mjoin jh jt)    = inj₁ (pmjoin (idPatternᴶ jh jt))
  idRowᴶ []                 = []
  idRowᴶ (d ∷ ds)           = idChildᴶ d ∷ idRowᴶ ds
  idRowᴹ []                 = []
  idRowᴹ (d ∷ ds)           = idChildᴹ d ∷ idRowᴹ ds

  -- Looking a child up in the identity row returns its identity choice.
  lookup-idRowᴶ : {ds : List (CJand Y)} {d : CJand Y} (d∈ : d ∈ ds) → All.lookup (idRowᴶ ds) d∈ ≡ idChildᴶ d
  lookup-idRowᴶ (here refl)  = refl
  lookup-idRowᴶ (there d∈)   = lookup-idRowᴶ d∈

  lookup-idRowᴹ : {ds : List (CMand Y)} {d : CMand Y} (d∈ : d ∈ ds) → All.lookup (idRowᴹ ds) d∈ ≡ idChildᴹ d
  lookup-idRowᴹ (here refl)  = refl
  lookup-idRowᴹ (there d∈)   = lookup-idRowᴹ d∈

  -- The generator y is a child of a join node of the tree.
  data JoinGen (y : Y) : CTerm Y → Type υ where
    join-here  : {h : CJand Y} {t : List (CJand Y)} → jgen y ∈ h ∷ t → JoinGen y (joinᶜ h t)
    join-inᴶ   : {h : CJand Y} {t : List (CJand Y)} {mh : CMand Y} {mt : List (CMand Y)}
               → jmeet mh mt ∈ h ∷ t → JoinGen y (meetᶜ mh mt) → JoinGen y (joinᶜ h t)
    join-inᴹ   : {h : CMand Y} {t : List (CMand Y)} {jh : CJand Y} {jt : List (CJand Y)}
               → mjoin jh jt ∈ h ∷ t → JoinGen y (joinᶜ jh jt) → JoinGen y (meetᶜ h t)

  -- The generator y is a child of a meet node of the tree.
  data MeetGen (y : Y) : CTerm Y → Type υ where
    meet-here  : {h : CMand Y} {t : List (CMand Y)} → mgen y ∈ h ∷ t → MeetGen y (meetᶜ h t)
    meet-inᴶ   : {h : CJand Y} {t : List (CJand Y)} {mh : CMand Y} {mt : List (CMand Y)}
               → jmeet mh mt ∈ h ∷ t → MeetGen y (meetᶜ mh mt) → MeetGen y (joinᶜ h t)
    meet-inᴹ   : {h : CMand Y} {t : List (CMand Y)} {jh : CJand Y} {jt : List (CJand Y)}
               → mjoin jh jt ∈ h ∷ t → MeetGen y (joinᶜ jh jt) → MeetGen y (meetᶜ h t)
```

A joinand `y` gives the identity pattern a cut labeled `y` whose cut child is
`y`, so `ℊ y` is a lower end of the box of `y` (`idPattern-joinGen`{.AgdaFunction});
dually a meetand makes `ℊ y` an upper end (`idPattern-meetGen`{.AgdaFunction}).
So the box of a generator that is both is the point `[y, y]`, and a family whose
truncation has the identity pattern sends `y` to `y`
(`point-box`{.AgdaFunction}).

```agda
  -- A joinand y puts ℊ y at the lower end of an interval of y.
  idPattern-joinGen : {y : Y} {D : CTerm Y} → JoinGen y D → Σ[ u ∈ LatTerm Y ] Bound (idPattern D) y (ℊ y) u
  idPattern-joinGen (join-here {h} {t} d∈) = ⋁ᴶ h t , cutᴶ d∈ (lookup-idRowᴶ {ds = h ∷ t} d∈)
  idPattern-joinGen (join-inᴶ {h} {t} d∈ g) =
    let (u , b) = idPattern-joinGen g in u , inᴶ d∈ (lookup-idRowᴶ {ds = h ∷ t} d∈) b
  idPattern-joinGen (join-inᴹ {h} {t} d∈ g) =
    let (u , b) = idPattern-joinGen g in u , inᴹ d∈ (lookup-idRowᴹ {ds = h ∷ t} d∈) b

  -- A meetand y puts ℊ y at the upper end of an interval of y.
  idPattern-meetGen : {y : Y} {D : CTerm Y} → MeetGen y D → Σ[ l ∈ LatTerm Y ] Bound (idPattern D) y l (ℊ y)
  idPattern-meetGen (meet-here {h} {t} d∈) = ⋀ᴹ h t , cutᴹ d∈ (lookup-idRowᴹ {ds = h ∷ t} d∈)
  idPattern-meetGen (meet-inᴶ {h} {t} d∈ g) =
    let (l , b) = idPattern-meetGen g in l , inᴶ d∈ (lookup-idRowᴶ {ds = h ∷ t} d∈) b
  idPattern-meetGen (meet-inᴹ {h} {t} d∈ g) =
    let (l , b) = idPattern-meetGen g in l , inᴹ d∈ (lookup-idRowᴹ {ds = h ∷ t} d∈) b

  -- Section 9.3: the box of a generator both joinand and meetand of the tree is a point.
  point-box : (τ : Sub Y Y) {C : CTerm Y} {D : CTerm Y} (r : Truncates._⊑_ τ C D) → patternOf τ r ≡ idPattern D
            → {y : Y} → JoinGen y D → MeetGen y D → τ y ≈ʷ ℊ y
  point-box τ r e {y} jg mg =
    let (u , b) = idPattern-joinGen jg
        (l , b′) = idPattern-meetGen mg
    in proj₂ (bound-sound τ r (subst (λ P → Bound P y l (ℊ y)) (sym e) b′))
     , proj₁ (bound-sound τ r (subst (λ P → Bound P y (ℊ y) u) (sym e) b))
```

The identity pattern is the pattern of the tree read inside a link as `FL(3)`:
the identity family truncates every canonical tree, through itself, with the
identity pattern (`self⊑`{.AgdaFunction}, `self-pattern`{.AgdaFunction}).  A
meet child is matched by itself, and a generator child `y` is a cut, its own
cut child, below `ℊ y`.  So inside a link the cut children are the generators
themselves, and the box of a generator that is both a joinand and a meetand of
the terms is a point (`point-box`{.AgdaFunction} with `self-pattern`).

```agda
module _ {Y : Type υ} where
  open Truncates (ℊ {X = Y})

  -- The truncation of a child of a join by itself, and of a child of a meet.
  Selfᴶ : CJand Y → Type υ
  Selfᴶ (jgen _)       = ⊤
  Selfᴶ (jmeet mh mt)  = jmeet mh mt ⊑ᴶ jmeet mh mt

  Selfᴹ : CMand Y → Type υ
  Selfᴹ (mgen _)       = ⊤
  Selfᴹ (mjoin jh jt)  = mjoin jh jt ⊑ᴹ mjoin jh jt

  self⊑      : (D : CTerm Y) → D ⊑ D
  selfᴶ      : (h : CJand Y) (t : List (CJand Y)) → joinᶜ h t ⊑ joinᶜ h t
  selfᴹ      : (h : CMand Y) (t : List (CMand Y)) → meetᶜ h t ⊑ meetᶜ h t
  selfChildᴶ : (d : CJand Y) → Selfᴶ d
  selfChildᴹ : (d : CMand Y) → Selfᴹ d
  selfRowᴶ   : (ds : List (CJand Y)) → All Selfᴶ ds
  selfRowᴹ   : (ds : List (CMand Y)) → All Selfᴹ ds

  -- A child of D, cut at itself if a generator, matched by itself otherwise.
  coverᴶ : {ys : List (CJand Y)} {d : CJand Y} → d ∈ ys → Selfᴶ d
         → Any (_⊑ᴶ d) ys ⊎ (Σ[ i ∈ Y ] jgen i ∈ ys × ⌊ d ⌋ᴶ ≤ʷ ℊ i)
  coverᴶ {d = jgen y}      d∈ _ = inj₂ (y , d∈ , ≤ʷ-refl)
  coverᴶ {d = jmeet _ _}   d∈ s = inj₁ (lose d∈ s)

  coverᴹ : {ys : List (CMand Y)} {d : CMand Y} → d ∈ ys → Selfᴹ d
         → Any (_⊑ᴹ d) ys ⊎ (Σ[ i ∈ Y ] mgen i ∈ ys × ℊ i ≤ʷ ⌊ d ⌋ᴹ)
  coverᴹ {d = mgen y}      d∈ _ = inj₂ (y , d∈ , ≤ʷ-refl)
  coverᴹ {d = mjoin _ _}   d∈ s = inj₁ (lose d∈ s)

  self⊑ (genᶜ y)           = gen⊑ (≈ʷ-refl′ (ℊ y))
    where
    ≈ʷ-refl′ : (u : LatTerm Y) → u ≈ʷ u
    ≈ʷ-refl′ u = ≤ʷ-refl , ≤ʷ-refl
  self⊑ (joinᶜ h t)        = selfᴶ h t
  self⊑ (meetᶜ h t)        = selfᴹ h t
  selfᴶ h t = join⊑ (≡→≈ʷ ([]-ℊ (⋁ᴶ h t))) (λ a∈ → lose a∈ (All.lookup (selfChildᴶ h ∷ selfRowᴶ t) a∈))
                    (λ d∈ → coverᴶ d∈ (All.lookup (selfChildᴶ h ∷ selfRowᴶ t) d∈))
  selfᴹ h t = meet⊑ (≡→≈ʷ ([]-ℊ (⋀ᴹ h t))) (λ a∈ → lose a∈ (All.lookup (selfChildᴹ h ∷ selfRowᴹ t) a∈))
                    (λ d∈ → coverᴹ d∈ (All.lookup (selfChildᴹ h ∷ selfRowᴹ t) d∈))
  selfChildᴶ (jgen _)       = tt
  selfChildᴶ (jmeet mh mt)  = jmeet⊑ (selfᴹ mh mt)
  selfChildᴹ (mgen _)       = tt
  selfChildᴹ (mjoin jh jt)  = mjoin⊑ (selfᴶ jh jt)
  selfRowᴶ []        = []
  selfRowᴶ (d ∷ ds)  = selfChildᴶ d ∷ selfRowᴶ ds
  selfRowᴹ []        = []
  selfRowᴹ (d ∷ ds)  = selfChildᴹ d ∷ selfRowᴹ ds
```

The pattern of the truncation by itself is the identity pattern, by the same
recursion: at each child the cover returns the label of a generator and the
pattern of the child's own truncation otherwise, whatever the position it is
found at (`anyᴶ-lose`{.AgdaFunction}).

```agda
  -- The pattern of a member found by its position is its own pattern.
  anyᴶ-lose : {ys : List (CJand Y)} {d : CJand Y} {c : CJand Y} (d∈ : c ∈ ys) (q : c ⊑ᴶ d)
            → anyᴶ ℊ (lose d∈ q) ≡ patternᴶ ℊ q
  anyᴶ-lose (here refl)  q = refl
  anyᴶ-lose (there d∈)   q = anyᴶ-lose d∈ q

  anyᴹ-lose : {ys : List (CMand Y)} {d : CMand Y} {c : CMand Y} (d∈ : c ∈ ys) (q : c ⊑ᴹ d)
            → anyᴹ ℊ (lose d∈ q) ≡ patternᴹ ℊ q
  anyᴹ-lose (here refl)  q = refl
  anyᴹ-lose (there d∈)   q = anyᴹ-lose d∈ q

  self-pattern   : (D : CTerm Y) → patternOf ℊ (self⊑ D) ≡ idPattern D
  self-patternᴶ  : (h : CJand Y) (t : List (CJand Y)) → patternOf ℊ (selfᴶ h t) ≡ idPatternᴶ h t
  self-patternᴹ  : (h : CMand Y) (t : List (CMand Y)) → patternOf ℊ (selfᴹ h t) ≡ idPatternᴹ h t
  self-childᴶ    : {ys : List (CJand Y)} (d : CJand Y) (d∈ : d ∈ ys)
                 → childᴶ ℊ (coverᴶ d∈ (selfChildᴶ d)) ≡ idChildᴶ d
  self-childᴹ    : {ys : List (CMand Y)} (d : CMand Y) (d∈ : d ∈ ys)
                 → childᴹ ℊ (coverᴹ d∈ (selfChildᴹ d)) ≡ idChildᴹ d
  self-rowᴶ      : {ys : List (CJand Y)} (ds : List (CJand Y)) (pre : ∀ {d} → d ∈ ds → d ∈ ys)
                 → collect (λ d∈ → childᴶ ℊ (coverᴶ (pre d∈) (All.lookup (selfRowᴶ ds) d∈))) ≡ idRowᴶ ds
  self-rowᴹ      : {ys : List (CMand Y)} (ds : List (CMand Y)) (pre : ∀ {d} → d ∈ ds → d ∈ ys)
                 → collect (λ d∈ → childᴹ ℊ (coverᴹ (pre d∈) (All.lookup (selfRowᴹ ds) d∈))) ≡ idRowᴹ ds

  self-pattern (genᶜ _)     = refl
  self-pattern (joinᶜ h t)  = self-patternᴶ h t
  self-pattern (meetᶜ h t)  = self-patternᴹ h t
  self-patternᴶ h t = cong pjoin (cong₂ _∷_ (self-childᴶ h (here refl)) (self-rowᴶ t (λ d∈ → there d∈)))
  self-patternᴹ h t = cong pmeet (cong₂ _∷_ (self-childᴹ h (here refl)) (self-rowᴹ t (λ d∈ → there d∈)))
  self-childᴶ (jgen _)       d∈ = refl
  self-childᴶ (jmeet mh mt)  d∈ =
    cong inj₁ (trans (anyᴶ-lose d∈ (jmeet⊑ (selfᴹ mh mt))) (cong pjmeet (self-patternᴹ mh mt)))
  self-childᴹ (mgen _)       d∈ = refl
  self-childᴹ (mjoin jh jt)  d∈ =
    cong inj₁ (trans (anyᴹ-lose d∈ (mjoin⊑ (selfᴶ jh jt))) (cong pmjoin (self-patternᴶ jh jt)))
  self-rowᴶ []        pre = refl
  self-rowᴶ (d ∷ ds)  pre = cong₂ _∷_ (self-childᴶ d (pre (here refl))) (self-rowᴶ ds (λ d∈ → pre (there d∈)))
  self-rowᴹ []        pre = refl
  self-rowᴹ (d ∷ ds)  pre = cong₂ _∷_ (self-childᴹ d (pre (here refl))) (self-rowᴹ ds (λ d∈ → pre (there d∈)))

  -- Section 9.3, inside FL(3): a family with the identity link's pattern fixes a generator
  -- that is both a joinand and a meetand of the tree.
  point-box-in-link : (τ : Sub Y Y) {C D : CTerm Y} (r : Truncates._⊑_ τ C D)
                    → patternOf τ r ≡ patternOf ℊ (self⊑ D)
                    → {y : Y} → JoinGen y D → MeetGen y D → τ y ≈ʷ ℊ y
  point-box-in-link τ {D = D} r e = point-box τ r (trans e (self-pattern D))
```


--------------------------------------

[DeansProblem.Truncation.Pattern]: DeansProblem.Truncation.Pattern.html
[DeansProblem.Truncation]: DeansProblem.Truncation.html
