---
layout: default
file: "src/DeansProblem/FixedGenerator.lagda.md"
title: "DeansProblem.FixedGenerator module"
date: "2026-10-14"
author: "the agda-lattices development team"
---

### A self-embedding of FL(3) with a fixed free triple fixes a generator

This is the [DeansProblem.FixedGenerator][] module of the [agda-lattices][] library.

[the paper]: https://arxiv.org/abs/YYMM.NNNNN

Let `Θ` be a proper self-embedding of `FL(3)` whose fixed sublattice contains a
copy of `FL(3)`, the first link of any coherent chain of length three
([DeansProblem.Coherent.Finite][]).  This module proves that `Θ` fixes one of
the three generators (`fixes-generator`{.AgdaFunction}), which is Theorem E of
[the paper][], Section 7.  The argument has four steps.

1.  **The descent lands on a join or meet of two generators.**  The descent of
    [DeansProblem.Fixed][] takes a fixed point of complexity at least two to
    an element of complexity one fixed by a positive power of `Θ`; kept with
    the parent of its last step (`descent-pair`{.AgdaFunction}), that element
    is a canonical joinand or meetand of an element of complexity two, so it
    is neither the top `x ∨ y ∨ z` nor the bottom `x ∧ y ∧ z` of `FL(3)`
    (`top-not-child`{.AgdaFunction}, `bot-not-child`{.AgdaFunction}): a
    canonical joinand lies below its element, a canonical meetand above, and
    the canonical joinands of an element form an antichain.
2.  **An inflationary power.**  If a power `Ψ` of `Θ` fixes `x ∨ y`, then
    `Ψ` or `Ψ²` is inflationary ([DeansProblem.Inflationary][]:
    `fixes-join`{.AgdaFunction}, `fixes-join-third`{.AgdaFunction}); the meet
    case is the join case for the dual embedding.
3.  **A strictly inflationary embedding fixes at most eleven elements**
    (`strict-fixed-in-T₁₁`{.AgdaFunction}).  Let `Ψ` be inflationary and move
    every generator.  Every node of the canonical tree of a fixed point is
    fixed, and a fixed canonical meet has no generator meetand
    (`meetand-gen-fixed`{.AgdaFunction}).  So a fixed canonical join is a
    join of generators and fixed meets, and a fixed canonical meet a meet of
    fixed joins; by induction on complexity every fixed point is, up to
    equality, one of the eleven elements `x ∨ y`, `x ∨ z`, `y ∨ z`,
    `x ∨ y ∨ z`, the three meets of two of the pairwise joins, their meet
    `⊥ᴮ`, and `x ∨ ⊥ᴮ`, `y ∨ ⊥ᴮ`, `z ∨ ⊥ᴮ` (`T₁₁`{.AgdaFunction}): the
    fourteen-element list `T₁₄`{.AgdaFunction} of those and the generators is
    closed under joins and `T₁₁` under meets, each a decision of Whitman's
    procedure on small terms (`T₁₄-∨`{.AgdaFunction},
    `T₁₁-∧`{.AgdaFunction}).  Every member of `T₁₁` has complexity at most
    three (`strict-fixed-complexity`{.AgdaFunction}).  Freese's own
    self-embedding `x ↦ x ∨ (y ∧ z)`, cyclically, fixes exactly these eleven.
4.  **Hence a fixed generator.**  A fixed free triple `τ` gives fixed points
    of every complexity: an embedding never lowers complexity
    ([Lattices.Free.Complexity][]), so the element named by a term of
    complexity four in the triple has complexity at least four.  The
    inflationary power of step 2 cannot move every generator, by step 3; the
    generator it fixes is fixed by `Θ` itself
    (`power-fixes→fixes`{.AgdaFunction}).

<!--
```agda
{-# OPTIONS --without-K --exact-split --safe #-}

module DeansProblem.FixedGenerator where

open import Agda.Primitive  using () renaming ( Set to Type )

-- Imports from the Agda Standard Library ---------------------------------------
open import Data.Empty                             using ( ⊥ ; ⊥-elim )
open import Data.Fin.Base                          using ( Fin )
open import Data.Fin.Patterns                      using ( 0F ; 1F ; 2F )
open import Data.Fin.Properties                    using ( _≟_ )
open import Data.List.Base                         using ( List ; [] ; _∷_ ; map ; allFin ; length )
open import Data.List.Properties                   using ( map-∘ ; map-cong )
open import Data.List.Membership.Propositional     using ( _∈_ ; find ; lose )
open import Data.List.Membership.Propositional.Properties
                                                   using ( ∈-allFin ; ∈-map⁺ ; ∈-map⁻ )
open import Data.List.Relation.Unary.All           using ( All ; [] ; _∷_ ; all? ; lookup ; tabulate )
open import Data.List.Relation.Unary.AllPairs      using ( AllPairs ; allPairs? )
open import Data.List.Relation.Unary.Any           using ( Any ; here ; there ; any? )
open import Data.List.Relation.Unary.Any.Properties
                                                   using ( map⁻ )
open import Data.Nat.Base                          using ( ℕ ; zero ; suc ; _+_ ; _*_ ; _≤_ ; s≤s )
open import Data.Nat.Properties                    using ( ≤-refl ; ≤-trans ; _≤?_ ; ≤-pred ; m≤n⇒∃[o]m+o≡n )
open import Data.Product                           using ( Σ-syntax ; _×_ ; _,_ ; proj₁ ; proj₂ )
open import Data.Sum.Base                          using ( _⊎_ ; inj₁ ; inj₂ ; [_,_]′ )
open import Function                               using ( _⇔_ ; mk⇔ )
open import Relation.Binary.PropositionalEquality  using ( _≡_ ; refl ; sym ; trans ; cong ; subst ; subst₂ )
open import Relation.Nullary                       using ( ¬_ )
open import Relation.Nullary.Decidable.Core        using ( Dec ; yes ; no ; from-yes ; map′ ; ¬? ; _×-dec_ )

import Data.List.Relation.Unary.Any as Any

-- Imports from the Agda Universal Algebra Library ------------------------------
open import Lattices.Free.Canonical.Algorithm      using ( module Canonicalization )
open import Lattices.Free.Canonical.Basic
  using  ( CTerm ; genᶜ ; joinᶜ ; meetᶜ ; CJand ; jgen ; jmeet ; CMand ; mgen ; mjoin ; ⌊_⌋ ; ⌊_⌋ᴶ ; ⌊_⌋ᴹ
         ; ⋁ᴶ≡⋁⁺ ; ⋀ᴹ≡⋀⁺ ; ≈ʷ-refl ; ≈ʷ-sym ; ≈ʷ-trans ; ∨̇-cong ; ∧̇-cong ; IsCanonical ; cjoin
         ; cmeet ; IsCanonicalJ ; cjgen ; cjmeet ; IsCanonicalM ; cmgen ; cmjoin ; ⋁⁺ ; ⋀⁺ ; asListJ
         ; asListM ; joinandsOf ; meetandsOf )
open import Lattices.Free.Canonical.Joinands       using ( canonicalJoinands ; canonicalMeetands
                                                         ; canonicalJoinands-upper ; canonicalJoinands-least
                                                         ; canonicalMeetands-lower ; canonicalMeetands-greatest
                                                         ; joinands-≈ˡ ; meetands-≈ˡ ; Any-resp-≈ˡ ; ≈ˡ-sym )
open import Lattices.Free.Canonical.Recognition    using ( module Recognize )
open import Lattices.Free.Canonical.Uniqueness     using ( gen≉join ; gen≉meet ; antichain-≤ )
open import DeansProblem.Chain                     using ( iter ; []-iter-suc )
open import Lattices.Free.Complexity               using ( complexity ; complexity-resp ; complexity-mono ; complexityᴶ
                                                         ; complexityᴹ ; depth ; depthΣJ-upper ; depthΣM-upper
                                                         ; module Bounded )
open import Lattices.Free.Embedding                using ( canonicalJoinands-antichain
                                                         ; canonicalMeetands-antichain )
open import DeansProblem.Fixed                     using ( fixed→image ; positive-not-gen ; descent-parent
                                                         ; joinand-periodic ; meetand-periodic ; iter-free
                                                         ; []-iter-* )
open import Lattices.Free.Duality                  using ( dual ; dual-involutive ; dual-cong ; dual-reflects
                                                         ; dual-reflects-≈ ; dual-antitone )
open import Lattices.Free.Generation               using ( FreelyGenerates ; JoinCondition ; MeetCondition
                                                         ; _≤⋁_ ; _⋀≤_
                                                         ; freelyGenerates→injective
                                                         ; MeetCondition→JoinConditionᵈ )
open import DeansProblem.Inflationary              using ( Inflationary ; Deflationary ; fixes-join
                                                         ; fixes-join-third ; fixes-join-swapped
                                                         ; iter-two ; power-fixes→fixes ; Node ; root
                                                         ; joinand ; meetand ; NoGeneratorMeetand ; S-node
                                                         ; strict-fixed-no-generator-meetand )
open import DeansProblem.Partition                 using ( other ; other' ; cover₃ )
open import Lattices.Free.Substitution             using ( Sub ; _[_] ; []-ℊ ; []-⨟ ; []-cong
                                                         ; []-congʳ ; dual-[] )
open import Lattices.Free.Term                     using ( LatTerm ; ℊ ; _∧̇_ ; _∨̇_ )
open import Lattices.Free.Whitman                  using ( _≤ʷ_ ; _≈ʷ_ ; ≤ʷ-refl ; ≤ʷ-trans ; ∨≤ ; ≤∧ ; ∧ˡ≤ ; ∧ʳ≤
                                                         ; ℊ≤ℊ ; ℊ≤∨ˡ ; ℊ≤∨ʳ ; ≤∨ˡ ; module Decision )

open Decision (_≟_ {3}) using ( _≈ʷ?_ )
open Recognize (_≟_ {3}) using ( isCanonical? )

private
  open Canonicalization (_≟_ {3}) using ( canonical ; canonical-sound ; canonical-isCanonical )

  -- An equation of terms, read as an equality in the free lattice.
  ≡→≈ʷ : {s t : LatTerm (Fin 3)} → s ≡ t → s ≈ʷ t
  ≡→≈ʷ {s = s} e = subst (s ≈ʷ_) e ≈ʷ-refl

  κ : LatTerm (Fin 3) → ℕ
  κ = complexity (_≟_ {3})

  CJ CM : LatTerm (Fin 3) → List (LatTerm (Fin 3))
  CJ = canonicalJoinands (_≟_ {3})
  CM = canonicalMeetands (_≟_ {3})
```
-->

#### The fourteen elements

```agda
-- The generators, their joins, the meets of two or three pairwise joins, and the three joins with ⊥ᴮ.
private
  x y z : LatTerm (Fin 3)
  x = ℊ 0F
  y = ℊ 1F
  z = ℊ 2F

  xy xz yz top : LatTerm (Fin 3)
  xy = x ∨̇ y
  xz = x ∨̇ z
  yz = y ∨̇ z
  top = x ∨̇ (y ∨̇ z)

  A B C ⊥ᴮ bot : LatTerm (Fin 3)
  A = xy ∧̇ xz
  B = xy ∧̇ yz
  C = xz ∧̇ yz
  ⊥ᴮ = xy ∧̇ (xz ∧̇ yz)
  bot = x ∧̇ (y ∧̇ z)

T₁₁ T₁₄ : List (LatTerm (Fin 3))
T₁₁ = xy ∷ xz ∷ yz ∷ top ∷ A ∷ B ∷ C ∷ ⊥ᴮ ∷ (x ∨̇ ⊥ᴮ) ∷ (y ∨̇ ⊥ᴮ) ∷ (z ∨̇ ⊥ᴮ) ∷ []
T₁₄ = x ∷ y ∷ z ∷ T₁₁
```

`T₁₄` is closed under joins and `T₁₁` under meets, up to equality, by
Whitman's procedure: for each of the 196 ordered pairs of members of `T₁₄`, a
search of `T₁₄` for a member equal to their join, and likewise for the 121
pairs of `T₁₁` and their meets; so the join of a
nonempty list of members of `T₁₄` is a member, and the meet of a nonempty list
of members of `T₁₁` is a member.  Every member of `T₁₁` has complexity at most
three.

```agda
-- Closure under joins and meets, decided.
T₁₄-∨ : All (λ a → All (λ b → Any ((a ∨̇ b) ≈ʷ_) T₁₄) T₁₄) T₁₄
T₁₄-∨ = from-yes (all? (λ a → all? (λ b → any? (λ t → (a ∨̇ b) ≈ʷ? t) T₁₄) T₁₄) T₁₄)

T₁₁-∧ : All (λ a → All (λ b → Any ((a ∧̇ b) ≈ʷ_) T₁₁) T₁₁) T₁₁
T₁₁-∧ = from-yes (all? (λ a → all? (λ b → any? (λ t → (a ∧̇ b) ≈ʷ? t) T₁₁) T₁₁) T₁₁)

-- Up to equality.
∨-closed : {a b : LatTerm (Fin 3)} → Any (a ≈ʷ_) T₁₄ → Any (b ≈ʷ_) T₁₄ → Any ((a ∨̇ b) ≈ʷ_) T₁₄
∨-closed pa pb =
  let (a′ , a′∈ , a≈) = find pa
      (b′ , b′∈ , b≈) = find pb
  in Any.map (≈ʷ-trans (∨̇-cong a≈ b≈)) (lookup (lookup T₁₄-∨ a′∈) b′∈)

∧-closed : {a b : LatTerm (Fin 3)} → Any (a ≈ʷ_) T₁₁ → Any (b ≈ʷ_) T₁₁ → Any ((a ∧̇ b) ≈ʷ_) T₁₁
∧-closed pa pb =
  let (a′ , a′∈ , a≈) = find pa
      (b′ , b′∈ , b≈) = find pb
  in Any.map (≈ʷ-trans (∧̇-cong a≈ b≈)) (lookup (lookup T₁₁-∧ a′∈) b′∈)

-- The join of a nonempty list of members of T₁₄ is a member; dually for T₁₁.
⋁⁺-closed : (u : LatTerm (Fin 3)) (us : List (LatTerm (Fin 3))) → Any (u ≈ʷ_) T₁₄
          → All (λ w → Any (w ≈ʷ_) T₁₄) us → Any (⋁⁺ u us ≈ʷ_) T₁₄
⋁⁺-closed u []        pu _            = pu
⋁⁺-closed u (w ∷ ws)  pu (pw ∷ pws)  = ∨-closed pu (⋁⁺-closed w ws pw pws)

⋀⁺-closed : (u : LatTerm (Fin 3)) (us : List (LatTerm (Fin 3))) → Any (u ≈ʷ_) T₁₁
          → All (λ w → Any (w ≈ʷ_) T₁₁) us → Any (⋀⁺ u us ≈ʷ_) T₁₁
⋀⁺-closed u []        pu _            = pu
⋀⁺-closed u (w ∷ ws)  pu (pw ∷ pws)  = ∧-closed pu (⋀⁺-closed w ws pw pws)

-- Generators are members of T₁₄; a member of T₁₄ that is no generator is a member of T₁₁.
gen∈T₁₄ : ∀ g → Any (ℊ g ≈ʷ_) T₁₄
gen∈T₁₄ 0F = here ≈ʷ-refl
gen∈T₁₄ 1F = there (here ≈ʷ-refl)
gen∈T₁₄ 2F = there (there (here ≈ʷ-refl))

T₁₁→T₁₄ : {w : LatTerm (Fin 3)} → Any (w ≈ʷ_) T₁₁ → Any (w ≈ʷ_) T₁₄
T₁₁→T₁₄ p = there (there (there p))

T₁₄→T₁₁ : {w : LatTerm (Fin 3)} → (∀ g → ¬ (w ≈ʷ ℊ g)) → Any (w ≈ʷ_) T₁₄ → Any (w ≈ʷ_) T₁₁
T₁₄→T₁₁ ng (here p)                          = ⊥-elim (ng 0F p)
T₁₄→T₁₁ ng (there (here p))                  = ⊥-elim (ng 1F p)
T₁₄→T₁₁ ng (there (there (here p)))          = ⊥-elim (ng 2F p)
T₁₄→T₁₁ ng (there (there (there p)))         = p

-- Every member of T₁₁ has complexity at most three.
T₁₁-complexity : All (λ t → κ t ≤ 3) T₁₁
T₁₁-complexity = from-yes (all? (λ t → κ t ≤? 3) T₁₁)

-- Exactly: 1, 1, 1, 1, 2, 2, 2, 2, 3, 3, 3.
T₁₁-complexities : map κ T₁₁ ≡ 1 ∷ 1 ∷ 1 ∷ 1 ∷ 2 ∷ 2 ∷ 2 ∷ 2 ∷ 3 ∷ 3 ∷ 3 ∷ []
T₁₁-complexities = refl

-- The fourteen are distinct elements of FL(3).
T₁₄-distinct : AllPairs (λ a b → ¬ (a ≈ʷ b)) T₁₄
T₁₄-distinct = from-yes (allPairs? (λ a b → ¬? (a ≈ʷ? b)) T₁₄)
```

#### Proposition 7.2: the fourteen elements are the set S

The set `S` of Section 7.3 of [the paper][] is
`NoGeneratorMeetand`{.AgdaFunction} of [DeansProblem.Inflationary][]: no node
of the canonical tree of the element has a generator among the meetands of a
meet node.  Proposition 7.2 says `S = T₁₄` (`S⇔T₁₄`{.AgdaFunction}), and both
inclusions follow the paper's proof.

`T₁₄ ⊆ S`.  The fourteen terms, written as canonical terms
(`T₁₄ᶜ`{.AgdaFunction}, which name them exactly, `T₁₄ᶜ-names`{.AgdaFunction}),
are canonical and have no generator meetand (`T₁₄ᶜ-canonical`{.AgdaFunction}),
decided by `isCanonical?`{.AgdaFunction} of
[Lattices.Free.Canonical.Recognition][] and by `noGenᶜ?`{.AgdaFunction}, which
decides the property on canonical terms (`NoGenᶜ`{.AgdaDatatype}).  A canonical
term with the property names an element of `S` (`rep→S`{.AgdaFunction}): by
Theorem 1.17, in its list form `joinands-≈ˡ`{.AgdaFunction} and
`meetands-≈ˡ`{.AgdaFunction} of [Lattices.Free.Canonical.Joinands][], the
canonical joinands and meetands of the element are those of the term up to
order and equality, so every node of the tree is again named by such a term
(`rep-node`{.AgdaFunction}), and no such term has a generator among its
meetands unless it is a generator (`rep-no-gen`{.AgdaFunction}).

`S ⊆ T₁₄`, by induction on complexity (`in-T₁₄`{.AgdaFunction}).  A generator
is in `T₁₄`.  A canonical join is the join of its joinands, each a generator
or a meet node of the tree, in `S` (`S-node`{.AgdaFunction}) and of smaller
complexity, so in `T₁₄`; and `T₁₄` is closed under joins.  A canonical meet in
`S` has no generator meetand, so its meetands are joins, nodes of the tree in
`S` of smaller complexity, in `T₁₄` and no generators, so in `T₁₁`; and `T₁₁`
is closed under meets.

```agda
-- No generator among the meetands of any meet node, read on a canonical term.
data NoGenᶜ : CTerm (Fin 3) → Type
data NoGenᴶ : CJand (Fin 3) → Type
data NoGenᴹ : CMand (Fin 3) → Type

data NoGenᶜ where
  ngen   : ∀ {g} → NoGenᶜ (genᶜ g)
  njoin  : ∀ {h t} → All NoGenᴶ (h ∷ t) → NoGenᶜ (joinᶜ h t)
  nmeet  : ∀ {h t} → All NoGenᴹ (h ∷ t) → NoGenᶜ (meetᶜ h t)

data NoGenᴶ where
  njgen   : ∀ {g} → NoGenᴶ (jgen g)
  njmeet  : ∀ {h t} → All NoGenᴹ (h ∷ t) → NoGenᴶ (jmeet h t)

-- A meetand must be a join.
data NoGenᴹ where
  nmjoin  : ∀ {h t} → All NoGenᴶ (h ∷ t) → NoGenᴹ (mjoin h t)

-- The property is decidable, by recursion on subterms.
noGenᶜ?     : (C : CTerm (Fin 3)) → Dec (NoGenᶜ C)
noGenᴶ?     : (a : CJand (Fin 3)) → Dec (NoGenᴶ a)
noGenᴹ?     : (a : CMand (Fin 3)) → Dec (NoGenᴹ a)
allNoGenᴶ?  : (as : List (CJand (Fin 3))) → Dec (All NoGenᴶ as)
allNoGenᴹ?  : (as : List (CMand (Fin 3))) → Dec (All NoGenᴹ as)

noGenᶜ? (genᶜ g)     = yes ngen
noGenᶜ? (joinᶜ h t)  = map′ (λ (p , ps) → njoin (p ∷ ps)) (λ { (njoin (p ∷ ps)) → p , ps })
                            (noGenᴶ? h ×-dec allNoGenᴶ? t)
noGenᶜ? (meetᶜ h t)  = map′ (λ (p , ps) → nmeet (p ∷ ps)) (λ { (nmeet (p ∷ ps)) → p , ps })
                            (noGenᴹ? h ×-dec allNoGenᴹ? t)

noGenᴶ? (jgen g)     = yes njgen
noGenᴶ? (jmeet h t)  = map′ (λ (p , ps) → njmeet (p ∷ ps)) (λ { (njmeet (p ∷ ps)) → p , ps })
                            (noGenᴹ? h ×-dec allNoGenᴹ? t)

noGenᴹ? (mgen g)     = no (λ ())
noGenᴹ? (mjoin h t)  = map′ (λ (p , ps) → nmjoin (p ∷ ps)) (λ { (nmjoin (p ∷ ps)) → p , ps })
                            (noGenᴶ? h ×-dec allNoGenᴶ? t)

allNoGenᴶ? []        = yes []
allNoGenᴶ? (a ∷ as)  = map′ (λ (p , ps) → p ∷ ps) (λ { (p ∷ ps) → p , ps }) (noGenᴶ? a ×-dec allNoGenᴶ? as)

allNoGenᴹ? []        = yes []
allNoGenᴹ? (a ∷ as)  = map′ (λ (p , ps) → p ∷ ps) (λ { (p ∷ ps) → p , ps }) (noGenᴹ? a ×-dec allNoGenᴹ? as)

-- An element named by a canonical term with no generator meetand.
Rep : LatTerm (Fin 3) → Type
Rep u = Σ[ D ∈ CTerm (Fin 3) ] IsCanonical D × NoGenᶜ D × ⌊ D ⌋ ≈ʷ u

private
  -- A member of a list is a member up to equality.
  ∈→Any≈ : {c : LatTerm (Fin 3)} {cs : List (LatTerm (Fin 3))} → c ∈ cs → Any (c ≈ʷ_) cs
  ∈→Any≈ = Any.map (λ { refl → ≈ʷ-refl })

  -- A non-generator joinand of such a term is named by such a term.
  joinand-rep : (D : CTerm (Fin 3)) → IsCanonical D → NoGenᶜ D → {a : CJand (Fin 3)}
              → a ∈ asListJ (joinandsOf D) → (∀ v → ¬ (⌊ a ⌋ᴶ ≈ʷ ℊ v)) → Rep ⌊ a ⌋ᴶ
  joinand-rep (genᶜ g)     _  _  (here refl)  ng  = ⊥-elim (ng g ≈ʷ-refl)
  joinand-rep (joinᶜ h t)  (cjoin _ cs _ _) (njoin ns) a∈ ng = child (lookup cs a∈) (lookup ns a∈) ng
    where
    child : {a : CJand (Fin 3)} → IsCanonicalJ a → NoGenᴶ a → (∀ v → ¬ (⌊ a ⌋ᴶ ≈ʷ ℊ v)) → Rep ⌊ a ⌋ᴶ
    child (cjgen {x = g})  _            ng′  = ⊥-elim (ng′ g ≈ʷ-refl)
    child (cjmeet ic)      (njmeet ms)  _    = meetᶜ _ _ , ic , nmeet ms , ≈ʷ-refl
  joinand-rep (meetᶜ h t)  cD nD (here refl)  _   = meetᶜ h t , cD , nD , ≈ʷ-refl

  -- A non-generator meetand of such a term is named by such a term.
  meetand-rep : (D : CTerm (Fin 3)) → IsCanonical D → NoGenᶜ D → {a : CMand (Fin 3)}
              → a ∈ asListM (meetandsOf D) → (∀ v → ¬ (⌊ a ⌋ᴹ ≈ʷ ℊ v)) → Rep ⌊ a ⌋ᴹ
  meetand-rep (genᶜ g)     _  _  (here refl)  ng  = ⊥-elim (ng g ≈ʷ-refl)
  meetand-rep (joinᶜ h t)  cD nD (here refl)  _   = joinᶜ h t , cD , nD , ≈ʷ-refl
  meetand-rep (meetᶜ h t)  (cmeet _ cs _ _) (nmeet ns) a∈ _ = child (lookup cs a∈) (lookup ns a∈)
    where
    child : {a : CMand (Fin 3)} → IsCanonicalM a → NoGenᴹ a → Rep ⌊ a ⌋ᴹ
    child cmgen        ()
    child (cmjoin ic)  (nmjoin js)  = joinᶜ _ _ , ic , njoin js , ≈ʷ-refl

  -- No meetand of such a term is a generator, unless the term is one.
  gen-meetand : {g : Fin 3} (D : CTerm (Fin 3)) → IsCanonical D → NoGenᶜ D → {a : CMand (Fin 3)}
              → a ∈ asListM (meetandsOf D) → ℊ g ≈ʷ ⌊ a ⌋ᴹ → (∀ v → ¬ (⌊ D ⌋ ≈ʷ ℊ v)) → ⊥
  gen-meetand (genᶜ x)     _  _  _            _  ng  = ng x ≈ʷ-refl
  gen-meetand (joinᶜ h t)  cD _  (here refl)  e  _   = gen≉join cD e
  gen-meetand {g} (meetᶜ h t) (cmeet _ cs _ _) (nmeet ns) a∈ e _ = child (lookup cs a∈) (lookup ns a∈) e
    where
    child : {a : CMand (Fin 3)} → IsCanonicalM a → NoGenᴹ a → ℊ g ≈ʷ ⌊ a ⌋ᴹ → ⊥
    child cmgen        ()
    child (cmjoin ic)  _   e′ = gen≉join ic e′

  -- A non-generator canonical joinand of an element named by such a term is named by one.
  rep-joinand : {u c : LatTerm (Fin 3)} → Rep u → c ∈ CJ u → (∀ v → ¬ (c ≈ʷ ℊ v)) → Rep c
  rep-joinand {c = c} (D , cD , nD , e) c∈ ng =
    let (c′ , c′∈ , c≈c′) = find (Any-resp-≈ˡ (≈ˡ-sym (joinands-≈ˡ (_≟_ {3}) D cD e)) (∈→Any≈ c∈))
        (a , a∈ , c′≡) = ∈-map⁻ ⌊_⌋ᴶ c′∈
        c≈a : c ≈ʷ ⌊ a ⌋ᴶ
        c≈a = subst (c ≈ʷ_) c′≡ c≈c′
        (D′ , cD′ , nD′ , e′) = joinand-rep D cD nD a∈ (λ v a≈v → ng v (≈ʷ-trans c≈a a≈v))
    in D′ , cD′ , nD′ , ≈ʷ-trans e′ (≈ʷ-sym c≈a)

  -- Likewise for a meetand.
  rep-meetand : {u c : LatTerm (Fin 3)} → Rep u → c ∈ CM u → (∀ v → ¬ (c ≈ʷ ℊ v)) → Rep c
  rep-meetand {c = c} (D , cD , nD , e) c∈ ng =
    let (c′ , c′∈ , c≈c′) = find (Any-resp-≈ˡ (≈ˡ-sym (meetands-≈ˡ (_≟_ {3}) D cD e)) (∈→Any≈ c∈))
        (a , a∈ , c′≡) = ∈-map⁻ ⌊_⌋ᴹ c′∈
        c≈a : c ≈ʷ ⌊ a ⌋ᴹ
        c≈a = subst (c ≈ʷ_) c′≡ c≈c′
        (D′ , cD′ , nD′ , e′) = meetand-rep D cD nD a∈ (λ v a≈v → ng v (≈ʷ-trans c≈a a≈v))
    in D′ , cD′ , nD′ , ≈ʷ-trans e′ (≈ʷ-sym c≈a)

-- Every node of the tree of an element named by such a term is named by one.
rep-node : {w u : LatTerm (Fin 3)} → Rep w → Node w u → Rep u
rep-node r root                = r
rep-node r (joinand nd c∈ ng)  = rep-joinand (rep-node r nd) c∈ ng
rep-node r (meetand nd c∈ ng)  = rep-meetand (rep-node r nd) c∈ ng

-- A non-generator element named by such a term has no generator among its canonical meetands.
rep-no-gen : {u : LatTerm (Fin 3)} → Rep u → (∀ v → ¬ (u ≈ʷ ℊ v)) → ∀ {g} → ¬ (ℊ g ∈ CM u)
rep-no-gen (D , cD , nD , e) ng {g} g∈ =
  let (c′ , c′∈ , g≈c′) = find (Any-resp-≈ˡ (≈ˡ-sym (meetands-≈ˡ (_≟_ {3}) D cD e)) (∈→Any≈ g∈))
      (a , a∈ , c′≡) = ∈-map⁻ ⌊_⌋ᴹ c′∈
  in gen-meetand D cD nD a∈ (subst (ℊ g ≈ʷ_) c′≡ g≈c′) (λ v D≈v → ng v (≈ʷ-trans (≈ʷ-sym e) D≈v))

-- So such an element is in S.
rep→S : {w : LatTerm (Fin 3)} → Rep w → NoGeneratorMeetand w
rep→S r nd ng = rep-no-gen (rep-node r nd) ng
```

The fourteen terms as canonical terms, and the inclusion `T₁₄ ⊆ S`.

```agda
private
  XY XZ YZ : CMand (Fin 3)
  XY = mjoin (jgen 0F) (jgen 1F ∷ [])
  XZ = mjoin (jgen 0F) (jgen 2F ∷ [])
  YZ = mjoin (jgen 1F) (jgen 2F ∷ [])

-- The fourteen, as canonical terms.
T₁₄ᶜ : List (CTerm (Fin 3))
T₁₄ᶜ = genᶜ 0F ∷ genᶜ 1F ∷ genᶜ 2F
     ∷ joinᶜ (jgen 0F) (jgen 1F ∷ []) ∷ joinᶜ (jgen 0F) (jgen 2F ∷ []) ∷ joinᶜ (jgen 1F) (jgen 2F ∷ [])
     ∷ joinᶜ (jgen 0F) (jgen 1F ∷ jgen 2F ∷ [])
     ∷ meetᶜ XY (XZ ∷ []) ∷ meetᶜ XY (YZ ∷ []) ∷ meetᶜ XZ (YZ ∷ []) ∷ meetᶜ XY (XZ ∷ YZ ∷ [])
     ∷ joinᶜ (jgen 0F) (jmeet XY (XZ ∷ YZ ∷ []) ∷ []) ∷ joinᶜ (jgen 1F) (jmeet XY (XZ ∷ YZ ∷ []) ∷ [])
     ∷ joinᶜ (jgen 2F) (jmeet XY (XZ ∷ YZ ∷ []) ∷ [])
     ∷ []

-- They name the fourteen terms.
T₁₄ᶜ-names : map ⌊_⌋ T₁₄ᶜ ≡ T₁₄
T₁₄ᶜ-names = refl

-- They are canonical, with no generator meetand.
T₁₄ᶜ-canonical : All (λ C → IsCanonical C × NoGenᶜ C) T₁₄ᶜ
T₁₄ᶜ-canonical = from-yes (all? (λ C → isCanonical? C ×-dec noGenᶜ? C) T₁₄ᶜ)

-- T₁₄ ⊆ S, up to equality.
T₁₄→S : {w : LatTerm (Fin 3)} → Any (w ≈ʷ_) T₁₄ → NoGeneratorMeetand w
T₁₄→S {w} p =
  let (C , C∈ , w≈C) = find (map⁻ {f = ⌊_⌋} {xs = T₁₄ᶜ} (subst (Any (w ≈ʷ_)) (sym T₁₄ᶜ-names) p))
      (cC , nC) = lookup T₁₄ᶜ-canonical C∈
  in rep→S (C , cC , nC , ≈ʷ-sym w≈C)
```

The converse, by induction on a bound for the complexity, through the shape of
the canonical form `C` (`byShapeˢ`{.AgdaFunction}, which carries the equation
`canonical w ≡ C` so that no `with` is needed).

```agda
private
  -- A successor is not below zero.
  suc≰0 : ∀ {m} → suc m ≤ 0 → ⊥
  suc≰0 ()

-- S ⊆ T₁₄, by induction on a bound for the complexity.
in-T₁₄ : (n : ℕ) (w : LatTerm (Fin 3)) → κ w ≤ n → NoGeneratorMeetand w → Any (w ≈ʷ_) T₁₄
byShapeˢ : (n : ℕ) (w : LatTerm (Fin 3)) (C : CTerm (Fin 3)) → canonical w ≡ C → IsCanonical C
         → ⌊ C ⌋ ≈ʷ w → κ w ≤ n → NoGeneratorMeetand w → Any (w ≈ʷ_) T₁₄

in-T₁₄ n w b s = byShapeˢ n w (canonical w) refl (canonical-isCanonical w) (canonical-sound w) b s

byShapeˢ n        w (genᶜ g)     eq _  e b s = Any.map (≈ʷ-trans (≈ʷ-sym e)) (gen∈T₁₄ g)
byShapeˢ zero     w (joinᶜ h t)  eq _  e b s = ⊥-elim (suc≰0 (subst (_≤ 0) (cong depth eq) b))
byShapeˢ zero     w (meetᶜ h t)  eq _  e b s = ⊥-elim (suc≰0 (subst (_≤ 0) (cong depth eq) b))
byShapeˢ (suc n)  w (joinᶜ h t)  eq (cjoin _ cs _ _) e b s =
  Any.map (≈ʷ-trans w≈)
          (⋁⁺-closed ⌊ h ⌋ᴶ (map ⌊_⌋ᴶ t) (joinand-in h (here refl) (lookup cs (here refl)))
                     (tabulate λ {m} m∈ →
                        let (a , a∈ , m≡) = ∈-map⁻ ⌊_⌋ᴶ m∈
                        in subst (λ u → Any (u ≈ʷ_) T₁₄) (sym m≡) (joinand-in a (there a∈) (lookup cs (there a∈)))))
  where
  -- w is the join of its canonical joinands.
  w≈ : w ≈ʷ ⋁⁺ ⌊ h ⌋ᴶ (map ⌊_⌋ᴶ t)
  w≈ = subst (w ≈ʷ_) (⋁ᴶ≡⋁⁺ h t) (≈ʷ-sym e)

  -- Each joinand has complexity at most n.
  children≤ : (a : CJand (Fin 3)) → a ∈ h ∷ t → IsCanonicalJ a → κ ⌊ a ⌋ᴶ ≤ n
  children≤ a a∈ ic =
    ≤-trans (subst (_≤ _) (sym (complexityᴶ _≟_ ic)) (depthΣJ-upper a∈))
            (≤-pred (subst (_≤ suc n) (cong depth eq) b))

  -- The membership of a joinand in the canonical joinands of w.
  joinand∈ : (a : CJand (Fin 3)) → a ∈ h ∷ t → ⌊ a ⌋ᴶ ∈ CJ w
  joinand∈ a a∈ = subst (λ D → ⌊ a ⌋ᴶ ∈ map ⌊_⌋ᴶ (asListJ (joinandsOf D))) (sym eq) (∈-map⁺ ⌊_⌋ᴶ a∈)

  -- Each joinand is in T₁₄: a generator, or a meet node of the tree, in S and of smaller complexity.
  joinand-in : (a : CJand (Fin 3)) → a ∈ h ∷ t → IsCanonicalJ a → Any (⌊ a ⌋ᴶ ≈ʷ_) T₁₄
  joinand-in (jgen g)       a∈ _            = gen∈T₁₄ g
  joinand-in (jmeet mh mt)  a∈ (cjmeet ic)  =
    in-T₁₄ n ⌊ jmeet mh mt ⌋ᴶ (children≤ (jmeet mh mt) a∈ (cjmeet ic))
           (S-node s (joinand root (joinand∈ (jmeet mh mt) a∈) (λ v e′ → gen≉meet ic (≈ʷ-sym e′))))
byShapeˢ (suc n)  w (meetᶜ h t)  eq ic@(cmeet _ cs _ _) e b s =
  T₁₁→T₁₄
    (Any.map (≈ʷ-trans w≈)
             (⋀⁺-closed ⌊ h ⌋ᴹ (map ⌊_⌋ᴹ t) (meetand-in h (here refl) (lookup cs (here refl)))
                        (tabulate λ {m} m∈ →
                           let (a , a∈ , m≡) = ∈-map⁻ ⌊_⌋ᴹ m∈
                           in subst (λ u → Any (u ≈ʷ_) T₁₁) (sym m≡) (meetand-in a (there a∈) (lookup cs (there a∈))))))
  where
  -- w is the meet of its canonical meetands.
  w≈ : w ≈ʷ ⋀⁺ ⌊ h ⌋ᴹ (map ⌊_⌋ᴹ t)
  w≈ = subst (w ≈ʷ_) (⋀ᴹ≡⋀⁺ h t) (≈ʷ-sym e)

  -- Each meetand has complexity at most n.
  children≤ : (a : CMand (Fin 3)) → a ∈ h ∷ t → IsCanonicalM a → κ ⌊ a ⌋ᴹ ≤ n
  children≤ a a∈ ic′ =
    ≤-trans (subst (_≤ _) (sym (complexityᴹ _≟_ ic′)) (depthΣM-upper a∈))
            (≤-pred (subst (_≤ suc n) (cong depth eq) b))

  -- The membership of a meetand in the canonical meetands of w.
  meetand∈ : (a : CMand (Fin 3)) → a ∈ h ∷ t → ⌊ a ⌋ᴹ ∈ CM w
  meetand∈ a a∈ = subst (λ D → ⌊ a ⌋ᴹ ∈ map ⌊_⌋ᴹ (asListM (meetandsOf D))) (sym eq) (∈-map⁺ ⌊_⌋ᴹ a∈)

  -- w is no generator: it is a canonical meet.
  w-not-gen : ∀ v → ¬ (w ≈ʷ ℊ v)
  w-not-gen v e′ = gen≉meet ic (≈ʷ-sym (≈ʷ-trans e e′))

  -- Each meetand is a join, a node of the tree in S of smaller complexity, so in T₁₁.
  meetand-in : (a : CMand (Fin 3)) → a ∈ h ∷ t → IsCanonicalM a → Any (⌊ a ⌋ᴹ ≈ʷ_) T₁₁
  meetand-in (mgen g)       a∈ _             = ⊥-elim (s root w-not-gen (meetand∈ (mgen g) a∈))
  meetand-in (mjoin jh jt)  a∈ (cmjoin ic′)  =
    T₁₄→T₁₁ ng
      (in-T₁₄ n ⌊ mjoin jh jt ⌋ᴹ (children≤ (mjoin jh jt) a∈ (cmjoin ic′))
              (S-node s (meetand root (meetand∈ (mjoin jh jt) a∈) ng)))
    where
    ng : ∀ v → ¬ (⌊ mjoin jh jt ⌋ᴹ ≈ʷ ℊ v)
    ng v e′ = gen≉join ic′ (≈ʷ-sym e′)

-- S ⊆ T₁₄.
S→T₁₄ : (w : LatTerm (Fin 3)) → NoGeneratorMeetand w → Any (w ≈ʷ_) T₁₄
S→T₁₄ w = in-T₁₄ (κ w) w ≤-refl

-- Proposition 7.2: S = T₁₄, up to equality.
S⇔T₁₄ : (w : LatTerm (Fin 3)) → NoGeneratorMeetand w ⇔ Any (w ≈ʷ_) T₁₄
S⇔T₁₄ w = mk⇔ (S→T₁₄ w) T₁₄→S
```

#### A strictly inflationary embedding fixes at most eleven elements

Fix an inflationary, freely generating `Ψ` that moves every generator.  No
fixed point is a generator (`fixed-not-gen`{.AgdaFunction}).  Proposition 7.3
(`strict-fixed-in-T₁₁`{.AgdaFunction}) is proved as in [the paper][]: by Lemma
3, every fixed point is in `S`
(`strict-fixed-no-generator-meetand`{.AgdaFunction}), so in `T₁₄` by
Proposition 7.2 (`S→T₁₄`{.AgdaFunction}), and in `T₁₁` since it is no
generator.  `in-T₁₁`{.AgdaFunction} keeps its bounded form as a use of it.
`byShape`{.AgdaFunction}, which ran the induction for fixed points before
Proposition 7.2 was stated, is deprecated: `in-T₁₄`{.AgdaFunction} runs it for
`S`.

```agda
module _ (Ψ : Sub (Fin 3) (Fin 3)) (Ψ-free : FreelyGenerates Ψ) (inf : Inflationary Ψ)
         (moves : ∀ g → ¬ (Ψ g ≈ʷ ℊ g)) where
  -- A fixed point is no generator.
  fixed-not-gen : (w : LatTerm (Fin 3)) → w [ Ψ ] ≈ʷ w → ∀ g → ¬ (w ≈ʷ ℊ g)
  fixed-not-gen w fix g e = moves g (≈ʷ-trans (≈ʷ-sym ([]-cong Ψ e)) (≈ʷ-trans fix e))

  -- Proposition 7.3: every fixed point is one of the eleven (Lemma 3 and Proposition 7.2).
  strict-fixed-in-T₁₁ : (w : LatTerm (Fin 3)) → w [ Ψ ] ≈ʷ w → Any (w ≈ʷ_) T₁₁
  strict-fixed-in-T₁₁ w fix =
    T₁₄→T₁₁ (fixed-not-gen w fix) (S→T₁₄ w (strict-fixed-no-generator-meetand Ψ Ψ-free inf moves w fix))

  -- The same, under a bound for the complexity.
  in-T₁₁ : (n : ℕ) (w : LatTerm (Fin 3)) → κ w ≤ n → w [ Ψ ] ≈ʷ w → Any (w ≈ʷ_) T₁₁
  in-T₁₁ n w b fix = strict-fixed-in-T₁₁ w fix

  -- Deprecated: the shape of the canonical form is no longer needed.
  byShape : (n : ℕ) (w : LatTerm (Fin 3)) (C : CTerm (Fin 3)) → canonical w ≡ C → IsCanonical C
          → ⌊ C ⌋ ≈ʷ w → κ w ≤ n → w [ Ψ ] ≈ʷ w → Any (w ≈ʷ_) T₁₁
  byShape n w C _ _ _ b fix = in-T₁₁ n w b fix
  {-# WARNING_ON_USAGE byShape
  "byShape is deprecated; use in-T₁₁, or in-T₁₄ for the induction on S (Proposition 7.2)." #-}

  -- Every fixed point has complexity at most three.
  strict-fixed-complexity : (w : LatTerm (Fin 3)) → w [ Ψ ] ≈ʷ w → κ w ≤ 3
  strict-fixed-complexity w fix =
    let (t , t∈ , e) = find (strict-fixed-in-T₁₁ w fix)
    in subst (_≤ 3) (sym (complexity-resp _≟_ e)) (lookup T₁₁-complexity t∈)
```

#### The descent, with the parent of its last step

The descent of [DeansProblem.Fixed][], with one more output: from a fixed
point of complexity `m + 2` it reaches an element `u` of complexity two fixed
by a positive power, and a canonical joinand or meetand `v` of `u` of
complexity one, fixed by a further power (`descent-pair`{.AgdaFunction}).  It
is the case `n = 3` of `descent-parent`{.AgdaFunction} of
[DeansProblem.Fixed][], which holds in `FL(n)`.  Every element lies below
`x ∨ y ∨ z` and above `x ∧ y ∧ z` (`≤-top`{.AgdaFunction},
`bot-≤`{.AgdaFunction}), and neither is a canonical joinand or meetand of an
element of complexity two (`top-not-child`{.AgdaFunction},
`bot-not-child`{.AgdaFunction}).

```agda
-- The descent, keeping the parent of the last step.
descent-pair : (m : ℕ) (θ : Sub (Fin 3) (Fin 3)) → FreelyGenerates θ
             → (w : LatTerm (Fin 3)) → w [ θ ] ≈ʷ w → κ w ≡ suc (suc m)
             → Σ[ d ∈ ℕ ] Σ[ u ∈ LatTerm (Fin 3) ] Σ[ v ∈ LatTerm (Fin 3) ]
                 u [ iter θ (suc d) ] ≈ʷ u × κ u ≡ 2 × (v ∈ CJ u ⊎ v ∈ CM u) × κ v ≡ 1
descent-pair = descent-parent

-- Every element lies below x ∨ y ∨ z and above x ∧ y ∧ z.
≤-top : (t : LatTerm (Fin 3)) → t ≤ʷ top
≤-top (ℊ 0F)   = ℊ≤∨ˡ (ℊ≤ℊ refl)
≤-top (ℊ 1F)   = ℊ≤∨ʳ (ℊ≤∨ˡ (ℊ≤ℊ refl))
≤-top (ℊ 2F)   = ℊ≤∨ʳ (ℊ≤∨ʳ (ℊ≤ℊ refl))
≤-top (s ∨̇ t)  = ∨≤ (≤-top s) (≤-top t)
≤-top (s ∧̇ t)  = ∧ˡ≤ (≤-top s)

bot-≤ : (t : LatTerm (Fin 3)) → bot ≤ʷ t
bot-≤ (ℊ 0F)   = ∧ˡ≤ (ℊ≤ℊ refl)
bot-≤ (ℊ 1F)   = ∧ʳ≤ (∧ˡ≤ (ℊ≤ℊ refl))
bot-≤ (ℊ 2F)   = ∧ʳ≤ (∧ʳ≤ (ℊ≤ℊ refl))
bot-≤ (s ∨̇ t)  = ≤∨ˡ (bot-≤ s)
bot-≤ (s ∧̇ t)  = ≤∧ (bot-≤ s) (bot-≤ t)

private
  -- Two is not one.
  2≢1 : 2 ≡ 1 → ⊥
  2≢1 ()

  -- An element of complexity two is neither the top nor the bottom.
  κ2≉top : (u : LatTerm (Fin 3)) → κ u ≡ 2 → ¬ (u ≈ʷ top)
  κ2≉top u κu e = 2≢1 (trans (sym κu) (complexity-resp _≟_ e))

  κ2≉bot : (u : LatTerm (Fin 3)) → κ u ≡ 2 → ¬ (u ≈ʷ bot)
  κ2≉bot u κu e = 2≢1 (trans (sym κu) (complexity-resp _≟_ e))

-- The top is no canonical joinand or meetand of an element of complexity two; nor is the bottom.
top-not-child : (u v : LatTerm (Fin 3)) → κ u ≡ 2 → v ≈ʷ top → ¬ (v ∈ CJ u ⊎ v ∈ CM u)
top-not-child u v κu v≈ (inj₁ v∈) =
  κ2≉top u κu (≤-top u , ≤ʷ-trans (proj₂ v≈) (canonicalJoinands-upper _≟_ v∈))
top-not-child u v κu v≈ (inj₂ v∈) =
  κ2≉top u κu (≤-top u , canonicalMeetands-greatest _≟_ (λ {c} c∈ →
    ≤ʷ-trans (proj₂ v≈) (antichain-≤ ≤ʷ-refl (canonicalMeetands-antichain _≟_ u) c∈ v∈
                                     (≤ʷ-trans (≤-top c) (proj₂ v≈)))))

bot-not-child : (u v : LatTerm (Fin 3)) → κ u ≡ 2 → v ≈ʷ bot → ¬ (v ∈ CJ u ⊎ v ∈ CM u)
bot-not-child u v κu v≈ (inj₂ v∈) =
  κ2≉bot u κu (≤ʷ-trans (canonicalMeetands-lower _≟_ v∈) (proj₁ v≈) , bot-≤ u)
bot-not-child u v κu v≈ (inj₁ v∈) =
  κ2≉bot u κu (canonicalJoinands-least _≟_ (λ {c} c∈ →
    ≤ʷ-trans (antichain-≤ ≤ʷ-refl (canonicalJoinands-antichain _≟_ u) v∈ c∈
                          (≤ʷ-trans (proj₁ v≈) (bot-≤ c))) (proj₁ v≈)) , bot-≤ u)
```

#### The join case

Fix a proper self-embedding `Θ` with a fixed free triple `τ`.  The element
named in the triple by a term of complexity four is fixed and has complexity
at least four (`u₄`{.AgdaFunction}).  Suppose a positive power `Ψ` of `Θ`
fixes `x′ ∨ y′`, the join of the two generators other than `z′`.  By
`fixes-join`{.AgdaFunction} and `fixes-join-swapped`{.AgdaFunction}, `Ψ` or
`Ψ²` is inflationary; call it `Φ`, again a positive power of `Θ`.  Either `Φ` fixes a generator, decided by Whitman's
procedure, and then so does `Θ` (`power-fixes→fixes`{.AgdaFunction}); or `Φ`
moves every generator, and then its fixed point `u₄` has complexity at most
three, which it has not (`join-case`{.AgdaFunction}).

```agda
module JoinCase (Θ : Sub (Fin 3) (Fin 3)) (Θ-free : FreelyGenerates Θ) (m : Fin 3) (m∉ : ∀ i → ¬ (ℊ m ≈ʷ Θ i))
                (τ : Sub (Fin 3) (Fin 3)) (τ-free : FreelyGenerates τ) (τ-fixed : ∀ i → τ i [ Θ ] ≈ʷ τ i) where
  private
    Θ-inj = freelyGenerates→injective Θ Θ-free
    τ-inj = freelyGenerates→injective τ τ-free

    -- Θ fixes every element of the sublattice τ generates.
    fixes-⟨τ⟩ : (t : LatTerm (Fin 3)) → t [ τ ] [ Θ ] ≈ʷ t [ τ ]
    fixes-⟨τ⟩ t = subst (_≈ʷ t [ τ ]) ([]-⨟ t τ Θ) ([]-congʳ t τ-fixed)

    -- A term of complexity four.
    w₄ : LatTerm (Fin 3)
    w₄ = x ∨̇ (y ∧̇ (z ∨̇ (x ∧̇ y)))

  -- The element it names in the triple: fixed, of complexity at least four.
  u₄ : LatTerm (Fin 3)
  u₄ = w₄ [ τ ]

  u₄-fixed : u₄ [ Θ ] ≈ʷ u₄
  u₄-fixed = fixes-⟨τ⟩ w₄

  4≤κu₄ : 4 ≤ κ u₄
  4≤κu₄ = complexity-mono _≟_ _≟_ τ τ-inj w₄

  private
    4≰3 : 4 ≤ 3 → ⊥
    4≰3 (s≤s (s≤s (s≤s ())))

    -- Inflation at the three generators, as a predicate on all of them.
    inflationary-of : (Φ : Sub (Fin 3) (Fin 3)) (z′ : Fin 3)
                    → ℊ (other z′) ≤ʷ Φ (other z′) → ℊ (other' z′) ≤ʷ Φ (other' z′) → ℊ z′ ≤ʷ Φ z′
                    → Inflationary Φ
    inflationary-of Φ z′ px py pz v = [ (λ v≡z → subst (λ u → ℊ u ≤ʷ Φ u) (sym v≡z) pz) , others ]′ (cover₃ z′ v)
      where
      others : v ∈ other z′ ∷ other' z′ ∷ [] → ℊ v ≤ʷ Φ v
      others (here p)          = subst (λ u → ℊ u ≤ʷ Φ u) (sym p) px
      others (there (here p))  = subst (λ u → ℊ u ≤ʷ Φ u) (sym p) py
      others (there (there ()))

  -- An inflationary positive power of Θ yields a generator fixed by Θ.
  conclude : (E : ℕ) → Inflationary (iter Θ (suc E)) → Σ[ g ∈ Fin 3 ] Θ g ≈ʷ ℊ g
  conclude E infΦ = decide (any? (λ g → iter Θ (suc E) g ≈ʷ? ℊ g) (allFin 3))
    where
    Φ : Sub (Fin 3) (Fin 3)
    Φ = iter Θ (suc E)

    decide : Dec (Any (λ g → Φ g ≈ʷ ℊ g) (allFin 3)) → Σ[ g ∈ Fin 3 ] Θ g ≈ʷ ℊ g
    decide (yes p)  = let (g , _ , fixg) = find p in g , power-fixes→fixes Θ Θ-free m m∉ E g fixg
    decide (no ¬p)  =
      ⊥-elim (4≰3 (≤-trans 4≤κu₄
               (strict-fixed-complexity Φ (iter-free Θ Θ-free (suc E)) infΦ moves u₄
                                        (fixed→image Θ Θ-inj u₄ u₄-fixed (suc E)))))
      where
      moves : ∀ g → ¬ (Φ g ≈ʷ ℊ g)
      moves g fixg = ¬p (lose (∈-allFin g) fixg)

  private
    -- The square of a power, on a generator.
    square : (e : ℕ) (v : Fin 3) → iter Θ (suc (e + (suc e + 0))) v ≡ iter Θ (suc e) v [ iter Θ (suc e) ]
    square e v =
      trans (sym ([]-iter-* (ℊ v) Θ (suc e) 2))
            (trans ([]-iter-suc (ℊ v) (iter Θ (suc e)) 1)
                   (trans ([]-iter-suc (iter Θ (suc e) v) (iter Θ (suc e)) 0)
                          ([]-ℊ (iter Θ (suc e) v [ iter Θ (suc e) ]))))

  -- A positive power of Θ fixing a join of two generators gives an inflationary positive power of Θ.
  join-power : (z′ : Fin 3) (e : ℕ)
             → iter Θ (suc e) (other z′) ∨̇ iter Θ (suc e) (other' z′) ≈ʷ ℊ (other z′) ∨̇ ℊ (other' z′)
             → Σ[ E ∈ ℕ ] Inflationary (iter Θ (suc E))
  join-power z′ e fixj = finish (proj₁ (fixes-join Ψ Ψ-free z′ fixj))
    where
    Ψ : Sub (Fin 3) (Fin 3)
    Ψ = iter Θ (suc e)

    Ψ-free : FreelyGenerates Ψ
    Ψ-free = iter-free Θ Θ-free (suc e)

    x′ y′ : Fin 3
    x′ = other z′
    y′ = other' z′

    z′≤ : ℊ z′ ≤ʷ Ψ z′
    z′≤ = fixes-join-third Ψ Ψ-free z′ fixj

    -- Straight: Ψ is inflationary.  Swapped: Ψ² is, by the last clause of Lemma 1.
    finish : (ℊ x′ ≤ʷ Ψ x′ × ℊ y′ ≤ʷ Ψ y′) ⊎ (ℊ x′ ≤ʷ Ψ y′ × ℊ y′ ≤ʷ Ψ x′) → Σ[ E ∈ ℕ ] Inflationary (iter Θ (suc E))
    finish (inj₁ (px , py)) = e , inflationary-of Ψ z′ px py z′≤
    finish (inj₂ (px , py)) =
      e + (suc e + 0) , λ v → subst (ℊ v ≤ʷ_) (trans (iter-two Ψ Ψ-free v) (sym (square e v)))
                                    (fixes-join-swapped Ψ Ψ-free z′ fixj px py v)

  -- And so a generator fixed by Θ.
  join-case : (z′ : Fin 3) (e : ℕ)
            → iter Θ (suc e) (other z′) ∨̇ iter Θ (suc e) (other' z′) ≈ʷ ℊ (other z′) ∨̇ ℊ (other' z′)
            → Σ[ g ∈ Fin 3 ] Θ g ≈ʷ ℊ g
  join-case z′ e fixj = let (E , infΦ) = join-power z′ e fixj in conclude E infΦ
```

#### Duality, and the theorem

The dual of a substitution dualizes every image (`dualˢ`{.AgdaFunction}); it
freely generates when the original does (`dual-free`{.AgdaFunction}), misses
the same generators (`dual-misses`{.AgdaFunction}), fixes the dual of each
fixed point (`dual-fixed`{.AgdaFunction}), and its iterates are the duals of
the iterates (`dual-iter`{.AgdaFunction}).  The first and the third are
equivalences (`dual-free⁻¹`{.AgdaFunction}, `dual-fixed⁻¹`{.AgdaFunction}),
since the dual is an involution, and the dual is inflationary exactly when the
original is deflationary (`dual-inflationary`{.AgdaFunction}, with its dual
`dual-deflationary`{.AgdaFunction}): these are the duality facts of Section 7.1
of [the paper][].  So a power fixing a meet of two generators is, for the dual
embedding, a power fixing their join, and a generator fixed by the dual
embedding is fixed by the original.

```agda
-- The dual of a substitution.
dualˢ : Sub (Fin 3) (Fin 3) → Sub (Fin 3) (Fin 3)
dualˢ σ v = dual (σ v)

private
  -- The join condition dualizes to the meet condition (the converse is in Lattices.Free.Generation).
  JoinCondition→MeetConditionᵈ : (σ : Sub (Fin 3) (Fin 3)) → JoinCondition σ → MeetCondition (dualˢ σ)
  JoinCondition→MeetConditionᵈ σ jc {i} {[]}      ()
  JoinCondition→MeetConditionᵈ σ jc {i} {j ∷ js}  p =
    jc {i} {j ∷ js} (dual-reflects (subst (_≤ʷ dual (σ i)) (sym dual-join) p))
    where
    dual-join : dual (⋁⁺ (σ j) (map σ js)) ≡ ⋀⁺ (dual (σ j)) (map (dualˢ σ) js)
    dual-join = trans (dual-⋁⁺′ (σ j) (map σ js)) (cong (⋀⁺ (dual (σ j))) (sym (map-∘ js)))
      where
      dual-⋁⁺′ : (u : LatTerm (Fin 3)) (us : List (LatTerm (Fin 3))) → dual (⋁⁺ u us) ≡ ⋀⁺ (dual u) (map dual us)
      dual-⋁⁺′ u []        = refl
      dual-⋁⁺′ u (w ∷ ws)  = cong (dual u ∧̇_) (dual-⋁⁺′ w ws)

-- The dual of a freely generating substitution freely generates.
dual-free : (σ : Sub (Fin 3) (Fin 3)) → FreelyGenerates σ → FreelyGenerates (dualˢ σ)
dual-free σ (jc , mc) = MeetCondition→JoinConditionᵈ σ mc , JoinCondition→MeetConditionᵈ σ jc

-- It misses the same generators.
dual-misses : (σ : Sub (Fin 3) (Fin 3)) (m : Fin 3) → (∀ i → ¬ (ℊ m ≈ʷ σ i)) → ∀ i → ¬ (ℊ m ≈ʷ dualˢ σ i)
dual-misses σ m m∉ i e = m∉ i (subst (ℊ m ≈ʷ_) (dual-involutive (σ i)) (dual-cong e))

-- It fixes the dual of each fixed point.
dual-fixed : (σ : Sub (Fin 3) (Fin 3)) (t : LatTerm (Fin 3)) → t [ σ ] ≈ʷ t → dual t [ dualˢ σ ] ≈ʷ dual t
dual-fixed σ t fix = subst (_≈ʷ dual t) (dual-[] t σ) (dual-cong fix)

-- Its iterates are the duals of the iterates.
dual-iter : (t : LatTerm (Fin 3)) (σ : Sub (Fin 3) (Fin 3)) (k : ℕ)
          → dual (t [ iter σ k ]) ≡ dual t [ iter (dualˢ σ) k ]
dual-iter t σ zero     = trans (cong dual ([]-ℊ t)) (sym ([]-ℊ (dual t)))
dual-iter t σ (suc k)  =
  trans (cong dual ([]-iter-suc t σ k))
        (trans (dual-iter (t [ σ ]) σ k)
               (trans (cong (_[ iter (dualˢ σ) k ]) (dual-[] t σ))
                      (sym ([]-iter-suc (dual t) (dualˢ σ) k))))

private
  -- Free generation depends only on the values of the family.
  free-resp : (σ σ′ : Sub (Fin 3) (Fin 3)) → (∀ v → σ v ≡ σ′ v) → FreelyGenerates σ → FreelyGenerates σ′
  free-resp σ σ′ eq (jc , mc) =
      (λ {i} {js} p → jc (subst₂ _≤⋁_ (sym (eq i)) (sym (map-cong eq js)) p))
    , (λ {i} {js} p → mc (subst₂ _⋀≤_ (sym (map-cong eq js)) (sym (eq i)) p))

-- A family freely generates exactly when its dual does: the converse of dual-free.
dual-free⁻¹ : (σ : Sub (Fin 3) (Fin 3)) → FreelyGenerates (dualˢ σ) → FreelyGenerates σ
dual-free⁻¹ σ fd = free-resp (dualˢ (dualˢ σ)) σ (λ v → dual-involutive (σ v)) (dual-free (dualˢ σ) fd)

-- The dual fixes the dual of an element only when the original fixes the element: the converse of dual-fixed.
dual-fixed⁻¹ : (σ : Sub (Fin 3) (Fin 3)) (t : LatTerm (Fin 3)) → dual t [ dualˢ σ ] ≈ʷ dual t → t [ σ ] ≈ʷ t
dual-fixed⁻¹ σ t fix = dual-reflects-≈ {s = t [ σ ]} {t = t} (subst (_≈ʷ dual t) (sym (dual-[] t σ)) fix)

-- The dual is inflationary exactly when the original is deflationary.
dual-inflationary : (σ : Sub (Fin 3) (Fin 3)) → Inflationary (dualˢ σ) ⇔ Deflationary σ
dual-inflationary σ =
  mk⇔ (λ inf v → subst (_≤ʷ ℊ v) (dual-involutive (σ v)) (dual-antitone (inf v)))
      (λ def v → dual-antitone (def v))

-- And deflationary exactly when the original is inflationary.
dual-deflationary : (σ : Sub (Fin 3) (Fin 3)) → Deflationary (dualˢ σ) ⇔ Inflationary σ
dual-deflationary σ =
  mk⇔ (λ def v → subst (ℊ v ≤ʷ_) (dual-involutive (σ v)) (dual-antitone (def v)))
      (λ inf v → dual-antitone (inf v))
```

The theorem assembles the steps: the descent from `u₄` reaches an element
`u` of complexity two fixed by a positive power and a canonical joinand or
meetand `v` of `u` of complexity one, fixed by a further power; `v` is, up to
equality, one of the generators (impossible, by its complexity), the top or
the bottom (impossible, by `top-not-child`{.AgdaFunction} and
`bot-not-child`{.AgdaFunction}), a join of two generators (the join case), or
a meet of two generators (the join case for the dual embedding).  Proposition
7.4 of [the paper][] is `inflationary-fixing-power`{.AgdaFunction}: the
inflationary power of `inflationary-power`{.AgdaFunction} fixes the triple, or
the dual triple, since every power of `Θ` fixes what `Θ` fixes
(`fixed→image`{.AgdaFunction}).  And a proper self-embedding that moves every
generator fixes no free triple (`moves→no-fixed-triple`{.AgdaFunction}), the
remark after Corollary 7.5.

```agda
module _ (Θ : Sub (Fin 3) (Fin 3)) (Θ-free : FreelyGenerates Θ) (m : Fin 3) (m∉ : ∀ i → ¬ (ℊ m ≈ʷ Θ i))
         (τ : Sub (Fin 3) (Fin 3)) (τ-free : FreelyGenerates τ) (τ-fixed : ∀ i → τ i [ Θ ] ≈ʷ τ i) where
  open JoinCase Θ Θ-free m m∉ τ τ-free τ-fixed using ( u₄ ; u₄-fixed ; 4≤κu₄ ; join-power ; conclude )
  open Bounded (_≟_ {3}) (allFin 3) ∈-allFin using ( bounded ; bounded-complete )

  -- The dual embedding, with the dual triple.
  Θᵈ : Sub (Fin 3) (Fin 3)
  Θᵈ = dualˢ Θ

  module Dual = JoinCase Θᵈ (dual-free Θ Θ-free) m (dual-misses Θ m m∉) (dualˢ τ) (dual-free τ τ-free)
                         (λ i → dual-fixed Θ (τ i) (τ-fixed i))

  private
    -- A generator fixed by the dual embedding is fixed by the original.
    back : Σ[ g ∈ Fin 3 ] Θᵈ g ≈ʷ ℊ g → Σ[ g ∈ Fin 3 ] Θ g ≈ʷ ℊ g
    back (g , e) = g , dual-reflects-≈ {s = Θ g} {t = ℊ g} e

    1≢0 : 1 ≡ 0 → ⊥
    1≢0 ()

  -- An inflationary positive power, of Θ or of its dual.
  InflationaryPower : Type
  InflationaryPower = (Σ[ E ∈ ℕ ] Inflationary (iter Θ (suc E))) ⊎ (Σ[ E ∈ ℕ ] Inflationary (iter Θᵈ (suc E)))

  -- Every proper self-embedding of FL(3) with a fixed free triple has one.
  inflationary-power : InflationaryPower
  inflationary-power =
    let (o , 4+o≡κ) = m≤n⇒∃[o]m+o≡n 4≤κu₄
        (d , u , v , fixu , κu , v∈ , κv) = descent-pair (suc (suc o)) Θ Θ-free u₄ u₄-fixed (sym 4+o≡κ)
        (d′ , fixv) = periodic d u v fixu v∈ κv
    in cases u v κu (d + d′ * suc d) fixv v∈ κv (bounded-complete 1 v (≤-reflexive′ κv))
    where
    ≤-reflexive′ : {a : ℕ} → a ≡ 1 → a ≤ 1
    ≤-reflexive′ refl = ≤-refl

    -- v is fixed by a positive power of the power fixing u, hence by a positive power of Θ.
    periodic : (d : ℕ) (u v : LatTerm (Fin 3)) → u [ iter Θ (suc d) ] ≈ʷ u → v ∈ CJ u ⊎ v ∈ CM u → κ v ≡ 1
             → Σ[ d′ ∈ ℕ ] v [ iter Θ (suc (d + d′ * suc d)) ] ≈ʷ v
    periodic d u v fixu v∈ κv =
      let (d′ , per) = step v∈
      in d′ , ≈ʷ-trans (≡→≈ʷ (sym ([]-iter-* v Θ (suc d) (suc d′)))) per
      where
      step : v ∈ CJ u ⊎ v ∈ CM u → Σ[ d′ ∈ ℕ ] v [ iter (iter Θ (suc d)) (suc d′) ] ≈ʷ v
      step (inj₁ v∈) = joinand-periodic (iter Θ (suc d)) (iter-free Θ Θ-free (suc d)) u fixu v∈ (positive-not-gen v 0 κv)
      step (inj₂ v∈) = meetand-periodic (iter Θ (suc d)) (iter-free Θ Θ-free (suc d)) u fixu v∈ (positive-not-gen v 0 κv)

    -- The join and meet cases, read off the representative.
    joinat : (z′ : Fin 3) (E : ℕ) (v : LatTerm (Fin 3)) → v [ iter Θ (suc E) ] ≈ʷ v
           → v ≈ʷ ℊ (other z′) ∨̇ ℊ (other' z′) → InflationaryPower
    joinat z′ E v fixv e =
      inj₁ (join-power z′ E (≈ʷ-trans ([]-cong (iter Θ (suc E)) (≈ʷ-sym e)) (≈ʷ-trans fixv e)))

    meetat : (z′ : Fin 3) (E : ℕ) (v : LatTerm (Fin 3)) → v [ iter Θ (suc E) ] ≈ʷ v
           → v ≈ʷ ℊ (other z′) ∧̇ ℊ (other' z′) → InflationaryPower
    meetat z′ E v fixv e =
      inj₂ (Dual.join-power z′ E
             (subst (_≈ʷ ℊ (other z′) ∨̇ ℊ (other' z′))
                    (dual-iter (ℊ (other z′) ∧̇ ℊ (other' z′)) Θ (suc E))
                    (dual-cong (≈ʷ-trans ([]-cong (iter Θ (suc E)) (≈ʷ-sym e)) (≈ʷ-trans fixv e)))))

    -- A generator has complexity zero, not one.
    genat : (v : LatTerm (Fin 3)) (g : Fin 3) → κ v ≡ 1 → ¬ (v ≈ʷ ℊ g)
    genat v g κv e = 1≢0 (trans (sym κv) (trans (complexity-resp _≟_ e) (κ-gen g)))
      where
      κ-gen : ∀ g → κ (ℊ g) ≡ 0
      κ-gen 0F = refl
      κ-gen 1F = refl
      κ-gen 2F = refl

    cases : (u v : LatTerm (Fin 3)) → κ u ≡ 2 → (E : ℕ) → v [ iter Θ (suc E) ] ≈ʷ v → v ∈ CJ u ⊎ v ∈ CM u → κ v ≡ 1
          → Any (v ≈ʷ_) (bounded 1) → InflationaryPower
    cases u v κu E fixv v∈ κv (here e)                                                                           = ⊥-elim (genat v 0F κv e)
    cases u v κu E fixv v∈ κv (there (here e))                                                                   = ⊥-elim (genat v 1F κv e)
    cases u v κu E fixv v∈ κv (there (there (here e)))                                                           = ⊥-elim (genat v 2F κv e)
    cases u v κu E fixv v∈ κv (there (there (there (here e))))                                                   = ⊥-elim (genat v 0F κv e)
    cases u v κu E fixv v∈ κv (there (there (there (there (here e)))))                                           = ⊥-elim (genat v 1F κv e)
    cases u v κu E fixv v∈ κv (there (there (there (there (there (here e))))))                                   = ⊥-elim (genat v 2F κv e)
    cases u v κu E fixv v∈ κv (there (there (there (there (there (there (here e)))))))                           = joinat 0F E v fixv e
    cases u v κu E fixv v∈ κv (there (there (there (there (there (there (there (here e))))))))                   = joinat 2F E v fixv e
    cases u v κu E fixv v∈ κv (there (there (there (there (there (there (there (there (here e)))))))))           = joinat 1F E v fixv e
    cases u v κu E fixv v∈ κv (there (there (there (there (there (there (there (there (there (here e))))))))))   = ⊥-elim (top-not-child u v κu e v∈)
    cases u v κu E fixv v∈ κv (there (there (there (there (there (there (there (there (there (there (here e)))))))))))
      = ⊥-elim (genat v 0F κv e)
    cases u v κu E fixv v∈ κv (there (there (there (there (there (there (there (there (there (there (there (here e))))))))))))
      = ⊥-elim (genat v 1F κv e)
    cases u v κu E fixv v∈ κv (there (there (there (there (there (there (there (there (there (there (there (there (here e)))))))))))))
      = ⊥-elim (genat v 2F κv e)
    cases u v κu E fixv v∈ κv (there (there (there (there (there (there (there (there (there (there (there (there (there (here e))))))))))))))
      = meetat 0F E v fixv e
    cases u v κu E fixv v∈ κv (there (there (there (there (there (there (there (there (there (there (there (there (there (there (here e)))))))))))))))
      = meetat 2F E v fixv e
    cases u v κu E fixv v∈ κv (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (here e))))))))))))))))
      = meetat 1F E v fixv e
    cases u v κu E fixv v∈ κv (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (here e)))))))))))))))))
      = ⊥-elim (bot-not-child u v κu e v∈)
    cases u v κu E fixv v∈ κv (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there ())))))))))))))))))

  -- Every proper self-embedding of FL(3) with a fixed free triple fixes a generator.
  fixes-generator : Σ[ g ∈ Fin 3 ] Θ g ≈ʷ ℊ g
  fixes-generator = [ (λ (E , infΦ) → conclude E infΦ) , (λ (E , infΦ) → back (Dual.conclude E infΦ)) ]′ inflationary-power

  -- So one that moves every generator fixes no free triple.
  moves→no-fixed-triple : (∀ g → ¬ (Θ g ≈ʷ ℊ g)) → ⊥
  moves→no-fixed-triple moves = let (g , fixg) = fixes-generator in moves g fixg

  -- Proposition 7.4, both halves: an inflationary positive power of Θ fixing the triple, or of Θᵈ fixing the dual triple.
  InflationaryFixingPower : Type
  InflationaryFixingPower =
      (Σ[ E ∈ ℕ ] Inflationary (iter Θ (suc E)) × (∀ i → τ i [ iter Θ (suc E) ] ≈ʷ τ i))
    ⊎ (Σ[ E ∈ ℕ ] Inflationary (iter Θᵈ (suc E)) × (∀ i → dualˢ τ i [ iter Θᵈ (suc E) ] ≈ʷ dualˢ τ i))

  inflationary-fixing-power : InflationaryFixingPower
  inflationary-fixing-power =
    [ (λ (E , inf) → inj₁ (E , inf , λ i → fixed→image Θ Θ-inj (τ i) (τ-fixed i) (suc E)))
    , (λ (E , inf) → inj₂ (E , inf , λ i → fixed→image Θᵈ Θᵈ-inj (dual (τ i)) (dual-fixed Θ (τ i) (τ-fixed i)) (suc E))) ]′
      inflationary-power
    where
    Θ-inj = freelyGenerates→injective Θ Θ-free
    Θᵈ-inj = freelyGenerates→injective Θᵈ (dual-free Θ Θ-free)
```

#### The paper's statements

Propositions 7.2 to 7.4 and Theorem E of [the paper][], each as one
statement.  A self-embedding of `FL(3)` is a substitution that freely
generates, proper when it misses a generator `m`; it fixes a free triple
`τ` when it fixes each `τ i`, and so every element of the copy of `FL(3)` the
triple generates.

**Proposition 7.2**: `S = T₁₄`, where `S` is the set of elements whose
canonical trees have no generator among the meetands of any meet node
(`NoGeneratorMeetand`{.AgdaFunction}), up to equality in `FL(3)`; and every
element of `T₁₁` has complexity at most 3.

```agda
-- Proposition 7.2: S is T₁₄, and the members of T₁₁ have complexity at most 3.
Proposition-7·2 : Type
Proposition-7·2 =  ((w : LatTerm (Fin 3)) → NoGeneratorMeetand w ⇔ Any (w ≈ʷ_) T₁₄)
                 × All (λ t → complexity (_≟_ {3}) t ≤ 3) T₁₁

-- The proof of Proposition 7.2.
proposition-7·2 : Proposition-7·2
proposition-7·2 = S⇔T₁₄ , T₁₁-complexity
```

**Proposition 7.3**: a strictly inflationary self-embedding `Ψ` fixes only
elements of `T₁₁`; in particular it has at most eleven fixed points, each of
complexity at most 3.

```agda
-- Proposition 7.3: a strictly inflationary self-embedding fixes only members of the eleven, each
-- of complexity at most 3.
Proposition-7·3 : Type
Proposition-7·3 =
  (Ψ : Sub (Fin 3) (Fin 3)) → FreelyGenerates Ψ → Inflationary Ψ → (∀ g → ¬ (Ψ g ≈ʷ ℊ g))
  →  ((w : LatTerm (Fin 3)) → w [ Ψ ] ≈ʷ w → Any (w ≈ʷ_) T₁₁)
   × length T₁₁ ≡ 11
   × ((w : LatTerm (Fin 3)) → w [ Ψ ] ≈ʷ w → complexity (_≟_ {3}) w ≤ 3)

-- The proof of Proposition 7.3.
proposition-7·3 : Proposition-7·3
proposition-7·3 Ψ Ψ-free inf moves =
  strict-fixed-in-T₁₁ Ψ Ψ-free inf moves , refl , strict-fixed-complexity Ψ Ψ-free inf moves
```

**Proposition 7.4**: if a proper self-embedding `Θ` fixes a free triple
`τ` pointwise, then a positive power of `Θ` is inflationary and fixes `τ`, or
a positive power of its dual `Θ^δ` (`dualˢ Θ`) is inflationary and fixes the
dual triple.

```agda
-- Proposition 7.4: an inflationary positive power of Θ fixing the triple, or of its dual fixing
-- the dual triple.
Proposition-7·4 : Type
Proposition-7·4 =
  (Θ : Sub (Fin 3) (Fin 3)) → FreelyGenerates Θ → (m : Fin 3) → (∀ i → ¬ (ℊ m ≈ʷ Θ i))
  → (τ : Sub (Fin 3) (Fin 3)) → FreelyGenerates τ → (∀ i → τ i [ Θ ] ≈ʷ τ i)
  →  (Σ[ E ∈ ℕ ] Inflationary (iter Θ (suc E)) × (∀ i → τ i [ iter Θ (suc E) ] ≈ʷ τ i))
   ⊎ (Σ[ E ∈ ℕ ] Inflationary (iter (dualˢ Θ) (suc E))
                 × (∀ i → dualˢ τ i [ iter (dualˢ Θ) (suc E) ] ≈ʷ dualˢ τ i))

-- The proof of Proposition 7.4.
proposition-7·4 : Proposition-7·4
proposition-7·4 = inflationary-fixing-power
```

**Theorem E**: every proper self-embedding of `FL(3)` whose fixed sublattice
contains a free triple fixes a generator.

```agda
-- Theorem E: a proper self-embedding fixing a free triple fixes a generator.
Theorem-E : Type
Theorem-E =  (Θ : Sub (Fin 3) (Fin 3)) → FreelyGenerates Θ → (m : Fin 3) → (∀ i → ¬ (ℊ m ≈ʷ Θ i))
             → (τ : Sub (Fin 3) (Fin 3)) → FreelyGenerates τ → (∀ i → τ i [ Θ ] ≈ʷ τ i)
             → Σ[ g ∈ Fin 3 ] Θ g ≈ʷ ℊ g

-- The proof of Theorem E.
theorem-E : Theorem-E
theorem-E = fixes-generator
```
