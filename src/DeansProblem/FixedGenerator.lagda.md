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
open import Data.List.Base                         using ( List ; [] ; _∷_ ; map ; allFin )
open import Data.List.Properties                   using ( map-∘ )
open import Data.List.Membership.Propositional     using ( _∈_ ; find ; lose )
open import Data.List.Membership.Propositional.Properties
                                                   using ( ∈-allFin ; ∈-map⁺ ; ∈-map⁻ )
open import Data.List.Relation.Unary.All           using ( All ; [] ; _∷_ ; all? ; lookup ; tabulate )
open import Data.List.Relation.Unary.Any           using ( Any ; here ; there ; any? )
open import Data.Nat.Base                          using ( ℕ ; zero ; suc ; _+_ ; _*_ ; _≤_ ; s≤s )
open import Data.Nat.Properties                    using ( ≤-refl ; ≤-trans ; _≤?_ ; ≤-pred ; m≤n⇒∃[o]m+o≡n )
open import Data.Product                           using ( Σ-syntax ; _×_ ; _,_ ; proj₁ ; proj₂ )
open import Data.Sum.Base                          using ( _⊎_ ; inj₁ ; inj₂ ; [_,_]′ )
open import Relation.Binary.PropositionalEquality  using ( _≡_ ; refl ; sym ; trans ; cong ; subst )
open import Relation.Nullary                       using ( ¬_ )
open import Relation.Nullary.Decidable.Core        using ( Dec ; yes ; no ; from-yes )

import Data.List.Relation.Unary.Any as Any

-- Imports from the Agda Universal Algebra Library ------------------------------
open import Lattices.Free.Canonical.Algorithm      using ( module Canonicalization )
open import Lattices.Free.Canonical.Basic
  using  ( CTerm ; genᶜ ; joinᶜ ; meetᶜ ; CJand ; jgen ; jmeet ; CMand ; mgen ; mjoin ; ⌊_⌋ ; ⌊_⌋ᴶ ; ⌊_⌋ᴹ
         ; ⋁ᴶ≡⋁⁺ ; ⋀ᴹ≡⋀⁺ ; ≈ʷ-refl ; ≈ʷ-sym ; ≈ʷ-trans ; ∨̇-cong ; ∧̇-cong ; IsCanonical ; cjoin
         ; cmeet ; IsCanonicalJ ; cjmeet ; IsCanonicalM ; cmjoin ; ⋁⁺ ; ⋀⁺ )
open import Lattices.Free.Canonical.Joinands       using ( canonicalJoinands ; canonicalMeetands
                                                         ; canonicalJoinands-upper ; canonicalJoinands-least
                                                         ; canonicalMeetands-lower ; canonicalMeetands-greatest )
open import Lattices.Free.Canonical.Uniqueness     using ( gen≉join ; gen≉meet ; antichain-≤ )
open import DeansProblem.Chain                     using ( iter ; []-iter-suc )
open import Lattices.Free.Complexity               using ( complexity ; complexity-resp ; complexity-mono ; complexityᴶ
                                                         ; complexityᴹ ; depth ; depthΣJ-upper ; depthΣM-upper
                                                         ; module Bounded )
open import Lattices.Free.Embedding                using ( canonicalJoinands-antichain
                                                         ; canonicalMeetands-antichain )
open import DeansProblem.Fixed                     using ( fixed→image ; child-of-complexity ; positive-not-gen
                                                         ; joinand-periodic ; meetand-periodic ; iter-free
                                                         ; []-iter-* )
open import Lattices.Free.Duality                  using ( dual ; dual-involutive ; dual-cong ; dual-reflects
                                                         ; dual-reflects-≈ )
open import Lattices.Free.Generation               using ( FreelyGenerates ; JoinCondition ; MeetCondition
                                                         ; freelyGenerates→injective
                                                         ; MeetCondition→JoinConditionᵈ )
open import DeansProblem.Inflationary              using ( Inflationary ; fixed-joinand-inflationary
                                                         ; fixed-meetand-inflationary ; meetand-gen-fixed
                                                         ; fixes-join ; fixes-join-third ; power-fixes→fixes )
open import DeansProblem.Partition                 using ( other ; other' ; cover₃ )
open import Lattices.Free.Substitution             using ( Sub ; _[_] ; []-ℊ ; []-⨟ ; []-mono ; []-cong
                                                         ; []-congʳ ; dual-[] )
open import Lattices.Free.Term                     using ( LatTerm ; ℊ ; _∧̇_ ; _∨̇_ )
open import Lattices.Free.Whitman                  using ( _≤ʷ_ ; _≈ʷ_ ; ≤ʷ-refl ; ≤ʷ-trans ; ∨≤ ; ≤∧ ; ∧ˡ≤ ; ∧ʳ≤
                                                         ; ℊ≤ℊ ; ℊ≤∨ˡ ; ℊ≤∨ʳ ; ≤∨ˡ ; module Decision )

open Decision (_≟_ {3}) using ( _≈ʷ?_ )

private
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
```

#### A strictly inflationary embedding fixes at most eleven elements

Fix an inflationary, freely generating `Ψ` that moves every generator.  No
fixed point is a generator (`fixed-not-gen`{.AgdaFunction}).  The induction
runs on a bound for the complexity of the fixed point `w`, through the shape
of its canonical form `C` (`byShape`{.AgdaFunction}, which carries the
equation `canonical w ≡ C` so that no `with` is needed): a generator is
impossible; the joinands of a canonical join are generators, members of
`T₁₄`, or canonical meets, which are fixed by
`fixed-joinand-inflationary`{.AgdaFunction}, have smaller complexity, and are
members of `T₁₁` by induction; so the join is a member of `T₁₄`, and of
`T₁₁` since it is no generator.  The meetands of a canonical meet are never
generators, since `meetand-gen-fixed`{.AgdaFunction} would fix one, so they
are fixed canonical joins and members of `T₁₁` by induction.

```agda
module _ (Ψ : Sub (Fin 3) (Fin 3)) (Ψ-free : FreelyGenerates Ψ) (inf : Inflationary Ψ)
         (moves : ∀ g → ¬ (Ψ g ≈ʷ ℊ g)) where
  open Canonicalization (_≟_ {3}) using ( canonical ; canonical-sound ; canonical-isCanonical )

  -- A fixed point is no generator.
  fixed-not-gen : (w : LatTerm (Fin 3)) → w [ Ψ ] ≈ʷ w → ∀ g → ¬ (w ≈ʷ ℊ g)
  fixed-not-gen w fix g e = moves g (≈ʷ-trans (≈ʷ-sym ([]-cong Ψ e)) (≈ʷ-trans fix e))

  private
    -- A successor is not below zero.
    suc≰0 : ∀ {m} → suc m ≤ 0 → ⊥
    suc≰0 ()

  -- Every fixed point is a member of T₁₁, by induction on a bound for its complexity.
  in-T₁₁ : (n : ℕ) (w : LatTerm (Fin 3)) → κ w ≤ n → w [ Ψ ] ≈ʷ w → Any (w ≈ʷ_) T₁₁
  byShape : (n : ℕ) (w : LatTerm (Fin 3)) (C : CTerm (Fin 3)) → canonical w ≡ C → IsCanonical C
          → ⌊ C ⌋ ≈ʷ w → κ w ≤ n → w [ Ψ ] ≈ʷ w → Any (w ≈ʷ_) T₁₁

  in-T₁₁ n w b fix = byShape n w (canonical w) refl (canonical-isCanonical w) (canonical-sound w) b fix

  byShape n        w (genᶜ g)     eq _                    e b fix = ⊥-elim (fixed-not-gen w fix g (≈ʷ-sym e))
  byShape zero     w (joinᶜ h t)  eq _                    e b fix = ⊥-elim (suc≰0 (subst (_≤ 0) (cong depth eq) b))
  byShape zero     w (meetᶜ h t)  eq _                    e b fix = ⊥-elim (suc≰0 (subst (_≤ 0) (cong depth eq) b))
  byShape (suc n)  w (joinᶜ h t)  eq (cjoin _ cs _ _)     e b fix =
    T₁₄→T₁₁ (fixed-not-gen w fix)
      (Any.map (≈ʷ-trans w≈)
               (⋁⁺-closed ⌊ h ⌋ᴶ (map ⌊_⌋ᴶ t) (joinand-in h (here refl) (lookup cs (here refl)))
                          (tabulate λ {m} m∈ →
                             let (a , a∈ , m≡) = ∈-map⁻ ⌊_⌋ᴶ m∈
                             in subst (λ u → Any (u ≈ʷ_) T₁₄) (sym m≡)
                                      (joinand-in a (there a∈) (lookup cs (there a∈))))))
    where
    -- w is the join of its canonical joinands.
    w≈ : w ≈ʷ ⋁⁺ ⌊ h ⌋ᴶ (map ⌊_⌋ᴶ t)
    w≈ = subst (w ≈ʷ_) (⋁ᴶ≡⋁⁺ h t) (≈ʷ-sym e)

    -- The depth of the join is at most n + 1, so each joinand has complexity at most n.
    children≤ : (a : CJand (Fin 3)) → a ∈ h ∷ t → IsCanonicalJ a → κ ⌊ a ⌋ᴶ ≤ n
    children≤ a a∈ ic =
      ≤-trans (subst (_≤ _) (sym (complexityᴶ _≟_ ic)) (depthΣJ-upper a∈))
              (≤-pred (subst (_≤ suc n) (cong depth eq) b))

    -- Each joinand is a member of T₁₄: a generator, or a fixed meet of smaller complexity.
    joinand-in : (a : CJand (Fin 3)) → a ∈ h ∷ t → IsCanonicalJ a → Any (⌊ a ⌋ᴶ ≈ʷ_) T₁₄
    joinand-in (jgen g)       a∈ _            = gen∈T₁₄ g
    joinand-in (jmeet mh mt)  a∈ (cjmeet ic)  =
      T₁₁→T₁₄ (in-T₁₁ n ⌊ jmeet mh mt ⌋ᴶ (children≤ (jmeet mh mt) a∈ (cjmeet ic))
                       (fixed-joinand-inflationary Ψ Ψ-free inf w fix
                          (subst (λ D → ⌊ jmeet mh mt ⌋ᴶ ∈ map ⌊_⌋ᴶ (proj₁ (joinandsOfC D) ∷ proj₂ (joinandsOfC D)))
                                 (sym eq) (∈-map⁺ ⌊_⌋ᴶ a∈))
                          (λ v e′ → gen≉meet ic (≈ʷ-sym e′))))
      where
      joinandsOfC : CTerm (Fin 3) → CJand (Fin 3) × List (CJand (Fin 3))
      joinandsOfC = Lattices.Free.Canonical.Basic.joinandsOf
  byShape (suc n)  w (meetᶜ h t)  eq (cmeet _ cs _ _)     e b fix =
    Any.map (≈ʷ-trans w≈)
            (⋀⁺-closed ⌊ h ⌋ᴹ (map ⌊_⌋ᴹ t) (meetand-in h (here refl) (lookup cs (here refl)))
                       (tabulate λ {m} m∈ →
                          let (a , a∈ , m≡) = ∈-map⁻ ⌊_⌋ᴹ m∈
                          in subst (λ u → Any (u ≈ʷ_) T₁₁) (sym m≡)
                                   (meetand-in a (there a∈) (lookup cs (there a∈)))))
    where
    w≈ : w ≈ʷ ⋀⁺ ⌊ h ⌋ᴹ (map ⌊_⌋ᴹ t)
    w≈ = subst (w ≈ʷ_) (⋀ᴹ≡⋀⁺ h t) (≈ʷ-sym e)

    children≤ : (a : CMand (Fin 3)) → a ∈ h ∷ t → IsCanonicalM a → κ ⌊ a ⌋ᴹ ≤ n
    children≤ a a∈ ic =
      ≤-trans (subst (_≤ _) (sym (complexityᴹ _≟_ ic)) (depthΣM-upper a∈))
              (≤-pred (subst (_≤ suc n) (cong depth eq) b))

    -- The membership of a meetand in the canonical meetands of w.
    meetand∈ : (a : CMand (Fin 3)) → a ∈ h ∷ t → ⌊ a ⌋ᴹ ∈ CM w
    meetand∈ a a∈ =
      subst (λ D → ⌊ a ⌋ᴹ ∈ map ⌊_⌋ᴹ (proj₁ (meetandsOfC D) ∷ proj₂ (meetandsOfC D))) (sym eq) (∈-map⁺ ⌊_⌋ᴹ a∈)
      where
      meetandsOfC : CTerm (Fin 3) → CMand (Fin 3) × List (CMand (Fin 3))
      meetandsOfC = Lattices.Free.Canonical.Basic.meetandsOf

    -- Each meetand is a fixed join of smaller complexity, a member of T₁₁; a generator meetand would be fixed.
    meetand-in : (a : CMand (Fin 3)) → a ∈ h ∷ t → IsCanonicalM a → Any (⌊ a ⌋ᴹ ≈ʷ_) T₁₁
    meetand-in (mgen g)       a∈ _            =
      ⊥-elim (moves g (meetand-gen-fixed Ψ Ψ-free inf w fix (meetand∈ (mgen g) a∈)))
    meetand-in (mjoin jh jt)  a∈ (cmjoin ic)  =
      in-T₁₁ n ⌊ mjoin jh jt ⌋ᴹ (children≤ (mjoin jh jt) a∈ (cmjoin ic))
             (fixed-meetand-inflationary Ψ Ψ-free inf w fix (meetand∈ (mjoin jh jt) a∈)
                                         (λ v e′ → gen≉join ic (≈ʷ-sym e′)))

  -- So every fixed point is one of the eleven, and has complexity at most three.
  strict-fixed-in-T₁₁ : (w : LatTerm (Fin 3)) → w [ Ψ ] ≈ʷ w → Any (w ≈ʷ_) T₁₁
  strict-fixed-in-T₁₁ w fix = in-T₁₁ (κ w) w ≤-refl fix

  strict-fixed-complexity : (w : LatTerm (Fin 3)) → w [ Ψ ] ≈ʷ w → κ w ≤ 3
  strict-fixed-complexity w fix =
    let (t , t∈ , e) = find (strict-fixed-in-T₁₁ w fix)
    in subst (_≤ 3) (sym (complexity-resp _≟_ e)) (lookup T₁₁-complexity t∈)
```

#### The descent, with the parent of its last step

The descent of [DeansProblem.Fixed][] is repeated here with one more
output: from a fixed point of complexity `m + 2` it reaches an element `u` of
complexity two fixed by a positive power, and a canonical joinand or meetand
`v` of `u` of complexity one, fixed by a further power
(`descent-pair`{.AgdaFunction}).  Every element lies below `x ∨ y ∨ z` and
above `x ∧ y ∧ z` (`≤-top`{.AgdaFunction}, `bot-≤`{.AgdaFunction}), and
neither is a canonical joinand or meetand of an element of complexity two
(`top-not-child`{.AgdaFunction}, `bot-not-child`{.AgdaFunction}).

```agda
-- The descent, keeping the parent of the last step.
descent-pair : (m : ℕ) (θ : Sub (Fin 3) (Fin 3)) → FreelyGenerates θ
             → (w : LatTerm (Fin 3)) → w [ θ ] ≈ʷ w → κ w ≡ suc (suc m)
             → Σ[ d ∈ ℕ ] Σ[ u ∈ LatTerm (Fin 3) ] Σ[ v ∈ LatTerm (Fin 3) ]
                 u [ iter θ (suc d) ] ≈ʷ u × κ u ≡ 2 × (v ∈ CJ u ⊎ v ∈ CM u) × κ v ≡ 1
descent-pair zero     θ θ-free w fix e =
  pack (child-of-complexity w 1 e)
  where
  -- The fixed point itself is the parent, and its child of complexity one the element.
  pack : (Σ[ c ∈ LatTerm (Fin 3) ] c ∈ CJ w × κ c ≡ 1) ⊎ (Σ[ c ∈ LatTerm (Fin 3) ] c ∈ CM w × κ c ≡ 1)
       → Σ[ d ∈ ℕ ] Σ[ u ∈ LatTerm (Fin 3) ] Σ[ v ∈ LatTerm (Fin 3) ]
           u [ iter θ (suc d) ] ≈ʷ u × κ u ≡ 2 × (v ∈ CJ u ⊎ v ∈ CM u) × κ v ≡ 1
  pack (inj₁ (c , c∈ , κc)) = 0 , w , c , fixed→image θ (freelyGenerates→injective θ θ-free) w fix 1 , e , inj₁ c∈ , κc
  pack (inj₂ (c , c∈ , κc)) = 0 , w , c , fixed→image θ (freelyGenerates→injective θ θ-free) w fix 1 , e , inj₂ c∈ , κc
descent-pair (suc m)  θ θ-free w fix e = step (child-of-complexity w (suc (suc m)) e)
  where
  -- Recurse on the child, under the power that fixes it.
  recurse : (c : LatTerm (Fin 3)) → κ c ≡ suc (suc m) → Σ[ d ∈ ℕ ] c [ iter θ (suc d) ] ≈ʷ c
          → Σ[ d ∈ ℕ ] Σ[ u ∈ LatTerm (Fin 3) ] Σ[ v ∈ LatTerm (Fin 3) ]
              u [ iter θ (suc d) ] ≈ʷ u × κ u ≡ 2 × (v ∈ CJ u ⊎ v ∈ CM u) × κ v ≡ 1
  recurse c κc (d₁ , per) =
    let (d₂ , u , v , fixu , κu , v∈ , κv) =
          descent-pair m (iter θ (suc d₁)) (iter-free θ θ-free (suc d₁)) c per κc
    in d₁ + d₂ * suc d₁ , u , v , ≈ʷ-trans (≡→≈ʷ (sym ([]-iter-* u θ (suc d₁) (suc d₂)))) fixu , κu , v∈ , κv

  step : (Σ[ c ∈ LatTerm (Fin 3) ] c ∈ CJ w × κ c ≡ suc (suc m)) ⊎ (Σ[ c ∈ LatTerm (Fin 3) ] c ∈ CM w × κ c ≡ suc (suc m))
       → Σ[ d ∈ ℕ ] Σ[ u ∈ LatTerm (Fin 3) ] Σ[ v ∈ LatTerm (Fin 3) ]
           u [ iter θ (suc d) ] ≈ʷ u × κ u ≡ 2 × (v ∈ CJ u ⊎ v ∈ CM u) × κ v ≡ 1
  step (inj₁ (c , c∈ , κc)) = recurse c κc (joinand-periodic θ θ-free w fix c∈ (positive-not-gen c (suc m) κc))
  step (inj₂ (c , c∈ , κc)) = recurse c κc (meetand-periodic θ θ-free w fix c∈ (positive-not-gen c (suc m) κc))

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
`fixes-join`{.AgdaFunction}, `Ψ` or `Ψ²` is inflationary; call it `Φ`, again a
positive power of `Θ`.  Either `Φ` fixes a generator, decided by Whitman's
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

    -- Straight: Ψ is inflationary.  Swapped: Ψ² is.
    finish : (ℊ x′ ≤ʷ Ψ x′ × ℊ y′ ≤ʷ Ψ y′) ⊎ (ℊ x′ ≤ʷ Ψ y′ × ℊ y′ ≤ʷ Ψ x′) → Σ[ E ∈ ℕ ] Inflationary (iter Θ (suc E))
    finish (inj₁ (px , py)) = e , inflationary-of Ψ z′ px py z′≤
    finish (inj₂ (px , py)) =
      e + (suc e + 0) , inflationary-of (iter Θ (suc (e + (suc e + 0)))) z′
        (subst (ℊ x′ ≤ʷ_) (sym (square e x′)) (≤ʷ-trans px ([]-mono Ψ py)))
        (subst (ℊ y′ ≤ʷ_) (sym (square e y′)) (≤ʷ-trans py ([]-mono Ψ px)))
        (subst (ℊ z′ ≤ʷ_) (sym (square e z′)) (≤ʷ-trans z′≤ ([]-mono Ψ z′≤)))

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
the iterates (`dual-iter`{.AgdaFunction}).  So a power fixing a meet of two
generators is, for the dual embedding, a power fixing their join, and a
generator fixed by the dual embedding is fixed by the original.

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
```

The theorem assembles the steps: the descent from `u₄` reaches an element
`u` of complexity two fixed by a positive power and a canonical joinand or
meetand `v` of `u` of complexity one, fixed by a further power; `v` is, up to
equality, one of the generators (impossible, by its complexity), the top or
the bottom (impossible, by `top-not-child`{.AgdaFunction} and
`bot-not-child`{.AgdaFunction}), a join of two generators (the join case), or
a meet of two generators (the join case for the dual embedding).

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
```
