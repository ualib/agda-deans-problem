---
layout: default
file: "src/DeansProblem/LengthThree.lagda.md"
title: "DeansProblem.LengthThree module"
date: "2026-10-14"
author: "the agda-lattices development team"
---

### No coherent chain of length three

This is the [DeansProblem.LengthThree][] module of the [agda-lattices][] library.

[the paper]: https://arxiv.org/abs/YYMM.NNNNN

A coherent chain of length three ([DeansProblem.Coherent.Finite][]) is three
proper self-embeddings `Θ₀, Θ₁, Θ₂` of `FL(3)` with `Θ₁ ∘ Θ₀ = Θ₀` and
`Θ₂ ∘ Θ₁ = Θ₁`: `Θ₁` fixes the free triple `Θ₀(x), Θ₀(y), Θ₀(z)` and `Θ₂`
fixes `Θ₁(FL(3))` pointwise.  This module proves that there is none
(`no-coherent₃`{.AgdaFunction}), so that no infinite coherent chain exists
(`no-coherentω`{.AgdaFunction}), and no chain of copies of `FL(3)` in a free
lattice satisfies the recurrence hypothesis under which
[DeansProblem.Coherent.Finite][] extracts a coherent chain of length three
(`no-chain-recurs`{.AgdaFunction}).  That there is none is Theorem G of
[the paper][], Section 8, from which the coherent form of Theorem C draws the
classical conclusion that no such chain exists at all (Theorem H);
[DeansProblem.NoChain][] proves Theorem H with no classical principle.  The
argument:

1.  `Θ₁` fixes a generator, say `z` ([DeansProblem.FixedGenerator][]).
2.  `Θ₂` fixes `z` too, and moves `x` and `y`, else it is the identity.  Since
    `Θ₂` fixes the free triple `Θ₁(x), Θ₁(y), Θ₁(z)`, a positive power of
    `Θ₂`, or of its dual, is inflationary (`inflationary-power`{.AgdaFunction}
    of [DeansProblem.FixedGenerator][]); it still fixes `Θ₁(FL(3))` and
    still moves `x` and `y`.
3.  **Lemma**: every fixed point of an inflationary self-embedding that fixes
    `z` and moves `x` and `y` lies above `c = z ∧ (x ∨ y)`
    (`above-c`{.AgdaFunction}).  By induction on the canonical form: a fixed
    generator is `z`; a fixed canonical join with a meet joinand lies above
    that joinand, which is fixed ([DeansProblem.Inflationary][]) and above
    `c` by induction, and a join of two or more generators lies above `c`;
    the meetands of a fixed canonical meet are `z` or fixed joins, since a
    generator meetand would be fixed (`meetand-gen-fixed`{.AgdaFunction}),
    and each lies above `c`.
4.  So `c ≤ Θ₁(y)`, and `Θ₁(x) ≤ x ∨ y` since `Θ₁` fixes `z`; hence
    `Θ₁(x) ∧ Θ₁(z) ≤ (x ∨ y) ∧ z = c ≤ Θ₁(y)`, which the meet condition of
    Corollary 1.13 of [Freese, Ježek, and Nation (1995)][] forbids for the
    free triple `Θ₁(x), Θ₁(y), Θ₁(z)` (`core`{.AgdaFunction}).

<!--
```agda
{-# OPTIONS --without-K --exact-split --safe #-}

module DeansProblem.LengthThree where

open import Agda.Primitive  using () renaming ( Set to Type )

-- Imports from the Agda Standard Library ---------------------------------------
open import Data.Empty                             using ( ⊥ ; ⊥-elim )
open import Data.Fin.Base                          using ( Fin )
open import Data.Fin.Patterns                      using ( 0F ; 1F ; 2F )
open import Data.Fin.Properties                    using ( _≟_ )
open import Data.List.Base                         using ( List ; [] ; _∷_ ; map ; allFin )
open import Data.List.Membership.Propositional     using ( _∈_ )
open import Data.List.Membership.Propositional.Properties
                                                   using ( ∈-allFin )
open import Data.List.Relation.Unary.All           using ( All ; all? ; lookup )
import Data.List.Relation.Unary.All as All
open import Data.List.Relation.Unary.AllPairs      using ( AllPairs ; _∷_ )
open import Data.List.Relation.Unary.Any           using ( here ; there )
open import Data.Nat.Base                          using ( ℕ ; zero ; suc ; _≤_ ; z≤n ; s≤s )
open import Data.Nat.Properties                    using ( ≤-refl ; ≤-trans ; ≤-pred )
open import Data.Product                           using ( _×_ ; _,_ ; proj₁ ; proj₂ )
open import Data.Sum.Base                          using ( _⊎_ ; inj₁ ; inj₂ ; [_,_]′ )
open import Level                                  using ( Level )
open import Relation.Binary.Definitions            using ( DecidableEquality )
open import Relation.Binary.PropositionalEquality  using ( _≡_ ; _≢_ ; refl ; sym ; cong ; subst )
open import Relation.Nullary                       using ( ¬_ )
open import Relation.Nullary.Decidable             using ( from-yes ; _⊎-dec_ )

-- Imports from the Agda Universal Algebra Library ------------------------------
open import Lattices.Free.Canonical.Algorithm      using ( module Canonicalization )
open import Lattices.Free.Canonical.Basic
  using  ( CTerm ; genᶜ ; joinᶜ ; meetᶜ ; CJand ; jgen ; jmeet ; CMand ; mgen ; mjoin ; ⌊_⌋ ; ⌊_⌋ᴶ ; ⌊_⌋ᴹ
         ; ⋁ᴶ-upper ; ⋀ᴹ-greatest ; ≈ʷ-sym ; ≈ʷ-trans ; IsCanonical ; cjoin ; cmeet
         ; IsCanonicalJ ; cjmeet ; IsCanonicalM ; cmjoin )
open import Lattices.Free.Canonical.Joinands       using ( canonicalJoinands ; canonicalMeetands )
open import Lattices.Free.Canonical.Uniqueness     using ( gen≉join ; gen≉meet )
open import DeansProblem.Chain                     using ( Chain ; iter ; []-iter-sucʳ )
open import DeansProblem.Coherent.Finite           using ( Coherent ; Coherentω ; Recurs ; chain→coherent₃ )
open import Lattices.Free.Complexity               using ( complexity ; complexityᴶ ; complexityᴹ ; depth
                                                         ; depthΣJ-upper ; depthΣM-upper )
open import Lattices.Free.Duality                  using ( dual ; dual-cong )
open import DeansProblem.Fixed                     using ( iter-free ; fixed→image )
open import DeansProblem.FixedGenerator            using ( fixes-generator ; inflationary-power ; dualˢ
                                                         ; dual-free ; dual-misses ; dual-iter )
open import Lattices.Free.Generation               using ( FreelyGenerates ; freelyGenerates→injective
                                                         ; generator-in-image )
open import DeansProblem.Inflationary              using ( Inflationary ; fixed-joinand-inflationary
                                                         ; fixed-meetand-inflationary ; meetand-gen-fixed )
open import DeansProblem.Partition                 using ( other ; other' ; cover₃ ; ∉others₃
                                                         ; module Partition ; fix-two-generators )
open import Lattices.Free.Substitution             using ( Sub ; _[_] ; []-cong ; injective→reflects )
open import Lattices.Free.Term                     using ( LatTerm ; ℊ ; _∧̇_ ; _∨̇_ )
open import Lattices.Free.Whitman                  using ( _≤ʷ_ ; _≈ʷ_ ; ≤ʷ-refl ; ≤ʷ-trans ; ∨≤ ; ≤∧ ; ∧ˡ≤ ; ∧ʳ≤
                                                         ; ℊ≤ℊ ; ℊ≤ℊ-inv ; ℊ≤∨-inv ; module Decision )

open Decision (_≟_ {3}) using ( _≤ʷ?_ )

private variable
  χ : Level
  X : Type χ

private
  κ : LatTerm (Fin 3) → ℕ
  κ = complexity (_≟_ {3})

  CJ CM : LatTerm (Fin 3) → List (LatTerm (Fin 3))
  CJ = canonicalJoinands (_≟_ {3})
  CM = canonicalMeetands (_≟_ {3})

  -- The element c = z ∧ (x ∨ y), for each choice of the generator z.
  c : Fin 3 → LatTerm (Fin 3)
  c z = ℊ z ∧̇ (ℊ (other z) ∨̇ ℊ (other' z))

  -- c lies below every join of two distinct generators: decided.
  c≤join-dec : All (λ z → All (λ g → All (λ g′ → g ≡ g′ ⊎ c z ≤ʷ ℊ g ∨̇ ℊ g′) (allFin 3)) (allFin 3)) (allFin 3)
  c≤join-dec = from-yes (all? (λ z → all? (λ g → all? (λ g′ → g ≟ g′ ⊎-dec c z ≤ʷ? ℊ g ∨̇ ℊ g′) (allFin 3))
                                          (allFin 3)) (allFin 3))

  c≤join : (z g g′ : Fin 3) → g ≢ g′ → c z ≤ʷ ℊ g ∨̇ ℊ g′
  c≤join z g g′ g≢g′ =
    [ (λ e → ⊥-elim (g≢g′ e)) , (λ p → p) ]′ (lookup (lookup (lookup c≤join-dec (∈-allFin z)) (∈-allFin g)) (∈-allFin g′))

  -- The head of an antichain is not below its second member.
  antichain-head : {A : Type} {R : A → A → Type} {u v : A} {us : List A}
                 → AllPairs (λ a b → ¬ R a b × ¬ R b a) (u ∷ v ∷ us) → ¬ R u v
  antichain-head (hd ∷ _) = proj₁ (All.head hd)

  suc≰0 : ∀ {m} → suc m ≤ 0 → ⊥
  suc≰0 ()
```
-->

#### The lemma: fixed points lie above `c`

Fix an inflationary, freely generating `Ψ` that fixes `z` and moves the other
two generators `x = other z` and `y = other' z`.

```agda
module _ (Ψ : Sub (Fin 3) (Fin 3)) (Ψ-free : FreelyGenerates Ψ) (inf : Inflationary Ψ) (z : Fin 3)
         (fixz : Ψ z ≈ʷ ℊ z) (movex : ¬ (Ψ (other z) ≈ʷ ℊ (other z))) (movey : ¬ (Ψ (other' z) ≈ʷ ℊ (other' z))) where
  open Canonicalization (_≟_ {3}) using ( canonical ; canonical-sound ; canonical-isCanonical )

  private
    -- A fixed generator is z.
    fixed-gen : (g : Fin 3) → Ψ g ≈ʷ ℊ g → g ≡ z
    fixed-gen g fixg = [ (λ e → e) , others ]′ (cover₃ z g)
      where
      others : g ∈ other z ∷ other' z ∷ [] → g ≡ z
      others (here refl)          = ⊥-elim (movex fixg)
      others (there (here refl))  = ⊥-elim (movey fixg)
      others (there (there ()))

    -- c lies below z.
    c≤z : c z ≤ʷ ℊ z
    c≤z = ∧ˡ≤ ≤ʷ-refl

  -- Every fixed point lies above c, by induction on a bound for its complexity.
  above-c : (n : ℕ) (w : LatTerm (Fin 3)) → κ w ≤ n → w [ Ψ ] ≈ʷ w → c z ≤ʷ w
  above-c-shape : (n : ℕ) (w : LatTerm (Fin 3)) (C : CTerm (Fin 3)) → canonical w ≡ C → IsCanonical C
          → ⌊ C ⌋ ≈ʷ w → κ w ≤ n → w [ Ψ ] ≈ʷ w → c z ≤ʷ w
  -- A meet joinand of a fixed canonical join of complexity at most n + 1 is fixed, and above c by induction.
  meet-joinand : (n : ℕ) (w : LatTerm (Fin 3)) (h : CJand (Fin 3)) (t : List (CJand (Fin 3)))
               → canonical w ≡ joinᶜ h t → All IsCanonicalJ (h ∷ t) → κ w ≤ suc n → w [ Ψ ] ≈ʷ w
               → (mh : CMand (Fin 3)) (mt : List (CMand (Fin 3))) → jmeet mh mt ∈ h ∷ t → c z ≤ʷ ⌊ jmeet mh mt ⌋ᴶ

  above-c n w b fix = above-c-shape n w (canonical w) refl (canonical-isCanonical w) (canonical-sound w) b fix

  meet-joinand n w h t eq cs b fix mh mt a∈ = recurse (lookup cs a∈)
    where
    joinandsOfC : CTerm (Fin 3) → CJand (Fin 3) × List (CJand (Fin 3))
    joinandsOfC = Lattices.Free.Canonical.Basic.joinandsOf

    -- The joinand has complexity at most n.
    small : IsCanonicalJ (jmeet mh mt) → κ ⌊ jmeet mh mt ⌋ᴶ ≤ n
    small ic =
      ≤-trans (subst (_≤ _) (sym (complexityᴶ _≟_ ic)) (depthΣJ-upper a∈))
              (≤-pred (subst (_≤ suc n) (cong depth eq) b))

    recurse : IsCanonicalJ (jmeet mh mt) → c z ≤ʷ ⌊ jmeet mh mt ⌋ᴶ
    recurse (cjmeet ic) =
      above-c n ⌊ jmeet mh mt ⌋ᴶ (small (cjmeet ic))
              (fixed-joinand-inflationary Ψ Ψ-free inf w fix
                 (subst (λ D → ⌊ jmeet mh mt ⌋ᴶ ∈ map ⌊_⌋ᴶ (proj₁ (joinandsOfC D) ∷ proj₂ (joinandsOfC D)))
                        (sym eq) (Data.List.Membership.Propositional.Properties.∈-map⁺ ⌊_⌋ᴶ a∈))
                 (λ v e′ → gen≉meet ic (≈ʷ-sym e′)))

  above-c-shape n        w (genᶜ g)     eq _                    e b fix =
    ≤ʷ-trans c≤z (subst (λ u → ℊ u ≤ʷ w) (fixed-gen g (≈ʷ-trans (≈ʷ-sym ([]-cong Ψ (≈ʷ-sym e))) (≈ʷ-trans fix (≈ʷ-sym e))))
                        (proj₁ e))
  above-c-shape zero     w (joinᶜ h t)  eq _                    e b fix = ⊥-elim (suc≰0 (subst (_≤ 0) (cong depth eq) b))
  above-c-shape zero     w (meetᶜ h t)  eq _                    e b fix = ⊥-elim (suc≰0 (subst (_≤ 0) (cong depth eq) b))
  -- A join: through a meet joinand, or through two distinct generator joinands.
  above-c-shape (suc n)  w (joinᶜ (jmeet mh mt) t)             eq (cjoin ne cs ac c4)  e b fix =
    ≤ʷ-trans (≤ʷ-trans (meet-joinand n w (jmeet mh mt) t eq cs b fix mh mt (here refl))
                       (⋁ᴶ-upper {h = jmeet mh mt} {t = t} (here refl))) (proj₁ e)
  above-c-shape (suc n)  w (joinᶜ (jgen g) [])                 eq (cjoin ne cs ac c4)  e b fix = ⊥-elim (ne refl)
  above-c-shape (suc n)  w (joinᶜ (jgen g) (jmeet mh mt ∷ t′)) eq (cjoin ne cs ac c4)  e b fix =
    ≤ʷ-trans (≤ʷ-trans (meet-joinand n w (jgen g) (jmeet mh mt ∷ t′) eq cs b fix mh mt (there (here refl)))
                       (⋁ᴶ-upper {h = jgen g} {t = jmeet mh mt ∷ t′} (there (here refl)))) (proj₁ e)
  above-c-shape (suc n)  w (joinᶜ (jgen g) (jgen g′ ∷ t′))     eq (cjoin ne cs ac c4)  e b fix =
    ≤ʷ-trans (≤ʷ-trans (c≤join z g g′ (λ e′ → antichain-head ac (ℊ≤ℊ e′)))
                       (∨≤ (⋁ᴶ-upper {h = jgen g} {t = jgen g′ ∷ t′} (here refl))
                           (⋁ᴶ-upper {h = jgen g} {t = jgen g′ ∷ t′} (there (here refl))))) (proj₁ e)
  above-c-shape (suc n)  w (meetᶜ h t)  eq (cmeet _ cs _ _)     e b fix =
    ≤ʷ-trans (⋀ᴹ-greatest (λ {a} a∈ → meetand a a∈ (lookup cs a∈))) (proj₁ e)
    where
    children≤ : (a : CMand (Fin 3)) → a ∈ h ∷ t → IsCanonicalM a → κ ⌊ a ⌋ᴹ ≤ n
    children≤ a a∈ ic =
      ≤-trans (subst (_≤ _) (sym (complexityᴹ _≟_ ic)) (depthΣM-upper a∈))
              (≤-pred (subst (_≤ suc n) (cong depth eq) b))

    meetand∈ : (a : CMand (Fin 3)) → a ∈ h ∷ t → ⌊ a ⌋ᴹ ∈ CM w
    meetand∈ a a∈ =
      subst (λ D → ⌊ a ⌋ᴹ ∈ map ⌊_⌋ᴹ (proj₁ (meetandsOfC D) ∷ proj₂ (meetandsOfC D))) (sym eq)
            (Data.List.Membership.Propositional.Properties.∈-map⁺ ⌊_⌋ᴹ a∈)
      where
      meetandsOfC : CTerm (Fin 3) → CMand (Fin 3) × List (CMand (Fin 3))
      meetandsOfC = Lattices.Free.Canonical.Basic.meetandsOf

    -- A generator meetand is z; a join meetand is fixed, and above c by induction.
    meetand : (a : CMand (Fin 3)) → a ∈ h ∷ t → IsCanonicalM a → c z ≤ʷ ⌊ a ⌋ᴹ
    meetand (mgen g)       a∈ _            =
      subst (λ u → c z ≤ʷ ℊ u) (sym (fixed-gen g (meetand-gen-fixed Ψ Ψ-free inf w fix (meetand∈ (mgen g) a∈)))) c≤z
    meetand (mjoin jh jt)  a∈ (cmjoin ic)  =
      above-c n ⌊ mjoin jh jt ⌋ᴹ (children≤ (mjoin jh jt) a∈ (cmjoin ic))
              (fixed-meetand-inflationary Ψ Ψ-free inf w fix (meetand∈ (mjoin jh jt) a∈)
                                          (λ v e′ → gen≉join ic (≈ʷ-sym e′)))

  -- So every fixed point lies above c.
  fixed-above-c : (w : LatTerm (Fin 3)) → w [ Ψ ] ≈ʷ w → c z ≤ʷ w
  fixed-above-c w fix = above-c (κ w) w ≤-refl fix
```

#### The contradiction

Let `Θ₁` be a proper self-embedding fixing `z`, and let an inflationary,
proper `Ψ` fix `Θ₁(x)`, `Θ₁(y)` and `Θ₁(z)`.  Then `Ψ` fixes `z` and moves
`x` and `y`; `Θ₁(x) ∧ Θ₁(z) ≤ c ≤ Θ₁(y)`, against the meet condition.

```agda
module _ (Θ₁ : Sub (Fin 3) (Fin 3)) (Θ₁-free : FreelyGenerates Θ₁) (z : Fin 3) (fixz₁ : Θ₁ z ≈ʷ ℊ z)
         (Ψ : Sub (Fin 3) (Fin 3)) (Ψ-free : FreelyGenerates Ψ) (inf : Inflationary Ψ)
         (m : Fin 3) (m∉ : ∀ i → ¬ (ℊ m ≈ʷ Ψ i)) (Ψ-fixes : ∀ i → Θ₁ i [ Ψ ] ≈ʷ Θ₁ i) where
  private
    x y : Fin 3
    x = other z
    y = other' z

    x≢z : x ≢ z
    x≢z e = ∉others₃ z (here (sym e))

    y≢z : y ≢ z
    y≢z e = ∉others₃ z (there (here (sym e)))

    y≢x : y ≢ x
    y≢x = other'≢other z
      where
      other'≢other : ∀ z′ → other' z′ ≢ other z′
      other'≢other 0F ()
      other'≢other 1F ()
      other'≢other 2F ()

    -- Ψ fixes z.
    fixz : Ψ z ≈ʷ ℊ z
    fixz = ≈ʷ-trans ([]-cong Ψ (≈ʷ-sym fixz₁)) (≈ʷ-trans (Ψ-fixes z) fixz₁)

    -- And moves x and y, else it would be the identity and miss no generator.
    movex : ¬ (Ψ x ≈ʷ ℊ x)
    movex fixx = m∉ m (≈ʷ-sym (fix-two-generators Ψ Ψ-free x≢z fixx fixz m))

    movey : ¬ (Ψ y ≈ʷ ℊ y)
    movey fixy = m∉ m (≈ʷ-sym (fix-two-generators Ψ Ψ-free y≢z fixy fixz m))

    -- Θ₁(x) lies below x ∨ y, by the partition at z: otherwise z = Θ₁(z) ≤ Θ₁(x ∨ y), so z ≤ x ∨ y.
    open Partition z x (y ∷ []) (cover₃ z) (∉others₃ z)

    a≤xy : Θ₁ x ≤ʷ ℊ x ∨̇ ℊ y
    a≤xy = [ (λ p → ≤ʷ-trans (≤ʷ-trans (ℊ≤∨ˡ′) p) ≤ʷ-refl) , (λ q → ⊥-elim (below q)) ]′ (partition (Θ₁ x ∨̇ Θ₁ y))
      where
      ℊ≤∨ˡ′ : Θ₁ x ≤ʷ Θ₁ x ∨̇ Θ₁ y
      ℊ≤∨ˡ′ = Lattices.Free.Whitman.∨̇-upperˡ

      below : ℊ z ≤ʷ Θ₁ x ∨̇ Θ₁ y → ⊥
      below q =
        [ (λ e → x≢z (sym (ℊ≤ℊ-inv e))) , (λ e → y≢z (sym (ℊ≤ℊ-inv e))) ]′
          (ℊ≤∨-inv (injective→reflects Θ₁ {s = ℊ z} {t = ℊ x ∨̇ ℊ y} (freelyGenerates→injective Θ₁ Θ₁-free)
                      (≤ʷ-trans (proj₁ fixz₁) q)))

  -- The contradiction.
  core : ⊥
  core = [ y≢x , y≢z ]′ (nothing (proj₂ Θ₁-free {y} {x ∷ z ∷ []} a∧z≤b))
    where
    -- Θ₁(x) ∧ Θ₁(z) ≤ (x ∨ y) ∧ z = c ≤ Θ₁(y).
    a∧z≤b : Θ₁ x ∧̇ Θ₁ z ≤ʷ Θ₁ y
    a∧z≤b = ≤ʷ-trans (≤∧ (∧ʳ≤ (proj₁ fixz₁)) (∧ˡ≤ a≤xy))
                     (fixed-above-c Ψ Ψ-free inf z fixz movex movey (Θ₁ y) (Ψ-fixes y))

    -- The meet condition puts y among x and z.
    nothing : y ∈ x ∷ z ∷ [] → y ≡ x ⊎ y ≡ z
    nothing (here p)          = inj₁ p
    nothing (there (here p))  = inj₂ p
    nothing (there (there ()))
```

#### No coherent chain of length three

```agda
module _ (Θ₁ : Sub (Fin 3) (Fin 3)) (Θ₁-free : FreelyGenerates Θ₁) (m′ : Fin 3) (m′∉ : ∀ i → ¬ (ℊ m′ ≈ʷ Θ₁ i))
         (τ : Sub (Fin 3) (Fin 3)) (τ-free : FreelyGenerates τ) (τ-fixed : ∀ i → τ i [ Θ₁ ] ≈ʷ τ i)
         (Φ : Sub (Fin 3) (Fin 3)) (Φ-free : FreelyGenerates Φ) (m : Fin 3) (m∉ : ∀ i → ¬ (ℊ m ≈ʷ Φ i))
         (Φ-fixes : ∀ i → Θ₁ i [ Φ ] ≈ʷ Θ₁ i) where
  private
    -- A positive power of a self-embedding that misses a generator misses it too.
    power-misses : (σ : Sub (Fin 3) (Fin 3)) → (∀ i → ¬ (ℊ m ≈ʷ σ i)) → (E : ℕ) → ∀ i → ¬ (ℊ m ≈ʷ iter σ (suc E) i)
    power-misses σ σ∉ E i e =
      let (j , e′) = generator-in-image σ (iter σ E i) (subst (ℊ m ≈ʷ_) ([]-iter-sucʳ (ℊ i) σ E) e) in σ∉ j e′

  -- No proper self-embedding fixes the image of a self-embedding with a fixed free triple.
  no-upper-link : ⊥
  no-upper-link =
    let (z , fixz₁) = fixes-generator Θ₁ Θ₁-free m′ m′∉ τ τ-free τ-fixed
    in [ (λ (E , infΨ) →
            core Θ₁ Θ₁-free z fixz₁ (iter Φ (suc E)) (iter-free Φ Φ-free (suc E)) infΨ m (power-misses Φ m∉ E)
                 (λ i → fixed→image Φ (freelyGenerates→injective Φ Φ-free) (Θ₁ i) (Φ-fixes i) (suc E)))
       , (λ (E , infΨ) →
            core (dualˢ Θ₁) (dual-free Θ₁ Θ₁-free) z (dual-cong fixz₁)
                 (iter (dualˢ Φ) (suc E)) (iter-free (dualˢ Φ) (dual-free Φ Φ-free) (suc E)) infΨ
                 m (power-misses (dualˢ Φ) (dual-misses Φ m m∉) E)
                 (λ i → subst (_≈ʷ dual (Θ₁ i)) (dual-iter (Θ₁ i) Φ (suc E))
                              (dual-cong (fixed→image Φ (freelyGenerates→injective Φ Φ-free) (Θ₁ i) (Φ-fixes i) (suc E))))) ]′
       (inflationary-power Φ Φ-free m m∉ Θ₁ Θ₁-free Φ-fixes)

-- There is no coherent chain of length three.
no-coherent₃ : Coherent 3 → ⊥
no-coherent₃ C =
  no-upper-link (Θ 1F) (Θ-free 1F) (missed 1F) (missed∉ 1F) (Θ 0F) (Θ-free 0F) (coherent (s≤s z≤n))
                (Θ 2F) (Θ-free 2F) (missed 2F) (missed∉ 2F) (coherent (s≤s (s≤s z≤n)))
  where open Coherent C

-- Hence no infinite coherent chain.
no-coherentω : Coherentω → ⊥
no-coherentω C = no-coherent₃ (Coherentω.prefix C 3)

-- And no chain of copies of FL(3) whose transition from the bottom to some link recurs beyond every bound.
no-chain-recurs : (_≟ˣ_ : DecidableEquality X) (c : Chain X) (j : ℕ) → Recurs _≟ˣ_ c j → ⊥
no-chain-recurs _≟ˣ_ c j R = no-coherent₃ (chain→coherent₃ _≟ˣ_ c j R)
```
