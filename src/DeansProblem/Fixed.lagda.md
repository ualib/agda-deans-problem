---
layout: default
file: "src/DeansProblem/Fixed.lagda.md"
title: "DeansProblem.Fixed module"
date: "2026-10-14"
author: "the agda-lattices development team"
---

### Fixed points of a self-embedding of a free lattice

This is the [DeansProblem.Fixed][] module of this repository.

[the paper]: https://arxiv.org/abs/YYMM.NNNNN

Let `θ` be an injective endomorphism of `FL(n)`.  This module proves three facts
about the elements it fixes, which are the elements `w` with `θ(w) = w`, and
about the elements it moves periodically.

+  **Periodic points are the elements in every image**
  (`image→periodic`{.AgdaFunction}, `periodic→image`{.AgdaFunction}).  If `m`
  lies in the image of every iterate `θᵏ`, say `m = θᵏ(mₖ)`, then
  `complexity mₖ ≤ complexity m` because `θᵏ` is an embedding
  ([Lattices.Free.Complexity][]), so the `mₖ` take finitely many values and
  `mₐ = m_b` for some `a < b`; injectivity of `θᵃ` then gives
  `m_b = θᵇ⁻ᵃ(m_b)`, and applying `θᵇ` gives `m = θᵇ⁻ᵃ(m)`.  Conversely an
  element fixed by `θᵈ` with `d ≥ 1` is fixed by every `θᵈᵏ`, and so lies in the
  image of every iterate.  A fixed point is in every image at once
  (`fixed→image`{.AgdaFunction}).  So the fixed sublattice of `θ` lies in the
  intersection of the descending chain `FL(n) ⊇ θ(FL(n)) ⊇ θ²(FL(n)) ⊇ ⋯`, which
  is exactly the set of periodic points.
+  **A power of `θ` fixes each non-generator canonical joinand of a fixed
  point** (`joinand-periodic`{.AgdaFunction}, dually
  `meetand-periodic`{.AgdaFunction}).  If `θ(w) = w` and `c` is a canonical
  joinand of `w` that is not a generator, Lemma 9.13 of [Freese, Ježek, and
  Nation (1995)][] (`embedding-canonicalJoinand`{.AgdaFunction} of
  [Lattices.Free.Embedding][]) makes `θ(c)` a canonical joinand of
  `θ(w) = w`, again not a generator, so the whole orbit of `c` stays among the
  finitely many canonical joinands of `w` (`joinand-orbit`{.AgdaFunction}),
  repeats, and the repeat is a period as above.  Reading "canonical joinand of
  `θ(w)`" as "canonical joinand of `w`" needs the canonical joinands of equal
  elements to agree up to equality, which is Theorem 1.17 in list form
  (`canonicalJoinand-resp`{.AgdaFunction} of
  [Lattices.Free.Canonical.Joinands][]).
+  **The descent** (`descent`{.AgdaFunction}).  A fixed point `w` of positive
  complexity has a canonical joinand or meetand of complexity exactly one less,
  which is not a generator when that complexity is positive and is then fixed by
  a power of `θ`; descending one level at a time ends at an element of
  complexity 1, a join or a meet of two or more generators, fixed by a power of
  `θ`.  Every power `θᵈ` with `d ≥ 1` of a proper self-embedding is proper and
  injective, so the fixed-sublattice question of [DeansProblem.Coherent][]
  reduces to self-embeddings that fix a join or a meet of generators.

<!--
```agda
{-# OPTIONS --without-K --exact-split --safe #-}

module DeansProblem.Fixed where

open import Agda.Primitive  using () renaming ( Set to Type )

-- Imports from the Agda Standard Library ---------------------------------------
open import Data.Fin.Base                          using ( Fin )
open import Data.Fin.Properties                    using ( _≟_ )
open import Data.List.Base                         using ( List ; [] ; _∷_ ; allFin ; map )
open import Data.List.Membership.Propositional     using ( _∈_ ; find ; lose )
open import Data.List.Membership.Propositional.Properties
                                                   using ( ∈-allFin ; ∈-map⁺ )
open import Data.List.Relation.Unary.All           using ( lookup )
open import Data.List.Relation.Unary.Any           using ( Any ; here ; there )
open import Data.Nat.Base                          using ( ℕ ; zero ; suc ; _+_ ; _*_ ; _⊔_ ; _≤_ ; _<_
                                                         ; s≤s )
open import Data.Nat.Properties                    using ( ≤-trans ; ≤-reflexive ; ≤-total ; +-comm
                                                         ; m≤n⇒∃[o]m+o≡n ; m≤m*n ; 0≢1+n
                                                         ; suc-injective ; m≤n⇒m⊔n≡n ; m≥n⇒m⊔n≡m )
open import Data.Product                           using ( Σ-syntax ; _×_ ; _,_ ; proj₁ ; proj₂ )
open import Data.Sum.Base                          using ( _⊎_ ; inj₁ ; inj₂ ; [_,_]′ )
open import Function                               using ( _⇔_ ; mk⇔ ; _∘_ )
open import Level                                  using ( Level )
open import Relation.Binary.PropositionalEquality  using ( _≡_ ; refl ; sym ; trans ; cong ; subst )
open import Relation.Nullary                       using ( ¬_ )

import Data.List.Relation.Unary.Any as Any

-- Imports from the Agda Universal Algebra Library ------------------------------
open import Lattices.Free.Canonical.Algorithm      using ( module Canonicalization )
open import Lattices.Free.Canonical.Basic
  using  ( CTerm ; genᶜ ; joinᶜ ; meetᶜ ; CJand ; CMand ; ⌊_⌋ ; ⌊_⌋ᴶ
         ; ⌊_⌋ᴹ ; ≈ʷ-refl ; ≈ʷ-sym ; ≈ʷ-trans ; IsCanonical ; cjoin ; cmeet ; asListJ ; asListM
         ; joinandsOf ; meetandsOf )
open import Lattices.Free.Canonical.Joinands       using ( canonicalJoinands ; canonicalMeetands
                                                         ; canonicalJoinand-resp ; canonicalMeetand-resp )
open import DeansProblem.Chain                     using ( iter ; []-iter-suc ; []-iter-sucʳ ; []-iter-+
                                                         ; iter-injective )
open import Lattices.Free.Complexity
  using  ( complexity ; complexity-resp ; complexity-mono ; complexityᴶ ; complexityᴹ ; depth ; depthJ
         ; depthM ; depthΣJ ; depthΣM ; module Bounded ; pigeonhole-≈ ; image-gen )
open import Lattices.Free.Embedding                using ( embedding-canonicalJoinand
                                                         ; embedding-canonicalMeetand )
open import Lattices.Free.Generation               using ( FreelyGenerates ; freelyGenerates→injective
                                                         ; injective→freelyGenerates )
open import Lattices.Free.Substitution             using ( Sub ; _[_] ; []-ℊ ; []-cong
                                                         ; subst-hom )
open import Lattices.Free.Term                     using ( LatTerm ; ℊ )
open import Lattices.Free.Whitman                  using ( _≈ʷ_ )
open import Setoid.Functions                       using ( IsInjective )

private variable
  χ : Level
  X : Type χ

private
  -- An equation of lattice terms, read as an equality in the free lattice.
  ≡→≈ʷ : {s t : LatTerm X} → s ≡ t → s ≈ʷ t
  ≡→≈ʷ {s = s} e = subst (s ≈ʷ_) e ≈ʷ-refl
```
-->

#### Iterates of iterates

An iterate of an iterate is an iterate (`[]-iter-*`{.AgdaFunction}): applying
`(σᵐ)ⁿ` is applying `σ^(n·m)`, by induction on `n` through
`[]-iter-+`{.AgdaFunction}.  The descent composes periods this way.

```agda
-- Iterates multiply: the n-th iterate of the m-th is the (n · m)-th.
[]-iter-* : (t : LatTerm X) (σ : Sub X X) (m n : ℕ) → t [ iter (iter σ m) n ] ≡ t [ iter σ (n * m) ]
[]-iter-* t σ m zero     = refl
[]-iter-* t σ m (suc n)  =
  trans ([]-iter-suc t (iter σ m) n)
        (trans ([]-iter-* (t [ iter σ m ]) σ m n) (sym ([]-iter-+ t σ m (n * m))))
```

#### Periodic points

Fix an injective `θ : Sub (Fin n) (Fin n)`.  An element `m` that is in the image
of every iterate is fixed by some positive iterate (`image→periodic`{.AgdaFunction}).
The preimages `mₖ` have complexity at most that of `m` (`complexity-mono`{.AgdaFunction}
for the embedding `θᵏ`), so they lie in the finite list `bounded`{.AgdaFunction}
and two of them agree: `mₐ ≈ʷ m_b` with `b = (d + 1) + a`.  Then
`mₐ [ θᵃ ] ≈ʷ m ≈ʷ m_b [ θᵇ ] ≡ m_b [ θᵈ⁺¹ ] [ θᵃ ]`, so `mₐ ≈ʷ m_b [ θᵈ⁺¹ ]` by
injectivity of `θᵃ`, that is, `m_b [ θᵈ⁺¹ ] ≈ʷ m_b`.  Then
`m [ θᵈ⁺¹ ] ≈ʷ m_b [ θᵇ ] [ θᵈ⁺¹ ] ≡ m_b [ θᵈ⁺¹ ] [ θᵃ ] [ θᵈ⁺¹ ] ≈ʷ m_b [ θᵃ ] [ θᵈ⁺¹ ] ≡ m_b [ θᵇ ] ≈ʷ m`,
since iterates commute (`[]-iter-+`{.AgdaFunction} both ways).

```agda
module _ {n : ℕ} (θ : Sub (Fin n) (Fin n)) (θ-inj : IsInjective (proj₁ (subst-hom θ))) where
  open Bounded (_≟_ {n}) (allFin n) ∈-allFin using ( bounded ; bounded-complete )

  private
    -- Complexity in FL(n).
    κ : LatTerm (Fin n) → ℕ
    κ = complexity (_≟_ {n})

  -- A fixed point is in the image of every iterate.
  fixed→image : (m : LatTerm (Fin n)) → m [ θ ] ≈ʷ m → ∀ k → m [ iter θ k ] ≈ʷ m
  fixed→image m e zero     = ≡→≈ʷ ([]-ℊ m)
  fixed→image m e (suc k)  =
    ≈ʷ-trans (≡→≈ʷ ([]-iter-sucʳ m θ k)) (≈ʷ-trans ([]-cong θ (fixed→image m e k)) e)

  -- An element in the image of every iterate is fixed by a positive iterate.
  image→periodic : (m : LatTerm (Fin n)) (pre : ℕ → LatTerm (Fin n)) → (∀ k → pre k [ iter θ k ] ≈ʷ m)
                 → Σ[ d ∈ ℕ ] m [ iter θ (suc d) ] ≈ʷ m
  image→periodic m pre e =
    let (a , b , a<b , r) = pigeonhole-≈ (bounded (κ m)) pre
                              (λ k → bounded-complete (κ m) (pre k) (pre-bound k))
        (d , a+d≡b) = m≤n⇒∃[o]m+o≡n a<b
        b≡ : b ≡ suc d + a
        b≡ = trans (sym a+d≡b) (cong suc (+-comm a d))
        -- m_b [ θᵇ ] ≡ m_b [ θᵈ⁺¹ ] [ θᵃ ], and likewise with the iterates the other way round.
        split : pre b [ iter θ b ] ≡ pre b [ iter θ (suc d) ] [ iter θ a ]
        split = trans (cong (λ k → pre b [ iter θ k ]) b≡) ([]-iter-+ (pre b) θ (suc d) a)
        split' : pre b [ iter θ b ] ≡ pre b [ iter θ a ] [ iter θ (suc d) ]
        split' = trans (cong (λ k → pre b [ iter θ k ]) (trans b≡ (+-comm (suc d) a)))
                       ([]-iter-+ (pre b) θ a (suc d))
        -- mₐ ≈ʷ m_b [ θᵈ⁺¹ ], by injectivity of θᵃ.
        shift : pre a ≈ʷ pre b [ iter θ (suc d) ]
        shift = iter-injective θ θ-inj a
                  (≈ʷ-trans (e a) (≈ʷ-trans (≈ʷ-sym (e b)) (≡→≈ʷ split)))
    in d , ≈ʷ-trans ([]-cong (iter θ (suc d)) (≈ʷ-sym (e b)))
             (≈ʷ-trans (≡→≈ʷ (cong (_[ iter θ (suc d) ]) split))
               (≈ʷ-trans ([]-cong (iter θ (suc d)) ([]-cong (iter θ a) (≈ʷ-trans (≈ʷ-sym shift) r)))
                 (≈ʷ-trans (≡→≈ʷ (sym split')) (e b))))
    where
    -- Each preimage has at most the complexity of m.
    pre-bound : ∀ k → κ (pre k) ≤ κ m
    pre-bound k = ≤-trans (complexity-mono _≟_ _≟_ (iter θ k) (iter-injective θ θ-inj k) (pre k))
                          (≤-reflexive (complexity-resp _≟_ (e k)))
```

The converse: an element fixed by `θᵈ⁺¹` is fixed by every `θ^(k·(d+1))`
(`periodic→fixed-multiples`{.AgdaFunction}), and since `k ≤ k · (d + 1)`, it is in
the image of `θᵏ` (`periodic→image`{.AgdaFunction}): `m ≈ʷ m [ θ^(k·(d+1)) ] ≡
m [ θ^(k·(d+1) − k) ] [ θᵏ ]`.

```agda
  -- An element fixed by a positive iterate is fixed by all its multiples.
  periodic→fixed-multiples : (m : LatTerm (Fin n)) (d : ℕ) → m [ iter θ (suc d) ] ≈ʷ m
                           → ∀ k → m [ iter θ (k * suc d) ] ≈ʷ m
  periodic→fixed-multiples m d e zero     = ≡→≈ʷ ([]-ℊ m)
  periodic→fixed-multiples m d e (suc k)  =
    ≈ʷ-trans (≡→≈ʷ ([]-iter-+ m θ (suc d) (k * suc d)))
             (≈ʷ-trans ([]-cong (iter θ (k * suc d)) e) (periodic→fixed-multiples m d e k))

  -- An element fixed by a positive iterate is in the image of every iterate.
  periodic→image : (m : LatTerm (Fin n)) (d : ℕ) → m [ iter θ (suc d) ] ≈ʷ m
                 → ∀ k → Σ[ mₖ ∈ LatTerm (Fin n) ] mₖ [ iter θ k ] ≈ʷ m
  periodic→image m d e k =
    let (o , k+o≡kd) = m≤n⇒∃[o]m+o≡n (m≤m*n k (suc d))
    in m [ iter θ o ] ,
       ≈ʷ-trans (≡→≈ʷ (sym ([]-iter-+ m θ o k)))
         (≈ʷ-trans (≡→≈ʷ (cong (λ j → m [ iter θ j ]) (trans (+-comm o k) k+o≡kd)))
                   (periodic→fixed-multiples m d e k))
```

**Corollary A4** of [the paper][], as one statement: for an injective
endomorphism `θ` of `FL(n)`, an element `m` lies in every image `θᵏ(FL(n))`
exactly when some positive power of `θ` fixes it.

```agda
-- Corollary A4: the intersection of the images θᵏ(FL(n)) is the set of periodic points of θ.
Corollary-A4 : Type
Corollary-A4 =  (n : ℕ) (θ : Sub (Fin n) (Fin n)) → IsInjective (proj₁ (subst-hom θ))
                → (m : LatTerm (Fin n))
                → (∀ k → Σ[ mₖ ∈ LatTerm (Fin n) ] mₖ [ iter θ k ] ≈ʷ m)
                  ⇔ (Σ[ d ∈ ℕ ] m [ iter θ (suc d) ] ≈ʷ m)

-- The proof of Corollary A4.
corollary-A4 : Corollary-A4
corollary-A4 n θ θ-inj m =
  mk⇔ (λ pre → image→periodic θ θ-inj m (proj₁ ∘ pre) (proj₂ ∘ pre))
      (λ (d , per) → periodic→image θ θ-inj m d per)
```

#### The canonical joinands of a fixed point

Now let `θ` freely generate (equivalently, be injective) and fix `w`.  A
non-generator canonical joinand `c` of `w` has an image `c [ θ ]` that is, up to
equality, a canonical joinand of `w [ θ ]`, hence of `w`
(`fixed-joinand`{.AgdaFunction}), and that image is not a generator either
(`image-gen`{.AgdaFunction} of [Lattices.Free.Complexity][]).  So every iterate
`c [ θᵏ ]` is a non-generator canonical joinand of `w` up to equality
(`joinand-orbit`{.AgdaFunction}), by induction on `k`.  The orbit lies in the
finite list `canonicalJoinands w`, so it repeats, and as for periodic points a
repeat `c [ θᵃ ] ≈ʷ c [ θᵇ ]` with `b = (d + 1) + a` gives `c ≈ʷ c [ θᵈ⁺¹ ]` by
injectivity of `θᵃ` (`joinand-periodic`{.AgdaFunction}).  Meetands are dual.

```agda
module _ {n : ℕ} (θ : Sub (Fin n) (Fin n)) (θ-free : FreelyGenerates θ) where
  open Canonicalization (_≟_ {n}) using ( canonical ; canonical-isCanonical )

  private
    θ-inj : IsInjective (proj₁ (subst-hom θ))
    θ-inj = freelyGenerates→injective θ θ-free

    -- Complexity in FL(n).
    κ : LatTerm (Fin n) → ℕ
    κ = complexity (_≟_ {n})

    -- The canonical joinands and meetands, over Fin n.
    CJ CM : LatTerm (Fin n) → List (LatTerm (Fin n))
    CJ = canonicalJoinands (_≟_ {n})
    CM = canonicalMeetands (_≟_ {n})

    -- A non-generator up to equality.
    NotGen : LatTerm (Fin n) → Type
    NotGen c = ∀ x → ¬ (c ≈ʷ ℊ x)

    -- Equal terms are non-generators together; the image of a non-generator is one.
    NotGen-resp : {c c' : LatTerm (Fin n)} → c ≈ʷ c' → NotGen c → NotGen c'
    NotGen-resp e ng x e' = ng x (≈ʷ-trans e e')

    NotGen-image : (c : LatTerm (Fin n)) → NotGen c → NotGen (c [ θ ])
    NotGen-image c ng y e = let (x , e') = image-gen _≟_ _≟_ θ θ-inj c e in ng x e'

  -- The image of a non-generator canonical joinand of a fixed point is a canonical joinand of it.
  fixed-joinand : (w : LatTerm (Fin n)) → w [ θ ] ≈ʷ w → {c : LatTerm (Fin n)} → c ∈ CJ w → NotGen c
                → Any (c [ θ ] ≈ʷ_) (CJ w)
  fixed-joinand w fix c∈ ng =
    canonicalJoinand-resp _≟_ fix (embedding-canonicalJoinand _≟_ _≟_ θ θ-inj w c∈ ng)

  fixed-meetand : (w : LatTerm (Fin n)) → w [ θ ] ≈ʷ w → {c : LatTerm (Fin n)} → c ∈ CM w → NotGen c
                → Any (c [ θ ] ≈ʷ_) (CM w)
  fixed-meetand w fix c∈ ng =
    canonicalMeetand-resp _≟_ fix (embedding-canonicalMeetand _≟_ _≟_ θ θ-inj w c∈ ng)

  -- The orbit of a non-generator canonical joinand of a fixed point stays among its canonical joinands.
  joinand-orbit : (w : LatTerm (Fin n)) → w [ θ ] ≈ʷ w → {c : LatTerm (Fin n)} → c ∈ CJ w → NotGen c
                → ∀ k → Any (λ c' → c [ iter θ k ] ≈ʷ c' × NotGen c') (CJ w)
  joinand-orbit w fix {c} c∈ ng zero     = lose c∈ (≡→≈ʷ ([]-ℊ c) , ng)
  joinand-orbit w fix {c} c∈ ng (suc k)  =
    let (c' , c'∈ , e , ng') = find (joinand-orbit w fix c∈ ng k)
        (c″ , c″∈ , e') = find (fixed-joinand w fix c'∈ ng')
        step : c [ iter θ (suc k) ] ≈ʷ c″
        step = ≈ʷ-trans (≡→≈ʷ ([]-iter-sucʳ c θ k)) (≈ʷ-trans ([]-cong θ e) e')
    in lose c″∈ (step , NotGen-resp e' (NotGen-image c' ng'))

  meetand-orbit : (w : LatTerm (Fin n)) → w [ θ ] ≈ʷ w → {c : LatTerm (Fin n)} → c ∈ CM w → NotGen c
                → ∀ k → Any (λ c' → c [ iter θ k ] ≈ʷ c' × NotGen c') (CM w)
  meetand-orbit w fix {c} c∈ ng zero     = lose c∈ (≡→≈ʷ ([]-ℊ c) , ng)
  meetand-orbit w fix {c} c∈ ng (suc k)  =
    let (c' , c'∈ , e , ng') = find (meetand-orbit w fix c∈ ng k)
        (c″ , c″∈ , e') = find (fixed-meetand w fix c'∈ ng')
        step : c [ iter θ (suc k) ] ≈ʷ c″
        step = ≈ʷ-trans (≡→≈ʷ ([]-iter-sucʳ c θ k)) (≈ʷ-trans ([]-cong θ e) e')
    in lose c″∈ (step , NotGen-resp e' (NotGen-image c' ng'))
```

A repeat along an orbit is a period (`repeat→period`{.AgdaFunction}), and so a
non-generator canonical joinand or meetand of a fixed point is fixed by a positive
power of `θ` (`joinand-periodic`{.AgdaFunction}, `meetand-periodic`{.AgdaFunction}).

```agda
  -- A repeat c [ θᵃ ] ≈ʷ c [ θᵇ ], a < b, is a period of c.
  repeat→period : (c : LatTerm (Fin n)) (a b : ℕ) → a < b → c [ iter θ a ] ≈ʷ c [ iter θ b ]
                → Σ[ d ∈ ℕ ] c [ iter θ (suc d) ] ≈ʷ c
  repeat→period c a b a<b e =
    let (d , a+d≡b) = m≤n⇒∃[o]m+o≡n a<b
        b≡ : b ≡ suc d + a
        b≡ = trans (sym a+d≡b) (cong suc (+-comm a d))
        e' : c [ iter θ a ] ≈ʷ c [ iter θ (suc d) ] [ iter θ a ]
        e' = subst (c [ iter θ a ] ≈ʷ_)
                   (trans (cong (λ k → c [ iter θ k ]) b≡) ([]-iter-+ c θ (suc d) a)) e
    in d , ≈ʷ-sym (iter-injective θ θ-inj a e')

  -- A non-generator canonical joinand of a fixed point is fixed by a positive power of θ.
  joinand-periodic : (w : LatTerm (Fin n)) → w [ θ ] ≈ʷ w → {c : LatTerm (Fin n)} → c ∈ CJ w → NotGen c
                   → Σ[ d ∈ ℕ ] c [ iter θ (suc d) ] ≈ʷ c
  joinand-periodic w fix {c} c∈ ng =
    let (a , b , a<b , e) = pigeonhole-≈ (CJ w) (λ k → c [ iter θ k ])
                              (λ k → Any.map proj₁ (joinand-orbit w fix c∈ ng k))
    in repeat→period c a b a<b e

  meetand-periodic : (w : LatTerm (Fin n)) → w [ θ ] ≈ʷ w → {c : LatTerm (Fin n)} → c ∈ CM w → NotGen c
                   → Σ[ d ∈ ℕ ] c [ iter θ (suc d) ] ≈ʷ c
  meetand-periodic w fix {c} c∈ ng =
    let (a , b , a<b , e) = pigeonhole-≈ (CM w) (λ k → c [ iter θ k ])
                              (λ k → Any.map proj₁ (meetand-orbit w fix c∈ ng k))
    in repeat→period c a b a<b e
```

#### The descent

The largest depth among the children of a canonical join or meet is attained
(`depthΣJ-attained`{.AgdaFunction}, `depthΣM-attained`{.AgdaFunction}), so an
element of complexity `m + 1` has a canonical joinand or meetand of complexity
`m` (`child-of-complexity`{.AgdaFunction}): the canonical form of `w` is a join
or a meet, its depth being positive, and the child of largest depth has
complexity one less than `w` (`complexityᴶ`{.AgdaFunction} of
[Lattices.Free.Complexity][]).  An element of positive complexity is not a
generator (`positive-not-gen`{.AgdaFunction}).

```agda
module _ {X : Type χ} where

  -- The largest depth among a nonempty list of children is attained.
  depthΣJ-attained : (h : CJand X) (t : List (CJand X))
                   → Σ[ a ∈ CJand X ] a ∈ h ∷ t × depthJ a ≡ depthΣJ h t
  depthΣJ-attained h []       = h , here refl , refl
  depthΣJ-attained h (a ∷ t)  = pick (depthΣJ-attained a t) (≤-total (depthJ h) (depthΣJ a t))
    where
    -- The head attains it, or the tail's largest does.
    pick : Σ[ b ∈ CJand X ] b ∈ a ∷ t × depthJ b ≡ depthΣJ a t
         → depthJ h ≤ depthΣJ a t ⊎ depthΣJ a t ≤ depthJ h
         → Σ[ b ∈ CJand X ] b ∈ h ∷ a ∷ t × depthJ b ≡ depthJ h ⊔ depthΣJ a t
    pick (b , b∈ , e)  (inj₁ h≤)  = b , there b∈ , trans e (sym (m≤n⇒m⊔n≡n h≤))
    pick _             (inj₂ ≤h)  = h , here refl , sym (m≥n⇒m⊔n≡m ≤h)

  depthΣM-attained : (h : CMand X) (t : List (CMand X))
                   → Σ[ a ∈ CMand X ] a ∈ h ∷ t × depthM a ≡ depthΣM h t
  depthΣM-attained h []       = h , here refl , refl
  depthΣM-attained h (a ∷ t)  = pick (depthΣM-attained a t) (≤-total (depthM h) (depthΣM a t))
    where
    pick : Σ[ b ∈ CMand X ] b ∈ a ∷ t × depthM b ≡ depthΣM a t
         → depthM h ≤ depthΣM a t ⊎ depthΣM a t ≤ depthM h
         → Σ[ b ∈ CMand X ] b ∈ h ∷ a ∷ t × depthM b ≡ depthM h ⊔ depthΣM a t
    pick (b , b∈ , e)  (inj₁ h≤)  = b , there b∈ , trans e (sym (m≤n⇒m⊔n≡n h≤))
    pick _             (inj₂ ≤h)  = h , here refl , sym (m≥n⇒m⊔n≡m ≤h)


module _ {n : ℕ} where
  open Canonicalization (_≟_ {n}) using ( canonical ; canonical-isCanonical )

  private
    κ : LatTerm (Fin n) → ℕ
    κ = complexity (_≟_ {n})

    CJ CM : LatTerm (Fin n) → List (LatTerm (Fin n))
    CJ = canonicalJoinands (_≟_ {n})
    CM = canonicalMeetands (_≟_ {n})

  -- A child of complexity one less, for a canonical term of positive depth.
  childᶜ : (w : LatTerm (Fin n)) (C : CTerm (Fin n)) → IsCanonical C
         → (∀ {a} → a ∈ asListJ (joinandsOf C) → ⌊ a ⌋ᴶ ∈ CJ w)
         → (∀ {a} → a ∈ asListM (meetandsOf C) → ⌊ a ⌋ᴹ ∈ CM w)
         → (m : ℕ) → depth C ≡ suc m
         → (Σ[ c ∈ LatTerm (Fin n) ] c ∈ CJ w × κ c ≡ m) ⊎ (Σ[ c ∈ LatTerm (Fin n) ] c ∈ CM w × κ c ≡ m)
  childᶜ w (genᶜ _)     _                 _   _   m ()
  childᶜ w (joinᶜ h t)  (cjoin _ cs _ _)  J∈  _   m e =
    let (a , a∈ , da) = depthΣJ-attained h t
    in inj₁ (⌊ a ⌋ᴶ , J∈ a∈ , trans (complexityᴶ _≟_ (lookup cs a∈)) (trans da (suc-injective e)))
  childᶜ w (meetᶜ h t)  (cmeet _ cs _ _)  _   M∈  m e =
    let (a , a∈ , da) = depthΣM-attained h t
    in inj₂ (⌊ a ⌋ᴹ , M∈ a∈ , trans (complexityᴹ _≟_ (lookup cs a∈)) (trans da (suc-injective e)))

  -- An element of complexity m + 1 has a canonical joinand or meetand of complexity m.
  child-of-complexity : (w : LatTerm (Fin n)) (m : ℕ) → κ w ≡ suc m
                      → (Σ[ c ∈ LatTerm (Fin n) ] c ∈ CJ w × κ c ≡ m) ⊎ (Σ[ c ∈ LatTerm (Fin n) ] c ∈ CM w × κ c ≡ m)
  child-of-complexity w m e =
    childᶜ w (canonical w) (canonical-isCanonical w) (∈-map⁺ ⌊_⌋ᴶ) (∈-map⁺ ⌊_⌋ᴹ) m e

  -- An element of positive complexity is not a generator.
  positive-not-gen : (c : LatTerm (Fin n)) (m : ℕ) → κ c ≡ suc m → ∀ x → ¬ (c ≈ʷ ℊ x)
  positive-not-gen c m e x c≈x = 0≢1+n (trans (sym (complexity-resp _≟_ c≈x)) e)
```

The descent itself (`descent`{.AgdaFunction}) is a recursion on the complexity.
A fixed point of complexity 1 is its own answer.  A fixed point of complexity
`m + 2` has a child of complexity `m + 1`, which is not a generator and so is
fixed by `θᵈ⁺¹` for some `d`; the recursion on the child and the power
`θᵈ⁺¹`, which freely generates too, yields an element of complexity 1 fixed by
a positive power of `θᵈ⁺¹`, which is a positive power of `θ`
(`[]-iter-*`{.AgdaFunction}).

```agda
  -- Every iterate of a freely generating substitution freely generates.
  iter-free : (θ : Sub (Fin n) (Fin n)) → FreelyGenerates θ → ∀ k → FreelyGenerates (iter θ k)
  iter-free θ θ-free k =
    injective→freelyGenerates (iter θ k) (iter-injective θ (freelyGenerates→injective θ θ-free) k)

  -- The descent, on the complexity m + 1 of the fixed point.
  descent≤ : (m : ℕ) (θ : Sub (Fin n) (Fin n)) → FreelyGenerates θ
           → (w : LatTerm (Fin n)) → w [ θ ] ≈ʷ w → κ w ≡ suc m
           → Σ[ d ∈ ℕ ] Σ[ v ∈ LatTerm (Fin n) ] v [ iter θ (suc d) ] ≈ʷ v × κ v ≡ 1
  descent≤ zero     θ θ-free w fix e = 0 , w , fixed→image θ (freelyGenerates→injective θ θ-free) w fix 1 , e
  descent≤ (suc m)  θ θ-free w fix e = step (child-of-complexity w (suc m) e)
    where
    -- Recurse on the child of complexity m + 1, under the power that fixes it.
    recurse : (c : LatTerm (Fin n)) → κ c ≡ suc m → Σ[ d ∈ ℕ ] c [ iter θ (suc d) ] ≈ʷ c
            → Σ[ d ∈ ℕ ] Σ[ v ∈ LatTerm (Fin n) ] v [ iter θ (suc d) ] ≈ʷ v × κ v ≡ 1
    recurse c κc (d , per) =
      let (d' , v , fixv , κv) = descent≤ m (iter θ (suc d)) (iter-free θ θ-free (suc d)) c per κc
      in d + d' * suc d , v , ≈ʷ-trans (≡→≈ʷ (sym ([]-iter-* v θ (suc d) (suc d')))) fixv , κv

    step : (Σ[ c ∈ LatTerm (Fin n) ] c ∈ CJ w × κ c ≡ suc m) ⊎ (Σ[ c ∈ LatTerm (Fin n) ] c ∈ CM w × κ c ≡ suc m)
         → Σ[ d ∈ ℕ ] Σ[ v ∈ LatTerm (Fin n) ] v [ iter θ (suc d) ] ≈ʷ v × κ v ≡ 1
    step (inj₁ (c , c∈ , κc)) = recurse c κc (joinand-periodic θ θ-free w fix c∈ (positive-not-gen c m κc))
    step (inj₂ (c , c∈ , κc)) = recurse c κc (meetand-periodic θ θ-free w fix c∈ (positive-not-gen c m κc))

  private
    -- A positive number is a successor.
    positive : (k : ℕ) → 0 < k → Σ[ m ∈ ℕ ] k ≡ suc m
    positive (suc m) _ = m , refl

  -- A fixed point of positive complexity descends to a fixed point of complexity 1 of a positive power.
  descent : (θ : Sub (Fin n) (Fin n)) → FreelyGenerates θ → (w : LatTerm (Fin n)) → w [ θ ] ≈ʷ w → 0 < κ w
          → Σ[ d ∈ ℕ ] Σ[ v ∈ LatTerm (Fin n) ] v [ iter θ (suc d) ] ≈ʷ v × κ v ≡ 1
  descent θ θ-free w fix pos = let (m , e) = positive (κ w) pos in descent≤ m θ θ-free w fix e
```

The descent can keep the parent of its last step (`descent-parent`{.AgdaFunction}):
from a fixed point of complexity `m + 2` it reaches an element `u` of
complexity 2, fixed by a positive power of `θ`, and a canonical joinand or
meetand `v` of `u` of complexity 1.  The recursion is the descent's, stopped
one level higher: at complexity 2 the fixed point itself is `u`, and its child
of complexity 1 is `v`.  [DeansProblem.FixedGenerator][] uses it in `FL(3)`,
as `descent-pair`{.AgdaFunction}.

```agda
  -- The descent, keeping the parent of the last step.
  descent-parent : (m : ℕ) (θ : Sub (Fin n) (Fin n)) → FreelyGenerates θ
                 → (w : LatTerm (Fin n)) → w [ θ ] ≈ʷ w → κ w ≡ suc (suc m)
                 → Σ[ d ∈ ℕ ] Σ[ u ∈ LatTerm (Fin n) ] Σ[ v ∈ LatTerm (Fin n) ]
                     u [ iter θ (suc d) ] ≈ʷ u × κ u ≡ 2 × (v ∈ CJ u ⊎ v ∈ CM u) × κ v ≡ 1
  descent-parent zero     θ θ-free w fix e =
    pack (child-of-complexity w 1 e)
    where
    -- The fixed point itself is the parent, and its child of complexity one the element.
    pack : (Σ[ c ∈ LatTerm (Fin n) ] c ∈ CJ w × κ c ≡ 1) ⊎ (Σ[ c ∈ LatTerm (Fin n) ] c ∈ CM w × κ c ≡ 1)
         → Σ[ d ∈ ℕ ] Σ[ u ∈ LatTerm (Fin n) ] Σ[ v ∈ LatTerm (Fin n) ]
             u [ iter θ (suc d) ] ≈ʷ u × κ u ≡ 2 × (v ∈ CJ u ⊎ v ∈ CM u) × κ v ≡ 1
    pack (inj₁ (c , c∈ , κc)) =
      0 , w , c , fixed→image θ (freelyGenerates→injective θ θ-free) w fix 1 , e , inj₁ c∈ , κc
    pack (inj₂ (c , c∈ , κc)) =
      0 , w , c , fixed→image θ (freelyGenerates→injective θ θ-free) w fix 1 , e , inj₂ c∈ , κc
  descent-parent (suc m)  θ θ-free w fix e = step (child-of-complexity w (suc (suc m)) e)
    where
    -- Recurse on the child, under the power that fixes it.
    recurse : (c : LatTerm (Fin n)) → κ c ≡ suc (suc m) → Σ[ d ∈ ℕ ] c [ iter θ (suc d) ] ≈ʷ c
            → Σ[ d ∈ ℕ ] Σ[ u ∈ LatTerm (Fin n) ] Σ[ v ∈ LatTerm (Fin n) ]
                u [ iter θ (suc d) ] ≈ʷ u × κ u ≡ 2 × (v ∈ CJ u ⊎ v ∈ CM u) × κ v ≡ 1
    recurse c κc (d₁ , per) =
      let (d₂ , u , v , fixu , κu , v∈ , κv) =
            descent-parent m (iter θ (suc d₁)) (iter-free θ θ-free (suc d₁)) c per κc
      in  d₁ + d₂ * suc d₁ , u , v
        , ≈ʷ-trans (≡→≈ʷ (sym ([]-iter-* u θ (suc d₁) (suc d₂)))) fixu , κu , v∈ , κv

    -- The child of complexity m + 2, a joinand or a meetand.
    step : (Σ[ c ∈ LatTerm (Fin n) ] c ∈ CJ w × κ c ≡ suc (suc m))
           ⊎ (Σ[ c ∈ LatTerm (Fin n) ] c ∈ CM w × κ c ≡ suc (suc m))
         → Σ[ d ∈ ℕ ] Σ[ u ∈ LatTerm (Fin n) ] Σ[ v ∈ LatTerm (Fin n) ]
             u [ iter θ (suc d) ] ≈ʷ u × κ u ≡ 2 × (v ∈ CJ u ⊎ v ∈ CM u) × κ v ≡ 1
    step (inj₁ (c , c∈ , κc)) =
      recurse c κc (joinand-periodic θ θ-free w fix c∈ (positive-not-gen c (suc m) κc))
    step (inj₂ (c , c∈ , κc)) =
      recurse c κc (meetand-periodic θ θ-free w fix c∈ (positive-not-gen c (suc m) κc))
```

**Lemma 6.11** of [the paper][], as one statement, for a self-embedding `θ` of
`FL(n)` and a fixed point `w`: (a) if `u` is a canonical joinand or meetand of
`w` that is not a generator, some positive power of `θ` fixes `u`; (b) if
`cx(w) ≥ 1`, some positive power of `θ` fixes an element `v` of complexity 1;
and, more precisely, if `cx(w) ≥ 2`, there are an element `u` of complexity 2
fixed by a positive power `θᵉ` and a canonical joinand or meetand `v` of `u` of
complexity 1 fixed by a positive power of `θᵉ`.  The last part is
`descent-parent`{.AgdaFunction} followed by part (a) for `θᵉ`.

```agda
-- Lemma 6.11: powers of θ fix the non-generator children of a fixed point, and a fixed point of
-- positive complexity descends to a periodic element of complexity 1, through one of complexity 2.
Lemma-6·11 : Type
Lemma-6·11 =
  (n : ℕ) (θ : Sub (Fin n) (Fin n)) → FreelyGenerates θ → (w : LatTerm (Fin n)) → w [ θ ] ≈ʷ w
  →  ({u : LatTerm (Fin n)} → u ∈ canonicalJoinands (_≟_ {n}) w ⊎ u ∈ canonicalMeetands (_≟_ {n}) w
      → (∀ x → ¬ (u ≈ʷ ℊ x)) → Σ[ d ∈ ℕ ] u [ iter θ (suc d) ] ≈ʷ u)
   × (1 ≤ complexity (_≟_ {n}) w
      → Σ[ d ∈ ℕ ] Σ[ v ∈ LatTerm (Fin n) ] v [ iter θ (suc d) ] ≈ʷ v × complexity (_≟_ {n}) v ≡ 1)
   × (2 ≤ complexity (_≟_ {n}) w
      → Σ[ e ∈ ℕ ] Σ[ u ∈ LatTerm (Fin n) ]
          u [ iter θ (suc e) ] ≈ʷ u × complexity (_≟_ {n}) u ≡ 2
        × Σ[ v ∈ LatTerm (Fin n) ]
            (v ∈ canonicalJoinands (_≟_ {n}) u ⊎ v ∈ canonicalMeetands (_≟_ {n}) u)
          × complexity (_≟_ {n}) v ≡ 1 × Σ[ d ∈ ℕ ] v [ iter (iter θ (suc e)) (suc d) ] ≈ʷ v)

-- The proof of Lemma 6.11.
lemma-6·11 : Lemma-6·11
lemma-6·11 n θ θ-free w fix =
    [ joinand-periodic θ θ-free w fix , meetand-periodic θ θ-free w fix ]′
  , descent θ θ-free w fix
  , precisely (complexity (_≟_ {n}) w) refl
  where
  -- The last part, by cases on the complexity of w.
  precisely : (k : ℕ) → complexity (_≟_ {n}) w ≡ k → 2 ≤ k
            → Σ[ e ∈ ℕ ] Σ[ u ∈ LatTerm (Fin n) ]
                u [ iter θ (suc e) ] ≈ʷ u × complexity (_≟_ {n}) u ≡ 2
              × Σ[ v ∈ LatTerm (Fin n) ]
                  (v ∈ canonicalJoinands (_≟_ {n}) u ⊎ v ∈ canonicalMeetands (_≟_ {n}) u)
                × complexity (_≟_ {n}) v ≡ 1 × Σ[ d ∈ ℕ ] v [ iter (iter θ (suc e)) (suc d) ] ≈ʷ v
  precisely zero          _  ()
  precisely (suc zero)    _  (s≤s ())
  precisely (suc (suc m)) κw _ =
    let (e , u , v , fixu , κu , v∈ , κv) = descent-parent m θ θ-free w fix κw
        θᵉ-free = iter-free θ θ-free (suc e)
        periodic = [ (λ v∈ → joinand-periodic (iter θ (suc e)) θᵉ-free u fixu v∈ (positive-not-gen v 0 κv))
                   , (λ v∈ → meetand-periodic (iter θ (suc e)) θᵉ-free u fixu v∈ (positive-not-gen v 0 κv)) ]′ v∈
    in  e , u , fixu , κu , v , v∈ , κv , periodic
```

--------------------------------------

[DeansProblem.Fixed]: DeansProblem.Fixed.html
[DeansProblem.Coherent]: DeansProblem.Coherent.html
[DeansProblem.FixedGenerator]: DeansProblem.FixedGenerator.html
[Lattices.Free.Canonical.Joinands]: Lattices.Free.Canonical.Joinands.html
[Lattices.Free.Complexity]: Lattices.Free.Complexity.html
[Lattices.Free.Embedding]: Lattices.Free.Embedding.html
