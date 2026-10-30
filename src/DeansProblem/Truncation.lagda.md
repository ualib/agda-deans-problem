---
layout: default
file: "src/DeansProblem/Truncation.lagda.md"
title: "DeansProblem.Truncation module"
date: "2026-10-13"
author: "the agda-lattices development team"
---

### Truncation: the term in the new generators truncates the canonical form

This is the [DeansProblem.Truncation][] module of this repository.

Let `τ` be a family of elements of `FL(Y)`, indexed by `I`, that freely
generates a copy of `FL(I)`: the homomorphism `FL(I) → FL(Y)` that `τ` induces is
injective.  An element `w` of that copy is `p [ τ ]` for a term `p` over `I`, and
it has two canonical forms in view: the canonical form `C` of `p`, a canonical
term over `I`, and the canonical form `D` of `w`, a canonical term over `Y`.
Freese ("Notes on Dean's problem", 1997, after his Lemma 1, which is Lemma 9.13
of [Freese, Ježek, and Nation (1995)][]) observes that the first is a
*truncation* of the second.  In his words, Lemma 1 "implies that if we look at
the term tree of `a` each path from `a` to a leaf (i.e., a generator) there is a
subterm `u` and an immediate subterm `v` of it such [that] either `a'`, `b'`, or
`c'` lies between `u` and `v`.  Another way of looking at this is that the term
in `a'`, `b'`, and `c'` giving `a` is just a 'truncation' of the term in the free
generators giving `a`."  This module states and proves the observation as a
relation between the two canonical terms.

**The relation**.  `C ⊑ D` (`_⊑_`{.AgdaDatatype}, in the module
`Truncates τ`{.AgdaModule}) says that `C`, read through `τ`, is `D` cut off at
the members of `τ`, as follows:

+  a generator `i` of `C` truncates `D` when `τ i` equals `D`;
+  a join `C = c₁ ∨ ⋯ ∨ cₙ` truncates a join `D = d₁ ∨ ⋯ ∨ dₘ` when the two are
   equal through `τ`, every child `cₖ` that is a meet truncates some child `dₗ`
   (it is *matched*), and every child `dₗ` of `D` is matched by some child of
   `C`, or lies below `τ i` for a child `cₖ = i` of `C` that is a generator (it
   is *cut*);
+  a meet truncates a meet in the dual way.

At a cut child `dₗ ≤ τ i` the member `τ i` lies between the node `D` and its
child `dₗ` (`cut-belowᴶ`{.AgdaFunction}: `τ i ≤ D`, since `i` is a child of
`C`), which is Freese's "`a'` lies between `u` and `v`".  The tree of `C`
(finite) maps into the tree of `D` through the matched children, node by node,
and every path down the tree of `D` leaves the image of `C` at a cut, where a
member of `τ` sits between the last node of the image and the next node.  That
is Freese's statement for every path, and the relation records more: which
node of `D` each node of `C` names, and which member each cut lies below.

**The theorem** (`truncation`{.AgdaFunction}).  If `C` and `D` are canonical and
`C [ τ ]` equals `D`, then `C ⊑ D`.  The proof is an induction on `C`, mutual
over its children as the uniqueness theorem's is, and it works on the two
canonical terms directly, never recomputing a canonical form.  At a join node
the work is done by two theorems the library already has, stated for lists:
Lemma 9.13 (`joinand-image`{.AgdaFunction} of [Lattices.Free.Embedding][]),
which matches each meet child `c` of `C` with a child `d` of `D` equal to
`c [ τ ]`, and Theorem 1.19 (`joinands-refine`{.AgdaFunction} of
[Lattices.Free.Canonical.Joinands][]), which puts every child of `D` below the
image of some child of `C`: if that child is a generator `i`, the child of `D`
is cut at `τ i`; if it is a meet `c`, then the child of `D` lies below the
child matched with `c`, and the children of `D` form an antichain, so the two
are the same child.  The matched pairs are then related by the induction
hypothesis.  For `D` the computed canonical form of `p [ τ ]` and `C` that of
`p`, this is Freese's truncation (`truncation-canonical`{.AgdaFunction}).

Two kinds of node are ruled out along the way: the image of a canonical join
is neither a generator (Corollary 1.6: a generator in the image of an embedding
is the image of a generator) nor a canonical meet (whose only canonical joinand
is itself, which Theorem 1.19 would put below the image of a single child of
the join, and injectivity below that child, against the antichain).

<!--
```agda
{-# OPTIONS --without-K --exact-split --safe #-}

module DeansProblem.Truncation where

open import Agda.Primitive  using ( Setω ) renaming ( Set to Type )

-- Imports from the Agda Standard Library ---------------------------------------
open import Data.Empty                             using ( ⊥-elim )
open import Data.List.Base                         using ( List ; [] ; _∷_ ; map )
open import Data.List.Membership.Propositional     using ( _∈_ ; find ; lose )
open import Data.List.Membership.Propositional.Properties
                                                   using ( ∈-map⁺ ; ∈-map⁻ )
open import Data.List.Relation.Unary.All           using ( All ; [] ; _∷_ ; lookup ; tabulate )
open import Data.List.Relation.Unary.AllPairs      using ( AllPairs ; [] ; _∷_ )
open import Data.List.Relation.Unary.Any           using ( Any ; here ; there )
open import Data.Product                           using ( Σ-syntax ; _×_ ; _,_ ; proj₁ ; proj₂ )
open import Data.Sum.Base                          using ( _⊎_ ; inj₁ ; inj₂ )
open import Data.Unit.Polymorphic                  using ( ⊤ ; tt )
open import Level                                  using ( Level ; _⊔_ )
open import Relation.Binary.Definitions            using ( DecidableEquality )
open import Relation.Binary.PropositionalEquality  using ( _≡_ ; refl ; sym ; trans ; cong ; subst )
open import Relation.Nullary                       using ( ¬_ )

import Data.List.Relation.Unary.All.Properties       as All
import Data.List.Relation.Unary.AllPairs.Properties  as AllPairs
import Data.List.Relation.Unary.Any.Properties       as Any

-- Imports from the Agda Universal Algebra Library ------------------------------
open import Lattices.Free.Canonical.Algorithm      using ( module Canonicalization )
open import Lattices.Free.Canonical.Basic
  using  ( CTerm ; genᶜ ; joinᶜ ; meetᶜ ; CJand ; jgen ; jmeet ; CMand ; mgen ; mjoin ; ⌊_⌋
         ; ⌊_⌋ᴶ ; ⌊_⌋ᴹ ; ⋁ᴶ ; ⋀ᴹ ; ⋁⁺ ; ⋀⁺ ; ⋁ᴶ≡⋁⁺ ; ⋀ᴹ≡⋀⁺ ; ⋁ᴶ-upper ; ⋀ᴹ-lower ; ≈ʷ-refl
         ; ≈ʷ-sym ; ≈ʷ-trans ; IsCanonical ; cjoin ; cmeet ; IsCanonicalJ ; cjmeet
         ; IsCanonicalM ; cmjoin )
open import Lattices.Free.Canonical.Joinands       using ( joinands-refine ; meetands-refine )
open import Lattices.Free.Canonical.Uniqueness     using ( module Antichains ; gen≉join ; gen≉meet )
open import Lattices.Free.Embedding                using ( joinand-image ; meetand-image )
open import Lattices.Free.Generation               using ( generator-in-image )
open import Lattices.Free.Substitution             using ( Sub ; _[_] ; subst-hom ; injective→reflects
                                                         ; []-mono ; []-cong ; ⋁⁺-[] ; ⋀⁺-[] )
open import Lattices.Free.Term                     using ( LatTerm ; ℊ )
open import Lattices.Free.Whitman                  using ( _≤ʷ_ ; _≈ʷ_ ; ≤ʷ-trans )
open import Setoid.Functions                       using ( IsInjective )

private variable
  ι υ ζ ℓ : Level
  A : Type ℓ
```
-->

#### Two facts about lists

In a list whose members are pairwise incomparable, a member below another member
is that member (`antichain-≡`{.AgdaFunction}); this is the step "the two are the
same child" of the proof.  An equation of lattice terms gives their equality in
the free lattice (`≡→≈ʷ`{.AgdaFunction}).

```agda
-- In an antichain, a member below a member is that member.
antichain-≡ : {R : A → A → Type ℓ} {xs : List A} → AllPairs (λ x y → ¬ R x y × ¬ R y x) xs
            → {x y : A} → x ∈ xs → y ∈ xs → R x y → x ≡ y
antichain-≡ (_ ∷ _)   (here refl)  (here refl)  _  = refl
antichain-≡ (Ix ∷ _)  (here refl)  (there y∈)   p  = ⊥-elim (proj₁ (lookup Ix y∈) p)
antichain-≡ (Iy ∷ _)  (there x∈)   (here refl)  p  = ⊥-elim (proj₂ (lookup Iy x∈) p)
antichain-≡ (_ ∷ I)   (there x∈)   (there y∈)   p  = antichain-≡ I x∈ y∈ p

-- An equation of lattice terms is an equality in the free lattice.
≡→≈ʷ : {Z : Type ζ} {s t : LatTerm Z} → s ≡ t → s ≈ʷ t
≡→≈ʷ refl = ≈ʷ-refl
```

#### The relation

Fix the family `τ`.  The three relations `_⊑_`{.AgdaDatatype} (canonical
terms), `_⊑ᴶ_`{.AgdaDatatype} (children of joins) and `_⊑ᴹ_`{.AgdaDatatype}
(children of meets) are defined together, as described at the top of the
module.  A child that is a generator never truncates a child of `D` (there is no
constructor for it): generator children of `C` enter only through the cuts.

```agda
module Truncates {I : Type ι} {Y : Type υ} (τ : Sub I Y) where
  infix 4 _⊑_ _⊑ᴶ_ _⊑ᴹ_

  data _⊑_   : CTerm I → CTerm Y → Type (ι ⊔ υ)
  data _⊑ᴶ_  : CJand I → CJand Y → Type (ι ⊔ υ)
  data _⊑ᴹ_  : CMand I → CMand Y → Type (ι ⊔ υ)

  data _⊑_ where
    -- A generator truncates the canonical form of its image.
    gen⊑   : {i : I} {D : CTerm Y} → τ i ≈ʷ ⌊ D ⌋ → genᶜ i ⊑ D
    -- A join truncates a join: equal through τ, meet children matched, the rest cut.
    join⊑  : {h : CJand I} {t : List (CJand I)} {h' : CJand Y} {t' : List (CJand Y)}
           → ⋁ᴶ h t [ τ ] ≈ʷ ⋁ᴶ h' t'
           → (∀ {mh mt} → jmeet mh mt ∈ h ∷ t → Any (jmeet mh mt ⊑ᴶ_) (h' ∷ t'))
           → (∀ {d} → d ∈ h' ∷ t'
                    → Any (_⊑ᴶ d) (h ∷ t) ⊎ (Σ[ i ∈ I ] jgen i ∈ h ∷ t × ⌊ d ⌋ᴶ ≤ʷ τ i))
           → joinᶜ h t ⊑ joinᶜ h' t'
    -- A meet truncates a meet, dually.
    meet⊑  : {h : CMand I} {t : List (CMand I)} {h' : CMand Y} {t' : List (CMand Y)}
           → ⋀ᴹ h t [ τ ] ≈ʷ ⋀ᴹ h' t'
           → (∀ {jh jt} → mjoin jh jt ∈ h ∷ t → Any (mjoin jh jt ⊑ᴹ_) (h' ∷ t'))
           → (∀ {d} → d ∈ h' ∷ t'
                    → Any (_⊑ᴹ d) (h ∷ t) ⊎ (Σ[ i ∈ I ] mgen i ∈ h ∷ t × τ i ≤ʷ ⌊ d ⌋ᴹ))
           → meetᶜ h t ⊑ meetᶜ h' t'

  data _⊑ᴶ_ where
    jmeet⊑ : {mh : CMand I} {mt : List (CMand I)} {mh' : CMand Y} {mt' : List (CMand Y)}
           → meetᶜ mh mt ⊑ meetᶜ mh' mt' → jmeet mh mt ⊑ᴶ jmeet mh' mt'

  data _⊑ᴹ_ where
    mjoin⊑ : {jh : CJand I} {jt : List (CJand I)} {jh' : CJand Y} {jt' : List (CJand Y)}
           → joinᶜ jh jt ⊑ joinᶜ jh' jt' → mjoin jh jt ⊑ᴹ mjoin jh' jt'
```

A truncation is an equation through `τ` (`⊑-sound`{.AgdaFunction}).  At a cut
of a join node, the member `τ i` lies below the node (`cut-belowᴶ`{.AgdaFunction}),
and the cut child below `τ i`, so `τ i` lies between them; dually at a cut of a
meet node (`cut-aboveᴹ`{.AgdaFunction}).

```agda
  -- A truncation is an equation through τ.
  ⊑-sound : {C : CTerm I} {D : CTerm Y} → C ⊑ D → ⌊ C ⌋ [ τ ] ≈ʷ ⌊ D ⌋
  ⊑-sound (gen⊑ e)       = e
  ⊑-sound (join⊑ e _ _)  = e
  ⊑-sound (meet⊑ e _ _)  = e

  -- At a cut of a join node, the member lies below the node.
  cut-belowᴶ : {h : CJand I} {t : List (CJand I)} {h' : CJand Y} {t' : List (CJand Y)} {i : I}
             → ⋁ᴶ h t [ τ ] ≈ʷ ⋁ᴶ h' t' → jgen i ∈ h ∷ t → τ i ≤ʷ ⋁ᴶ h' t'
  cut-belowᴶ e i∈ = ≤ʷ-trans ([]-mono τ (⋁ᴶ-upper i∈)) (proj₁ e)

  -- At a cut of a meet node, the member lies above the node.
  cut-aboveᴹ : {h : CMand I} {t : List (CMand I)} {h' : CMand Y} {t' : List (CMand Y)} {i : I}
             → ⋀ᴹ h t [ τ ] ≈ʷ ⋀ᴹ h' t' → mgen i ∈ h ∷ t → ⋀ᴹ h' t' ≤ʷ τ i
  cut-aboveᴹ e i∈ = ≤ʷ-trans (proj₂ e) ([]-mono τ (⋀ᴹ-lower i∈))
```

#### The theorem

Now let `τ` induce an injective homomorphism.  It reflects the order, and an
element whose image is a generator is a generator (`image-gen`{.AgdaFunction}),
by Corollary 1.6 (`generator-in-image`{.AgdaFunction}) and injectivity.  The
image of a join, as a term, is the join of the images of its children
(`image≡ᴶ`{.AgdaFunction}), and dually (`image≡ᴹ`{.AgdaFunction}).  The induction
hypothesis for a child is `Truncᴶ`{.AgdaFunction} (or `Truncᴹ`{.AgdaFunction}):
nothing for a generator, and for a meet the theorem itself, for every canonical
child of `D` equal to its image.

```agda
module _ {I : Type ι} {Y : Type υ} (τ : Sub I Y) (inj : IsInjective (proj₁ (subst-hom τ))) where
  open Truncates τ
  open Antichains {A = CJand I} (λ u v → ⌊ u ⌋ᴶ ≤ʷ ⌊ v ⌋ᴶ) ≤ʷ-trans
    using () renaming ( antichain-no-max to no-maxᴶ )
  open Antichains {A = CMand I} (λ u v → ⌊ u ⌋ᴹ ≤ʷ ⌊ v ⌋ᴹ) ≤ʷ-trans
    using () renaming ( antichain-no-min to no-minᴹ )

  private
    -- The embedding reflects the order.
    reflect : {s t : LatTerm I} → s [ τ ] ≤ʷ t [ τ ] → s ≤ʷ t
    reflect {s} {t} = injective→reflects τ {s = s} {t = t} inj

    -- An element whose image is a generator is a generator.
    image-gen : (w : LatTerm I) {y : Y} → w [ τ ] ≈ʷ ℊ y → Σ[ x ∈ I ] w ≈ʷ ℊ x
    image-gen w e = let (x , y≈) = generator-in-image τ w (≈ʷ-sym e)
                    in x , inj {w} {ℊ x} (≈ʷ-trans e y≈)

    -- The image of a join of children is the join of their images; dually for meets.
    image≡ᴶ : (h : CJand I) (t : List (CJand I))
            → ⋁ᴶ h t [ τ ] ≡ ⋁⁺ (⌊ h ⌋ᴶ [ τ ]) (map (_[ τ ]) (map ⌊_⌋ᴶ t))
    image≡ᴶ h t = trans (cong (_[ τ ]) (⋁ᴶ≡⋁⁺ h t)) (⋁⁺-[] τ ⌊ h ⌋ᴶ (map ⌊_⌋ᴶ t))

    image≡ᴹ : (h : CMand I) (t : List (CMand I))
            → ⋀ᴹ h t [ τ ] ≡ ⋀⁺ (⌊ h ⌋ᴹ [ τ ]) (map (_[ τ ]) (map ⌊_⌋ᴹ t))
    image≡ᴹ h t = trans (cong (_[ τ ]) (⋀ᴹ≡⋀⁺ h t)) (⋀⁺-[] τ ⌊ h ⌋ᴹ (map ⌊_⌋ᴹ t))

  -- The induction hypothesis for a child of a join, and for a child of a meet.
  Truncᴶ : CJand I → Type (ι ⊔ υ)
  Truncᴶ (jgen _)       = ⊤
  Truncᴶ (jmeet mh mt)  = ∀ d → IsCanonicalJ (jmeet mh mt) → IsCanonicalJ d
                        → ⋀ᴹ mh mt [ τ ] ≈ʷ ⌊ d ⌋ᴶ → jmeet mh mt ⊑ᴶ d

  Truncᴹ : CMand I → Type (ι ⊔ υ)
  Truncᴹ (mgen _)       = ⊤
  Truncᴹ (mjoin jh jt)  = ∀ d → IsCanonicalM (mjoin jh jt) → IsCanonicalM d
                        → ⋁ᴶ jh jt [ τ ] ≈ʷ ⌊ d ⌋ᴹ → mjoin jh jt ⊑ᴹ d
```

The mutual induction runs over `C`: the theorem for a join (and a meet) of
children collects the induction hypotheses of all the children first, by
structural recursion on the list, so that every recursive call is on a
subterm, as in the proof of `≈ʷ⇒≈ᶜ`{.AgdaFunction}.

```agda
  truncation       : (C : CTerm I) (D : CTerm Y) → IsCanonical C → IsCanonical D
                   → ⌊ C ⌋ [ τ ] ≈ʷ ⌊ D ⌋ → C ⊑ D
  truncation-join  : (h : CJand I) (t : List (CJand I)) (D : CTerm Y)
                   → IsCanonical (joinᶜ h t) → IsCanonical D → ⋁ᴶ h t [ τ ] ≈ʷ ⌊ D ⌋
                   → joinᶜ h t ⊑ D
  truncation-meet  : (h : CMand I) (t : List (CMand I)) (D : CTerm Y)
                   → IsCanonical (meetᶜ h t) → IsCanonical D → ⋀ᴹ h t [ τ ] ≈ʷ ⌊ D ⌋
                   → meetᶜ h t ⊑ D
  truncationᴶ      : (a : CJand I) → Truncᴶ a
  truncationᴹ      : (a : CMand I) → Truncᴹ a
  truncationᴶs     : (as : List (CJand I)) → All Truncᴶ as
  truncationᴹs     : (as : List (CMand I)) → All Truncᴹ as

  truncation (genᶜ _)     _ _   _   e = gen⊑ e
  truncation (joinᶜ h t)  D cC  cD  e = truncation-join h t D cC cD e
  truncation (meetᶜ h t)  D cC  cD  e = truncation-meet h t D cC cD e

  truncationᴶ (jgen _)                                        = tt
  truncationᴶ (jmeet mh mt)  (jgen _)         (cjmeet cC)  _            e =
    let (_ , w≈) = image-gen (⋀ᴹ mh mt) e in ⊥-elim (gen≉meet cC (≈ʷ-sym w≈))
  truncationᴶ (jmeet mh mt)  (jmeet mh' mt')  (cjmeet cC)  (cjmeet cD)  e =
    jmeet⊑ (truncation-meet mh mt (meetᶜ mh' mt') cC cD e)

  truncationᴹ (mgen _)                                        = tt
  truncationᴹ (mjoin jh jt)  (mgen _)         (cmjoin cC)  _            e =
    let (_ , w≈) = image-gen (⋁ᴶ jh jt) e in ⊥-elim (gen≉join cC (≈ʷ-sym w≈))
  truncationᴹ (mjoin jh jt)  (mjoin jh' jt')  (cmjoin cC)  (cmjoin cD)  e =
    mjoin⊑ (truncation-join jh jt (joinᶜ jh' jt') cC cD e)

  truncationᴶs []        = []
  truncationᴶs (a ∷ as)  = truncationᴶ a ∷ truncationᴶs as
  truncationᴹs []        = []
  truncationᴹs (a ∷ as)  = truncationᴹ a ∷ truncationᴹs as
```

The case of a join `C`.  A generator `D` and a meet `D` are ruled out as
described at the top.  For a join `D`, `image`{.AgdaFunction} is Lemma 9.13 for
the meet children of `C`, read for the two lists of children:
`joinand-image`{.AgdaFunction} takes the antichain and condition 4 of `C`, the
bounds of the children of `D` against the image, and the refinement of the
children of `D` (Theorem 1.19, `refineᴶ`{.AgdaFunction}), and returns a child of
`D` equal to the image of the meet child.  Each matched pair is related by the
induction hypothesis (`matched`{.AgdaFunction}).  A child of `D` lies below the
image of some child of `C` (`refine`{.AgdaFunction}), and `cover`{.AgdaFunction}
decides what that says: below `τ i` for a generator child `i`, a cut; below the
image of a meet child, which equals a child of `D`, which the antichain makes
the same child, so the meet child matches it.

```agda
  truncation-join h t (genᶜ _) cC _ e =
    let (_ , w≈) = image-gen (⋁ᴶ h t) e in ⊥-elim (gen≉join cC (≈ʷ-sym w≈))
  truncation-join h t (meetᶜ mh' mt') (cjoin ne _ ac _) cD e =
    let (_ , a∈ , D≤a) = find (Any.map⁻ {f = ⌊_⌋ᴶ} (Any.map⁻ {f = _[ τ ]}
                           (joinands-refine (meetᶜ mh' mt') cD (≈ʷ-trans (≈ʷ-sym e) (≡→≈ʷ (image≡ᴶ h t)))
                                            (here refl))))
    in ⊥-elim (no-maxᴶ ac ne a∈ λ v∈ → ≤ʷ-trans (⋁ᴶ-upper v∈) (reflect (≤ʷ-trans (proj₁ e) D≤a)))
  truncation-join h t (joinᶜ h' t') (cjoin _ cs ac c4) cD@(cjoin _ cs' ac' _) e = join⊑ e matched covered
    where
    -- The induction hypotheses for the children of C.
    ih : All Truncᴶ (h ∷ t)
    ih = truncationᴶ h ∷ truncationᴶs t

    -- D as the join of the images of the children of C.
    rep : ⋁ᴶ h' t' ≈ʷ ⋁⁺ (⌊ h ⌋ᴶ [ τ ]) (map (_[ τ ]) (map ⌊_⌋ᴶ t))
    rep = ≈ʷ-trans (≈ʷ-sym e) (≡→≈ʷ (image≡ᴶ h t))

    -- Each embedded child of D lies below the image (Theorem 1.19).
    upperᴶ : ∀ {u} → u ∈ map ⌊_⌋ᴶ (h' ∷ t') → u ≤ʷ ⋁ᴶ h t [ τ ]
    upperᴶ u∈ with ∈-map⁻ ⌊_⌋ᴶ u∈
    ... | _ , d∈ , refl = ≤ʷ-trans (⋁ᴶ-upper d∈) (proj₂ e)

    refineᴶ : ∀ {u} → u ∈ map ⌊_⌋ᴶ (h' ∷ t') → Any (u ≤ʷ_) (map (_[ τ ]) (map ⌊_⌋ᴶ (h ∷ t)))
    refineᴶ u∈ with ∈-map⁻ ⌊_⌋ᴶ u∈
    ... | _ , d∈ , refl = joinands-refine (joinᶜ h' t') cD rep d∈

    -- Lemma 9.13: a meet child's image equals a child of D.
    image : ∀ {mh mt} → jmeet mh mt ∈ h ∷ t
          → Σ[ d ∈ CJand Y ] d ∈ h' ∷ t' × ⋀ᴹ mh mt [ τ ] ≈ʷ ⌊ d ⌋ᴶ
    image {mh} {mt} a∈ =
      find (Any.map⁻ {f = ⌊_⌋ᴶ}
        (subst (λ v → Any (v [ τ ] ≈ʷ_) (map ⌊_⌋ᴶ (h' ∷ t'))) (sym (⋀ᴹ≡⋀⁺ mh mt))
          (joinand-image τ inj {W = ⋁ᴶ h t} {m₀ = ⌊ mh ⌋ᴹ} {j₀ = ⌊ h ⌋ᴶ} {ms = map ⌊_⌋ᴹ mt}
                         {js = map ⌊_⌋ᴶ t} {u₀ = ⌊ h' ⌋ᴶ} {us = map ⌊_⌋ᴶ t'}
            (subst (_∈ map ⌊_⌋ᴶ (h ∷ t)) (⋀ᴹ≡⋀⁺ mh mt) (∈-map⁺ ⌊_⌋ᴶ a∈))
            (AllPairs.map⁺ ac)
            (≡→≈ʷ (⋁ᴶ≡⋁⁺ h t))
            (All.map⁺ (tabulate λ m∈ → c4 a∈ m∈))
            upperᴶ
            (subst (⋁ᴶ h t [ τ ] ≤ʷ_) (⋁ᴶ≡⋁⁺ h' t') (proj₁ e))
            refineᴶ)))

    -- A meet child truncates the child of D its image equals.
    matched : ∀ {mh mt} → jmeet mh mt ∈ h ∷ t → Any (jmeet mh mt ⊑ᴶ_) (h' ∷ t')
    matched a∈ = let (d , d∈ , eq) = image a∈
                 in lose d∈ (lookup ih a∈ d (lookup cs a∈) (lookup cs' d∈) eq)

    -- Each child of D lies below the image of a child of C.
    refine : ∀ {d} → d ∈ h' ∷ t' → Any (λ a → ⌊ d ⌋ᴶ ≤ʷ ⌊ a ⌋ᴶ [ τ ]) (h ∷ t)
    refine d∈ = Any.map⁻ {f = ⌊_⌋ᴶ} (Any.map⁻ {f = _[ τ ]} (joinands-refine (joinᶜ h' t') cD rep d∈))

    -- Below a generator child's image it is cut; below a meet child's image, matched.
    cover : ∀ {d} → d ∈ h' ∷ t' → Σ[ a ∈ CJand I ] a ∈ h ∷ t × ⌊ d ⌋ᴶ ≤ʷ ⌊ a ⌋ᴶ [ τ ]
          → Any (_⊑ᴶ d) (h ∷ t) ⊎ (Σ[ i ∈ I ] jgen i ∈ h ∷ t × ⌊ d ⌋ᴶ ≤ʷ τ i)
    cover _ (jgen i , a∈ , d≤) = inj₂ (i , a∈ , d≤)
    cover {d} d∈ (jmeet mh mt , a∈ , d≤) =
      let (d' , d'∈ , eq) = image a∈
          d≡d' = antichain-≡ {R = λ u v → ⌊ u ⌋ᴶ ≤ʷ ⌊ v ⌋ᴶ} ac' d∈ d'∈ (≤ʷ-trans d≤ (proj₁ eq))
      in inj₁ (lose a∈ (subst (jmeet mh mt ⊑ᴶ_) (sym d≡d')
                              (lookup ih a∈ d' (lookup cs a∈) (lookup cs' d'∈) eq)))

    covered : ∀ {d} → d ∈ h' ∷ t' → Any (_⊑ᴶ d) (h ∷ t) ⊎ (Σ[ i ∈ I ] jgen i ∈ h ∷ t × ⌊ d ⌋ᴶ ≤ʷ τ i)
    covered d∈ = cover d∈ (find (refine d∈))
```

The case of a meet `C` is dual, with Lemma 9.13 for meetands
(`meetand-image`{.AgdaFunction}) and the dual of Theorem 1.19
(`meetands-refine`{.AgdaFunction}).

```agda
  truncation-meet h t (genᶜ _) cC _ e =
    let (_ , w≈) = image-gen (⋀ᴹ h t) e in ⊥-elim (gen≉meet cC (≈ʷ-sym w≈))
  truncation-meet h t (joinᶜ jh' jt') (cmeet ne _ ac _) cD e =
    let (_ , a∈ , a≤D) = find (Any.map⁻ {f = ⌊_⌋ᴹ} (Any.map⁻ {f = _[ τ ]}
                           (meetands-refine (joinᶜ jh' jt') cD (≈ʷ-trans (≈ʷ-sym e) (≡→≈ʷ (image≡ᴹ h t)))
                                            (here refl))))
    in ⊥-elim (no-minᴹ ac ne a∈ λ v∈ → ≤ʷ-trans (reflect (≤ʷ-trans a≤D (proj₂ e))) (⋀ᴹ-lower v∈))
  truncation-meet h t (meetᶜ h' t') (cmeet _ cs ac c4) cD@(cmeet _ cs' ac' _) e = meet⊑ e matched covered
    where
    -- The induction hypotheses for the children of C.
    ih : All Truncᴹ (h ∷ t)
    ih = truncationᴹ h ∷ truncationᴹs t

    -- D as the meet of the images of the children of C.
    rep : ⋀ᴹ h' t' ≈ʷ ⋀⁺ (⌊ h ⌋ᴹ [ τ ]) (map (_[ τ ]) (map ⌊_⌋ᴹ t))
    rep = ≈ʷ-trans (≈ʷ-sym e) (≡→≈ʷ (image≡ᴹ h t))

    -- Each embedded child of D lies above the image (dual of Theorem 1.19).
    lowerᴹ : ∀ {u} → u ∈ map ⌊_⌋ᴹ (h' ∷ t') → ⋀ᴹ h t [ τ ] ≤ʷ u
    lowerᴹ u∈ with ∈-map⁻ ⌊_⌋ᴹ u∈
    ... | _ , d∈ , refl = ≤ʷ-trans (proj₁ e) (⋀ᴹ-lower d∈)

    refineᴹ : ∀ {u} → u ∈ map ⌊_⌋ᴹ (h' ∷ t') → Any (_≤ʷ u) (map (_[ τ ]) (map ⌊_⌋ᴹ (h ∷ t)))
    refineᴹ u∈ with ∈-map⁻ ⌊_⌋ᴹ u∈
    ... | _ , d∈ , refl = meetands-refine (meetᶜ h' t') cD rep d∈

    -- Lemma 9.13, dually: a join child's image equals a child of D.
    image : ∀ {jh jt} → mjoin jh jt ∈ h ∷ t
          → Σ[ d ∈ CMand Y ] d ∈ h' ∷ t' × ⋁ᴶ jh jt [ τ ] ≈ʷ ⌊ d ⌋ᴹ
    image {jh} {jt} a∈ =
      find (Any.map⁻ {f = ⌊_⌋ᴹ}
        (subst (λ v → Any (v [ τ ] ≈ʷ_) (map ⌊_⌋ᴹ (h' ∷ t'))) (sym (⋁ᴶ≡⋁⁺ jh jt))
          (meetand-image τ inj {W = ⋀ᴹ h t} {j₀ = ⌊ jh ⌋ᴶ} {m₀ = ⌊ h ⌋ᴹ} {js = map ⌊_⌋ᴶ jt}
                         {ms = map ⌊_⌋ᴹ t} {u₀ = ⌊ h' ⌋ᴹ} {us = map ⌊_⌋ᴹ t'}
            (subst (_∈ map ⌊_⌋ᴹ (h ∷ t)) (⋁ᴶ≡⋁⁺ jh jt) (∈-map⁺ ⌊_⌋ᴹ a∈))
            (AllPairs.map⁺ ac)
            (≡→≈ʷ (⋀ᴹ≡⋀⁺ h t))
            (All.map⁺ (tabulate λ j∈ → c4 a∈ j∈))
            lowerᴹ
            (subst (_≤ʷ ⋀ᴹ h t [ τ ]) (⋀ᴹ≡⋀⁺ h' t') (proj₂ e))
            refineᴹ)))

    -- A join child truncates the child of D its image equals.
    matched : ∀ {jh jt} → mjoin jh jt ∈ h ∷ t → Any (mjoin jh jt ⊑ᴹ_) (h' ∷ t')
    matched a∈ = let (d , d∈ , eq) = image a∈
                 in lose d∈ (lookup ih a∈ d (lookup cs a∈) (lookup cs' d∈) eq)

    -- Each child of D lies above the image of a child of C.
    refine : ∀ {d} → d ∈ h' ∷ t' → Any (λ a → ⌊ a ⌋ᴹ [ τ ] ≤ʷ ⌊ d ⌋ᴹ) (h ∷ t)
    refine d∈ = Any.map⁻ {f = ⌊_⌋ᴹ} (Any.map⁻ {f = _[ τ ]} (meetands-refine (meetᶜ h' t') cD rep d∈))

    -- Above a generator child's image it is cut; above a join child's image, matched.
    cover : ∀ {d} → d ∈ h' ∷ t' → Σ[ a ∈ CMand I ] a ∈ h ∷ t × ⌊ a ⌋ᴹ [ τ ] ≤ʷ ⌊ d ⌋ᴹ
          → Any (_⊑ᴹ d) (h ∷ t) ⊎ (Σ[ i ∈ I ] mgen i ∈ h ∷ t × τ i ≤ʷ ⌊ d ⌋ᴹ)
    cover _ (mgen i , a∈ , ≤d) = inj₂ (i , a∈ , ≤d)
    cover {d} d∈ (mjoin jh jt , a∈ , ≤d) =
      let (d' , d'∈ , eq) = image a∈
          d'≡d = antichain-≡ {R = λ u v → ⌊ u ⌋ᴹ ≤ʷ ⌊ v ⌋ᴹ} ac' d'∈ d∈ (≤ʷ-trans (proj₂ eq) ≤d)
      in inj₁ (lose a∈ (subst (mjoin jh jt ⊑ᴹ_) d'≡d
                              (lookup ih a∈ d' (lookup cs a∈) (lookup cs' d'∈) eq)))

    covered : ∀ {d} → d ∈ h' ∷ t' → Any (_⊑ᴹ d) (h ∷ t) ⊎ (Σ[ i ∈ I ] mgen i ∈ h ∷ t × τ i ≤ʷ ⌊ d ⌋ᴹ)
    covered d∈ = cover d∈ (find (refine d∈))
```

#### Freese's truncation

With decidable equality on both sets of generators, canonical forms are
computed, and the canonical form of a term `p` truncates the canonical form of
its image `p [ τ ]` (`truncation-canonical`{.AgdaFunction}).  For Freese's
setting, `I` is the three generators of `FL(3)`, `τ` is the triple `a'`, `b'`,
`c'`, and `p` is the term expressing `a` in it.

```agda
module _ {I : Type ι} {Y : Type υ} (_≟ᴵ_ : DecidableEquality I) (_≟ʸ_ : DecidableEquality Y)
         (τ : Sub I Y) (inj : IsInjective (proj₁ (subst-hom τ))) where
  open Truncates τ
  open Canonicalization _≟ᴵ_ using () renaming ( canonical to canonicalᴵ ; canonical-sound to soundᴵ
                                               ; canonical-isCanonical to isCanonicalᴵ )
  open Canonicalization _≟ʸ_ using () renaming ( canonical to canonicalʸ ; canonical-sound to soundʸ
                                               ; canonical-isCanonical to isCanonicalʸ )

  -- The canonical form of p truncates the canonical form of p [ τ ].
  truncation-canonical : (p : LatTerm I) → canonicalᴵ p ⊑ canonicalʸ (p [ τ ])
  truncation-canonical p =
    truncation τ inj (canonicalᴵ p) (canonicalʸ (p [ τ ])) (isCanonicalᴵ p) (isCanonicalʸ (p [ τ ]))
               (≈ʷ-trans ([]-cong τ (soundᴵ p)) (≈ʷ-sym (soundʸ (p [ τ ]))))
```

**Theorem 9.1** of the paper (the truncation theorem), as one statement: for
an embedding `τ` of `FL(I)` in `FL(Y)`, a term `p` over `I` with canonical
form `C`, and the canonical form `D` of `τ(p)`, `C` truncates `D` through `τ`
(`Truncates._⊑_`{.AgdaDatatype}).  A canonical form of an element is a
canonical term naming it; no decidable equality is needed.

```agda
-- Theorem 9.1: the canonical form of p truncates that of its image under an embedding.
Theorem-9·1 : Setω
Theorem-9·1 =  ∀ {ι υ} {I : Type ι} {Y : Type υ} (τ : Sub I Y) → IsInjective (proj₁ (subst-hom τ))
               → (p : LatTerm I) (C : CTerm I) (D : CTerm Y)
               → IsCanonical C → ⌊ C ⌋ ≈ʷ p → IsCanonical D → ⌊ D ⌋ ≈ʷ p [ τ ]
               → Truncates._⊑_ τ C D

-- The proof of Theorem 9.1.
theorem-9·1 : Theorem-9·1
theorem-9·1 τ inj p C D icC eC icD eD =
  truncation τ inj C D icC icD (≈ʷ-trans ([]-cong τ eC) (≈ʷ-sym eD))
```

--------------------------------------

[DeansProblem.Truncation]: DeansProblem.Truncation.html
[Freese, Ježek, and Nation (1995)]: https://doi.org/10.1090/surv/042
[Lattices.Free.Canonical.Joinands]: Lattices.Free.Canonical.Joinands.html
[Lattices.Free.Embedding]: Lattices.Free.Embedding.html
