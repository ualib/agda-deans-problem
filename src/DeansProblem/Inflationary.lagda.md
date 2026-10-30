---
layout: default
file: "src/DeansProblem/Inflationary.lagda.md"
title: "DeansProblem.Inflationary module"
date: "2026-10-14"
author: "the agda-lattices development team"
---

### Inflationary self-embeddings of FL(3), and rigidity for a class

This is the [DeansProblem.Inflationary][] module of this repository.

[the paper]: https://arxiv.org/abs/YYMM.NNNNN

A self-embedding `Θ` of `FL(3)` (a freely generating substitution, Corollary
1.13 of [Freese, Ježek, and Nation (1995)][]) is *inflationary* when `g ≤ Θ g`
for every generator `g`, hence `w ≤ Θ w` for every element
(`inflationary-term`{.AgdaFunction}).  The self-embedding of Theorem D of
[the paper][] (Section 6), `θ₁ : x ↦ x ∨ (y ∧ z), y ↦ y ∨ (x ∧ z), z ↦ z`, is
one; and a proper self-embedding `Θ` whose fixed sublattice contains a copy of
`FL(3)` has, up to duality, `Θ` or `Θ²` inflationary (Corollary E1, Section 7,
[DeansProblem.Shape][]).
This module proves what such embeddings must look like and when nothing but the
identity fixes their image pointwise, the *rigidity* that would rule out a
coherent chain of length three ([DeansProblem.Coherent.Finite][]).

+  **A fixed join of two generators**
   (`fixes-join`{.AgdaFunction}, `fixes-join-third`{.AgdaFunction}).  If
   `Θ (x ∨ y) = x ∨ y` then `Θ x` and `Θ y` lie below `x ∨ y`, and either
   `x ≤ Θ x` and `y ≤ Θ y`, or `x ≤ Θ y` and `y ≤ Θ x` (the latter makes `Θ²`
   inflationary on `x` and `y`); and the third generator satisfies `z ≤ Θ z`,
   since `Θ z ≤ x ∨ y` would put `Θ (x ∨ y ∨ z)` below `Θ (x ∨ y)` and so
   `z` below `x ∨ y`.  By the descent of [DeansProblem.Fixed][], every
   self-embedding with a fixed point of complexity at least two has a power
   fixing a join or meet of two generators (the descent never ends at the top
   or bottom element), so every self-embedding with a fixed copy of `FL(3)`
   has, up to permutation and duality, a power that is inflationary with
   `x ≤ Θ x ≤ x ∨ y`, `y ≤ Θ y ≤ x ∨ y` and `z ≤ Θ z`.  The last clause of
   Lemma 1 of [the paper][], that in the swapped case `Θ²` is inflationary, is
   `fixes-join-swapped`{.AgdaFunction}.
+  **A fixed generator of a power is fixed**
   (`power-fixes→fixes`{.AgdaFunction}).  If `Θᵉ⁺¹ g = g` for a proper `Θ`
   then `Θ g = g`: by Corollary 1.6 the element `Θᵉ g` is a generator `g′`
   with `Θ g′ = g`, and if `g′ ≠ g` then `Θᵉ⁺¹` fixes two generators, so it is
   the identity ([DeansProblem.Partition][]) and `Θ` is onto.  So whether a
   self-embedding fixes a generator is decided by any of its powers.
+  **The fixed points of an inflationary embedding**.  Lemma 9.13 makes the
   image of a non-generator canonical joinand `c` of a fixed point `w` a
   canonical joinand of `w` again; it lies above `c`, and the canonical
   joinands form an antichain, so it is `c`: an inflationary embedding fixes
   every non-generator node of the canonical tree of each of its fixed points
   (`fixed-joinand-inflationary`{.AgdaFunction},
   `fixed-meetand-inflationary`{.AgdaFunction}, `node-fixed`{.AgdaFunction}).
   A fixed canonical meet with a generator meetand `g` has `Θ g ≤ g`, by
   Whitman's rule for a meet below a generator, so `Θ g = g`
   (`meetand-gen-fixed`{.AgdaFunction}); hence a proper inflationary
   self-embedding of `FL(3)` fixes no meet of two generators
   (`fixes-no-meet`{.AgdaFunction}), and no fixed point of one that fixes `z`
   has a meet node with `x` or `y` as a meetand
   (`fixes-z-no-meetand`{.AgdaFunction}), the remark after Lemma 3 of
   [the paper][].  If `Θ` moves every generator, no fixed point lies below a
   generator (`strict-fixed-not-below`{.AgdaFunction}), and every fixed point
   lies in the set `S` of Section 7.3, the elements whose canonical trees have
   no generator among the meetands of a meet node
   (`NoGeneratorMeetand`{.AgdaFunction},
   `strict-fixed-no-generator-meetand`{.AgdaFunction}).
+  **Inflation transfers through a fixed element**
   (`inflation-transfer`{.AgdaFunction}).  Let `Φ` fix the generator `z` and an
   element `a` with `x ≤ a` and `y ≰ a`.  Then `x ≤ Φ x`.  The proof reads the
   filter above `x` as a homomorphism to the two-element lattice: a generator
   lies below `t [ σ ]` exactly when `t` is satisfied by the valuation
   `v ↦ (the generator lies below σ v)` (`Sat`{.AgdaFunction},
   `≤[]→sat`{.AgdaFunction}, `sat→≤[]`{.AgdaFunction}), and `x ≤ a = a [ Φ ]`
   makes `a` satisfied by `v ↦ x ≤ Φ v`, which holds at `v = z` never and at
   `v = x` only if `x ≤ Φ x`; were it false there, `a` would be satisfied by
   `v ↦ v ≡ y`, that is, `y ≤ a`.
+  **Rigidity for a class** (`rigid-fixed`{.AgdaFunction},
   `rigid-class`{.AgdaFunction}).  Let `Θ₁ = (a, b, z)` be a self-embedding
   fixing `z` with `x ≤ a`, `y ≰ a`, `y ≤ b`, `x ≰ b` (every inflationary
   self-embedding fixing `z` is of this form), let `Φ` be a self-embedding
   fixing `a`, `b` and `z`, hence every element of the sublattice they
   generate, and suppose the canonical tree of some element `Φ` fixes has a
   meet node with `x` or `y` among its meetands (`Node`{.AgdaDatatype}).
   Then `Φ` is the identity: it is inflationary by the transfer, fixes the
   meet node, hence its generator meetand, hence two generators.  For `θ₁`
   the node is `y ∧ z`, the meetand of `x ∨ (y ∧ z)`; the worked examples in
   [DeansProblem.Examples.Rigidity][] apply the theorem to it and to a second
   member of the class.

<!--
```agda
{-# OPTIONS --without-K --exact-split --safe #-}

module DeansProblem.Inflationary where

open import Agda.Primitive  using () renaming ( Set to Type )

-- Imports from the Agda Standard Library ---------------------------------------
open import Data.Empty                             using ( ⊥ ; ⊥-elim )
open import Data.Fin.Base                          using ( Fin )
open import Data.Fin.Patterns                      using ( 0F ; 1F ; 2F )
open import Data.Fin.Properties                    using ( _≟_ )
open import Data.List.Base                         using ( List ; [] ; _∷_ ; map )
open import Data.List.Membership.Propositional     using ( _∈_ ; find )
open import Data.List.Relation.Unary.Any           using ( here ; there )
open import Data.List.Relation.Unary.Any.Properties
                                                   using ( map⁻ )
open import Data.Nat.Base                          using ( ℕ ; suc )
open import Data.Product                           using ( _×_ ; _,_ ; proj₁ ; proj₂ )
open import Data.Sum.Base                          using ( _⊎_ ; inj₁ ; inj₂ ; [_,_]′ )
open import Function                               using ( _∘_ )
open import Level                                  using ( Level )
open import Relation.Binary.PropositionalEquality  using ( _≡_ ; _≢_ ; refl ; sym ; trans ; subst )
open import Relation.Nullary                       using ( ¬_ )
open import Relation.Nullary.Decidable.Core        using ( Dec ; yes ; no )

-- Imports from the Agda Universal Algebra Library ------------------------------
open import Lattices.Free.Canonical.Basic          using ( ≈ʷ-refl ; ≈ʷ-sym ; ≈ʷ-trans ; ⋀⁺
                                                         ; ⋀⁺-gen-below )
open import Lattices.Free.Canonical.Joinands       using ( canonicalJoinands ; canonicalMeetands
                                                         ; canonicalMeetands-lower )
open import Lattices.Free.Canonical.Uniqueness     using ( antichain-≤ )
open import DeansProblem.Chain                     using ( iter ; []-iter-suc ; []-iter-sucʳ )
open import Lattices.Free.Embedding                using ( canonicalJoinands-antichain
                                                         ; canonicalMeetands-antichain
                                                         ; meetand-representation ; meetand₀ ; meetands₊ )
open import DeansProblem.Fixed                     using ( fixed-joinand ; fixed-meetand ; iter-free )
open import Lattices.Free.Generation               using ( FreelyGenerates ; freelyGenerates→injective
                                                         ; generator-in-image )
open import DeansProblem.Partition                 using ( other ; other' ; cover₃ ; ∉others₃
                                                         ; module Partition ; fix-two-generators )
open import Lattices.Free.Substitution             using ( Sub ; _[_] ; []-ℊ ; []-mono ; []-cong ; ⋀⁺-[]
                                                         ; injective→reflects )
open import Lattices.Free.Term                     using ( LatTerm ; ℊ ; _∧̇_ ; _∨̇_ )
open import Lattices.Free.Whitman                  using ( _≤ʷ_ ; _≈ʷ_ ; ≤ʷ-refl ; ≤ʷ-trans ; ∨≤ ; ∨≤-inv ; ℊ≤∧
                                                         ; ℊ≤ℊ ; ℊ≤ℊ-inv ; ℊ≤∨ˡ ; ℊ≤∨ʳ ; ℊ≤∨-inv
                                                         ; ≤∧ ; ≤∧-inv ; ∧≤ℊ-inv ; ≤∨ˡ ; ≤∨ʳ ; ∧ˡ≤ ; ∧ʳ≤
                                                         ; ∨̇-upperˡ ; ∨̇-upperʳ ; module Decision )

private variable
  ℓ χ υ : Level
  X : Type χ
  Y : Type υ
```
-->

#### Satisfaction, and the filter above a generator

A valuation of the generators by types satisfies a term as a Boolean formula
would (`Sat`{.AgdaFunction}): a generator by its value, a join when either
joinand is satisfied, a meet when both meetands are.  The filter above a
generator `g` of `FL(Y)`, read through a substitution `σ : Sub X Y`, is the set
of terms satisfied by `v ↦ ℊ g ≤ʷ σ v` (`≤[]→sat`{.AgdaFunction},
`sat→≤[]`{.AgdaFunction}): `g` is join prime, and lies below a meet when it
lies below both meetands.  Satisfaction is monotone in the valuation
(`sat-mono`{.AgdaFunction}), and no term is satisfied by the empty valuation
(`sat-empty`{.AgdaFunction}).  The dual (`Satᵈ`{.AgdaFunction}) reads the ideal
below a generator.

```agda
-- Boolean satisfaction of a term under a valuation of its generators by types.
Sat : (X → Type ℓ) → LatTerm X → Type ℓ
Sat β (ℊ v)    = β v
Sat β (s ∨̇ t)  = Sat β s ⊎ Sat β t
Sat β (s ∧̇ t)  = Sat β s × Sat β t

-- A generator below a substituted term: the term is satisfied by "the generator lies below the image".
≤[]→sat : (g : Y) (σ : Sub X Y) (t : LatTerm X) → ℊ g ≤ʷ t [ σ ] → Sat (λ v → ℊ g ≤ʷ σ v) t
≤[]→sat g σ (ℊ v)    p = p
≤[]→sat g σ (s ∨̇ t)  p = [ inj₁ ∘ ≤[]→sat g σ s , inj₂ ∘ ≤[]→sat g σ t ]′ (ℊ≤∨-inv p)
≤[]→sat g σ (s ∧̇ t)  p = ≤[]→sat g σ s (proj₁ (≤∧-inv p)) , ≤[]→sat g σ t (proj₂ (≤∧-inv p))

-- And conversely.
sat→≤[] : (g : Y) (σ : Sub X Y) (t : LatTerm X) → Sat (λ v → ℊ g ≤ʷ σ v) t → ℊ g ≤ʷ t [ σ ]
sat→≤[] g σ (ℊ v)    p         = p
sat→≤[] g σ (s ∨̇ t)  (inj₁ p)  = ℊ≤∨ˡ (sat→≤[] g σ s p)
sat→≤[] g σ (s ∨̇ t)  (inj₂ p)  = ℊ≤∨ʳ (sat→≤[] g σ t p)
sat→≤[] g σ (s ∧̇ t)  (p , q)   = ℊ≤∧ (sat→≤[] g σ s p) (sat→≤[] g σ t q)

-- Satisfaction is monotone in the valuation.
sat-mono : {β β′ : X → Type ℓ} → (∀ v → β v → β′ v) → (t : LatTerm X) → Sat β t → Sat β′ t
sat-mono f (ℊ v)    p         = f v p
sat-mono f (s ∨̇ t)  (inj₁ p)  = inj₁ (sat-mono f s p)
sat-mono f (s ∨̇ t)  (inj₂ p)  = inj₂ (sat-mono f t p)
sat-mono f (s ∧̇ t)  (p , q)   = sat-mono f s p , sat-mono f t q

-- No term is satisfied by the empty valuation.
sat-empty : {β : X → Type ℓ} → (∀ v → β v → ⊥) → (t : LatTerm X) → Sat β t → ⊥
sat-empty f (ℊ v)    p         = f v p
sat-empty f (s ∨̇ t)  (inj₁ p)  = sat-empty f s p
sat-empty f (s ∨̇ t)  (inj₂ p)  = sat-empty f t p
sat-empty f (s ∧̇ t)  (p , q)   = sat-empty f s p

-- The dual: a substituted term below a generator.
Satᵈ : (X → Type ℓ) → LatTerm X → Type ℓ
Satᵈ β (ℊ v)    = β v
Satᵈ β (s ∨̇ t)  = Satᵈ β s × Satᵈ β t
Satᵈ β (s ∧̇ t)  = Satᵈ β s ⊎ Satᵈ β t

[]≤→satᵈ : (g : Y) (σ : Sub X Y) (t : LatTerm X) → t [ σ ] ≤ʷ ℊ g → Satᵈ (λ v → σ v ≤ʷ ℊ g) t
[]≤→satᵈ g σ (ℊ v)    p = p
[]≤→satᵈ g σ (s ∨̇ t)  p = []≤→satᵈ g σ s (proj₁ (∨≤-inv p)) , []≤→satᵈ g σ t (proj₂ (∨≤-inv p))
[]≤→satᵈ g σ (s ∧̇ t)  p = [ inj₁ ∘ []≤→satᵈ g σ s , inj₂ ∘ []≤→satᵈ g σ t ]′ (∧≤ℊ-inv p)

satᵈ-empty : {β : X → Type ℓ} → (∀ v → β v → ⊥) → (t : LatTerm X) → Satᵈ β t → ⊥
satᵈ-empty f (ℊ v)    p         = f v p
satᵈ-empty f (s ∨̇ t)  (p , q)   = satᵈ-empty f s p
satᵈ-empty f (s ∧̇ t)  (inj₁ p)  = satᵈ-empty f s p
satᵈ-empty f (s ∧̇ t)  (inj₂ p)  = satᵈ-empty f t p
```

#### Inflationary substitutions

```agda
-- A substitution is inflationary when every generator lies below its image.
Inflationary : Sub X X → Type _
Inflationary Φ = ∀ v → ℊ v ≤ʷ Φ v

-- Then every term lies below its image.
inflationary-term : {Φ : Sub X X} → Inflationary Φ → (t : LatTerm X) → t ≤ʷ t [ Φ ]
inflationary-term inf (ℊ v)    = inf v
inflationary-term inf (s ∨̇ t)  = ∨≤ (≤∨ˡ (inflationary-term inf s)) (≤∨ʳ (inflationary-term inf t))
inflationary-term inf (s ∧̇ t)  = ≤∧ (∧ˡ≤ (inflationary-term inf s)) (∧ʳ≤ (inflationary-term inf t))

-- A substitution is deflationary when every generator lies above its image.
Deflationary : Sub X X → Type _
Deflationary Φ = ∀ v → Φ v ≤ʷ ℊ v
```

#### The fixed points of an inflationary self-embedding

Fix an inflationary, freely generating `Φ : Sub (Fin n) (Fin n)`.  If `Φ` fixes
`w` and `c` is a non-generator canonical joinand of `w`, then `c [ Φ ]` is a
canonical joinand of `w` (Lemma 9.13 with Theorem 1.17,
`fixed-joinand`{.AgdaFunction} of [DeansProblem.Fixed][]) lying above `c`, and
the antichain of canonical joinands leaves `c [ Φ ] ≈ʷ c`
(`fixed-joinand-inflationary`{.AgdaFunction}); dually for meetands.  So `Φ`
fixes every node of the canonical tree of `w` reached through non-generator
joinands and meetands (`Node`{.AgdaDatatype}, `node-fixed`{.AgdaFunction}).  A
fixed canonical meet `u` with a generator meetand `g` has `Φ g ≈ʷ ℊ g`
(`meetand-gen-fixed`{.AgdaFunction}): `u [ Φ ]` is the meet of the images of
the meetands and lies below `ℊ g`, so some image `m [ Φ ]` lies below `ℊ g`
(Whitman's rule for a meet below a generator), `m ≤ m [ Φ ] ≤ ℊ g` makes `m`
the meetand `ℊ g` by the antichain, and `Φ g ≤ ℊ g`.

A node of the tree of a node of `w` is a node of the tree of `w`
(`node-trans`{.AgdaFunction}), so the property below passes from an element to
the nodes of its tree (`S-node`{.AgdaFunction}).  The set `S` of Section 7.3 of [the paper][] is
the set of elements whose canonical trees have no generator among the meetands
of any meet node (`NoGeneratorMeetand`{.AgdaFunction}).  It is stated over all
non-generator nodes: a node that is a join has itself as its only canonical
meetand, so a generator meetand of a non-generator node marks a meet node.  A
strictly inflationary embedding fixes only elements of `S`
(`strict-fixed-no-generator-meetand`{.AgdaFunction}), the first step of the
proof of Proposition 7.3: every node of a fixed point is fixed, and a generator
meetand of a fixed node would be fixed.

```agda
-- The nodes of the canonical tree of w reached through non-generator canonical joinands and meetands.
data Node {n : ℕ} (w : LatTerm (Fin n)) : LatTerm (Fin n) → Type where
  root     : Node w w
  joinand  : ∀ {u c} → Node w u → c ∈ canonicalJoinands (_≟_ {n}) u → (∀ v → ¬ (c ≈ʷ ℊ v)) → Node w c
  meetand  : ∀ {u c} → Node w u → c ∈ canonicalMeetands (_≟_ {n}) u → (∀ v → ¬ (c ≈ʷ ℊ v)) → Node w c

-- A node of the tree of a node is a node of the tree.
node-trans : {n : ℕ} {w u c : LatTerm (Fin n)} → Node w u → Node u c → Node w c
node-trans nd root                 = nd
node-trans nd (joinand nd′ c∈ ng)  = joinand (node-trans nd nd′) c∈ ng
node-trans nd (meetand nd′ c∈ ng)  = meetand (node-trans nd nd′) c∈ ng

-- The set S: no non-generator node of the canonical tree of w has a generator among its canonical meetands.
NoGeneratorMeetand : {n : ℕ} → LatTerm (Fin n) → Type
NoGeneratorMeetand {n} w =
  ∀ {u} → Node w u → (∀ v → ¬ (u ≈ʷ ℊ v)) → ∀ {g} → ¬ (ℊ g ∈ canonicalMeetands (_≟_ {n}) u)

-- S passes to the nodes of the tree.
S-node : {n : ℕ} {w c : LatTerm (Fin n)} → NoGeneratorMeetand w → Node w c → NoGeneratorMeetand c
S-node s nd nd′ = s (node-trans nd nd′)

module _ {n : ℕ} (Φ : Sub (Fin n) (Fin n)) (Φ-free : FreelyGenerates Φ) (inf : Inflationary Φ) where
  private
    CJ CM : LatTerm (Fin n) → List (LatTerm (Fin n))
    CJ = canonicalJoinands (_≟_ {n})
    CM = canonicalMeetands (_≟_ {n})

  -- An inflationary embedding fixes each non-generator canonical joinand of a fixed point.
  fixed-joinand-inflationary : (w : LatTerm (Fin n)) → w [ Φ ] ≈ʷ w → {c : LatTerm (Fin n)} → c ∈ CJ w
                             → (∀ v → ¬ (c ≈ʷ ℊ v)) → c [ Φ ] ≈ʷ c
  fixed-joinand-inflationary w fix {c} c∈ ng =
    let (c′ , c′∈ , e) = find (fixed-joinand Φ Φ-free w fix c∈ ng)
        c≤c′ : c ≤ʷ c′
        c≤c′ = ≤ʷ-trans (inflationary-term inf c) (proj₁ e)
    in ≤ʷ-trans (proj₁ e) (antichain-≤ ≤ʷ-refl (canonicalJoinands-antichain _≟_ w) c∈ c′∈ c≤c′)
     , inflationary-term inf c

  -- And each non-generator canonical meetand.
  fixed-meetand-inflationary : (w : LatTerm (Fin n)) → w [ Φ ] ≈ʷ w → {c : LatTerm (Fin n)} → c ∈ CM w
                             → (∀ v → ¬ (c ≈ʷ ℊ v)) → c [ Φ ] ≈ʷ c
  fixed-meetand-inflationary w fix {c} c∈ ng =
    let (c′ , c′∈ , e) = find (fixed-meetand Φ Φ-free w fix c∈ ng)
        c≤c′ : c ≤ʷ c′
        c≤c′ = ≤ʷ-trans (inflationary-term inf c) (proj₁ e)
    in ≤ʷ-trans (proj₁ e) (antichain-≤ ≤ʷ-refl (canonicalMeetands-antichain _≟_ w) c∈ c′∈ c≤c′)
     , inflationary-term inf c

  -- Every node of the canonical tree of a fixed point is fixed.
  node-fixed : (w : LatTerm (Fin n)) → w [ Φ ] ≈ʷ w → {u : LatTerm (Fin n)} → Node w u → u [ Φ ] ≈ʷ u
  node-fixed w fix root                = fix
  node-fixed w fix (joinand nd c∈ ng)  = fixed-joinand-inflationary _ (node-fixed w fix nd) c∈ ng
  node-fixed w fix (meetand nd c∈ ng)  = fixed-meetand-inflationary _ (node-fixed w fix nd) c∈ ng

  -- A fixed canonical meet with a generator meetand g has Φ g = g.
  meetand-gen-fixed : (u : LatTerm (Fin n)) → u [ Φ ] ≈ʷ u → {g : Fin n} → ℊ g ∈ CM u → Φ g ≈ʷ ℊ g
  meetand-gen-fixed u fix {g} g∈ =
    let -- u [ Φ ] is the meet of the images of the canonical meetands of u, and lies below ℊ g.
        below : ⋀⁺ (meetand₀ _≟_ u [ Φ ]) (map (_[ Φ ]) (meetands₊ _≟_ u)) ≤ʷ ℊ g
        below = ≤ʷ-trans (subst (_≤ʷ u) (⋀⁺-[] Φ (meetand₀ _≟_ u) (meetands₊ _≟_ u))
                                (≤ʷ-trans (proj₁ ([]-cong Φ (≈ʷ-sym (meetand-representation _≟_ u))))
                                          (proj₁ fix)))
                         (canonicalMeetands-lower _≟_ g∈)
        (m , m∈ , m[Φ]≤g) = find (map⁻ (⋀⁺-gen-below below))
        -- m ≤ m [ Φ ] ≤ ℊ g, so the meetand m is ℊ g, up to equality.
        g≤m : ℊ g ≤ʷ m
        g≤m = antichain-≤ ≤ʷ-refl (canonicalMeetands-antichain _≟_ u) m∈ g∈
                          (≤ʷ-trans (inflationary-term inf m) m[Φ]≤g)
    in ≤ʷ-trans ([]-mono Φ g≤m) m[Φ]≤g , inf g

  -- If Φ moves every generator, no fixed point lies below a generator.
  strict-fixed-not-below : (∀ v → ¬ (Φ v ≤ʷ ℊ v)) → (w : LatTerm (Fin n)) → w [ Φ ] ≈ʷ w
                         → (g : Fin n) → ¬ (w ≤ʷ ℊ g)
  strict-fixed-not-below strict w fix g w≤g =
    satᵈ-empty none w ([]≤→satᵈ g Φ w (≤ʷ-trans (proj₁ fix) w≤g))
    where
    -- Φ v ≤ g is impossible: v ≤ Φ v ≤ g makes v the generator g, and then Φ g ≤ g.
    none : ∀ v → Φ v ≤ʷ ℊ g → ⊥
    none v p = strict g (subst (λ u → Φ u ≤ʷ ℊ g) (ℊ≤ℊ-inv (≤ʷ-trans (inf v) p)) p)

  -- If Φ fixes no generator, each of its fixed points is in S.
  strict-fixed-no-generator-meetand : (∀ v → ¬ (Φ v ≈ʷ ℊ v)) → (w : LatTerm (Fin n)) → w [ Φ ] ≈ʷ w
                                    → NoGeneratorMeetand w
  strict-fixed-no-generator-meetand moves w fix nd _ {g} g∈ =
    moves g (meetand-gen-fixed _ (node-fixed w fix nd) g∈)
```

#### A fixed join of two generators, and a fixed generator of a power

Fix a freely generating `Φ : Sub (Fin 3) (Fin 3)`, a generator `z`, and write
`x`, `y` for the other two (`other`{.AgdaFunction}, `other'`{.AgdaFunction} of
[DeansProblem.Partition][]).  If `Φ x ∨ Φ y = x ∨ y` then `x ≤ Φ x` or
`x ≤ Φ y`, and likewise for `y`, by join primality; both below `Φ x` would put
`Φ y ≤ x ∨ y ≤ Φ x`, hence `y ≤ x` since an embedding reflects the order
(`fixes-join`{.AgdaFunction}).  And `z ≤ Φ z` (`fixes-join-third`{.AgdaFunction}):
otherwise `Φ z ≤ x ∨ y` by the partition at `z`, so `Φ (x ∨ y ∨ z) ≤ Φ (x ∨ y)`
and `z ≤ x ∨ y`.  In the swapped case `Φ²` is inflationary
(`fixes-join-swapped`{.AgdaFunction}), the last clause of Lemma 1:
`x ≤ Φ y ≤ Φ (Φ x)` and `y ≤ Φ x ≤ Φ (Φ y)` by monotonicity, and
`z ≤ Φ z ≤ Φ (Φ z)`.  Here `Φ²` is the iterate `iter Φ 2`, which applies `Φ`
twice (`iter-two`{.AgdaFunction}).

```agda
module _ (Φ : Sub (Fin 3) (Fin 3)) (Φ-free : FreelyGenerates Φ) where
  private
    Φ-inj = freelyGenerates→injective Φ Φ-free

    -- The two generators other than z differ from each other and from z.
    other≢other' : ∀ z → other z ≢ other' z
    other≢other' 0F ()
    other≢other' 1F ()
    other≢other' 2F ()

    z≢other : ∀ z → z ≢ other z
    z≢other z e = ∉others₃ z (here e)

    z≢other' : ∀ z → z ≢ other' z
    z≢other' z e = ∉others₃ z (there (here e))

  -- If Φ x ∨ Φ y = x ∨ y, then x and y lie below the images, straight or swapped, and the images below x ∨ y.
  fixes-join : (z : Fin 3) → Φ (other z) ∨̇ Φ (other' z) ≈ʷ ℊ (other z) ∨̇ ℊ (other' z)
             → ((ℊ (other z) ≤ʷ Φ (other z) × ℊ (other' z) ≤ʷ Φ (other' z))
                 ⊎ (ℊ (other z) ≤ʷ Φ (other' z) × ℊ (other' z) ≤ʷ Φ (other z)))
               × Φ (other z) ≤ʷ ℊ (other z) ∨̇ ℊ (other' z) × Φ (other' z) ≤ʷ ℊ (other z) ∨̇ ℊ (other' z)
  fixes-join z e =
    cases (ℊ≤∨-inv (≤ʷ-trans ∨̇-upperˡ (proj₂ e))) (ℊ≤∨-inv (≤ʷ-trans ∨̇-upperʳ (proj₂ e)))
    , ≤ʷ-trans ∨̇-upperˡ (proj₁ e) , ≤ʷ-trans ∨̇-upperʳ (proj₁ e)
    where
    x y : Fin 3
    x = other z
    y = other' z

    -- Both generators below one image would make the other image, hence the other generator, below it.
    cases : ℊ x ≤ʷ Φ x ⊎ ℊ x ≤ʷ Φ y → ℊ y ≤ʷ Φ x ⊎ ℊ y ≤ʷ Φ y
          → (ℊ x ≤ʷ Φ x × ℊ y ≤ʷ Φ y) ⊎ (ℊ x ≤ʷ Φ y × ℊ y ≤ʷ Φ x)
    cases (inj₁ p) (inj₂ q) = inj₁ (p , q)
    cases (inj₂ p) (inj₁ q) = inj₂ (p , q)
    cases (inj₁ p) (inj₁ q) =
      ⊥-elim (other≢other' z (sym (ℊ≤ℊ-inv (injective→reflects Φ {s = ℊ y} {t = ℊ x} Φ-inj
                (≤ʷ-trans (≤ʷ-trans ∨̇-upperʳ (proj₁ e)) (∨≤ p q))))))
    cases (inj₂ p) (inj₂ q) =
      ⊥-elim (other≢other' z (ℊ≤ℊ-inv (injective→reflects Φ {s = ℊ x} {t = ℊ y} Φ-inj
                (≤ʷ-trans (≤ʷ-trans ∨̇-upperˡ (proj₁ e)) (∨≤ p q)))))

  -- If Φ x ∨ Φ y = x ∨ y, then z ≤ Φ z.
  fixes-join-third : (z : Fin 3) → Φ (other z) ∨̇ Φ (other' z) ≈ʷ ℊ (other z) ∨̇ ℊ (other' z) → ℊ z ≤ʷ Φ z
  fixes-join-third z e = [ (λ p → ⊥-elim (below p)) , (λ q → q) ]′ (partition (Φ z))
    where
    open Partition z (other z) (other' z ∷ []) (cover₃ z) (∉others₃ z)

    -- Φ z ≤ x ∨ y would make Φ (x ∨ y ∨ z) ≤ Φ (x ∨ y), so z ≤ x ∨ y.
    below : Φ z ≤ʷ ℊ (other z) ∨̇ ℊ (other' z) → ⊥
    below p =
      [ (λ q → z≢other z (ℊ≤ℊ-inv q)) , (λ q → z≢other' z (ℊ≤ℊ-inv q)) ]′
        (ℊ≤∨-inv (proj₂ (∨≤-inv (injective→reflects Φ
          {s = (ℊ (other z) ∨̇ ℊ (other' z)) ∨̇ ℊ z} {t = ℊ (other z) ∨̇ ℊ (other' z)} Φ-inj
          (∨≤ ≤ʷ-refl (≤ʷ-trans p (proj₂ e)))))))

  -- The second iterate applies Φ twice.
  iter-two : ∀ v → iter Φ 2 v ≡ Φ v [ Φ ]
  iter-two v = trans ([]-iter-suc (Φ v) Φ 0) ([]-ℊ (Φ v [ Φ ]))

  -- Lemma 1, its last clause: in the swapped case Φ² is inflationary.
  fixes-join-swapped : (z : Fin 3) → Φ (other z) ∨̇ Φ (other' z) ≈ʷ ℊ (other z) ∨̇ ℊ (other' z)
                     → ℊ (other z) ≤ʷ Φ (other' z) → ℊ (other' z) ≤ʷ Φ (other z) → Inflationary (iter Φ 2)
  fixes-join-swapped z e px py v = subst (ℊ v ≤ʷ_) (sym (iter-two v)) twice
    where
    pz : ℊ z ≤ʷ Φ z
    pz = fixes-join-third z e

    -- x ≤ Φ y ≤ Φ (Φ x), y ≤ Φ x ≤ Φ (Φ y), and z ≤ Φ z ≤ Φ (Φ z).
    others : v ∈ other z ∷ other' z ∷ [] → ℊ v ≤ʷ Φ v [ Φ ]
    others (here p)          = subst (λ u → ℊ u ≤ʷ Φ u [ Φ ]) (sym p) (≤ʷ-trans px ([]-mono Φ py))
    others (there (here p))  = subst (λ u → ℊ u ≤ʷ Φ u [ Φ ]) (sym p) (≤ʷ-trans py ([]-mono Φ px))
    others (there (there ()))

    twice : ℊ v ≤ʷ Φ v [ Φ ]
    twice = [ (λ v≡z → subst (λ u → ℊ u ≤ʷ Φ u [ Φ ]) (sym v≡z) (≤ʷ-trans pz ([]-mono Φ pz))) , others ]′
              (cover₃ z v)
```

A positive power `Φᵉ⁺¹` of a proper `Φ` that fixes a generator `g` has `Φ g = g`
(`power-fixes→fixes`{.AgdaFunction}).  By Corollary 1.6
(`generator-in-image`{.AgdaFunction}), `Φᵉ g` is a generator `j` with `Φ j = g`.
If `j = g` we are done.  Otherwise `Φᵉ⁺¹` fixes `j` as well (`Φᵉ⁺¹ j = Φᵉ g = j`),
so it fixes two generators and is the identity
(`fix-two-generators`{.AgdaFunction}); then the generator `Φ` misses is
`Φ (Φᵉ m)`, in the image of `Φ`, and Corollary 1.6 makes it one of the `Φ i`.

```agda
  -- If a positive power of Φ fixes a generator, Φ fixes it.
  power-fixes→fixes : (m : Fin 3) → (∀ i → ¬ (ℊ m ≈ʷ Φ i)) → (e : ℕ) (g : Fin 3)
                    → iter Φ (suc e) g ≈ʷ ℊ g → Φ g ≈ʷ ℊ g
  power-fixes→fixes m m∉ e g fix =
    let (j , g≈Φj) = generator-in-image Φ (iter Φ e g) (≈ʷ-sym step)
    in decide j (j ≟ g) g≈Φj
    where
    -- Φᵉ⁺¹ g is Φ applied to Φᵉ g.
    step : iter Φ e g [ Φ ] ≈ʷ ℊ g
    step = subst (_≈ʷ ℊ g) ([]-iter-sucʳ (ℊ g) Φ e) fix

    decide : (j : Fin 3) → Dec (j ≡ g) → ℊ g ≈ʷ Φ j → Φ g ≈ʷ ℊ g
    decide j (yes refl)  g≈Φj = ≈ʷ-sym g≈Φj
    decide j (no j≢g)    g≈Φj =
      let -- Φᵉ g = j, by injectivity, so Φᵉ⁺¹ fixes j too.
          e≈j : iter Φ e g ≈ʷ ℊ j
          e≈j = Φ-inj {iter Φ e g} {ℊ j} (≈ʷ-trans step g≈Φj)
          fixj : iter Φ (suc e) j ≈ʷ ℊ j
          fixj = ≈ʷ-trans (subst (_≈ʷ Φ j [ iter Φ e ]) (sym ([]-iter-suc (ℊ j) Φ e)) ≈ʷ-refl)
                          (≈ʷ-trans ([]-cong (iter Φ e) (≈ʷ-sym g≈Φj)) e≈j)
          -- So Φᵉ⁺¹ is the identity, and the missed generator is in the image of Φ.
          all : ∀ v → iter Φ (suc e) v ≈ʷ ℊ v
          all = fix-two-generators (iter Φ (suc e)) (iter-free Φ Φ-free (suc e)) {g} {j}
                                   (λ g≡j → j≢g (sym g≡j)) fix fixj
          (j′ , m≈Φj′) = generator-in-image Φ (iter Φ e m)
                           (≈ʷ-sym (subst (_≈ʷ ℊ m) ([]-iter-sucʳ (ℊ m) Φ e) (all m)))
      in ⊥-elim (m∉ j′ m≈Φj′)
```

#### Inflation transfers through a fixed element

Let `Φ` fix `z` and an element `a` with `x ≤ a` and `y ≰ a`, where `x`, `y`,
`z` are the three generators in some order.  Then `x ≤ Φ x`
(`inflation-transfer`{.AgdaFunction}).  Decide `x ≤ Φ x` by Whitman's
procedure; if it fails, read `x ≤ a = a [ Φ ]` as the satisfaction of `a` by
`v ↦ x ≤ Φ v`, which holds at neither `x` (the case) nor `z` (`Φ z = z`), so
only at `y`; then `a` is satisfied by `v ↦ y ≤ v`, which says `y ≤ a`.

```agda
  -- Inflation transfers: Φ z = z, Φ a = a, x ≤ a and y ≰ a give x ≤ Φ x.
  inflation-transfer : (g h k : Fin 3) → (∀ v → v ≡ g ⊎ v ≡ h ⊎ v ≡ k) → g ≢ k → Φ k ≈ʷ ℊ k
                     → (a : LatTerm (Fin 3)) → a [ Φ ] ≈ʷ a → ℊ g ≤ʷ a → ¬ (ℊ h ≤ʷ a) → ℊ g ≤ʷ Φ g
  inflation-transfer g h k cover g≢k fixk a fixa g≤a h≰a = decide (ℊ g ≤ʷ? Φ g)
    where
    open Decision (_≟_ {3}) using ( _≤ʷ?_ )

    decide : Dec (ℊ g ≤ʷ Φ g) → ℊ g ≤ʷ Φ g
    decide (yes p)   = p
    decide (no ¬p)   = ⊥-elim (h≰a (subst (ℊ h ≤ʷ_) ([]-ℊ a) (sat→≤[] h ℊ a (sat-mono shrink a sat))))
      where
      -- g lies below a [ Φ ], so a is satisfied by v ↦ g ≤ Φ v.
      sat : Sat (λ v → ℊ g ≤ʷ Φ v) a
      sat = ≤[]→sat g Φ a (≤ʷ-trans g≤a (proj₂ fixa))

      -- Only h can satisfy it: not g, by the case, and not k, since Φ k = k and g ≠ k.
      shrink : ∀ v → ℊ g ≤ʷ Φ v → ℊ h ≤ʷ ℊ v
      shrink v p =
        [ (λ v≡g → ⊥-elim (¬p (subst (λ u → ℊ g ≤ʷ Φ u) v≡g p)))
        , [ (λ v≡h → ℊ≤ℊ (sym v≡h))
          , (λ v≡k → ⊥-elim (g≢k (ℊ≤ℊ-inv (≤ʷ-trans (subst (λ u → ℊ g ≤ʷ Φ u) v≡k p) (proj₁ fixk))))) ]′ ]′
        (cover v)
```

#### The remark after Lemma 3

Let `Φ` be a proper inflationary self-embedding of `FL(3)`, missing the
generator `m`.  It fixes no meet `g ∧ h` of two generators
(`fixes-no-meet`{.AgdaFunction}): the canonical meetands of `g ∧ h` are `g` and
`h`, so Lemma 3(b) (`meetand-gen-fixed`{.AgdaFunction}) would fix both, and a
self-embedding fixing two generators is the identity
(`fix-two-generators`{.AgdaFunction}), which misses nothing.  If `Φ` fixes `z`,
no node of the canonical tree of a fixed point has a generator other than `z`
among its canonical meetands (`fixes-z-no-meetand`{.AgdaFunction}): Lemma 3(a)
(`node-fixed`{.AgdaFunction}) fixes the node, Lemma 3(b) the generator, and
with `z` that is two.

```agda
module _ (Φ : Sub (Fin 3) (Fin 3)) (Φ-free : FreelyGenerates Φ) (inf : Inflationary Φ)
         (m : Fin 3) (m∉ : ∀ i → ¬ (ℊ m ≈ʷ Φ i)) where
  private
    -- A proper Φ is not the identity.
    not-identity : ¬ (∀ v → Φ v ≈ʷ ℊ v)
    not-identity id = m∉ m (≈ʷ-sym (id m))

    -- The two generators of a meet of two distinct generators are its canonical meetands.
    meetands-of-meet : (g h : Fin 3) → g ≢ h
                     → ℊ g ∈ canonicalMeetands (_≟_ {3}) (ℊ g ∧̇ ℊ h) × ℊ h ∈ canonicalMeetands (_≟_ {3}) (ℊ g ∧̇ ℊ h)
    meetands-of-meet 0F 0F g≢h  = ⊥-elim (g≢h refl)
    meetands-of-meet 0F 1F _    = here refl , there (here refl)
    meetands-of-meet 0F 2F _    = here refl , there (here refl)
    meetands-of-meet 1F 0F _    = here refl , there (here refl)
    meetands-of-meet 1F 1F g≢h  = ⊥-elim (g≢h refl)
    meetands-of-meet 1F 2F _    = here refl , there (here refl)
    meetands-of-meet 2F 0F _    = here refl , there (here refl)
    meetands-of-meet 2F 1F _    = here refl , there (here refl)
    meetands-of-meet 2F 2F g≢h  = ⊥-elim (g≢h refl)

  -- A proper inflationary self-embedding of FL(3) fixes no meet of two generators.
  fixes-no-meet : {g h : Fin 3} → g ≢ h → ¬ ((ℊ g ∧̇ ℊ h) [ Φ ] ≈ʷ ℊ g ∧̇ ℊ h)
  fixes-no-meet {g} {h} g≢h fix =
    let (g∈ , h∈) = meetands-of-meet g h g≢h
    in not-identity (fix-two-generators Φ Φ-free g≢h (meetand-gen-fixed Φ Φ-free inf _ fix g∈)
                                                      (meetand-gen-fixed Φ Φ-free inf _ fix h∈))

  -- If it fixes z, no node of the canonical tree of a fixed point has x or y among its canonical meetands.
  fixes-z-no-meetand : (z : Fin 3) → Φ z ≈ʷ ℊ z → (w : LatTerm (Fin 3)) → w [ Φ ] ≈ʷ w
                     → {u : LatTerm (Fin 3)} → Node w u → {g : Fin 3} → g ≢ z
                     → ¬ (ℊ g ∈ canonicalMeetands (_≟_ {3}) u)
  fixes-z-no-meetand z fixz w fix nd g≢z g∈ =
    not-identity (fix-two-generators Φ Φ-free g≢z
                   (meetand-gen-fixed Φ Φ-free inf _ (node-fixed Φ Φ-free inf w fix nd) g∈) fixz)
```

#### Rigidity for a class

Let `Θ₁ = (a, b, z)` fix `z` with `x ≤ a`, `y ≰ a`, `y ≤ b`, `x ≰ b`.  Then
every freely generating `Φ` fixing `a`, `b` and `z` is inflationary, by the
transfer (`class-inflationary`{.AgdaFunction}); so it fixes every node of the
canonical trees of `a` and `b`; and if one of those nodes is a meet with `x` or
`y` among its meetands, `Φ` fixes that generator too, hence two generators, and
is the identity (`rigid-class`{.AgdaFunction}).

```agda
module _ (Φ : Sub (Fin 3) (Fin 3)) (Φ-free : FreelyGenerates Φ) (z : Fin 3) (fixz : Φ z ≈ʷ ℊ z)
         (a b : LatTerm (Fin 3)) (fixa : a [ Φ ] ≈ʷ a) (fixb : b [ Φ ] ≈ʷ b)
         (x≤a : ℊ (other z) ≤ʷ a) (y≰a : ¬ (ℊ (other' z) ≤ʷ a))
         (y≤b : ℊ (other' z) ≤ʷ b) (x≰b : ¬ (ℊ (other z) ≤ʷ b)) where
  private
    x y : Fin 3
    x = other z
    y = other' z

    -- The three generators cover Fin 3, in the two orders the transfer needs.
    from-others : ∀ v → v ∈ x ∷ y ∷ [] → v ≡ x ⊎ v ≡ y
    from-others v (here p)          = inj₁ p
    from-others v (there (here p))  = inj₂ p
    from-others v (there (there ()))

    cover-x : ∀ v → v ≡ x ⊎ v ≡ y ⊎ v ≡ z
    cover-x v = [ (λ p → inj₂ (inj₂ p)) , (λ p → [ inj₁ , (λ q → inj₂ (inj₁ q)) ]′ (from-others v p)) ]′ (cover₃ z v)

    cover-y : ∀ v → v ≡ y ⊎ v ≡ x ⊎ v ≡ z
    cover-y v = [ (λ p → inj₂ (inj₂ p)) , (λ p → [ (λ q → inj₂ (inj₁ q)) , inj₁ ]′ (from-others v p)) ]′ (cover₃ z v)

    x≢z : x ≢ z
    x≢z e = ∉others₃ z (here (sym e))

    y≢z : y ≢ z
    y≢z e = ∉others₃ z (there (here (sym e)))

  -- Φ is inflationary.
  class-inflationary : Inflationary Φ
  class-inflationary v =
    [ (λ v≡x → subst (λ u → ℊ u ≤ʷ Φ u) (sym v≡x) x≤Φx)
    , [ (λ v≡y → subst (λ u → ℊ u ≤ʷ Φ u) (sym v≡y) y≤Φy)
      , (λ v≡z → subst (λ u → ℊ u ≤ʷ Φ u) (sym v≡z) (proj₂ fixz)) ]′ ]′ (cover-x v)
    where
    x≤Φx : ℊ x ≤ʷ Φ x
    x≤Φx = inflation-transfer Φ Φ-free x y z cover-x x≢z fixz a fixa x≤a y≰a

    y≤Φy : ℊ y ≤ʷ Φ y
    y≤Φy = inflation-transfer Φ Φ-free y x z cover-y y≢z fixz b fixb y≤b x≰b

  -- If a node of the tree of any fixed point of Φ is a meet with a generator other than z among its
  -- meetands, Φ is the identity.
  rigid-fixed : (w : LatTerm (Fin 3)) → w [ Φ ] ≈ʷ w → {u : LatTerm (Fin 3)} → Node w u → {g : Fin 3} → g ≢ z
              → ℊ g ∈ canonicalMeetands (_≟_ {3}) u → ∀ v → Φ v ≈ʷ ℊ v
  rigid-fixed w fixw nd g≢z g∈ =
    fix-two-generators Φ Φ-free g≢z
      (meetand-gen-fixed Φ Φ-free class-inflationary _ (node-fixed Φ Φ-free class-inflationary w fixw nd) g∈) fixz

  -- In particular for a node of the tree of a or b.
  rigid-class : {u : LatTerm (Fin 3)} → Node a u ⊎ Node b u → {g : Fin 3} → g ≢ z
              → ℊ g ∈ canonicalMeetands (_≟_ {3}) u → ∀ v → Φ v ≈ʷ ℊ v
  rigid-class (inj₁ nd) = rigid-fixed a fixa nd
  rigid-class (inj₂ nd) = rigid-fixed b fixb nd
```

#### The paper's statements

Lemmas 1 to 4 and Theorem F of [the paper][], each as one statement, in
`FL(3)` as the paper states them; the names above hold the lemmas in `FL(n)`
where they can.  The generators the paper calls `x`, `y` and `z` are any
three: in Lemma 1 and Theorem F, `z` and the other two, `other z` and
`other' z`, which play `x` and `y`; in Lemma 4, any `x`, `y`, `z` that cover
`Fin 3` with `x ≠ z`.  A self-embedding of `FL(3)` is a substitution that
freely generates, and it is proper when it misses a generator.

**Lemma 1**: if a self-embedding `Θ` fixes `x ∨ y`, then `Θ(x), Θ(y) ≤ x ∨ y`
and `z ≤ Θ(z)`, and either `x ≤ Θ(x)` and `y ≤ Θ(y)`, or `x ≤ Θ(y)` and
`y ≤ Θ(x)`, in which case `Θ²` is inflationary.

```agda
-- Lemma 1: a self-embedding fixing x ∨ y moves x and y up, straight or swapped, below x ∨ y, and
-- z up; swapped, its square is inflationary.
Lemma-1 : Type
Lemma-1 =  (Θ : Sub (Fin 3) (Fin 3)) → FreelyGenerates Θ → (z : Fin 3)
           → let x = other z ; y = other' z in
             (ℊ x ∨̇ ℊ y) [ Θ ] ≈ʷ ℊ x ∨̇ ℊ y
           → (Θ x ≤ʷ ℊ x ∨̇ ℊ y × Θ y ≤ʷ ℊ x ∨̇ ℊ y) × ℊ z ≤ʷ Θ z
           × ((ℊ x ≤ʷ Θ x × ℊ y ≤ʷ Θ y) ⊎ (ℊ x ≤ʷ Θ y × ℊ y ≤ʷ Θ x × Inflationary (iter Θ 2)))

-- The proof of Lemma 1.
lemma-1 : Lemma-1
lemma-1 Θ Θ-free z fix =
  let (cases , bx , by) = fixes-join Θ Θ-free z fix
  in  (bx , by) , fixes-join-third Θ Θ-free z fix
    , [ inj₁ , (λ (p , q) → inj₂ (p , q , fixes-join-swapped Θ Θ-free z fix p q)) ]′ cases
```

**Lemma 2**: if a positive power `Θⁿ` of a proper self-embedding `Θ` fixes a
generator `g`, so does `Θ`.

```agda
-- Lemma 2: a generator fixed by a positive power of a proper self-embedding is fixed by it.
Lemma-2 : Type
Lemma-2 =  (Θ : Sub (Fin 3) (Fin 3)) → FreelyGenerates Θ → (m : Fin 3) → (∀ i → ¬ (ℊ m ≈ʷ Θ i))
           → (e : ℕ) (g : Fin 3) → iter Θ (suc e) g ≈ʷ ℊ g → Θ g ≈ʷ ℊ g

-- The proof of Lemma 2.
lemma-2 : Lemma-2
lemma-2 = power-fixes→fixes
```

**Lemma 3**, for an inflationary self-embedding `Θ`: (a) a non-generator
canonical joinand or meetand of a fixed point is fixed, and so every
non-generator node of the canonical tree of a fixed point
(`Node`{.AgdaDatatype}, the root included); (b) if a generator `g` is a
canonical meetand of a fixed point, `Θ(g) = g`; (c) if `Θ` is strictly
inflationary, moving every generator, no fixed point lies below a generator.

```agda
-- Lemma 3: an inflationary self-embedding fixes the nodes of its fixed points' trees and their
-- generator meetands; strictly inflationary, it has no fixed point below a generator.
Lemma-3 : Type
Lemma-3 =
  (Θ : Sub (Fin 3) (Fin 3)) → FreelyGenerates Θ → Inflationary Θ
  →  ((w : LatTerm (Fin 3)) → w [ Θ ] ≈ʷ w → {u : LatTerm (Fin 3)}
      → u ∈ canonicalJoinands (_≟_ {3}) w ⊎ u ∈ canonicalMeetands (_≟_ {3}) w
      → (∀ v → ¬ (u ≈ʷ ℊ v)) → u [ Θ ] ≈ʷ u)
   × ((w : LatTerm (Fin 3)) → w [ Θ ] ≈ʷ w → {u : LatTerm (Fin 3)} → Node w u → u [ Θ ] ≈ʷ u)
   × ((w : LatTerm (Fin 3)) → w [ Θ ] ≈ʷ w → {g : Fin 3} → ℊ g ∈ canonicalMeetands (_≟_ {3}) w
      → Θ g ≈ʷ ℊ g)
   × ((∀ g → ¬ (Θ g ≈ʷ ℊ g)) → (w : LatTerm (Fin 3)) → w [ Θ ] ≈ʷ w → (g : Fin 3) → ¬ (w ≤ʷ ℊ g))

-- The proof of Lemma 3.
lemma-3 : Lemma-3
lemma-3 Θ Θ-free inf =
    (λ w fix → [ fixed-joinand-inflationary Θ Θ-free inf w fix
               , fixed-meetand-inflationary Θ Θ-free inf w fix ]′)
  , node-fixed Θ Θ-free inf
  , meetand-gen-fixed Θ Θ-free inf
  , (λ moves → strict-fixed-not-below Θ Θ-free inf (λ v le → moves v (le , inf v)))
```

**Lemma 4**: if a self-embedding `Φ` fixes `z` and an element `a` with
`x ≤ a` and `y ≰ a`, then `x ≤ Φ(x)`.

```agda
-- Lemma 4: inflation transfers to x through a fixed element above x and not above y.
Lemma-4 : Type
Lemma-4 =  (Φ : Sub (Fin 3) (Fin 3)) → FreelyGenerates Φ → (x y z : Fin 3)
           → (∀ v → v ≡ x ⊎ v ≡ y ⊎ v ≡ z) → x ≢ z → Φ z ≈ʷ ℊ z
           → (a : LatTerm (Fin 3)) → a [ Φ ] ≈ʷ a → ℊ x ≤ʷ a → ¬ (ℊ y ≤ʷ a) → ℊ x ≤ʷ Φ x

-- The proof of Lemma 4.
lemma-4 : Lemma-4
lemma-4 = inflation-transfer
```

**Theorem F**: let `Θ₁ : x, y, z ↦ a, b, z` be a self-embedding fixing `z`
with `x ≤ a`, `y ≰ a`, `y ≤ b` and `x ≰ b`, and let `Φ` be a self-embedding
fixing `a`, `b` and `z`; if the canonical tree of some fixed point of `Φ` has a
meet node with `x` or `y` among its meetands, then `Φ` is the identity.

```agda
-- Theorem F: rigidity for a class: a meet node with x or y as a meetand, in the tree of a fixed
-- point of an embedding fixing Θ₁'s images, makes that embedding the identity.
Theorem-F : Type
Theorem-F =
  (z : Fin 3) (Θ₁ : Sub (Fin 3) (Fin 3)) → FreelyGenerates Θ₁ → Θ₁ z ≈ʷ ℊ z
  → let x = other z ; y = other' z in
    ℊ x ≤ʷ Θ₁ x → ¬ (ℊ y ≤ʷ Θ₁ x) → ℊ y ≤ʷ Θ₁ y → ¬ (ℊ x ≤ʷ Θ₁ y)
  → (Φ : Sub (Fin 3) (Fin 3)) → FreelyGenerates Φ → (∀ i → Θ₁ i [ Φ ] ≈ʷ Θ₁ i)
  → (w : LatTerm (Fin 3)) → w [ Φ ] ≈ʷ w → {u : LatTerm (Fin 3)} → Node w u
  → {g : Fin 3} → g ≢ z → ℊ g ∈ canonicalMeetands (_≟_ {3}) u → ∀ v → Φ v ≈ʷ ℊ v

-- The proof of Theorem F.
theorem-F : Theorem-F
theorem-F z Θ₁ _ fixz₁ x≤a y≰a y≤b x≰b Φ Φ-free fix =
  rigid-fixed Φ Φ-free z fixz (Θ₁ (other z)) (Θ₁ (other' z)) (fix (other z)) (fix (other' z))
              x≤a y≰a y≤b x≰b
  where
  -- Φ fixes z, the image of z.
  fixz : Φ z ≈ʷ ℊ z
  fixz = ≈ʷ-trans ([]-cong Φ (≈ʷ-sym fixz₁)) (≈ʷ-trans (fix z) fixz₁)
```

--------------------------------------

[DeansProblem.Inflationary]: DeansProblem.Inflationary.html
[DeansProblem.Coherent.Finite]: DeansProblem.Coherent.Finite.html
[DeansProblem.Examples.Rigidity]: DeansProblem.Examples.Rigidity.html
[DeansProblem.Fixed]: DeansProblem.Fixed.html
[DeansProblem.Partition]: DeansProblem.Partition.html
[DeansProblem.Shape]: DeansProblem.Shape.html
[Freese, Ježek, and Nation (1995)]: https://doi.org/10.1090/surv/042
