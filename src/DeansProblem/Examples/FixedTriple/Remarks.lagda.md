---
layout: default
file: "src/DeansProblem/Examples/FixedTriple/Remarks.lagda.md"
title: "DeansProblem.Examples.FixedTriple.Remarks module"
date: "2026-10-27"
author: "the agda-lattices development team"
---

### The self-embedding θ₁ of Theorem D: its fixed sublattice, and a remark on Lemma 9.13

This is the [DeansProblem.Examples.FixedTriple.Remarks][] module of the [agda-lattices][] library.

[DeansProblem.Examples.FixedTriple][] decides that the self-embedding

    θ₁ : x ↦ x ∨ (y ∧ z),    y ↦ y ∨ (x ∧ z),    z ↦ z

of `FL(3)` is proper and fixes a free triple `m₁`, `m₂`, `m₃`.  This module
states what else the paper on Dean's problem says of `θ₁`, each a short
consequence of a few more decisions in `FL(3)`, as follows.

+  **Lemma 9.13 needs its hypothesis** that the canonical joinand is not a
   generator.  `θ₁` fixes `x ∨ y`, whose canonical joinands are `x` and `y`,
   and `θ₁(x) = x ∨ (y ∧ z)` is not a canonical joinand of
   `θ₁(x ∨ y)`.  So the conclusion of
   `embedding-canonicalJoinand`{.AgdaFunction} fails for the joinand `x`
   (`generator-joinand-not-preserved`{.AgdaFunction}).
+  **`Fix(θ₁)` contains the sublattice `⟨p, q, z⟩`**, where
   `c = z ∧ (x ∨ y)`, `p = x ∨ c` and `q = y ∨ c`
   (`⟨pqz⟩-fixed`{.AgdaFunction}); in it `p ∧ z = q ∧ z = c`; and it is
   infinite (`⟨pqz⟩-infinite`{.AgdaFunction},
   `⟨pqz⟩-not-finite`{.AgdaFunction}).
+  **`Fix(θ₁)` contains a copy of `FL(ω)`** (Remark 6.8 of the paper,
   `ω-embedding`{.AgdaFunction}, `ω-fixed`{.AgdaFunction}): the countable
   free family of Theorem 1.28 of [Freese, Ježek, and Nation (1995)][],
   followed by `x, y, z ↦ m₁, m₂, m₃`.
+  **`θ₁` fixes `x ∨ y`, `x ∨ z` and `y ∨ z` outright**, and `c`; so it
   preserves the ideal `(x ∨ y]` and the filter `[z)` of the partition lemma
   of [DeansProblem.Partition][]; and it moves `x` to `x ∨ (y ∧ c)` and `y` to
   `y ∨ (x ∧ c)`, joins with meets with `c`, not to `p = x ∨ c` and `q`.

None of this assumes a chain, and the module imports neither
[DeansProblem.NoChain][] nor [DeansProblem.LengthThree][], directly or
through another module.

<!--
```agda
{-# OPTIONS --without-K --exact-split --safe #-}

module DeansProblem.Examples.FixedTriple.Remarks where

open import Agda.Primitive  using () renaming ( Set to Type )

-- Imports from the Agda Standard Library ---------------------------------------
open import Data.Fin.Base                          using ( Fin )
open import Data.Fin.Patterns                      using ( 0F ; 1F ; 2F )
open import Data.Fin.Properties                    using ( _≟_ )
open import Data.List.Base                         using ( List ; [] ; _∷_ )
open import Data.List.Membership.Propositional     using ( _∈_ )
open import Data.List.Relation.Unary.Any           using ( Any ; here ; any? )
open import Data.Nat.Base                          using ( ℕ )
open import Data.Nat.Properties                    using ( <-irrefl )
open import Data.Product                           using ( _×_ ; _,_ ; proj₁ )
open import Level                                  using ( Level )
open import Relation.Binary.PropositionalEquality  using ( _≡_ ; refl ; sym ; subst )
open import Relation.Nullary                       using ( ¬_ )
open import Relation.Nullary.Decidable.Core        using ( from-yes ; from-no )

-- Imports from the Agda Universal Algebra Library ------------------------------
open import Setoid.Functions                       using ( IsInjective )
open import Setoid.Subalgebras.Basic               using ( _IsSubalgebraOf_ )

-- Imports from the agda-lattices library ---------------------------------------
open import Lattices.Free.Canonical.Basic          using ( ≈ʷ-sym ; ≈ʷ-trans )
open import Lattices.Free.Canonical.Joinands       using ( canonicalJoinands )
open import Lattices.Free.Complexity               using ( pigeonhole-≈ )
open import Lattices.Free.Countable                using ( countable-injective )
open import Lattices.Free.Generation              using ( FreelyGenerates ; freelyGenerates→injective
                                                         ; injective→freelyGenerates )
open import Lattices.Free.Substitution             using ( Sub ; _[_] ; _⨟_ ; []-mono ; []-congʳ ; []-⨟
                                                         ; subst-hom ; ⨟-injective )
open import Lattices.Free.Term                     using ( LatTerm ; ℊ ; _∧̇_ ; _∨̇_ )
open import Lattices.Free.Universal                using ( FL )
open import Lattices.Free.Whitman                  using ( _≤ʷ_ ; _≈ʷ_ ; ≤ʷ-trans ; ℊ≤ℊ-inv
                                                         ; module Decision )
open import Lattices.Free.WhitmanPolynomials       using ( σ )
open import DeansProblem.Examples.FixedTriple      using ( x ; y ; z ; θ₁ ; c ; p ; q ; m₃ ; Θ ; m-free
                                                         ; θ₁-fixes ; θ₁-free )

private variable
  ι : Level
```
-->

```agda
open Decision (_≟_ {3}) using ( _≈ʷ?_ )
```

#### A fixed generating set fixes the sublattice it generates

If `θ` fixes every member of a family `τ`, it fixes every element `t [ τ ]` of
the sublattice `τ` generates (`fixes-generated`{.AgdaFunction}): applying `τ`
and then `θ` is applying the composite, which agrees with `τ` pointwise.

```agda
-- θ fixes the sublattice generated by a family it fixes.
fixes-generated : {I : Type ι} (τ : Sub I (Fin 3)) (θ : Sub (Fin 3) (Fin 3))
                → (∀ i → τ i [ θ ] ≈ʷ τ i) → (t : LatTerm I) → t [ τ ] [ θ ] ≈ʷ t [ τ ]
fixes-generated τ θ fix t = subst (_≈ʷ t [ τ ]) ([]-⨟ t τ θ) ([]-congʳ t fix)
```

#### Lemma 9.13 needs its hypothesis

Lemma 9.13 of [Freese, Ježek, and Nation (1995)][]
(`embedding-canonicalJoinand`{.AgdaFunction} of [Lattices.Free.Embedding][])
says that an embedding `σ` sends a canonical joinand `w₁` of `w` that is not
a generator to a canonical joinand of `σ(w)`.  For a generator it fails.
`θ₁` is an embedding (`θ₁-injective`{.AgdaFunction}), it fixes `x ∨ y`
(`θ₁-fixes-x∨y`{.AgdaFunction}), whose canonical joinands are `x` and `y`
(`joinands-x∨y`{.AgdaFunction}, computed), and `θ₁(x) = x ∨ (y ∧ z)` is none
of the canonical joinands of `θ₁(x ∨ y)` (`θ₁x-not-joinand`{.AgdaFunction},
decided).  So the lemma's conclusion, asserted of every embedding of `FL(3)`
and every canonical joinand with no hypothesis on it
(`Lemma-9-13-for-every-joinand`{.AgdaFunction}), is false
(`generator-joinand-not-preserved`{.AgdaFunction}).

```agda
-- θ₁ is an embedding.
θ₁-injective : IsInjective (proj₁ (subst-hom θ₁))
θ₁-injective = freelyGenerates→injective θ₁ θ₁-free

-- θ₁ fixes x ∨ y.
θ₁-fixes-x∨y : (x ∨̇ y) [ θ₁ ] ≈ʷ x ∨̇ y
θ₁-fixes-x∨y = from-yes ((x ∨̇ y) [ θ₁ ] ≈ʷ? x ∨̇ y)

-- The canonical joinands of x ∨ y are x and y.
joinands-x∨y : canonicalJoinands _≟_ (x ∨̇ y) ≡ x ∷ y ∷ []
joinands-x∨y = refl

-- θ₁(x) is not a canonical joinand of θ₁(x ∨ y).
θ₁x-not-joinand : ¬ Any (θ₁ 0F ≈ʷ_) (canonicalJoinands _≟_ ((x ∨̇ y) [ θ₁ ]))
θ₁x-not-joinand = from-no (any? (θ₁ 0F ≈ʷ?_) (canonicalJoinands _≟_ ((x ∨̇ y) [ θ₁ ])))

-- Lemma 9.13's conclusion for every canonical joinand, a generator or not.
Lemma-9-13-for-every-joinand : Type
Lemma-9-13-for-every-joinand =
  (τ : Sub (Fin 3) (Fin 3)) → IsInjective (proj₁ (subst-hom τ)) → (w : LatTerm (Fin 3))
  {w₁ : LatTerm (Fin 3)} → w₁ ∈ canonicalJoinands _≟_ w
  → Any (w₁ [ τ ] ≈ʷ_) (canonicalJoinands _≟_ (w [ τ ]))

-- It is false: the hypothesis that the joinand is not a generator cannot be dropped.
generator-joinand-not-preserved : ¬ Lemma-9-13-for-every-joinand
generator-joinand-not-preserved lemma =
  θ₁x-not-joinand (lemma θ₁ θ₁-injective (x ∨̇ y) (subst (x ∈_) (sym joinands-x∨y) (here refl)))
```

#### What θ₁ fixes and preserves

`θ₁` fixes `z` by definition, and `x ∨ y`, `x ∨ z`, `y ∨ z` and
`c = z ∧ (x ∨ y)` by decision (`θ₁-fixes-joins`{.AgdaFunction},
`θ₁-fixes-c`{.AgdaFunction}).  Since it fixes `x ∨ y` and `z` and is
monotone, it maps the ideal `(x ∨ y]` and the filter `[z)` of the partition
lemma into themselves (`θ₁-ideal`{.AgdaFunction},
`θ₁-filter`{.AgdaFunction}).  Inside the ideal it moves `x` to
`x ∨ (y ∧ c)` and `y` to `y ∨ (x ∧ c)` (`θ₁-moves`{.AgdaFunction}), since
`y ∧ z = y ∧ c` and `x ∧ z = x ∧ c`; that is, by joins with meets with `c`,
and not by joins with `c`, since `θ₁(x)` is not `p = x ∨ c`
(`θ₁x≉p`{.AgdaFunction}).  As `y ∧ c ≤ c`, it still fixes `p`, and likewise
`q`.

```agda
-- θ₁ fixes the three joins of two generators, and c.
θ₁-fixes-joins : ((x ∨̇ y) [ θ₁ ] ≈ʷ x ∨̇ y) × ((x ∨̇ z) [ θ₁ ] ≈ʷ x ∨̇ z)
               × ((y ∨̇ z) [ θ₁ ] ≈ʷ y ∨̇ z)
θ₁-fixes-joins =
  θ₁-fixes-x∨y , from-yes ((x ∨̇ z) [ θ₁ ] ≈ʷ? x ∨̇ z) , from-yes ((y ∨̇ z) [ θ₁ ] ≈ʷ? y ∨̇ z)

θ₁-fixes-c : c [ θ₁ ] ≈ʷ c
θ₁-fixes-c = from-yes (c [ θ₁ ] ≈ʷ? c)

-- θ₁ maps the ideal (x ∨ y] into itself, and the filter [z) into itself.
θ₁-ideal : {w : LatTerm (Fin 3)} → w ≤ʷ x ∨̇ y → w [ θ₁ ] ≤ʷ x ∨̇ y
θ₁-ideal w≤ = ≤ʷ-trans ([]-mono θ₁ w≤) (proj₁ θ₁-fixes-x∨y)

θ₁-filter : {w : LatTerm (Fin 3)} → z ≤ʷ w → z ≤ʷ w [ θ₁ ]
θ₁-filter z≤ = []-mono θ₁ z≤

-- θ₁ moves x and y up by joins with their meets with c.
θ₁-moves : (θ₁ 0F ≈ʷ x ∨̇ (y ∧̇ c)) × (θ₁ 1F ≈ʷ y ∨̇ (x ∧̇ c))
θ₁-moves = from-yes (θ₁ 0F ≈ʷ? x ∨̇ (y ∧̇ c)) , from-yes (θ₁ 1F ≈ʷ? y ∨̇ (x ∧̇ c))

-- θ₁(x) is not x ∨ c.
θ₁x≉p : ¬ (θ₁ 0F ≈ʷ p)
θ₁x≉p = from-no (θ₁ 0F ≈ʷ? p)
```

#### The sublattice ⟨p, q, z⟩

`pqz`{.AgdaFunction} is the triple `(p, q, z)`; the elements of `⟨p, q, z⟩`
are the `t [ pqz ]`.  `θ₁` fixes `p`, `q` and `z`
(`θ₁-fixes-pqz`{.AgdaFunction}, three decisions, the last by definition), so
it fixes the whole sublattice (`⟨pqz⟩-fixed`{.AgdaFunction}); and
`p ∧ z = q ∧ z = c` (`p∧z≈c`{.AgdaFunction}, `q∧z≈c`{.AgdaFunction}).

```agda
-- The generators of ⟨p, q, z⟩.
pqz : Sub (Fin 3) (Fin 3)
pqz 0F = p
pqz 1F = q
pqz 2F = z

-- θ₁ fixes p, q and z.
θ₁-fixes-pqz : ∀ i → pqz i [ θ₁ ] ≈ʷ pqz i
θ₁-fixes-pqz 0F = from-yes (p [ θ₁ ] ≈ʷ? p)
θ₁-fixes-pqz 1F = from-yes (q [ θ₁ ] ≈ʷ? q)
θ₁-fixes-pqz 2F = from-yes (z [ θ₁ ] ≈ʷ? z)

-- So Fix(θ₁) contains ⟨p, q, z⟩.
⟨pqz⟩-fixed : (t : LatTerm (Fin 3)) → t [ pqz ] [ θ₁ ] ≈ʷ t [ pqz ]
⟨pqz⟩-fixed = fixes-generated pqz θ₁ θ₁-fixes-pqz

-- In ⟨p, q, z⟩, p ∧ z = q ∧ z = c.
p∧z≈c : p ∧̇ z ≈ʷ c
p∧z≈c = from-yes (p ∧̇ z ≈ʷ? c)

q∧z≈c : q ∧̇ z ≈ʷ c
q∧z≈c = from-yes (q ∧̇ z ≈ʷ? c)
```

The free triple of Theorem D lies in `⟨p, q, z⟩`.  `m₁ = p`;
`m₂ = z ∨ ((x ∨ z) ∧ q)` with `x ∨ z = p ∨ z`, since `c ≤ z`; and `m₃` in its
second form, `((z ∨ (p ∧ q)) ∧ (x ∨ y)) ∨ q`, with `x ∨ y = p ∨ q`
(`x∨z≈p∨z`{.AgdaFunction}, `x∨y≈p∨q`{.AgdaFunction},
`m₃≈`{.AgdaFunction}; the printed form of `m₃` has the joinand `y`, which is
not in `⟨p, q, z⟩`).  So `mᵢ = μᵢ(p, q, z)` for the terms
`μ`{.AgdaFunction} below (`Θ≈μ[pqz]`{.AgdaFunction}, decided directly).

```agda
-- The joins the triple's terms need, in p, q and z.
x∨z≈p∨z : x ∨̇ z ≈ʷ p ∨̇ z
x∨z≈p∨z = from-yes (x ∨̇ z ≈ʷ? p ∨̇ z)

x∨y≈p∨q : x ∨̇ y ≈ʷ p ∨̇ q
x∨y≈p∨q = from-yes (x ∨̇ y ≈ʷ? p ∨̇ q)

-- The second form of m₃.
m₃≈ : m₃ ≈ʷ ((z ∨̇ (p ∧̇ q)) ∧̇ (x ∨̇ y)) ∨̇ q
m₃≈ = from-yes (m₃ ≈ʷ? ((z ∨̇ (p ∧̇ q)) ∧̇ (x ∨̇ y)) ∨̇ q)

-- The terms of m₁, m₂, m₃ in p, q, z, written over the generators x, y, z of FL(3).
μ : Sub (Fin 3) (Fin 3)
μ 0F = x
μ 1F = z ∨̇ ((x ∨̇ z) ∧̇ y)
μ 2F = ((z ∨̇ (x ∧̇ y)) ∧̇ (x ∨̇ y)) ∨̇ y

-- The triple of Theorem D lies in ⟨p, q, z⟩.
Θ≈μ[pqz] : ∀ i → Θ i ≈ʷ μ i [ pqz ]
Θ≈μ[pqz] 0F = from-yes (Θ 0F ≈ʷ? μ 0F [ pqz ])
Θ≈μ[pqz] 1F = from-yes (Θ 1F ≈ʷ? μ 1F [ pqz ])
Θ≈μ[pqz] 2F = from-yes (Θ 2F ≈ʷ? μ 2F [ pqz ])
```

#### A copy of FL(ω) in Fix(θ₁)

Remark 6.8 of the paper.  Let `σ`{.AgdaFunction} be the countable family of
[Lattices.Free.WhitmanPolynomials][], which freely generates a copy of `FL(ω)`
in `FL(3)` (`countable-embedding`{.AgdaFunction} of
[Lattices.Free.Countable][], Theorem 1.28 of [Freese, Ježek, and Nation
(1995)][]), and let `Ω = σ ⨟ Θ`{.AgdaFunction}, its image under
`x, y, z ↦ m₁, m₂, m₃`.  `Ω` is injective, as a composite of injective
homomorphisms (`Ω-injective`{.AgdaFunction}), so it freely generates
(`Ω-free`{.AgdaFunction}) and embeds `FL(ω)` in `FL(3)`
(`ω-embedding`{.AgdaFunction}).  Each member `σ n [ Θ ]` lies in
`⟨m₁, m₂, m₃⟩`, which `θ₁` fixes, so `θ₁` fixes the whole image
(`ω-fixed`{.AgdaFunction}).

```agda
-- The countable family, carried by the triple of Theorem D.
Ω : Sub ℕ (Fin 3)
Ω = σ ⨟ Θ

-- It is injective, so it freely generates a copy of FL(ω).
Ω-injective : IsInjective (proj₁ (subst-hom Ω))
Ω-injective = ⨟-injective σ Θ countable-injective (freelyGenerates→injective Θ m-free)

Ω-free : FreelyGenerates Ω
Ω-free = injective→freelyGenerates Ω Ω-injective

-- FL(ω) embeds in FL(3) by Ω.
ω-embedding : proj₁ (FL ℕ) IsSubalgebraOf proj₁ (FL (Fin 3))
ω-embedding = subst-hom Ω , Ω-injective

-- θ₁ fixes every element of the image of Ω.
ω-fixed : (t : LatTerm ℕ) → t [ Ω ] [ θ₁ ] ≈ʷ t [ Ω ]
ω-fixed = fixes-generated Ω θ₁ (λ n → fixes-generated Θ θ₁ θ₁-fixes (σ n))
```

#### ⟨p, q, z⟩ is infinite

The members of `Ω` lie in `⟨p, q, z⟩`: `Ω n = σ n [ Θ ]`, and `Θ` is `μ`
followed by `pqz` up to equality, so `Ω n` is the element of `⟨p, q, z⟩`
named by the term `ω-term n = σ n [ μ ]`{.AgdaFunction}
(`ω-term-in-⟨pqz⟩`{.AgdaFunction}).  Distinct indices name distinct
elements, since `Ω` is injective on the generators of `FL(ω)`
(`⟨pqz⟩-infinite`{.AgdaFunction}); so no finite list contains every element
of `⟨p, q, z⟩` up to equality, by the pigeonhole principle on the list
(`⟨pqz⟩-not-finite`{.AgdaFunction}).

```agda
-- The terms in p, q, z of the members of Ω.
ω-term : ℕ → LatTerm (Fin 3)
ω-term n = σ n [ μ ]

-- Each member of Ω is the element of ⟨p, q, z⟩ its term names.
ω-term-in-⟨pqz⟩ : ∀ n → ω-term n [ pqz ] ≈ʷ Ω n
ω-term-in-⟨pqz⟩ n = ≈ʷ-sym (subst (Ω n ≈ʷ_) ([]-⨟ (σ n) μ pqz) ([]-congʳ (σ n) Θ≈μ[pqz]))

-- Distinct indices name distinct elements of ⟨p, q, z⟩.
⟨pqz⟩-infinite : ∀ m n → ω-term m [ pqz ] ≈ʷ ω-term n [ pqz ] → m ≡ n
⟨pqz⟩-infinite m n e =
  ℊ≤ℊ-inv (proj₁ (Ω-injective {ℊ m} {ℊ n}
    (≈ʷ-trans (≈ʷ-sym (ω-term-in-⟨pqz⟩ m)) (≈ʷ-trans e (ω-term-in-⟨pqz⟩ n)))))

-- No finite list contains every element of ⟨p, q, z⟩.
⟨pqz⟩-not-finite : (L : List (LatTerm (Fin 3))) → ¬ (∀ t → Any (t [ pqz ] ≈ʷ_) L)
⟨pqz⟩-not-finite L cover =
  let (i , j , i<j , e) = pigeonhole-≈ L (λ k → ω-term k [ pqz ]) (λ k → cover (ω-term k))
  in <-irrefl (⟨pqz⟩-infinite i j e) i<j
```
