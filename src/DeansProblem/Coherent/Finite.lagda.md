---
layout: default
file: "src/DeansProblem/Coherent/Finite.lagda.md"
title: "DeansProblem.Coherent.Finite module"
date: "2026-10-14"
author: "the agda-lattices development team"
---

### Coherent chains of finite length

This is the [DeansProblem.Coherent.Finite][] module of this repository.

[the paper]: https://arxiv.org/abs/YYMM.NNNNN

A *coherent chain of length `n`* is a sequence `Θ₀, …, Θₙ₋₁` of proper
self-embeddings of `FL(3)` with `Θₖ ∘ Θⱼ = Θⱼ` for every `j < k`: each later
embedding fixes the image of each earlier one pointwise.  Their images form a
strictly ascending chain `Θ₀(FL(3)) ⊊ Θ₁(FL(3)) ⊊ ⋯ ⊊ Θₙ₋₁(FL(3)) ⊊ FL(3)` of
copies of `FL(3)`, and Theorem C of [the paper][], in its coherent form
(Section 6), shows that an infinite ascending chain of copies of `FL(3)` in a
free lattice exists if and only if an infinite coherent chain does.  This
module states the finite form as a record
(`Coherent`{.AgdaRecord}) and proves the following about it.

+  **The chain of images**.  In a coherent chain, strictness of the ascent is
   properness: for `j < k` the containment `Θⱼ(FL(3)) ⊆ Θₖ(FL(3))` is a step of
   [DeansProblem.Chain][] whose terms are `Θⱼ` itself and whose fresh generator
   is the one `Θⱼ` misses (`step`{.AgdaFunction}); and each `Θⱼ(FL(3)) ⊊ FL(3)`
   is a step with the identity above (`top-step`{.AgdaFunction}).
+  **Length two is the fixed-sublattice configuration**: a `Coherent 2` is a
   `FixedSublattice`{.AgdaRecord} of [DeansProblem.Coherent][] and conversely
   (`coherent₂→fixed`{.AgdaFunction}, `fixed→coherent₂`{.AgdaFunction}), and a
   coherent chain loses its top or its bottom link and stays coherent
   (`drop-top`{.AgdaFunction}, `drop-bottom`{.AgdaFunction}).
+  **The four-link criterion**.  For a chain `L₀ ⊊ L₁ ⊊ ⋯` with transitions
   `θ_{j,k}` ([DeansProblem.Coherent][]), four links `i < j < k < l` with
   `θ_{i,j} = θ_{i,l}` and `θ_{j,k} = θ_{j,l}` give a coherent chain of length
   three, `Θ₀ = θ_{i,l}`, `Θ₁ = θ_{j,l}`, `Θ₂ = θ_{k,l}`
   (`four-links→coherent₃`{.AgdaFunction}).  The cocycle identity
   `θ_{a,c} = θ_{b,c} ∘ θ_{a,b}` (`transition-⨟′`{.AgdaFunction}, from any base)
   turns the two equations into the three coherence equations: the third,
   `θ_{i,k} = θ_{i,l}`, follows from the other two, so it is derived here rather
   than assumed.
+  **An infinite coherent chain has unbounded complexity**.  An infinite
   coherent chain (`Coherentω`{.AgdaRecord}, indexed by `ℕ`) whose embeddings
   all have generator images of complexity at most some `C` would repeat an
   embedding, `Θⱼ = Θₖ` with `j < k`, by the pigeonhole for triples; then
   `Θⱼ = Θₖ ∘ Θⱼ = Θⱼ ∘ Θⱼ`, and injectivity makes `Θⱼ` the identity, which
   misses no generator (`coherentω-unbounded`{.AgdaFunction}).  So a
   compactness argument for Dean's problem (coherent chains of every finite
   length giving an infinite one) cannot run under a uniform complexity bound;
   Theorem G ([DeansProblem.LengthThree][]) makes the point moot.
+  **The extraction, under a recurrence hypothesis**.  The one-step theorem of
   [DeansProblem.Coherent][] is a finite pigeonhole on the transitions from
   the bottom.  Length three needs a link `j` whose transition from the bottom,
   `θ_{0,j}`, recurs beyond every bound (`Recurs`{.AgdaFunction}): then the
   transitions `θ_{j,·}` at the recurrences have bounded complexity, two of them
   agree, and the four links are at hand (`chain→coherent₃`{.AgdaFunction}).
   Classically the hypothesis holds for some `j` in every chain, because the
   transitions from the bottom take finitely many values and one of them recurs
   infinitely often; but the number of recurrences that a given `j` needs
   depends on the complexity of the `j`-th link, which no bound fixes in
   advance, so the step is not a finite pigeonhole and the hypothesis stays
   explicit here.  [DeansProblem.Coherent.Infinite][] derives it from the
   infinite pigeonhole principle, itself taken as a hypothesis
   (`some-link-recurs`{.AgdaFunction}), as Section 6 of [the paper][] argues.

<!--
```agda
{-# OPTIONS --without-K --exact-split --safe #-}

module DeansProblem.Coherent.Finite where

open import Agda.Primitive  using ( Setω ) renaming ( Set to Type )

-- Imports from the Agda Standard Library ---------------------------------------
open import Data.Empty                             using ( ⊥ )
open import Data.Fin.Base                          using ( Fin ; zero ; suc ; toℕ ; inject₁ ; _<_ )
open import Data.Fin.Patterns                      using ( 0F ; 1F ; 2F )
open import Data.Fin.Properties                    using ( _≟_ ; toℕ-inject₁ )
open import Data.List.Base                         using ( allFin )
open import Data.List.Membership.Propositional.Properties
                                                   using ( ∈-allFin )
open import Data.Nat.Base                          using ( ℕ ; zero ; suc ; _+_ ; _≤_ ; z≤n ; s≤s )
                                                   renaming ( _<_ to _<ℕ_ )
open import Data.Nat.Properties                    using ( ≤-trans ; +-assoc ; +-comm
                                                         ; +-suc ; +-identityʳ ; m≤n⇒∃[o]m+o≡n ; <-trans
                                                         ; m≤m+n )
open import Data.Product                           using ( Σ-syntax ; _×_ ; _,_ ; proj₁ ; proj₂ )
open import Level                                  using ( Level )
open import Relation.Binary.Definitions            using ( DecidableEquality )
open import Relation.Binary.PropositionalEquality  using ( _≡_ ; refl ; sym ; trans ; cong ; subst )
open import Relation.Nullary                       using ( ¬_ )
open import Relation.Unary                         using ( _⊂_ )

-- Imports from the Agda Universal Algebra Library ------------------------------
open import Lattices.Free.Canonical.Basic          using ( ≈ʷ-refl ; ≈ʷ-sym ; ≈ʷ-trans )
open import DeansProblem.Chain                     using ( Step ; Chain ; fresh∉⟨σ⟩ )
open import DeansProblem.Chain.Condition           using ( ⟨_⟩ ; step→⊂ )
open import DeansProblem.Coherent                  using ( FixedSublattice ; Θ-misses ; ℊ-free
                                                         ; first-factor-injective ; bound
                                                         ; transition ; gens≈transition )
open import DeansProblem.Coherent public          using ( transition-bound′ )
open import Lattices.Free.Complexity               using ( complexity ; module Bounded
                                                         ; pigeonhole-≈ⁿ )
open import Lattices.Free.Generation               using ( FreelyGenerates
                                                         ; freelyGenerates→injective
                                                         ; injective→freelyGenerates
                                                         ; generator-in-image )
open import Lattices.Free.Substitution             using ( Sub ; _[_] ; []-ℊ ; []-⨟ ; []-cong
                                                         ; []-congʳ )
open import Lattices.Free.Term                     using ( LatTerm ; ℊ )
open import Lattices.Free.Whitman                  using ( _≈ʷ_ )

private variable
  χ : Level
  X : Type χ
```
-->

#### Coherent chains

A `Coherent n`{.AgdaRecord} is `n` substitutions `Θ j : Sub (Fin 3) (Fin 3)`,
each freely generating (so each induces a self-embedding, by Corollary 1.13 of
[Freese, Ježek, and Nation (1995)][]), each missing a generator (so none is
onto, by Corollary 1.6), with `Θ j i [ Θ k ] ≈ʷ Θ j i` for `j < k`: the later
embedding fixes each generator of the earlier image, hence the whole image
(`fixes-⟨Θ⟩`{.AgdaFunction}).

```agda
-- A coherent chain of length n: proper self-embeddings Θ₀, …, Θₙ₋₁ of FL(3)
-- with Θ k ∘ Θ j = Θ j for j < k.
record Coherent (n : ℕ) : Type where
  field
    Θ         : Fin n → Sub (Fin 3) (Fin 3)
    Θ-free    : ∀ j → FreelyGenerates (Θ j)
    missed    : Fin n → Fin 3
    missed∉   : ∀ j i → ¬ (ℊ (missed j) ≈ʷ Θ j i)
    coherent  : ∀ {j k} → j < k → ∀ i → Θ j i [ Θ k ] ≈ʷ Θ j i

  -- Θ k fixes every element of the sublattice Θ j generates, for j < k.
  fixes-⟨Θ⟩ : ∀ {j k} → j < k → (t : LatTerm (Fin 3)) → t [ Θ j ] [ Θ k ] ≈ʷ t [ Θ j ]
  fixes-⟨Θ⟩ j<k t = subst (_≈ʷ t [ Θ _ ]) ([]-⨟ t (Θ _) (Θ _)) ([]-congʳ t (coherent j<k))
```

#### The chain of images

For `j < k`, the containment `Θⱼ(FL(3)) ⊆ Θₖ(FL(3))` is a step
(`step`{.AgdaFunction}): its terms are `Θ j` itself, since
`Θ j i ≈ʷ Θ j i [ Θ k ]`, and its fresh generator is the one `Θ j` misses.  So
in a coherent chain the strictness of the ascent is just the properness of the
lower embedding.  The top containment `Θⱼ(FL(3)) ⊊ FL(3)` is a step with the
identity substitution above (`top-step`{.AgdaFunction}).

```agda
module _ {n : ℕ} (C : Coherent n) where
  open Coherent C

  -- The containment Θ j (FL(3)) ⊊ Θ k (FL(3)) for j < k, as a step.
  step : ∀ {j k} → j < k → Step (Fin 3)
  step {j} {k} j<k = record
    { σ        = Θ j
    ; τ        = Θ k
    ; σ-free   = Θ-free j
    ; τ-free   = Θ-free k
    ; p        = Θ j
    ; σ≈p[τ]   = λ i → ≈ʷ-sym (coherent j<k i)
    ; fresh    = missed j
    ; fresh∉p  = missed∉ j
    }

  -- The containment Θ j (FL(3)) ⊊ FL(3), as a step.
  top-step : Fin n → Step (Fin 3)
  top-step j = record
    { σ        = Θ j
    ; τ        = ℊ
    ; σ-free   = Θ-free j
    ; τ-free   = ℊ-free
    ; p        = Θ j
    ; σ≈p[τ]   = λ i → subst (Θ j i ≈ʷ_) (sym ([]-ℊ (Θ j i))) ≈ʷ-refl
    ; fresh    = missed j
    ; fresh∉p  = missed∉ j
    }
```

#### Length two, and dropping a link

A coherent chain of length two is exactly a `FixedSublattice`{.AgdaRecord}: the
upper embedding `Θ 1F` is its `θ`, the lower `Θ 0F` its fixed copy `Θ`.  In the
converse direction the generator the lower embedding misses is the one
`Θ-misses`{.AgdaFunction} finds by Whitman decisions.

```agda
-- A coherent chain of length two is a fixed-sublattice configuration.
coherent₂→fixed : Coherent 2 → FixedSublattice
coherent₂→fixed C = record
  { θ         = Θ 1F
  ; θ-free    = Θ-free 1F
  ; missed    = missed 1F
  ; missed∉θ  = missed∉ 1F
  ; Θ         = Θ 0F
  ; Θ-free    = Θ-free 0F
  ; fixes     = coherent (s≤s z≤n)
  }
  where open Coherent C

-- And conversely.
fixed→coherent₂ : FixedSublattice → Coherent 2
fixed→coherent₂ F = record
  { Θ         = Θ₂
  ; Θ-free    = Θ₂-free
  ; missed    = missed₂
  ; missed∉   = missed∉₂
  ; coherent  = coh
  }
  where
  open FixedSublattice F

  Θ₂ : Fin 2 → Sub (Fin 3) (Fin 3)
  Θ₂ 0F = Θ
  Θ₂ 1F = θ

  Θ₂-free : ∀ j → FreelyGenerates (Θ₂ j)
  Θ₂-free 0F = Θ-free
  Θ₂-free 1F = θ-free

  missed₂ : Fin 2 → Fin 3
  missed₂ 0F = proj₁ (Θ-misses F)
  missed₂ 1F = missed

  missed∉₂ : ∀ j i → ¬ (ℊ (missed₂ j) ≈ʷ Θ₂ j i)
  missed∉₂ 0F = proj₂ (Θ-misses F)
  missed∉₂ 1F = missed∉θ

  coh : ∀ {j k} → j < k → ∀ i → Θ₂ j i [ Θ₂ k ] ≈ʷ Θ₂ j i
  coh {0F} {1F} _        = fixes
  coh {0F} {0F} ()
  coh {1F} {0F} ()
  coh {1F} {1F} (s≤s ())
```

**Lemma 6.3** of [the paper][], as one statement.  For a coherent chain
`Θ₀, …, Θₙ₋₁`, the images `Mⱼ = Θⱼ(FL(3))`, the sublattices `⟨ Θ j ⟩`, ascend
strictly, `Mⱼ ⊊ Mₖ` for `j < k`; each is proper in `FL(3)`, some generator
lying outside it, so that `Mₙ₋₁ ⊊ FL(3)`; and each is a copy of `FL(3)`,
since `Θⱼ` freely generates.  And a coherent chain of length two is exactly
the configuration of the one-step form of Theorem C, a proper self-embedding
`Θ₁` fixing pointwise the copy `Θ₀(FL(3))` (`FixedSublattice`{.AgdaRecord}):
each gives the other, with `Θ₁` its embedding and `Θ₀` its copy.

```agda
-- Lemma 6.3: the images of a coherent chain ascend strictly inside FL(3), each a copy of FL(3);
-- and a coherent chain of length two is the configuration of Theorem C (one step).
Lemma-6·3 : Type
Lemma-6·3 =
    (∀ {n} (C : Coherent n)
     →  (∀ {j k} → j < k → ⟨ Coherent.Θ C j ⟩ ⊂ ⟨ Coherent.Θ C k ⟩)
      × (∀ j → Σ[ g ∈ Fin 3 ] ¬ ⟨ Coherent.Θ C j ⟩ (ℊ g))
      × (∀ j → FreelyGenerates (Coherent.Θ C j)))
  × ((C : Coherent 2) → Σ[ F ∈ FixedSublattice ]
       FixedSublattice.θ F ≡ Coherent.Θ C 1F × FixedSublattice.Θ F ≡ Coherent.Θ C 0F)
  × ((F : FixedSublattice) → Σ[ C ∈ Coherent 2 ]
       Coherent.Θ C 1F ≡ FixedSublattice.θ F × Coherent.Θ C 0F ≡ FixedSublattice.Θ F)

-- The proof of Lemma 6.3.
lemma-6·3 : Lemma-6·3
lemma-6·3 =
    (λ C →  (λ j<k → step→⊂ (step C j<k))
          , (λ j → Coherent.missed C j , λ (t , e) → fresh∉⟨σ⟩ (top-step C j) t e)
          , Coherent.Θ-free C)
  , (λ C → coherent₂→fixed C , refl , refl)
  , (λ F → fixed→coherent₂ F , refl , refl)
```

Dropping the top link, or the bottom one, keeps a coherent chain coherent: the
first `n` of `n + 1` embeddings, or the last `n`, with the same equations.

```agda
-- The first n links of a coherent chain of length n + 1.
drop-top : {n : ℕ} → Coherent (suc n) → Coherent n
drop-top C = record
  { Θ         = λ j → Θ (inject₁ j)
  ; Θ-free    = λ j → Θ-free (inject₁ j)
  ; missed    = λ j → missed (inject₁ j)
  ; missed∉   = λ j → missed∉ (inject₁ j)
  ; coherent  = λ {j} {k} j<k → coherent (inject₁-< j<k)
  }
  where
  open Coherent C

  -- inject₁ preserves the order.
  inject₁-< : ∀ {m} {j k : Fin m} → j < k → inject₁ j < inject₁ k
  inject₁-< {j = j} {k} j<k =
    subst (λ a → a <ℕ toℕ (inject₁ k)) (sym (toℕ-inject₁ j))
          (subst (toℕ j <ℕ_) (sym (toℕ-inject₁ k)) j<k)

-- The last n links of a coherent chain of length n + 1.
drop-bottom : {n : ℕ} → Coherent (suc n) → Coherent n
drop-bottom C = record
  { Θ         = λ j → Θ (suc j)
  ; Θ-free    = λ j → Θ-free (suc j)
  ; missed    = λ j → missed (suc j)
  ; missed∉   = λ j → missed∉ (suc j)
  ; coherent  = λ j<k → coherent (s≤s j<k)
  }
  where open Coherent C
```

#### An infinite coherent chain has unbounded complexity

An infinite coherent chain is the same record with `ℕ` for `Fin n`
(`Coherentω`{.AgdaRecord}); it is what the coherent form of Theorem C of
[the paper][] extracts from a chain, and what Dean's problem asks for.  If its
embeddings had generator images of bounded complexity, two of them would
coincide, `Θ j ≈ Θ k` with `j < k`; coherence gives `Θ j i [ Θ j ] ≈ʷ Θ j i`
for every `i`, so every `t [ Θ j ]` equals `t [ Θ j ] [ Θ j ]`, and injectivity
of `Θ j` makes `t ≈ʷ t [ Θ j ]` for every `t`: `Θ j` fixes every generator, and
misses none.

```agda
-- An infinite coherent chain: proper self-embeddings Θ₀, Θ₁, … with Θ k ∘ Θ j = Θ j for j < k.
record Coherentω : Type where
  field
    Θ         : ℕ → Sub (Fin 3) (Fin 3)
    Θ-free    : ∀ j → FreelyGenerates (Θ j)
    missed    : ℕ → Fin 3
    missed∉   : ∀ j i → ¬ (ℊ (missed j) ≈ʷ Θ j i)
    coherent  : ∀ {j k} → j <ℕ k → ∀ i → Θ j i [ Θ k ] ≈ʷ Θ j i

  -- The first n links, as a coherent chain of length n.
  prefix : (n : ℕ) → Coherent n
  prefix n = record
    { Θ         = λ j → Θ (toℕ j)
    ; Θ-free    = λ j → Θ-free (toℕ j)
    ; missed    = λ j → missed (toℕ j)
    ; missed∉   = λ j → missed∉ (toℕ j)
    ; coherent  = λ j<k → coherent j<k
    }

-- No infinite coherent chain has generator images of bounded complexity.
coherentω-unbounded : (C : Coherentω) (B : ℕ)
                    → (∀ j i → complexity (_≟_ {3}) (Coherentω.Θ C j i) ≤ B) → ⊥
coherentω-unbounded C B bnd =
  let (j , k , j<k , e) = pigeonhole-≈ⁿ (bounded B) 3 Θ (λ j i → bounded-complete B (Θ j i) (bnd j i))
      -- Θ j absorbs itself: Θ j i [ Θ j ] ≈ʷ Θ j i.
      self : ∀ i → Θ j i [ Θ j ] ≈ʷ Θ j i
      self i = ≈ʷ-trans ([]-congʳ (Θ j i) e) (coherent j<k i)
      -- So Θ j fixes every generator.
      fixes : ∀ i → Θ j i ≈ʷ ℊ i
      fixes i = ≈ʷ-sym (freelyGenerates→injective (Θ j) (Θ-free j) {ℊ i} {Θ j i} (≈ʷ-sym (self i)))
  in missed∉ j (missed j) (≈ʷ-sym (fixes (missed j)))
  where
  open Coherentω C
  open Bounded (_≟_ {3}) (allFin 3) ∈-allFin using ( bounded ; bounded-complete )
```

**Proposition 6.6** of [the paper][], as one statement: no infinite coherent
chain has generator images of bounded complexity.

```agda
-- Proposition 6.6: the generator images of an infinite coherent chain have unbounded complexity.
Proposition-6·6 : Type
Proposition-6·6 =  (C : Coherentω) (B : ℕ)
                   → ¬ (∀ j i → complexity (_≟_ {3}) (Coherentω.Θ C j i) ≤ B)

-- The proof of Proposition 6.6.
proposition-6·6 : Proposition-6·6
proposition-6·6 = coherentω-unbounded
```

#### Transitions from any base

[DeansProblem.Coherent][] defines the transition `transition c j e` of a
chain `c`, the terms `θ_{j,e+j}` expressing the `j`-th link in the `(e + j)`-th,
and proves that transitions from the bottom compose.  They compose from any base
(`transition-⨟′`{.AgdaFunction}): `θ_{j,e+d+j} = θ_{d+j,e+d+j} ∘ θ_{j,d+j}`, by
induction on `e`.  And from any base they have bounded complexity
(`transition-bound′`{.AgdaFunction}): `gens j i` is `θ_{j,e+j} i` evaluated at
the embedding `gens (e + j)`, which never lowers complexity.

```agda
module _ {X : Type χ} (c : Chain X) where
  open Chain c

  -- Transitions compose from any base.
  transition-⨟′ : ∀ j d e i → transition c j (e + d) i ≡ transition c j d i [ transition c (d + j) e ]
  transition-⨟′ j d zero     i = sym ([]-ℊ (transition c j d i))
  transition-⨟′ j d (suc e)  i =
    trans (cong (_[ terms (e + d + j) ]) (transition-⨟′ j d e i))
          (trans (cong (λ m → transition c j d i [ transition c (d + j) e ] [ terms m ]) (+-assoc e d j))
                 (sym ([]-⨟ (transition c j d i) (transition c (d + j) e) (terms (e + (d + j))))))

```

#### The four-link criterion

Fix a chain and four links `i ≤ j < k < l`, given by `i` and the offsets
`j = d₁ + i`, `k = suc d₂ + j`, `l = suc d₃ + k`.  Suppose `θ_{i,j} = θ_{i,l}` and
`θ_{j,k} = θ_{j,l}`.  Then `Θ₀ = θ_{i,l}`, `Θ₁ = θ_{j,l}`, `Θ₂ = θ_{k,l}` form a
coherent chain of length three (`four-links→coherent₃′`{.AgdaFunction}):

+  each `θ_{a,l}` freely generates, as a first factor of the injective `gens a`
   (`gens a = gens l ∘ θ_{a,l}`);
+  each misses the fresh generator of the last step before `l`, because
   `θ_{a,l}` is `θ_{a,l-1}` followed by the terms of that step, and
   Corollary 1.6 keeps the fresh generator outside the image of those terms;
+  `Θ₁ ∘ Θ₀ = Θ₀`: `θ_{i,l} = θ_{j,l} ∘ θ_{i,j} = θ_{j,l} ∘ θ_{i,l}`;
   `Θ₂ ∘ Θ₁ = Θ₁`: `θ_{j,l} = θ_{k,l} ∘ θ_{j,k} = θ_{k,l} ∘ θ_{j,l}`; and
   `Θ₂ ∘ Θ₀ = Θ₀` through the derived equation
   `θ_{i,k} = θ_{j,k} ∘ θ_{i,j} = θ_{j,l} ∘ θ_{i,l} = θ_{i,l}`.

The offset `d₁` may be zero (then `Θ₀ = Θ₁` and the hypotheses are
contradictory, which costs the construction nothing); `d₂` and `d₃` are
positive, so that `l` has a last step and `Θ₂` is proper.

```agda
module _ {X : Type χ} (c : Chain X) where
  open Chain c

  private
    -- θ_{a,l} freely generates, as a first factor of the injective gens a.
    transition-free : ∀ a e → FreelyGenerates (transition c a e)
    transition-free a e =
      injective→freelyGenerates _
        (first-factor-injective (transition c a e) (gens (e + a)) (gens a)
                                (gens≈transition c a e)
                                (freelyGenerates→injective (gens a) (gens-free a)))

    -- θ_{a,l} misses the fresh generator of the last step before l = suc e + a.
    transition-misses : ∀ a e i → ¬ (ℊ (fresh (e + a)) ≈ʷ transition c a (suc e) i)
    transition-misses a e i p =
      let (i' , e') = generator-in-image (terms (e + a)) (transition c a e i) p
      in fresh∉ (e + a) i' e'

  -- Four links i ≤ j < k < l with θ_{i,j} = θ_{i,l} and θ_{j,k} = θ_{j,l} give a coherent chain of length three.
  four-links→coherent₃′ : (i d₁ d₂ d₃ : ℕ)
    → (∀ v → transition c i d₁ v ≈ʷ transition c i (suc d₃ + suc d₂ + d₁) v)
    → (∀ v → transition c (d₁ + i) (suc d₂) v ≈ʷ transition c (d₁ + i) (suc d₃ + suc d₂) v)
    → Coherent 3
  four-links→coherent₃′ i d₁ d₂ d₃ H₁ H₂ = record
    { Θ         = Θ₃
    ; Θ-free    = Θ₃-free
    ; missed    = λ _ → fresh (d₃ + (suc d₂ + (d₁ + i)))
    ; missed∉   = Θ₃-misses
    ; coherent  = coh
    }
    where
    -- The links j and k, and the offsets to l.
    j k : ℕ
    j = d₁ + i
    k = suc d₂ + j

    -- The three embeddings: θ_{i,l}, θ_{j,l}, θ_{k,l}.
    Θ₀ Θ₁ Θ₂ : Sub (Fin 3) (Fin 3)
    Θ₀ = transition c i (suc d₃ + suc d₂ + d₁)
    Θ₁ = transition c j (suc d₃ + suc d₂)
    Θ₂ = transition c k (suc d₃)

    Θ₃ : Fin 3 → Sub (Fin 3) (Fin 3)
    Θ₃ 0F = Θ₀
    Θ₃ 1F = Θ₁
    Θ₃ 2F = Θ₂

    Θ₃-free : ∀ a → FreelyGenerates (Θ₃ a)
    Θ₃-free 0F = transition-free i (suc d₃ + suc d₂ + d₁)
    Θ₃-free 1F = transition-free j (suc d₃ + suc d₂)
    Θ₃-free 2F = transition-free k (suc d₃)

    -- l - 1, written three ways.
    l₁ : d₃ + suc d₂ + d₁ + i ≡ d₃ + (suc d₂ + (d₁ + i))
    l₁ = trans (+-assoc (d₃ + suc d₂) d₁ i) (+-assoc d₃ (suc d₂) (d₁ + i))

    l₂ : d₃ + suc d₂ + j ≡ d₃ + (suc d₂ + (d₁ + i))
    l₂ = +-assoc d₃ (suc d₂) (d₁ + i)

    Θ₃-misses : ∀ a v → ¬ (ℊ (fresh (d₃ + (suc d₂ + (d₁ + i)))) ≈ʷ Θ₃ a v)
    Θ₃-misses 0F v = subst (λ m → ¬ (ℊ (fresh m) ≈ʷ Θ₀ v)) l₁ (transition-misses i (d₃ + suc d₂ + d₁) v)
    Θ₃-misses 1F v = subst (λ m → ¬ (ℊ (fresh m) ≈ʷ Θ₁ v)) l₂ (transition-misses j (d₃ + suc d₂) v)
    Θ₃-misses 2F v = transition-misses k d₃ v

    -- The cocycles: θ_{i,l} = θ_{j,l} ∘ θ_{i,j}, θ_{j,l} = θ_{k,l} ∘ θ_{j,k},
    -- θ_{i,k} = θ_{j,k} ∘ θ_{i,j}, θ_{i,l} = θ_{k,l} ∘ θ_{i,k}.
    il : ∀ v → Θ₀ v ≡ transition c i d₁ v [ Θ₁ ]
    il v = transition-⨟′ c i d₁ (suc d₃ + suc d₂) v

    jl : ∀ v → Θ₁ v ≡ transition c j (suc d₂) v [ Θ₂ ]
    jl v = transition-⨟′ c j (suc d₂) (suc d₃) v

    ik : ∀ v → transition c i (suc d₂ + d₁) v ≡ transition c i d₁ v [ transition c j (suc d₂) ]
    ik v = transition-⨟′ c i d₁ (suc d₂) v

    il′ : ∀ v → Θ₀ v ≡ transition c i (suc d₂ + d₁) v [ Θ₂ ]
    il′ v = trans (cong (λ m → transition c i m v) (+-assoc (suc d₃) (suc d₂) d₁))
                  (trans (transition-⨟′ c i (suc d₂ + d₁) (suc d₃) v)
                         (cong (λ m → transition c i (suc d₂ + d₁) v [ transition c m (suc d₃) ])
                               (+-assoc (suc d₂) d₁ i)))

    -- Θ₁ ∘ Θ₀ = Θ₀.
    coh₀₁ : ∀ v → Θ₀ v [ Θ₁ ] ≈ʷ Θ₀ v
    coh₀₁ v = ≈ʷ-trans ([]-cong Θ₁ (≈ʷ-sym (H₁ v))) (subst (transition c i d₁ v [ Θ₁ ] ≈ʷ_) (sym (il v)) ≈ʷ-refl)

    -- Θ₂ ∘ Θ₁ = Θ₁.
    coh₁₂ : ∀ v → Θ₁ v [ Θ₂ ] ≈ʷ Θ₁ v
    coh₁₂ v = ≈ʷ-trans ([]-cong Θ₂ (≈ʷ-sym (H₂ v))) (subst (transition c j (suc d₂) v [ Θ₂ ] ≈ʷ_) (sym (jl v)) ≈ʷ-refl)

    -- The derived equation θ_{i,k} = θ_{i,l}.
    H₃ : ∀ v → transition c i (suc d₂ + d₁) v ≈ʷ Θ₀ v
    H₃ v = ≈ʷ-trans (subst (_≈ʷ transition c i d₁ v [ transition c j (suc d₂) ]) (sym (ik v)) ≈ʷ-refl)
             (≈ʷ-trans ([]-congʳ (transition c i d₁ v) H₂)
               (≈ʷ-trans ([]-cong Θ₁ (H₁ v)) (coh₀₁ v)))

    -- Θ₂ ∘ Θ₀ = Θ₀.
    coh₀₂ : ∀ v → Θ₀ v [ Θ₂ ] ≈ʷ Θ₀ v
    coh₀₂ v = ≈ʷ-trans ([]-cong Θ₂ (≈ʷ-sym (H₃ v))) (subst (transition c i (suc d₂ + d₁) v [ Θ₂ ] ≈ʷ_) (sym (il′ v)) ≈ʷ-refl)

    coh : ∀ {a b} → a < b → ∀ v → Θ₃ a v [ Θ₃ b ] ≈ʷ Θ₃ a v
    coh {0F} {1F} _ = coh₀₁
    coh {0F} {2F} _ = coh₀₂
    coh {1F} {2F} _ = coh₁₂
    coh {0F} {0F} ()
    coh {1F} {0F} ()
    coh {1F} {1F} (s≤s ())
    coh {2F} {0F} ()
    coh {2F} {1F} (s≤s ())
    coh {2F} {2F} (s≤s (s≤s ()))
```

The construction uses no decision, so it takes no decidable equality on the
generators.  An earlier form took it, as an argument it never used, and is
kept under its name for its users (`four-links→coherent₃`{.AgdaFunction}).

```agda
module _ {X : Type χ} (_≟ˣ_ : DecidableEquality X) (c : Chain X) where
  -- The four-link criterion, with decidable equality it does not use, kept for its users.
  four-links→coherent₃ : (i d₁ d₂ d₃ : ℕ)
    → (∀ v → transition c i d₁ v ≈ʷ transition c i (suc d₃ + suc d₂ + d₁) v)
    → (∀ v → transition c (d₁ + i) (suc d₂) v ≈ʷ transition c (d₁ + i) (suc d₃ + suc d₂) v)
    → Coherent 3
  four-links→coherent₃ = four-links→coherent₃′ c
```

**Theorem C (four links)** of [the paper][], as one statement: four links
`i ≤ j < k < l` of a chain, given by `i` and the offsets `j = d₁ + i`,
`k = suc d₂ + j` and `l = suc d₃ + k`, with `θ_{i,j} = θ_{i,l}` and
`θ_{j,k} = θ_{j,l}`, give a coherent chain of length three, namely
`Θ₀ = θ_{i,l}`, `Θ₁ = θ_{j,l}` and `Θ₂ = θ_{k,l}`.  The transition `θ_{a,b}`
is `transition c a (b ∸ a)`.  The paper asks `i < j`; the statement allows
`i = j` too.  It has no hypothesis beyond the paper's.

```agda
-- Theorem C (four links): four links with θ_{i,j} = θ_{i,l} and θ_{j,k} = θ_{j,l} give the
-- coherent chain θ_{i,l}, θ_{j,l}, θ_{k,l} of length three.
Theorem-C-four-links : Setω
Theorem-C-four-links =
  ∀ {χ} {X : Type χ} (c : Chain X) (i d₁ d₂ d₃ : ℕ)
  → (∀ v → transition c i d₁ v ≈ʷ transition c i (suc d₃ + suc d₂ + d₁) v)
  → (∀ v → transition c (d₁ + i) (suc d₂) v ≈ʷ transition c (d₁ + i) (suc d₃ + suc d₂) v)
  → Σ[ C ∈ Coherent 3 ]  Coherent.Θ C 0F ≡ transition c i (suc d₃ + suc d₂ + d₁)
                       × Coherent.Θ C 1F ≡ transition c (d₁ + i) (suc d₃ + suc d₂)
                       × Coherent.Θ C 2F ≡ transition c (suc d₂ + (d₁ + i)) (suc d₃)

-- The proof of Theorem C (four links).
theorem-C-four-links : Theorem-C-four-links
theorem-C-four-links c i d₁ d₂ d₃ H₁ H₂ = four-links→coherent₃′ c i d₁ d₂ d₃ H₁ H₂ , refl , refl , refl
```

#### The extraction under a recurrence hypothesis

`Recurs j`{.AgdaFunction} says that the transition `θ_{0,j}` recurs beyond
every bound: for every `m` there is an offset `e > m` with `θ_{0,e+j} = θ_{0,j}`.
From it a strictly increasing sequence of recurrences is read off
(`offsets`{.AgdaFunction}), the transitions `θ_{j,eₜ+j}` along it have
complexity bounded by the generators of link `j`, so two of them agree by the
pigeonhole for triples, and the four links `0 ≤ j < eₜ + j < eₜ′ + j` satisfy
the criterion (`chain→coherent₃`{.AgdaFunction}).

```agda
module _ {X : Type χ} (_≟ˣ_ : DecidableEquality X) (c : Chain X) where
  open Chain c
  open Bounded (_≟_ {3}) (allFin 3) ∈-allFin using ( bounded ; bounded-complete )

  private
    κˣ : LatTerm X → ℕ
    κˣ = complexity _≟ˣ_

  -- The transition from the bottom to link j recurs beyond every bound.
  Recurs : ℕ → Type
  Recurs j = ∀ m → Σ[ e ∈ ℕ ] m <ℕ e × (∀ v → transition c 0 (e + j) v ≈ʷ transition c 0 j v)

  module _ (j : ℕ) (R : Recurs j) where
    -- A strictly increasing sequence of recurrences.
    offsets : ℕ → ℕ
    offsets zero     = proj₁ (R 0)
    offsets (suc t)  = proj₁ (R (offsets t))

    offsets-step : ∀ t → offsets t <ℕ offsets (suc t)
    offsets-step t = proj₁ (proj₂ (R (offsets t)))

    offsets-mono : ∀ t d → offsets t <ℕ offsets (suc d + t)
    offsets-mono t zero     = offsets-step t
    offsets-mono t (suc d)  = <-trans (offsets-mono t d) (offsets-step (suc d + t))

    offsets-positive : ∀ t → 0 <ℕ offsets t
    offsets-positive zero     = proj₁ (proj₂ (R 0))
    offsets-positive (suc t)  = <-trans (offsets-positive t) (offsets-step t)

    offsets-recur : ∀ t v → transition c 0 (offsets t + j) v ≈ʷ transition c 0 j v
    offsets-recur zero     = proj₂ (proj₂ (R 0))
    offsets-recur (suc t)  = proj₂ (proj₂ (R (offsets t)))

    -- Two of the transitions θ_{j, offsets t + j} agree.
    transitions-repeat : Σ[ t ∈ ℕ ] Σ[ t′ ∈ ℕ ] t <ℕ t′
                       × (∀ v → transition c j (offsets t) v ≈ʷ transition c j (offsets t′) v)
    transitions-repeat =
      let (C , C-bound) = bound 3 (λ v → κˣ (gens j v))
      in pigeonhole-≈ⁿ (bounded C) 3 (λ t → transition c j (offsets t))
           (λ t v → bounded-complete C (transition c j (offsets t) v)
                      (≤-trans (transition-bound′ _≟ˣ_ c j (offsets t) v) (C-bound v)))

    -- A coherent chain of length three.
    chain→coherent₃ : Coherent 3
    chain→coherent₃ =
      let (t , t′ , t<t′ , E) = transitions-repeat
          (d , t+d≡t′) = m≤n⇒∃[o]m+o≡n t<t′
          -- t′ = suc d + t
          t′≡ : t′ ≡ suc d + t
          t′≡ = trans (sym t+d≡t′) (cong suc (+-comm t d))
          -- offsets t = suc d₂, offsets t′ = suc d₃ + suc d₂
          (d₂ , 1+d₂≡e) = m≤n⇒∃[o]m+o≡n (offsets-positive t)
          e≡ : offsets t ≡ suc d₂
          e≡ = sym 1+d₂≡e
          (d₃ , e+d₃≡e′) = m≤n⇒∃[o]m+o≡n (subst (λ u → offsets t <ℕ offsets u) (sym t′≡) (offsets-mono t d))
          e′≡ : offsets t′ ≡ suc d₃ + suc d₂
          e′≡ = trans (sym e+d₃≡e′)
                      (trans (cong (λ m → suc m + d₃) e≡)
                             (cong suc (trans (cong suc (+-comm d₂ d₃)) (sym (+-suc d₃ d₂)))))
          H₁ : ∀ v → transition c 0 j v ≈ʷ transition c 0 (suc d₃ + suc d₂ + j) v
          H₁ v = ≈ʷ-sym (subst (λ m → transition c 0 (m + j) v ≈ʷ transition c 0 j v) e′≡ (offsets-recur t′ v))
          H₂ : ∀ v → transition c (j + 0) (suc d₂) v ≈ʷ transition c (j + 0) (suc d₃ + suc d₂) v
          H₂ v = subst (λ a → transition c a (suc d₂) v ≈ʷ transition c a (suc d₃ + suc d₂) v)
                       (sym (+-identityʳ j))
                       (subst (λ m → transition c j (suc d₂) v ≈ʷ transition c j m v) e′≡
                              (subst (λ m → transition c j m v ≈ʷ transition c j (offsets t′) v) e≡ (E v)))
      in four-links→coherent₃ _≟ˣ_ c 0 j d₂ d₃ H₁ H₂
```

**Theorem C (length three)** of [the paper][], as one statement: if the
transition from the bottom to some link `j` recurs beyond every bound, for
every `m` there being `l > m` with `θ_{0,l} = θ_{0,j}`, the chain yields a
coherent chain of length three.  The hypothesis is the paper's, read with `l`
an index of a link; `Recurs`{.AgdaFunction} reads it with `l = e + j`.  The
hypothesis beyond the paper's is decidable equality on the generators, which
the bound of Lemma 6.1 needs.

```agda
-- Theorem C (length three): a recurring transition from the bottom yields a coherent chain of
-- length three.
Theorem-C-length-three : Setω
Theorem-C-length-three =
  ∀ {χ} {X : Type χ} → DecidableEquality X → (c : Chain X) (j : ℕ)
  → (∀ m → Σ[ l ∈ ℕ ] m <ℕ l × (∀ i → transition c 0 l i ≈ʷ transition c 0 j i))
  → Coherent 3

-- The proof of Theorem C (length three).
theorem-C-length-three : Theorem-C-length-three
theorem-C-length-three _≟ˣ_ c j H = chain→coherent₃ _≟ˣ_ c j R
  where
  -- The hypothesis read with l = e + j: H at m + j gives l = suc m + o + j.
  R : Recurs _≟ˣ_ c j
  R m =
    let (l , m+j<l , e) = H (m + j)
        (o , lo) = m≤n⇒∃[o]m+o≡n m+j<l
        l≡ : suc (m + o) + j ≡ l
        l≡ = trans (cong suc (trans (+-assoc m o j) (trans (cong (m +_) (+-comm o j)) (sym (+-assoc m j o)))))
                   lo
    in  suc (m + o) , s≤s (m≤m+n m o)
      , λ v → subst (λ k → transition c 0 k v ≈ʷ transition c 0 j v) (sym l≡) (e v)
```

--------------------------------------

[DeansProblem.Coherent.Finite]: DeansProblem.Coherent.Finite.html
[DeansProblem.Chain]: DeansProblem.Chain.html
[DeansProblem.Coherent]: DeansProblem.Coherent.html
[DeansProblem.Coherent.Infinite]: DeansProblem.Coherent.Infinite.html
[DeansProblem.LengthThree]: DeansProblem.LengthThree.html
[Freese, Ježek, and Nation (1995)]: https://doi.org/10.1090/surv/042
