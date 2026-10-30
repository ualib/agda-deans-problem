---
layout: default
file: "src/DeansProblem/Coherent/Infinite.lagda.md"
title: "DeansProblem.Coherent.Infinite module"
date: "2026-10-27"
author: "the agda-lattices development team"
---

### Infinite coherent chains, from the infinite pigeonhole principle

This is the [DeansProblem.Coherent.Infinite][] module of this repository.

[the paper]: https://arxiv.org/abs/YYMM.NNNNN

Three statements of [the paper][] rest on the infinite pigeonhole principle,
which is classically true and not provable in Agda's constructive logic.  This
module proves each from the principle taken as a hypothesis, the record
`InfinitePigeonhole`{.AgdaRecord} of [DeansProblem.Pigeonhole][], which every
statement using it takes as an explicit argument; the converse directions use
nothing.  The statements are as follows.

+  **Remark 5.1** (`bottom-recurrence`{.AgdaFunction}).  In a chain
   `L₀ ⊊ L₁ ⊊ ⋯` with transitions `θ_{j,k}` ([DeansProblem.Coherent][]), one
   proper self-embedding `Θ` of `FL(3)` is the transition `θ_{0,k}` from the
   bottom for infinitely many `k`, so it expresses the bottom triple, by the
   same three terms, in infinitely many later triples.
+  **The length-three form of Theorem C, without its hypothesis**.  Some link
   `j` satisfies the recurrence hypothesis `Recurs j`{.AgdaFunction} of
   [DeansProblem.Coherent.Finite][] (`some-link-recurs`{.AgdaFunction}): an
   occurrence of the recurring value of Remark 5.1 serves.  So every chain
   yields a coherent chain of length three
   (`pigeonhole→coherent₃`{.AgdaFunction}), which is Remark 6.5's classical
   argument as a theorem.
+  **Theorem C, the coherent form** (`coherent-form`{.AgdaFunction}).  After
   passing to a subsequence of the chain, itself a chain
   (`subchain`{.AgdaFunction}), the transition from the `j`-th link to each
   later one depends only on `j`: it is one proper self-embedding `Θⱼ`, and
   the `Θⱼ` form an infinite coherent chain
   (`Coherentω`{.AgdaRecord}).  Conversely, the images of any infinite
   coherent chain form a chain inside `FL(3)`
   (`coherentω→chain`{.AgdaFunction}), with no hypothesis.
+  **Corollary 6.4** (`positive⇔coherentω`{.AgdaFunction}).  Dean's problem
   has a positive answer, over generators with decidable equality, if and only
   if an infinite coherent chain exists: the forward direction is the coherent
   form, under the principle, and the reverse direction the converse, with
   none.

**What is not in scope**.  Theorem H ([DeansProblem.NoChain][]) refutes every
chain, and Theorem G ([DeansProblem.LengthThree][]) every coherent chain of
length three, so with either in scope every statement here that assumes a
chain would follow by `⊥-elim`{.AgdaFunction} and argue nothing that the
paper argues.  This module imports neither, directly or through another
module; it repeats privately the two definitions of
[DeansProblem.NoChain][] that bound the transitions from a link, and its
proofs are the paper's arguments.

<!--
```agda
{-# OPTIONS --without-K --exact-split --safe #-}

module DeansProblem.Coherent.Infinite where

open import Agda.Primitive  using ( Setω ) renaming ( Set to Type )

-- Imports from the Agda Standard Library ---------------------------------------
open import Data.Fin.Base                          using ( Fin )
open import Data.Fin.Properties                    using ( _≟_ )
open import Data.List.Base                         using ( allFin )
open import Data.List.Membership.Propositional.Properties
                                                   using ( ∈-allFin )
open import Data.List.Relation.Unary.Any           using ( Any )
open import Data.Nat.Base                          using ( ℕ ; zero ; suc ; _+_ ; _∸_ ; _≤_ ; _<_ ; pred
                                                         ; z≤n ; s≤s )
open import Data.Nat.Properties                    using ( ≤-refl ; ≤-reflexive ; ≤-trans ; <-trans ; <⇒≤
                                                         ; n≤1+n ; n<1+n ; m≤n+m ; +-comm ; +-∸-assoc
                                                         ; m∸n+n≡m ; n∸n≡0 ; m+n≤o⇒m≤o∸n
                                                         ; m≤n⇒m<n∨m≡n ; m≤n⇒∃[o]m+o≡n )
open import Data.Product                           using ( Σ-syntax ; _×_ ; _,_ ; proj₁ ; proj₂ )
open import Data.Sum.Base                          using ( [_,_]′ )
open import Function                               using ( _⇔_ ; mk⇔ )
open import Level                                  using ( Level ; 0ℓ ) renaming ( suc to lsuc )
open import Relation.Binary.Definitions            using ( DecidableEquality )
open import Relation.Binary.PropositionalEquality  using ( _≡_ ; refl ; sym ; trans ; cong ; subst ; subst₂ )
open import Relation.Nullary                       using ( ¬_ )

-- Imports from the Agda Universal Algebra Library ------------------------------
open import Lattices.Free.Canonical.Basic          using ( ≈ʷ-sym ; ≈ʷ-trans )
open import DeansProblem.Chain                     using ( Chain )
open import DeansProblem.Chain.Copies              using ( CopyChain ; copyChain→chain ; chain→copyChain )
open import DeansProblem.Coherent                  using ( bound ; first-factor-injective ; transition
                                                         ; gens≈transition ; transition-bound′ )
open import DeansProblem.Coherent.Finite           using ( Coherent ; Coherentω ; Recurs ; chain→coherent₃
                                                         ; transition-⨟′ )
open import DeansProblem.Pigeonhole                using ( InfinitePigeonhole ; constant-along )
open import Lattices.Free.Complexity               using ( complexity ; module Bounded )
open import Lattices.Free.Generation               using ( FreelyGenerates ; freelyGenerates→injective
                                                         ; injective→freelyGenerates ; generator-in-image )
open import Lattices.Free.Substitution             using ( Sub ; _[_] ; []-cong )
open import Lattices.Free.Term                     using ( ℊ )
open import Lattices.Free.Whitman                  using ( _≈ʷ_ )

private variable
  χ : Level
  X : Type χ
```
-->

#### Transitions between links

The transition `θ_{j,k}` between links `j ≤ k` (`between`{.AgdaFunction}) is
the transition from `j` over `k ∸ j` steps; between a link and itself it is the
identity (`between-refl`{.AgdaFunction}).  It expresses link `j` in link `k`
(`gens≈between`{.AgdaFunction}) and freely generates, as a first factor of the
injective `gens j` (`between-free`{.AgdaFunction}); for `j < k` it misses the
fresh generator of the step from `k - 1` to `k`, because it is the transition
to `k - 1` followed by the terms of that step, and Corollary 1.6 of [Freese,
Ježek, and Nation (1995)][] keeps the fresh generator outside the image of
those terms (`between-misses`{.AgdaFunction}).  For `j ≤ k ≤ l` the cocycle
identity reads `θ_{j,l} = θ_{k,l} ∘ θ_{j,k}` (`between-cocycle`{.AgdaFunction}),
the cocycle from any base with the offsets `k ∸ j` and `l ∸ k`, which add up
to `l ∸ j` (`∸-split`{.AgdaFunction}).

```agda
-- The offset from j to l splits at k, for j ≤ k ≤ l.
∸-split : {j k l : ℕ} → j ≤ k → k ≤ l → l ∸ j ≡ (l ∸ k) + (k ∸ j)
∸-split {j} {k} {l} j≤k k≤l = trans (cong (_∸ j) (sym (m∸n+n≡m k≤l))) (+-∸-assoc (l ∸ k) j≤k)

module _ {X : Type χ} (c : Chain X) where
  open Chain c

  -- The transition θ_{j,k} between links j ≤ k: the transition from j over k ∸ j steps.
  between : ℕ → ℕ → Sub (Fin 3) (Fin 3)
  between j k = transition c j (k ∸ j)

  -- Between a link and itself it is the identity.
  between-refl : ∀ j i → between j j i ≡ ℊ i
  between-refl j i = cong (λ e → transition c j e i) (n∸n≡0 j)

  -- It expresses link j in link k.
  gens≈between : ∀ {j k} → j ≤ k → ∀ i → gens j i ≈ʷ between j k i [ gens k ]
  gens≈between {j} {k} j≤k i =
    subst (λ m → gens j i ≈ʷ between j k i [ gens m ]) (m∸n+n≡m j≤k) (gens≈transition c j (k ∸ j) i)

  -- It freely generates, as a first factor of the injective gens j.
  between-free : ∀ j k → FreelyGenerates (between j k)
  between-free j k =
    injective→freelyGenerates _
      (first-factor-injective (between j k) (gens (k ∸ j + j)) (gens j) (gens≈transition c j (k ∸ j))
                              (freelyGenerates→injective (gens j) (gens-free j)))

  private
    -- The transition from a over e + 1 steps misses the fresh generator of its last step.
    transition-misses : ∀ a e i → ¬ (ℊ (fresh (e + a)) ≈ʷ transition c a (suc e) i)
    transition-misses a e i p =
      let (i′ , p′) = generator-in-image (terms (e + a)) (transition c a e i) p
      in fresh∉ (e + a) i′ p′

  -- For j < k it misses the fresh generator of the step from k - 1 to k.
  between-misses : ∀ {j k} → j < k → ∀ i → ¬ (ℊ (fresh (pred k)) ≈ʷ between j k i)
  between-misses {j} (s≤s {n = k} j≤k) i p =
    transition-misses j (k ∸ j) i
      (subst₂ (λ m e → ℊ (fresh m) ≈ʷ transition c j e i) (sym (m∸n+n≡m j≤k)) (+-∸-assoc 1 j≤k) p)

  -- The cocycle identity between links j ≤ k ≤ l.
  between-cocycle : ∀ {j k l} → j ≤ k → k ≤ l → ∀ i → between j l i ≡ between j k i [ between k l ]
  between-cocycle {j} {k} {l} j≤k k≤l i =
    trans (cong (λ e → transition c j e i) (∸-split j≤k k≤l))
          (trans (transition-⨟′ c j (k ∸ j) (l ∸ k) i)
                 (cong (λ m → between j k i [ transition c m (l ∸ k) ]) (m∸n+n≡m j≤k)))
```

#### Subsequences of a chain

A selection `h`, a strictly increasing sequence of natural numbers, picks the
links `h 0 < h 1 < ⋯` of a chain.  A selection moves every index forward and
preserves the strict and the weak order.  The selected links form a chain
(`subchain`{.AgdaFunction}): its `j`-th step is the containment
`L_{h j} ⊊ L_{h (j+1)}`, whose terms are the transition between the two links
and whose fresh generator is that of the last step before `h (j + 1)`.  Its
transitions are the transitions between the selected links
(`subchain-transition`{.AgdaFunction}), by induction on the number of steps
and the cocycle identity.

```agda
private
  module _ {h : ℕ → ℕ} (h-inc : ∀ t → h t < h (suc t)) where
    -- A selection moves every index forward.
    increasing-id : ∀ t → t ≤ h t
    increasing-id zero     = z≤n
    increasing-id (suc t)  = ≤-trans (s≤s (increasing-id t)) (h-inc t)

    -- It preserves the strict order.
    increasing-< : ∀ {a b} → a < b → h a < h b
    increasing-< (s≤s {n = b} a≤b) = [ (λ a<b → <-trans (increasing-< a<b) (h-inc b))
                                     , (λ a≡b → subst (λ a → h a < h (suc b)) (sym a≡b) (h-inc b))
                                     ]′ (m≤n⇒m<n∨m≡n a≤b)

    -- And the weak order.
    increasing-≤ : ∀ {a b} → a ≤ b → h a ≤ h b
    increasing-≤ a≤b = [ (λ a<b → <⇒≤ (increasing-< a<b)) , (λ a≡b → ≤-reflexive (cong h a≡b)) ]′
                         (m≤n⇒m<n∨m≡n a≤b)

module _ {X : Type χ} (c : Chain X) (h : ℕ → ℕ) (h-inc : ∀ t → h t < h (suc t)) where
  open Chain c

  -- The links h 0 < h 1 < ⋯ of the chain, as a chain.
  subchain : Chain X
  subchain = record
    { gens       = λ j → gens (h j)
    ; gens-free  = λ j → gens-free (h j)
    ; terms      = λ j → between c (h j) (h (suc j))
    ; gens≈      = λ j → gens≈between c (<⇒≤ (h-inc j))
    ; fresh      = λ j → fresh (pred (h (suc j)))
    ; fresh∉     = λ j → between-misses c (h-inc j)
    }

  -- Its transitions are the transitions between the selected links.
  subchain-transition : ∀ j e i → transition subchain j e i ≡ between c (h j) (h (e + j)) i
  subchain-transition j zero     i = sym (between-refl c (h j) i)
  subchain-transition j (suc e)  i =
    trans (cong (_[ between c (h (e + j)) (h (suc (e + j))) ]) (subchain-transition j e i))
          (sym (between-cocycle c (increasing-≤ h-inc (m≤n+m j e)) (<⇒≤ (h-inc (e + j))) i))
```

#### The statements

Remark 5.1 is a record (`BottomRecurrence`{.AgdaRecord}): a proper
self-embedding `Θ`, freely generating and missing a generator, and for every
`m` a link `k > m` whose transition from the bottom is `Θ`.  So `Θ` expresses
the bottom triple in the `k`-th by the same three terms
(`expresses`{.AgdaFunction}), since `θ_{0,k}` does.

```agda
-- Remark 5.1: one proper self-embedding of FL(3) is the transition from the bottom to infinitely many links.
record BottomRecurrence {X : Type χ} (c : Chain X) : Type where
  field
    Θ        : Sub (Fin 3) (Fin 3)
    Θ-free   : FreelyGenerates Θ
    missed   : Fin 3
    missed∉  : ∀ i → ¬ (ℊ missed ≈ʷ Θ i)
    recurs   : ∀ m → Σ[ k ∈ ℕ ] m < k × (∀ i → transition c 0 k i ≈ʷ Θ i)

  -- So Θ expresses the bottom triple in each of those links, by the same three terms.
  expresses : ∀ m → Σ[ k ∈ ℕ ] m < k × (∀ i → Chain.gens c 0 i ≈ʷ Θ i [ Chain.gens c k ])
  expresses m =
    let (k , m<k , e) = recurs m
    in k , m<k , λ i → ≈ʷ-trans (gens≈between c {k = k} z≤n i) ([]-cong (Chain.gens c k) (e i))
```

The coherent form of Theorem C is a record too (`CoherentForm`{.AgdaRecord}):
a selection `select` of the chain's links, an infinite coherent chain
`coherent-chain`, and the equation `θ_{select j, select l} = Θⱼ` for every
`j < l`.  Read in the selected subchain (`subsequence`{.AgdaFunction}), the
equation says that the subchain's transition from its `j`-th link to any later
one is `Θⱼ` (`subsequence-depends`{.AgdaFunction}): after passing to a
subsequence of the chain, the transition `θ_{j,k}` depends only on `j`, as
the paper states it.

```agda
-- Theorem C, the coherent form: a subsequence of the chain whose transitions from each link are one
-- proper self-embedding, and those embeddings form an infinite coherent chain.
record CoherentForm {X : Type χ} (c : Chain X) : Type where
  field
    select          : ℕ → ℕ
    ascends         : ∀ j → select j < select (suc j)
    coherent-chain  : Coherentω
    depends         : ∀ {j l} → j < l → ∀ i → between c (select j) (select l) i ≈ʷ Coherentω.Θ coherent-chain j i

  -- The subsequence, as a chain.
  subsequence : Chain X
  subsequence = subchain c select ascends

  -- Its transition from link j to any later one is Θ j.
  subsequence-depends : ∀ j e i → transition subsequence j (suc e) i ≈ʷ Coherentω.Θ coherent-chain j i
  subsequence-depends j e i =
    subst (_≈ʷ Coherentω.Θ coherent-chain j i) (sym (subchain-transition c select ascends j (suc e) i))
          (depends (s≤s (m≤n+m j e)) i)
```

#### Remark 5.1, and the length-three form without its hypothesis

Fix a chain over generators with decidable equality.  The transitions from a
link `j` are covered by the finite list of elements of `FL(3)` of complexity
at most the generators of link `j` (`transition-covered`{.AgdaFunction}, by
`transition-bound′`{.AgdaFunction} and `bounded-complete`{.AgdaFunction}).
For Remark 5.1, the principle gives a selection `h` along which the
transitions from the bottom are constant (`constant-along`{.AgdaFunction});
`Θ = θ_{0,h(1)}` is proper, since `h 1 > h 0 ≥ 0`, and it is the transition
to every `h (m + 1) > m`.  For `Recurs j`{.AgdaFunction}, take for `j` the
link `k₀ > 0` with `θ_{0,k₀} = Θ` that the remark gives first: for every `m`,
the remark's link `k > m + j` has `θ_{0,k} = Θ = θ_{0,j}`, so the offset
`k ∸ j > m` is a recurrence.  The length-three form of Theorem C
(`chain→coherent₃`{.AgdaFunction}) then applies with no further hypothesis.

```agda
module _ {X : Type χ} (_≟ˣ_ : DecidableEquality X) (c : Chain X) where
  open Chain c
  open Bounded (_≟_ {3}) (allFin 3) ∈-allFin using ( bounded ; bounded-complete )

  private
    -- A common complexity bound for the generators at link j.
    generator-bound : ℕ → ℕ
    generator-bound j = proj₁ (bound 3 (λ v → complexity _≟ˣ_ (gens j v)))

    -- Every transition from link j has a representative in the list of elements under that bound.
    transition-covered : ∀ j e v → Any (transition c j e v ≈ʷ_) (bounded (generator-bound j))
    transition-covered j e v =
      bounded-complete (generator-bound j) (transition c j e v)
        (≤-trans (transition-bound′ _≟ˣ_ c j e v) (proj₂ (bound 3 (λ v → complexity _≟ˣ_ (gens j v))) v))

  -- Remark 5.1, from the principle.
  bottom-recurrence : InfinitePigeonhole → BottomRecurrence c
  bottom-recurrence P = record
    { Θ        = transition c 0 (h 1)
    ; Θ-free   = between-free c 0 (h 1)
    ; missed   = fresh (pred (h 1))
    ; missed∉  = between-misses c (≤-trans (s≤s z≤n) (h-inc 0))
    ; recurs   = λ m → h (suc m) , increasing-id h-inc (suc m)
                     , λ i → ≈ʷ-trans (h-const (suc m) i) (≈ʷ-sym (h-const 1 i))
    }
    where
    -- A selection along which the transitions from the bottom are constant.
    constancy : Σ[ h ∈ (ℕ → ℕ) ] (∀ t → h t < h (suc t))
                × (∀ t i → transition c 0 (h t) i ≈ʷ transition c 0 (h 0) i)
    constancy = constant-along P (bounded (generator-bound 0)) 3 (transition c 0) (transition-covered 0)

    -- The selection, its steps, and the constancy.
    h : ℕ → ℕ
    h = proj₁ constancy

    h-inc : ∀ t → h t < h (suc t)
    h-inc = proj₁ (proj₂ constancy)

    h-const : ∀ t i → transition c 0 (h t) i ≈ʷ transition c 0 (h 0) i
    h-const = proj₂ (proj₂ constancy)

  -- Some link's transition from the bottom recurs beyond every bound, from the principle.
  some-link-recurs : InfinitePigeonhole → Σ[ j ∈ ℕ ] Recurs _≟ˣ_ c j
  some-link-recurs P = j , R
    where
    open BottomRecurrence (bottom-recurrence P)

    -- The first link the remark gives.
    j : ℕ
    j = proj₁ (recurs 0)

    -- Its transition from the bottom is Θ.
    j-recurs : ∀ v → transition c 0 j v ≈ʷ Θ v
    j-recurs = proj₂ (proj₂ (recurs 0))

    -- Every later link the remark gives beyond m + j is a recurrence of θ_{0,j}.
    R : Recurs _≟ˣ_ c j
    R m =
      let (k , m+j<k , e) = recurs (m + j)
          -- The link is past j.
          j≤k : j ≤ k
          j≤k = ≤-trans (m≤n+m j m) (<⇒≤ m+j<k)
      in k ∸ j , m+n≤o⇒m≤o∸n (suc m) m+j<k
       , λ v → subst (λ n → transition c 0 n v ≈ʷ transition c 0 j v) (sym (m∸n+n≡m j≤k))
                     (≈ʷ-trans (e v) (≈ʷ-sym (j-recurs v)))

  -- Theorem C, the length-three form, with its hypothesis from the principle (Remark 6.5).
  pigeonhole→coherent₃ : InfinitePigeonhole → Coherent 3
  pigeonhole→coherent₃ P = let (j , R) = some-link-recurs P in chain→coherent₃ _≟ˣ_ c j R
```

#### Theorem C, the coherent form

The diagonal argument of [the paper][] chooses `k₀ = 0` and an infinite set
`S₀` of indices `k > k₀` on which `θ_{k₀,k}` is constant; then
`k₁ = min S₀` and an infinite `S₁ ⊆ S₀` of indices `k > k₁` on which
`θ_{k₁,k}` is constant; and so on.  Here an infinite set is a selection, and
the recursion's state is the selection alone, its first value the current
link (`sets`{.AgdaFunction}).  The zeroth selection lists every index, so its
first value is `k₀ = 0`.  From a selection `g`, the transitions from `g 0` to
the later members `g (t + 1)` are covered by a finite list, so the principle
gives a selection `s` along which they are constant, and the next selection
is `t ↦ g (s t + 1)` (`next-set`{.AgdaFunction}): the paper's `Sⱼ`, with first
value `k_{j+1} = min Sⱼ` (`chosen`{.AgdaFunction}).  The witnesses the
principle returns are the only choices made, so no choice principle enters.

Each selection selects from the one before, so `θ_{kⱼ,k}` is the constant
value `Θⱼ = θ_{kⱼ,k_{j+1}}` for every member `k` of `Sⱼ`
(`first-constant`{.AgdaFunction}) and of every later selection
(`later-constant`{.AgdaFunction}), in particular for `k = k_l` with `l > j`
(`chosen-depends`{.AgdaFunction}).  Each `Θⱼ` is proper, by
`between-misses`{.AgdaFunction}, since `kⱼ < k_{j+1}`.  And the cocycle
identity `θ_{kⱼ,k_{l+1}} = θ_{k_l,k_{l+1}} ∘ θ_{kⱼ,k_l}`, for `j < l`, reads
`Θⱼ = Θ_l ∘ Θⱼ` (`Θ-coherent`{.AgdaFunction}): the `Θⱼ` form an infinite
coherent chain.

```agda
  module _ (P : InfinitePigeonhole) where
    private
      -- From a selection's first member, a selection of its later members on which the transitions are constant.
      constancy : (g : ℕ → ℕ) → Σ[ s ∈ (ℕ → ℕ) ] (∀ t → s t < s (suc t))
                  × (∀ t i → between c (g 0) (g (suc (s t))) i ≈ʷ between c (g 0) (g (suc (s 0))) i)
      constancy g = constant-along P (bounded (generator-bound (g 0))) 3 (λ t → between c (g 0) (g (suc t)))
                                   (λ t → transition-covered (g 0) (g (suc t) ∸ g 0))

      -- One level of the diagonal argument: those later members.
      next-set : (ℕ → ℕ) → ℕ → ℕ
      next-set g t = g (suc (proj₁ (constancy g) t))

      -- The selections: every index, then S₀ ⊇ S₁ ⊇ ⋯.
      sets : ℕ → ℕ → ℕ
      sets zero     t = t
      sets (suc j)  = next-set (sets j)

      -- The links of the subsequence: k₀ = 0, and k_{j+1} = min Sⱼ.
      chosen : ℕ → ℕ
      chosen j = sets j 0

      -- Each selection is strictly increasing.
      sets-increasing : ∀ j t → sets j t < sets j (suc t)
      sets-increasing zero     t = ≤-refl
      sets-increasing (suc j)  t = increasing-< (sets-increasing j) (s≤s (proj₁ (proj₂ (constancy (sets j))) t))

      -- So are the links.
      chosen-increasing : ∀ j → chosen j < chosen (suc j)
      chosen-increasing j = increasing-< (sets-increasing j) (s≤s z≤n)

      -- The constant values: Θⱼ = θ_{kⱼ,k_{j+1}}.
      Θ : ℕ → Sub (Fin 3) (Fin 3)
      Θ j = between c (chosen j) (chosen (suc j))

      -- From kⱼ, the transitions to the members of Sⱼ are all Θⱼ.
      first-constant : ∀ j t i → between c (chosen j) (sets (suc j) t) i ≈ʷ Θ j i
      first-constant j = proj₂ (proj₂ (constancy (sets j)))

      -- And to the members of every later selection, which selects from Sⱼ.
      later-constant : ∀ j d t i → between c (chosen j) (sets (d + suc j) t) i ≈ʷ Θ j i
      later-constant j zero     = first-constant j
      later-constant j (suc d)  t = later-constant j d (suc (proj₁ (constancy (sets (d + suc j))) t))

      -- So θ_{kⱼ,k_l} is Θⱼ for every l > j.
      chosen-depends : ∀ {j l} → j < l → ∀ i → between c (chosen j) (chosen l) i ≈ʷ Θ j i
      chosen-depends {j} {l} j<l i =
        let (d , e) = m≤n⇒∃[o]m+o≡n j<l
        in subst (λ m → between c (chosen j) (chosen m) i ≈ʷ Θ j i) (trans (+-comm d (suc j)) e)
                 (later-constant j d 0 i)

      -- The cocycle identity reads as coherence: Θ_l ∘ Θⱼ = Θⱼ for j < l.
      Θ-coherent : ∀ {j l} → j < l → ∀ i → Θ j i [ Θ l ] ≈ʷ Θ j i
      Θ-coherent {j} {l} j<l i =
        ≈ʷ-trans ([]-cong (Θ l) (≈ʷ-sym (chosen-depends j<l i)))
                 (subst (_≈ʷ Θ j i)
                        (between-cocycle c (<⇒≤ (increasing-< chosen-increasing j<l)) (<⇒≤ (chosen-increasing l)) i)
                        (chosen-depends (≤-trans j<l (n≤1+n l)) i))

      -- The Θⱼ form an infinite coherent chain.
      diagonal-chain : Coherentω
      diagonal-chain = record
        { Θ         = Θ
        ; Θ-free    = λ j → between-free c (chosen j) (chosen (suc j))
        ; missed    = λ j → fresh (pred (chosen (suc j)))
        ; missed∉   = λ j → between-misses c (chosen-increasing j)
        ; coherent  = Θ-coherent
        }

    -- Theorem C, the coherent form, from the principle.
    coherent-form : CoherentForm c
    coherent-form = record
      { select          = chosen
      ; ascends         = chosen-increasing
      ; coherent-chain  = diagonal-chain
      ; depends         = chosen-depends
      }
```

#### The converse and Corollary 6.4

Conversely, an infinite coherent chain is a chain inside `FL(3)`
(`coherentω→chain`{.AgdaFunction}): its triples are the `Θ k`, each expressed
in the next by itself, since `Θ (k + 1)` fixes it, and the fresh generator of
step `k` is the one `Θ k` misses.  This is Lemma 6.3 read for an infinite
chain; as a chain of copies (`coherentω→copyChain`{.AgdaFunction}) its links
are the images `Mₖ = Θₖ(FL(3))`.  It needs no hypothesis.

A positive answer to Dean's problem (`PositiveAnswer`{.AgdaFunction}) is a
type `X` of generators with decidable equality, the hypothesis Section 8.3 of
[the paper][] discloses, and a chain of copies of `FL(3)` in `FL(X)` as
Definition 4.1 states it ([DeansProblem.Chain.Copies][]).  From one, the
coherent form gives an infinite coherent chain, under the principle
(`positive→coherentω`{.AgdaFunction}); from an infinite coherent chain, the
converse gives a chain in `FL(3)`, whose generators have decidable equality,
with no hypothesis (`coherentω→positive`{.AgdaFunction}).  Together they are
Corollary 6.4 (`positive⇔coherentω`{.AgdaFunction}).

```agda
-- An infinite coherent chain is a chain inside FL(3).
coherentω→chain : Coherentω → Chain (Fin 3)
coherentω→chain C = record
  { gens       = Θ
  ; gens-free  = Θ-free
  ; terms      = Θ
  ; gens≈      = λ k i → ≈ʷ-sym (coherent (n<1+n k) i)
  ; fresh      = missed
  ; fresh∉     = missed∉
  }
  where open Coherentω C

-- The same as a chain of copies of FL(3): the images Mₖ = Θₖ(FL(3)) ascend strictly.
coherentω→copyChain : Coherentω → CopyChain (Fin 3)
coherentω→copyChain C = chain→copyChain (coherentω→chain C)

-- A positive answer to Dean's problem: a chain of copies of FL(3) in FL(X), X with decidable equality.
PositiveAnswer : Type (lsuc 0ℓ)
PositiveAnswer = Σ[ X ∈ Type ] DecidableEquality X × CopyChain X

-- From a positive answer, an infinite coherent chain, from the principle.
positive→coherentω : InfinitePigeonhole → PositiveAnswer → Coherentω
positive→coherentω P (X , _≟ˣ_ , c) = CoherentForm.coherent-chain (coherent-form _≟ˣ_ (copyChain→chain c) P)

-- From an infinite coherent chain, a positive answer, with no hypothesis.
coherentω→positive : Coherentω → PositiveAnswer
coherentω→positive C = Fin 3 , _≟_ , coherentω→copyChain C

-- Corollary 6.4: Dean's problem has a positive answer if and only if an infinite coherent chain exists.
positive⇔coherentω : InfinitePigeonhole → PositiveAnswer ⇔ Coherentω
positive⇔coherentω P = mk⇔ (positive→coherentω P) coherentω→positive
```

**Theorem C (coherent form)** of [the paper][], as one statement.  Its first
part: after passing to a subsequence of a chain, the transition `θ_{j,k}`
depends only on `j`, there being proper self-embeddings `Θ₀, Θ₁, …` with
`θ_{j,k} = Θⱼ` for all `k > j`, which form an infinite coherent chain
(`CoherentForm`{.AgdaRecord}: the selection `select`, the chain
`coherent-chain`, and `depends`).  Its second: the images `Mⱼ = Θⱼ(FL(3))` of
any infinite coherent chain form a chain inside `FL(3)`, whose `j`-th triple is
`Θⱼ`.  The first part takes the infinite pigeonhole principle
(`InfinitePigeonhole`{.AgdaRecord}) and decidable equality on the generators
as hypotheses; the second takes neither.

```agda
-- Theorem C (coherent form): a subsequence of a chain whose transitions form an infinite
-- coherent chain, from the principle; and the images of an infinite coherent chain form a chain.
record Theorem-C-coherent : Setω where
  field
    part-1 : ∀ {χ} {X : Type χ} → DecidableEquality X → (c : Chain X) → InfinitePigeonhole
             → CoherentForm c
    part-2 : (C : Coherentω) → Σ[ c ∈ Chain (Fin 3) ] (∀ k i → Chain.gens c k i ≡ Coherentω.Θ C k i)

-- The proof of Theorem C (coherent form).
theorem-C-coherent : Theorem-C-coherent
theorem-C-coherent = record
  { part-1 = coherent-form
  ; part-2 = λ C → coherentω→chain C , λ k i → refl
  }
```

**Corollary 6.4** of [the paper][], as one statement: Dean's problem has a
positive answer, some free lattice containing a chain of copies of `FL(3)`,
if and only if an infinite coherent chain exists.  The forward direction takes
the infinite pigeonhole principle, through the coherent form of Theorem C, and
decidable equality on the free lattice's generators, which a positive answer
here includes; the reverse direction gives `FL(3)`, whose generators have it,
and takes no hypothesis (`coherentω→positive`{.AgdaFunction}).

```agda
-- Corollary 6.4: from the principle, Dean's problem has a positive answer if and only if an
-- infinite coherent chain exists.
Corollary-6·4 : Type (lsuc 0ℓ)
Corollary-6·4 =  InfinitePigeonhole
                 → (Σ[ X ∈ Type ] DecidableEquality X × CopyChain X) ⇔ Coherentω

-- The proof of Corollary 6.4.
corollary-6·4 : Corollary-6·4
corollary-6·4 = positive⇔coherentω
```

--------------------------------------

[DeansProblem.Coherent.Infinite]: DeansProblem.Coherent.Infinite.html
[DeansProblem.Chain.Copies]: DeansProblem.Chain.Copies.html
[DeansProblem.Coherent]: DeansProblem.Coherent.html
[DeansProblem.Coherent.Finite]: DeansProblem.Coherent.Finite.html
[DeansProblem.LengthThree]: DeansProblem.LengthThree.html
[DeansProblem.NoChain]: DeansProblem.NoChain.html
[DeansProblem.Pigeonhole]: DeansProblem.Pigeonhole.html
