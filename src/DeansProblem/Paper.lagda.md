---
layout: default
file: "src/DeansProblem/Paper.lagda.md"
title: "DeansProblem.Paper module"
date: "2026-10-30"
author: "the agda-lattices development team"
---

### The paper's results, in its order

This is the [DeansProblem.Paper][] module of this repository.

[the paper]: https://arxiv.org/abs/YYMM.NNNNN

Each of the 48 results of [the paper][] is one Agda definition here, whose
type is the result's statement, with one proof: the statement of Theorem 4.5
is the type `Theorem-4·5`, and its proof is `theorem-4·5 : Theorem-4·5`.  The
lettered results are `Theorem-A` to `Theorem-H`, `Corollary-A1` to
`Corollary-A4`, `Corollary-E1` and `Lemma-1` to `Lemma-5`, and the four forms
of Theorem C are `Theorem-C-one-step`, `Theorem-C-four-links`,
`Theorem-C-length-three` and `Theorem-C-coherent`.  Agda reserves `.` for
qualified names, so the numbers are written with the middle dot `·`.  The
numbering is that of the paper's full version; Theorem H, stated in Section 1
and again in Section 8, has one statement.

This module proves nothing.  It re-exports each statement and its proof from
the module that proves it, in the paper's order, so that a reader can read the
results in order, and checking this module checks them all.  Each statement is
defined in its module beside its proof, with prose that says how it reads the
paper's statement.  A statement in several parts whose parts quantify over
universe levels separately is a record in `Setω` with fields `part-1`,
`part-2`, ..., in the paper's order; this module re-exports the record's
module too.

**Conventions**.  The free lattice `FL(X)` is `FL X`, whose elements are the
lattice terms over `X` under Whitman's equality `_≈ʷ_`.  A homomorphism from
`FL(I)` to `FL(X)` is a substitution `σ : Sub I X`, the images of the
generators; it is an embedding when it freely generates (`FreelyGenerates σ`),
which by Corollary 2.5 is when it is injective.  So a self-embedding of
`FL(3)` is a substitution `θ : Sub (Fin 3) (Fin 3)` that freely generates, and
it is proper when some generator is none of its three values.  `⟨ σ ⟩` is the
sublattice that `σ` generates.  A chain of copies of `FL(3)` (Definition 4.1)
is `CopyChain X`, and the record of a chain by its free triples is `Chain X`,
which [DeansProblem.Chain.Copies][] proves equivalent to it.

**Hypotheses beyond the paper's**.  Each is in the statement's type and said in
the prose above it, as follows:

+  decidable equality on the generators, wherever a decision needs it: to
   decide the order, or to compute canonical forms or complexity, so in
   Theorems 2.3 (its decision), 2.6, 2.7, A, B, C (one step, length three and
   coherent form) and H, Lemmas 2.8, 2.9 and 6.1, and Corollaries A1, A3 and
   6.4; the paper's sets have it classically;
+  the infinite pigeonhole principle, as the explicit argument
   `InfinitePigeonhole`, never a postulate, in the coherent form of Theorem C
   and Corollary 6.4, whose converse directions take none.

No result stays in prose.

#### Section 1

+  **Theorem H** (Dean's problem): no free lattice contains an infinite
   strictly ascending chain of sublattices isomorphic to `FL(3)`.
   [DeansProblem.NoChain][].

#### Section 2: preliminaries

All in [DeansProblem.Preliminaries][], from agda-lattices' statements of
FJN's results.

+  **Theorem 2.1** (FJN 1.8 and 1.9): `FL(X)` satisfies (W), and so does every
   sublattice of a free lattice.
+  **Lemma 2.2** (FJN 1.2, 1.4 and 1.5): under (†) the generators are join and
   meet prime, and a partition of the generators partitions the lattice into a
   filter and an ideal; (†) holds in `FL(X)`.
+  **Theorem 2.3** (FJN 1.11, Whitman): Whitman's rules decide the order of
   `FL(X)`.
+  **Corollary 2.4** (FJN 1.6): every generating set contains the generators,
   and every automorphism is induced by a permutation of them.
+  **Corollary 2.5** (FJN 1.12 and 1.13): a family freely generates exactly
   when it satisfies the join condition and its dual.
+  **Theorem 2.6** (FJN 1.17 and 1.18): each element has a term of least rank,
   unique up to commutativity, and a term has least rank exactly when it
   satisfies the conditions of canonical form.
+  **Theorem 2.7** (FJN 1.19): the canonical joinands refine every join
   representation, and dually.
+  **Lemma 2.8** (FJN 9.13): an embedding sends a canonical joinand that is
   not a generator to a canonical joinand of the image, and dually.
+  **Theorem B**: a lattice embedding never lowers complexity.
+  **Lemma 2.9**: finitely many elements of `FL(X)`, `X` finite, have
   complexity at most `n`; so infinite sequences of elements, or of tuples,
   of bounded complexity repeat.

#### Section 4: chains as sequences of self-embeddings

+  **Proposition 4.2**: the union of a chain is the direct limit of its
   self-embeddings, and embeds in `FL(X)`; conversely, proper self-embeddings
   whose direct limit embeds in `FL(X)` give a chain.
   [DeansProblem.Chain.Limit][].
+  **Proposition 4.3**: a step that an injective endomorphism `Φ` carries to
   itself gives a chain, the triples `Φᵏ(σ)`. [DeansProblem.Chain][].
+  **Lemma 4.4**: in any lattice, the rungs of a ladder lie below its bound,
   ascend, interlace, and are stable under a smaller bound.
   [DeansProblem.Ladder][].
+  **Theorem 4.5**: the ladder in `FL(3)` is an infinite strictly ascending
   chain of 3-generated sublattices, none a copy of `FL(3)`, and every free
   lattice with three generators contains such a chain.
   [DeansProblem.Examples.ChainCondition][].

#### Section 5: no step is self-similar

+  **Theorem A**: an injective endomorphism that maps a finitely generated
   sublattice onto a superset of it maps it onto itself.
   [DeansProblem.Chain.Condition][].
+  **Corollary A1**: no step admits an injective endomorphism carrying its
   lower triple to its upper one. [DeansProblem.SelfSimilar][].
+  **Corollary A2**: Freese's equations have no injective solution.
   [DeansProblem.Examples.FreeseEquations][].
+  **Corollary A3**: in a chain of finitely generated sublattices, no
   injective endomorphism maps a link onto a later one.
   [DeansProblem.Chain.Condition][].
+  **Corollary A4**: the elements in every image `θᵏ(FL(n))` are the periodic
   points of `θ`. [DeansProblem.Fixed][].

#### Section 6: coherent chains and the fixed-sublattice question

+  **Lemma 6.1**: the transitions from a link are bounded in complexity by its
   generators, and take finitely many values. [DeansProblem.Coherent][].
+  **Theorem C (one step)**: two transitions from the bottom coincide, and then
   a proper transition fixes a proper copy of `FL(3)` pointwise.
   [DeansProblem.Coherent][].
+  **Lemma 6.3**: the images of a coherent chain ascend strictly inside
   `FL(3)`, each a copy of `FL(3)`, and a coherent chain of length two is the
   configuration of the one-step form. [DeansProblem.Coherent.Finite][].
+  **Theorem C (four links)**: four suitable links give a coherent chain of
   length three. [DeansProblem.Coherent.Finite][].
+  **Theorem C (length three)**: a recurring transition from the bottom gives
   a coherent chain of length three. [DeansProblem.Coherent.Finite][].
+  **Theorem C (coherent form)**: from the infinite pigeonhole principle, a
   subsequence of any chain gives an infinite coherent chain; conversely, an
   infinite coherent chain gives a chain inside `FL(3)`.
   [DeansProblem.Coherent.Infinite][].
+  **Corollary 6.4**: from the principle, Dean's problem has a positive answer
   if and only if an infinite coherent chain exists.
   [DeansProblem.Coherent.Infinite][].
+  **Proposition 6.6**: no infinite coherent chain has generator images of
   bounded complexity. [DeansProblem.Coherent.Finite][].
+  **Theorem D**: `θ₁` is a proper self-embedding of `FL(3)` that fixes a free
   triple, so the two form a coherent chain of length two.
   [DeansProblem.Examples.FixedTriple][].
+  **Proposition 6.9**: nothing but the identity fixes `θ₁(x)`, `θ₁(y)`,
   `θ₁(z)`, so that chain has no third link.
   [DeansProblem.Examples.FixedTriple][].
+  **Lemma 6.10**: a self-embedding fixing every generator but one fixes that
   one too; consequences in `FL(3)`. [DeansProblem.Partition][].
+  **Lemma 6.11**: powers of a self-embedding fix the non-generator canonical
   joinands and meetands of its fixed points, and a fixed point of positive
   complexity descends to a periodic element of complexity 1.
   [DeansProblem.Fixed][].

#### Section 7: self-embeddings with a fixed free triple

+  **Lemma 1**: a self-embedding fixing `x ∨ y` moves `x` and `y` up, and `z`
   up. [DeansProblem.Inflationary][].
+  **Lemma 2**: a generator fixed by a positive power of a proper
   self-embedding is fixed by it. [DeansProblem.Inflationary][].
+  **Lemma 3**: an inflationary self-embedding fixes the nodes of the trees of
   its fixed points. [DeansProblem.Inflationary][].
+  **Lemma 4**: inflation transfers through a fixed element.
   [DeansProblem.Inflationary][].
+  **Proposition 7.2**: `S = T₁₄`, and the members of `T₁₁` have complexity at
   most 3. [DeansProblem.FixedGenerator][].
+  **Proposition 7.3**: a strictly inflationary self-embedding fixes only
   members of `T₁₁`. [DeansProblem.FixedGenerator][].
+  **Proposition 7.4**: a proper self-embedding fixing a free triple has an
   inflationary positive power, or its dual has.
   [DeansProblem.FixedGenerator][].
+  **Theorem E**: a proper self-embedding fixing a free triple fixes a
   generator. [DeansProblem.FixedGenerator][].
+  **Corollary 7.5**: Freese's self-embedding fixes exactly the eleven
   elements of `T₁₁`. [DeansProblem.Examples.SelfEmbedding][].
+  **Corollary E1**: the shape of a proper self-embedding with a fixed free
   triple. [DeansProblem.Shape][].

#### Section 8: rigidity, and the answer

+  **Theorem F**: rigidity for a class of self-embeddings.
   [DeansProblem.Inflationary][].
+  **Lemma 5**: the fixed points of an inflationary self-embedding that fixes
   `z` and moves `x` and `y` lie above `z ∧ (x ∨ y)`.
   [DeansProblem.LengthThree][].
+  **Lemma 8.1** (the core): no proper inflationary self-embedding fixes the
   images of a self-embedding that fixes `z`. [DeansProblem.LengthThree][].
+  **Theorem G**: there is no coherent chain of length three.
   [DeansProblem.LengthThree][].

#### Section 9: Freese's almost-proof

+  **Theorem 9.1** (the truncation theorem): the canonical form of a term
   truncates that of its image under an embedding.
   [DeansProblem.Truncation][].
+  **Theorem 9.2**: free triples in one box, one inside the other's
   sublattice, agree where the box is irredundant; so no step, and no two
   links of a chain, lie in such a box. [DeansProblem.AlmostProof.Links][].

```agda
{-# OPTIONS --without-K --exact-split --safe #-}

module DeansProblem.Paper where

-- Section 1.
open import DeansProblem.NoChain                    public using ( Theorem-H ; theorem-H )

-- Section 2.
open import DeansProblem.Preliminaries              public using ( Theorem-2·1 ; module Theorem-2·1 ; theorem-2·1 )
open import DeansProblem.Preliminaries              public using ( Lemma-2·2 ; module Lemma-2·2 ; lemma-2·2 )
open import DeansProblem.Preliminaries              public using ( Theorem-2·3 ; theorem-2·3 )
open import DeansProblem.Preliminaries              public using ( Corollary-2·4 ; module Corollary-2·4 ; corollary-2·4 )
open import DeansProblem.Preliminaries              public using ( Corollary-2·5 ; corollary-2·5 )
open import DeansProblem.Preliminaries              public using ( Theorem-2·6 ; theorem-2·6 )
open import DeansProblem.Preliminaries              public using ( Theorem-2·7 ; theorem-2·7 )
open import DeansProblem.Preliminaries              public using ( Lemma-2·8 ; lemma-2·8 )
open import DeansProblem.Preliminaries              public using ( Theorem-B ; theorem-B )
open import DeansProblem.Preliminaries              public using ( Lemma-2·9 ; lemma-2·9 )

-- Section 4.
open import DeansProblem.Chain.Limit                public using ( Proposition-4·2 ; proposition-4·2 )
open import DeansProblem.Chain                      public using ( Proposition-4·3 ; proposition-4·3 )
open import DeansProblem.Ladder                     public using ( Lemma-4·4 ; lemma-4·4 )
open import DeansProblem.Examples.ChainCondition    public using ( Theorem-4·5 ; module Theorem-4·5 ; theorem-4·5 )

-- Section 5.
open import DeansProblem.Chain.Condition            public using ( Theorem-A ; theorem-A )
open import DeansProblem.SelfSimilar                public using ( Corollary-A1 ; corollary-A1 )
open import DeansProblem.Examples.FreeseEquations   public using ( Corollary-A2 ; corollary-A2 )
open import DeansProblem.Chain.Condition            public using ( Corollary-A3 ; corollary-A3 )
open import DeansProblem.Fixed                      public using ( Corollary-A4 ; corollary-A4 )

-- Section 6.
open import DeansProblem.Coherent                   public using ( Lemma-6·1 ; lemma-6·1 )
open import DeansProblem.Coherent                   public using ( Theorem-C-one-step ; theorem-C-one-step )
open import DeansProblem.Coherent.Finite            public using ( Lemma-6·3 ; lemma-6·3 )
open import DeansProblem.Coherent.Finite            public using ( Theorem-C-four-links ; theorem-C-four-links )
open import DeansProblem.Coherent.Finite            public using ( Theorem-C-length-three ; theorem-C-length-three )
open import DeansProblem.Coherent.Infinite          public using ( Theorem-C-coherent ; module Theorem-C-coherent ; theorem-C-coherent )
open import DeansProblem.Coherent.Infinite          public using ( Corollary-6·4 ; corollary-6·4 )
open import DeansProblem.Coherent.Finite            public using ( Proposition-6·6 ; proposition-6·6 )
open import DeansProblem.Examples.FixedTriple       public using ( Theorem-D ; theorem-D )
open import DeansProblem.Examples.FixedTriple       public using ( Proposition-6·9 ; proposition-6·9 )
open import DeansProblem.Partition                  public using ( Lemma-6·10 ; module Lemma-6·10 ; lemma-6·10 )
open import DeansProblem.Fixed                      public using ( Lemma-6·11 ; lemma-6·11 )

-- Section 7.
open import DeansProblem.Inflationary               public using ( Lemma-1 ; lemma-1 )
open import DeansProblem.Inflationary               public using ( Lemma-2 ; lemma-2 )
open import DeansProblem.Inflationary               public using ( Lemma-3 ; lemma-3 )
open import DeansProblem.Inflationary               public using ( Lemma-4 ; lemma-4 )
open import DeansProblem.FixedGenerator             public using ( Proposition-7·2 ; proposition-7·2 )
open import DeansProblem.FixedGenerator             public using ( Proposition-7·3 ; proposition-7·3 )
open import DeansProblem.FixedGenerator             public using ( Proposition-7·4 ; proposition-7·4 )
open import DeansProblem.FixedGenerator             public using ( Theorem-E ; theorem-E )
open import DeansProblem.Examples.SelfEmbedding     public using ( Corollary-7·5 ; corollary-7·5 )
open import DeansProblem.Shape                      public using ( Corollary-E1 ; corollary-E1 )

-- Section 8.
open import DeansProblem.Inflationary               public using ( Theorem-F ; theorem-F )
open import DeansProblem.LengthThree                public using ( Lemma-5 ; lemma-5 )
open import DeansProblem.LengthThree                public using ( Lemma-8·1 ; lemma-8·1 )
open import DeansProblem.LengthThree                public using ( Theorem-G ; theorem-G )

-- Section 9.
open import DeansProblem.Truncation                 public using ( Theorem-9·1 ; theorem-9·1 )
open import DeansProblem.AlmostProof.Links          public using ( Theorem-9·2 ; theorem-9·2 )
```

--------------------------------------

[DeansProblem.Paper]: DeansProblem.Paper.html
[DeansProblem.NoChain]: DeansProblem.NoChain.html
[DeansProblem.Preliminaries]: DeansProblem.Preliminaries.html
[DeansProblem.Chain]: DeansProblem.Chain.html
[DeansProblem.Chain.Copies]: DeansProblem.Chain.Copies.html
[DeansProblem.Chain.Limit]: DeansProblem.Chain.Limit.html
[DeansProblem.Chain.Condition]: DeansProblem.Chain.Condition.html
[DeansProblem.Ladder]: DeansProblem.Ladder.html
[DeansProblem.Examples.ChainCondition]: DeansProblem.Examples.ChainCondition.html
[DeansProblem.SelfSimilar]: DeansProblem.SelfSimilar.html
[DeansProblem.Examples.FreeseEquations]: DeansProblem.Examples.FreeseEquations.html
[DeansProblem.Fixed]: DeansProblem.Fixed.html
[DeansProblem.Coherent]: DeansProblem.Coherent.html
[DeansProblem.Coherent.Finite]: DeansProblem.Coherent.Finite.html
[DeansProblem.Coherent.Infinite]: DeansProblem.Coherent.Infinite.html
[DeansProblem.Examples.FixedTriple]: DeansProblem.Examples.FixedTriple.html
[DeansProblem.Partition]: DeansProblem.Partition.html
[DeansProblem.Inflationary]: DeansProblem.Inflationary.html
[DeansProblem.FixedGenerator]: DeansProblem.FixedGenerator.html
[DeansProblem.Examples.SelfEmbedding]: DeansProblem.Examples.SelfEmbedding.html
[DeansProblem.Shape]: DeansProblem.Shape.html
[DeansProblem.LengthThree]: DeansProblem.LengthThree.html
[DeansProblem.Truncation]: DeansProblem.Truncation.html
[DeansProblem.AlmostProof.Links]: DeansProblem.AlmostProof.Links.html
