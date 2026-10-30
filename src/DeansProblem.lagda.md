---
layout: default
file: "src/DeansProblem.lagda.md"
title: "DeansProblem module"
date: "2026-10-22"
author: "the agda-lattices development team"
---

### Dean's problem

This is the [DeansProblem][] module of the [agda-lattices][] library.

[the paper]: https://arxiv.org/abs/YYMM.NNNNN

R. A. Dean asked whether a free lattice can contain an infinite strictly
ascending chain of sublattices, each isomorphic to the free lattice `FL(3)` on
three generators.  The modules under `DeansProblem` are the formal development
of [the paper][] that answers the question in the negative.  They rest on the
free-lattice development of [Lattices.Free][], which they import and never
modify.

This is a barrel module: it declares nothing of its own and re-exports the
modules below; the worked examples and [DeansProblem.Irredundant][] are imported
on their own.

### Guide to the submodules of <span class="AgdaModule">DeansProblem</span>

+  [DeansProblem.Truncation][]: Freese's truncation, the induction over all
   levels: the canonical form of a term truncates the canonical form of its
   image under an embedding, with the members of the embedding at the cuts;
+  [DeansProblem.Chain][]: steps and chains of freely generated copies of
   `FL(3)`, the data of Dean's problem, and the theorem that a self-similar
   step would give a chain;
+  [DeansProblem.Chain.Copies][]: chains of copies of `FL(3)` as the problem
   states them, sequences of embeddings `FL(3) ≤ FL(X)` whose images ascend
   strictly, proved equivalent to the record of a chain;
+  [DeansProblem.SelfSimilar][]: no step is self-similar, since an injective
   endomorphism that maps a free sublattice of finite rank onto a superset of
   it maps it onto itself;
+  [DeansProblem.Coherent][]: the transitions of a chain, and the one-step
   coherent-chain theorem: some transition is a proper self-embedding of
   `FL(3)` fixing a copy of `FL(3)` pointwise, the configuration of the
   fixed-sublattice question;
+  [DeansProblem.Coherent.Finite][]: coherent chains of finite length, the
   four-link criterion that reads one of length three off a chain, the
   extraction under a recurrence hypothesis, and the theorem that an infinite
   coherent chain has unbounded complexity;
+  [DeansProblem.Pigeonhole][]: the infinite pigeonhole principle as a
   record, taken as an explicit hypothesis and never postulated, the proof
   that it decides LPO, and its form for the transitions of a chain: a
   sequence of tuples covered by a finite list is constant along a selection;
+  [DeansProblem.Coherent.Infinite][]: from the principle, the recurrence of
   Remark 5.1, the length-three form of Theorem C without its hypothesis, the
   coherent form of Theorem C and Corollary 6.4 (Dean's problem has a positive
   answer if and only if an infinite coherent chain exists); with no
   hypothesis, subsequences of a chain, and the converse: an infinite coherent
   chain is a chain inside `FL(3)`;
+  [DeansProblem.Inflationary][]: inflationary self-embeddings of `FL(3)`,
   what a fixed join of two generators and a fixed generator of a power force,
   the transfer of inflation through a fixed element, and rigidity for a class
   of self-embeddings with fixed free triples;
+  [DeansProblem.FixedGenerator][]: every proper self-embedding of `FL(3)`
   whose fixed sublattice contains a free triple fixes a generator, because a
   strictly inflationary self-embedding fixes at most eleven elements;
+  [DeansProblem.Shape][]: Corollary E1, the unique fixed generator and the
   inflationary member among an embedding, its square, its dual and its dual
   square, with the three fixed pairwise joins and the generator bounds;
+  [DeansProblem.LengthThree][]: there is no coherent chain of length three,
   hence no infinite coherent chain, and no chain of copies of `FL(3)` whose
   transition from the bottom to some link recurs beyond every bound: every
   fixed point of an inflationary self-embedding fixing `z` lies above
   `z ∧ (x ∨ y)`, which the free triple of a middle link cannot allow;
+  [DeansProblem.NoChain][]: no free lattice over generators with decidable
   equality contains an infinite strictly ascending chain of copies of
   `FL(3)`, by finite searches and induction on the number of transition
   values, with no classical principle, both for the record of a chain and
   for chains of copies;
+  [DeansProblem.Chain.Condition][]: the chain condition for finitely
   generated sublattices of a free lattice (Takahasi's analogue, the variant
   without freeness in Section 4 of [the paper][]), which contains Theorem H
   and fails in `FL(3)`; Theorem A and Corollary A3 for every finitely
   generated sublattice, free or not; and the interleaving and transport of
   strictly ascending chains;
+  [DeansProblem.Partition][]: a free lattice on finitely many generators is
   the disjoint union of the ideal below the join of all generators but one
   and the filter above that one, so an embedding fixing all generators but
   one is the identity;
+  [DeansProblem.Fixed][]: the fixed points of a self-embedding of `FL(n)`:
   they are among the periodic points, which are the elements in the image of
   every iterate; a power of the embedding fixes each non-generator canonical
   joinand of a fixed point; and a fixed point of positive complexity descends
   to a fixed join or meet of generators of a power;
+  [DeansProblem.AlmostProof][]: Freese's almost-proof that no chain exists:
   Lemma 2 in `FL(X)`, the boxes a recurring truncation pattern pins the
   generators into, the theorem that no step has both triples in a strongly
   irredundant box, and that hypothesis, the gap, as a decidable predicate;
+  [DeansProblem.AlmostProof.Links][]: the last clause of Theorem 9.2, that
   two links of a strictly ascending chain of 3-generated sublattices, or of
   a chain, never lie in one strongly irredundant box;
+  [DeansProblem.Truncation.Pattern][]: labeled patterns as a type, the
   pattern of a truncation, a complete finite list of the patterns on a fixed
   tree, the box of a pattern, and the point box of a generator inside a link
   read as `FL(3)`;
+  [DeansProblem.Chain.Powers][]: the steps of a chain are never the powers of
   one map, by the bound on the transitions from the bottom;
+  [DeansProblem.Chain.TwoGenerated][]: two elements generate at most four, so
   the chain condition for 2-generated sublattices holds.

Freese's Lemma 2 itself, which holds in any lattice, is
[DeansProblem.Irredundant][], and the ladder of Section 4 in any lattice
(Lemma 4.4) is [DeansProblem.Ladder][]; both are imported on their own.

The worked examples are as follows.  [DeansProblem.Examples.FreeseStep][]
verifies Freese's example, the step `⟨a, b, c⟩ ⊊ ⟨a′, b′, c′⟩` of his notes;
[DeansProblem.Examples.SelfEmbedding][] decides that Freese's step, read inside
`FL(3)`, is a proper self-embedding; [DeansProblem.Examples.FixedTriple][]
decides that a proper self-embedding of `FL(3)` fixes a copy of `FL(3)`
pointwise, which answers the fixed-sublattice question;
[DeansProblem.Examples.FreeseBox][] decides that the box of Freese's step is
strongly irredundant and proves that his terms express his base in at most one
link of any chain; [DeansProblem.Examples.Rigidity][] proves the rigidity of two
self-embeddings by Theorem F; [DeansProblem.Examples.FreeseEquations][] shows
that Freese's equations have no injective solution; and
[DeansProblem.Examples.ChainCondition][] builds an infinite strictly ascending
chain of 3-generated sublattices of `FL(3)`, none of them a copy of `FL(3)`, so
that the chain condition fails; and [DeansProblem.Examples.FreeseGap][] proves
that the generator `a₁` of Freese's box lies outside his link.

```agda
{-# OPTIONS --without-K --exact-split --safe #-}

module DeansProblem where

open import DeansProblem.AlmostProof        public
open import DeansProblem.AlmostProof.Links  public
open import DeansProblem.Chain              public
open import DeansProblem.Chain.Copies       public
open import DeansProblem.Chain.Condition    public
open import DeansProblem.Chain.Powers       public
open import DeansProblem.Chain.TwoGenerated public
open import DeansProblem.Coherent           public
open import DeansProblem.Coherent.Finite    public
open import DeansProblem.Coherent.Infinite  public
open import DeansProblem.Fixed              public
open import DeansProblem.FixedGenerator     public
open import DeansProblem.Inflationary       public
open import DeansProblem.LengthThree        public
open import DeansProblem.NoChain            public
open import DeansProblem.Partition          public
open import DeansProblem.Pigeonhole         public
open import DeansProblem.SelfSimilar        public
open import DeansProblem.Shape              public
open import DeansProblem.Truncation         public
open import DeansProblem.Truncation.Pattern public
```
