<!-- File: README.md -->

# agda-deans-problem

[![check](https://github.com/ualib/agda-deans-problem/actions/workflows/check.yml/badge.svg?branch=main)](https://github.com/ualib/agda-deans-problem/actions/workflows/check.yml)
[![ci](https://github.com/ualib/agda-deans-problem/actions/workflows/ci.yml/badge.svg?branch=main)](https://github.com/ualib/agda-deans-problem/actions/workflows/ci.yml)
[![License: Apache 2.0](https://img.shields.io/badge/License-Apache_2.0-blue.svg)](./LICENSE)
[![Agda 2.9.0, pre-release](https://img.shields.io/badge/Agda-2.9.0_pre--release-purple.svg)](https://github.com/agda/agda/commit/da66a8c75f11d10699a6b38b261efdf244b66f2a)
[![stdlib 2.3, patched for Agda 2.9.0](https://img.shields.io/badge/stdlib-2.3_patched-orange.svg)](https://github.com/formalverification/agda-stdlib/releases/tag/v2.3-agda-2.9.0)
[![agda-lattices, pinned at bea91e54](https://img.shields.io/badge/agda--lattices-bea91e54-teal.svg)](https://github.com/ualib/agda-lattices/tree/bea91e546637d5907dd577d2b987650e9924e87f)

The formal development, in [Agda][], of the paper

> William DeMeo and Ralph Freese, *No free lattice contains an infinite
> ascending chain of copies of FL(3)*, [arXiv:YYMM.NNNNN][paper].

The paper answers R. A. Dean's question in the negative: no free lattice
contains an infinite strictly ascending chain of sublattices, each isomorphic
to the free lattice `FL(3)` on three generators.  This repository holds the
paper's own development, the modules under `DeansProblem`; the general
lattice theory it uses comes from the library [agda-lattices][], which the
flake pins at one commit, so that the paper's code is frozen by the pin.
Every module is checked by Agda under `--without-K --exact-split --safe`.

The reference throughout is R. Freese, J. Ježek and J. B. Nation, *Free
Lattices*, Mathematical Surveys and Monographs 42, American Mathematical
Society, 1995 (FJN below), cited by theorem number.  The lettered results
(Theorems A to H, Corollaries A1 to A4 and E1) and the numbered lemmas are
the paper's.

## Checking it

The toolchain is a [Nix][] flake, so a machine with Nix 2.28 or later, with
flakes enabled, needs nothing else:

    git clone https://github.com/ualib/agda-deans-problem.git
    cd agda-deans-problem
    nix develop --command make check

`make check` first runs `scripts/check-safety.sh` (below), then generates
`src/EverythingDeansProblem.agda`, which imports every module under `src/`
and the two modules of agda-lattices that the table below names and no
module here imports (`Lattices.Free.Canonical` and
`Lattices.Free.Semidistributive`), and type-checks it with a heap limit of
6 GiB (`+RTS -M6G -A128M`), the limit under which the paper's costs are
measured.  It exits 0 when every module checks.  There is no separate test step:
type-checking is the test.

The Agda is a pre-release of Agda 2.9.0, which Nix builds from source in about
an hour unless it can fetch it from the public binary cache
`formalverification` on [Cachix][], where the Agda Universal Algebra Library's
CI puts it.  To fetch it, run `cachix use formalverification` once, or add the
following lines to your Nix configuration (`/etc/nix/nix.conf`, or the
`nix.conf` in your user's Nix configuration directory if you are a trusted
user):

    extra-substituters = https://formalverification.cachix.org
    extra-trusted-public-keys = formalverification.cachix.org-1:KG/AJuuli2F4/bA56rUYC9V8ZE/Zw6iZjxJEf40cQOo=

The first `make check` also checks the modules of agda-lattices and of the
Agda Universal Algebra Library that the development imports, and keeps their
interface files under `.deps/`, so later runs check this repository's modules
alone.

### The toolchain

`flake.lock` pins every input, as follows:

+  [agda-lattices][] at commit [`bea91e54`][lattices-pin] of its main branch,
   pinned in `flake.nix` itself as well;
+  the [Agda Universal Algebra Library][agda-algebras] at commit
   [`922d138b`][algebras-pin] of its master branch, the commit agda-lattices
   is checked against, since the flake follows that library's own input;
+  Agda 2.9.0, a pre-release built from [agda/agda][] at commit
   [`da66a8c7`][agda-pin], and the [Agda standard library][agda-stdlib] 2.3
   patched to check under it, both taken from the Agda Universal Algebra
   Library's flake;
+  nixpkgs, which follows that library's own pin.

`nix develop` writes a project-local Agda configuration (`.agda/`) and an
`agda` wrapper that names the standard library, the Agda Universal Algebra
Library, agda-lattices and this repository explicitly, so nothing in your own
Agda configuration takes part.

## What is checked

+  Every module carries the pragma
   `{-# OPTIONS --without-K --exact-split --safe #-}`, and no other.  Under
   `--safe` Agda refuses postulates, unsafe primitives and non-terminating
   definitions, so every theorem is proved from the type theory alone.
   `scripts/check-safety.sh` (`make safety`, the first step of `make check`)
   checks without running Agda that every module carries that pragma, and
   that its code holds no `postulate` and no pragma that switches a check off.
   The script is agda-lattices' own, with the aggregator's name changed; it
   lets a worked example add `--lossy-unification`, and no module here
   does.
+  A statement proved by induction is checked when its proof term has the
   stated type.  A statement about explicit terms is checked by computation:
   Whitman's procedure is a decision `s ≤ʷ? t`, which Agda evaluates while it
   checks the module, and `from-yes` or `from-no` turns the answer into a
   proof.  When the terms are too large for the procedure to run within the
   heap limit, as for Freese's example, the decision runs on smaller terms
   checked equal to the defined ones, and the statement is transported along
   the equality.
+  The one hypothesis of the main theorem, `no-copy-chain` in
   `DeansProblem.NoChain`, is decidable equality on the generators:

       no-copy-chain : (_≟ˣ_ : DecidableEquality X) → CopyChain X → ⊥

   says that the free lattice over a type `X` of generators with decidable
   equality contains no infinite strictly ascending chain of sublattices
   isomorphic to `FL(3)`.  Its proof uses finite searches and induction on a
   natural number, and no classical principle.
+  The paper says which of its statements are checked and in what form.
   Three of them rest on the infinite pigeonhole principle, which is
   classically true and which Agda's constructive logic does not prove, since
   it decides LPO: the coherent form of its Theorem C, its Corollary 6.4 and
   the recurrence of its Remark 5.1.  They are checked with the principle as
   a hypothesis, the record `InfinitePigeonhole` of `DeansProblem.Pigeonhole`,
   which each of them takes as an explicit argument and names in its type,
   never as a postulate; their converse directions take none, and neither
   does the proof of Theorem H.  The clause of its ladder theorem that no
   link of the chain is a copy of `FL(3)` stays in prose there.

## The paper's statements and their names

The table maps the statements of the paper to their names in Agda.  A module
under `Lattices` is agda-lattices', at the pinned commit; a module under
`DeansProblem` is this repository's.  A few names are defined inside a
parameterized submodule of the module given (`_≤ʷ?_` in
`Lattices.Free.Whitman.Decision`, for instance, which takes decidable
equality on the generators).

| Statement | Names | Module |
| --- | --- | --- |
| Whitman's rules decide the order, and are sound and complete (FJN Theorems 1.8 and 1.11) | `_≤ʷ_`, `_≤ʷ?_`; `≤ʷ→≤`, `≤→≤ʷ` | `Lattices.Free.Whitman`, `Lattices.Free.Universal` |
| `FL(X)` with the universal property | `FL`, `FL-extend` | `Lattices.Free.Universal` |
| canonical form exists and is unique up to permutation, with the conditions of FJN Theorems 1.17 and 1.18 | `canonical`, `IsCanonical`, `≈ʷ⇒≈ᶜ`, `isCanonical?` | `Lattices.Free.Canonical` and its submodules |
| canonical joinands refine every join (FJN Theorem 1.19); equal elements have the same canonical joinands | `canonicalJoinands-refine`, `canonicalJoinands-≈ˡ` | `Lattices.Free.Canonical.Joinands` |
| `FL(X)` satisfies (W) and is semidistributive (FJN Theorems 1.8 and 1.21) | `FL-satisfiesW`, `FL-isSemidistributive` | `Lattices.Free.Semidistributive` |
| substitutions induce the homomorphisms; every homomorphism is induced | `subst-hom`, `hom-induced` | `Lattices.Free.Substitution` |
| free generation is injectivity (FJN Corollary 1.13), decided; a generator in a generated sublattice is a generator of it (FJN Corollary 1.6) | `freelyGenerates⇔injective`, `freelyGenerates?`, `generator-in-image` | `Lattices.Free.Generation` |
| FJN Lemma 9.13 and its dual | `embedding-canonicalJoinand` | `Lattices.Free.Embedding` |
| Theorem B; finitely many elements of bounded complexity; the pigeonhole for tuples, infinite and finite | `complexity-mono`, `bounded-complete`, `pigeonhole-≈`, `pigeonhole-≈ⁿ`, `finite-pigeonhole-≈ⁿ` | `Lattices.Free.Complexity` |
| steps and chains; a self-similar step gives a chain | `Step`, `Chain`, `selfSimilar→chain` | `DeansProblem.Chain` |
| chains of sublattices isomorphic to `FL(3)`, as embeddings whose images ascend strictly; equivalent to the record of a chain | `CopyChain`, `copyChain→chain`, `chain→copyChain` | `DeansProblem.Chain.Copies` |
| Theorem A for a free sublattice; Corollary A1 | `self-similar-onto`, `no-self-similar-step` | `DeansProblem.SelfSimilar` |
| Theorem A; Corollary A3; the chain condition for 3-generated sublattices, which contains Theorem H | `generated-onto`, `no-onto-later`, `StrictlyAscending`, `ChainCondition`, `chainCondition→no-copy-chain` | `DeansProblem.Chain.Condition` |
| the ladder: its rungs, and an infinite strictly ascending chain of 3-generated sublattices of `FL(3)` | `stable`, `A-strict`, `inv-A`, `ladder`, `chain-condition-fails`, `ladder-in` | `DeansProblem.Examples.ChainCondition` |
| Freese's example | `abc-free`, `abc'-free`, `abc≈`, `a'∉⟨abc⟩` | `DeansProblem.Examples.FreeseStep` |
| Freese's step inside `FL(3)`, the descending chain | `θ-free`, `x∉θ`, `inside`, `descending` | `DeansProblem.Examples.SelfEmbedding` |
| Corollary A2: Freese's equations have no injective solution; the three candidates | `no-FreeseΦ`, `π-fails`, `bar-not-free` | `DeansProblem.Examples.FreeseEquations` |
| the transitions of a chain, their bound and a repeat; Theorem C (one step); the configuration of the fixed-sublattice question | `transition`, `transition-bound′`, `transition-bound`, `transition-repeats`, `chain→fixed-sublattice`, `FixedSublattice` | `DeansProblem.Coherent` |
| the partition lemma; an embedding fixing all generators but one is the identity | `partition`, `fixes-last`, `fix-two-generators` | `DeansProblem.Partition` |
| Corollary A4 (both directions); the descent of a fixed point | `image→periodic`, `periodic→image`, `joinand-periodic`, `descent` | `DeansProblem.Fixed` |
| Theorem D; nothing but the identity fixes the image of `θ₁` | `fixed-triple`, `coherent₂`, `rigid`, `no-extension` | `DeansProblem.Examples.FixedTriple` |
| coherent chains of length `n` and their images; Theorem C (four links, and length three); an infinite coherent chain has unbounded complexity | `Coherent`, `step`, `coherent₂→fixed`, `four-links→coherent₃`, `Recurs`, `chain→coherent₃`, `Coherentω`, `coherentω-unbounded` | `DeansProblem.Coherent.Finite` |
| the infinite pigeonhole principle, as a hypothesis; it decides LPO; a sequence of covered tuples is constant along a selection | `InfinitePigeonhole`, `pigeonhole→LPO`, `constant-along` | `DeansProblem.Pigeonhole` |
| from the principle: the recurrence of Remark 5.1; Theorem C (length three) without its hypothesis; Theorem C (coherent form); Corollary 6.4; with none: a subsequence of a chain is a chain, and the converse of the coherent form | `BottomRecurrence`, `bottom-recurrence`, `some-link-recurs`, `pigeonhole→coherent₃`, `CoherentForm`, `coherent-form`, `PositiveAnswer`, `positive⇔coherentω`, `subchain`, `coherentω→chain`, `coherentω→copyChain` | `DeansProblem.Coherent.Infinite` |
| Lemmas 1 to 4; Theorem F | `fixes-join`, `fixes-join-third`, `power-fixes→fixes`, `node-fixed`, `meetand-gen-fixed`, `strict-fixed-not-below`, `inflation-transfer`, `rigid-class` | `DeansProblem.Inflationary` |
| the fourteen elements and the eleven fixed points; the descent with the parent; an inflationary power; Theorem E | `T₁₄-∨`, `T₁₁-∧`, `strict-fixed-in-T₁₁`, `descent-pair`, `inflationary-power`, `fixes-generator` | `DeansProblem.FixedGenerator` |
| Corollary E1: the unique fixed generator, the inflationary member, its three fixed joins and two bounds | `Shape`, `InflationaryShape`, `shape` | `DeansProblem.Shape` |
| Lemma 5; the core lemma; Theorem G; no infinite coherent chain; no chain with a recurring transition | `fixed-above-c`, `core`, `no-coherent₃`, `no-coherentω`, `no-chain-recurs` | `DeansProblem.LengthThree` |
| Theorem H, for the record of a chain and as stated, by finite searches | `recurrences-bounded`, `chain-escapes`, `finite-colors-exhausted`, `no-chain`, `no-copy-chain` | `DeansProblem.NoChain` |
| `θ₁` rigid by Theorem F; `θ₂` fixes the same triple and is rigid | `rigid′`, `fixed-triple₂`, `rigid₂` | `DeansProblem.Examples.Rigidity` |
| the truncation theorem | `_⊑_`, `truncation`, `truncation-canonical` | `DeansProblem.Truncation` |
| Freese's Lemma 2 in any lattice; the partition lemma for a generated sublattice | `above-or-below`, `lemma-2-at`, `lemma-2` | `DeansProblem.Irredundant` |
| boxes, the gap as a predicate, and the theorem that no step has both triples in a strongly irredundant box | `StronglyIrredundant`, `stronglyIrredundant?`, `box-agree`, `no-step-in-box` | `DeansProblem.AlmostProof` |
| Freese's box is strongly irredundant; his terms express his base in at most one link | `freese-box-irredundant`, `freese-terms-in-box`, `freese-terms-once` | `DeansProblem.Examples.FreeseBox` |

## The modules

Every module of this repository is under `src/DeansProblem/`, with the barrel
`DeansProblem`, which re-exports the modules below but the worked examples and
`DeansProblem.Irredundant`.

+  **Chains**.  `DeansProblem.Chain` (steps and chains of free triples),
   `DeansProblem.Chain.Copies` (chains of sublattices isomorphic to `FL(3)`,
   the paper's definition, proved equivalent to the record of a chain) and
   `DeansProblem.Chain.Condition` (Theorem A for a finitely generated
   sublattice, and the chain condition for `n`-generated sublattices).
+  **Toward Theorem H**.  `DeansProblem.SelfSimilar` (Theorem A for a free
   sublattice), `DeansProblem.Coherent` and `DeansProblem.Coherent.Finite`
   (transitions and coherent chains, Theorem C), `DeansProblem.Partition`
   (the partition lemma), `DeansProblem.Fixed` (periodic and fixed points),
   `DeansProblem.Inflationary` (Lemmas 1 to 4 and Theorem F),
   `DeansProblem.FixedGenerator` (Theorem E), `DeansProblem.Shape`
   (Corollary E1), `DeansProblem.LengthThree` (Theorem G) and
   `DeansProblem.NoChain` (Theorem H).
+  **Freese's notes**.  `DeansProblem.Truncation` (the truncation theorem),
   `DeansProblem.Irredundant` (Freese's Lemma 2 in any lattice) and
   `DeansProblem.AlmostProof` (boxes, and the gap in Freese's almost proof as
   a predicate).
+  **Worked examples**, under `DeansProblem.Examples`: `FreeseStep` (Freese's
   example, on terms over nine generators), `SelfEmbedding`,
   `FreeseEquations`, `FreeseBox`, `FixedTriple` (Theorem D), `Rigidity` and
   `ChainCondition` (the ladder).

## The cost

The cost of the check is stated for the paper's tag, measured as follows:
`make check` from a clean clone, with the Agda already in the Nix store, timed
for wall time and peak resident memory, three runs, the median reported; once
with the interface files of agda-lattices and of the Agda Universal Algebra
Library built in the same run, and once with them already built, which is the
cost of this repository's modules alone.  The figures, and the counts of
modules and lines the paper states, will be added here when the tag is cut.
The cost is where the Whitman decisions are, above all in the worked examples
on Freese's terms.

## Provenance

The development was first written together with the general modules that
now form agda-lattices, and moved into the namespace `DeansProblem` in October
2026, when those were published as a library of their own.  One module, `DeansProblem.Examples.FreeseStep` (Freese's example),
was first written in the [Agda Universal Algebra Library][agda-algebras].

## Contributing

Contributions are welcome.  [`CONTRIBUTING.md`](CONTRIBUTING.md) says how a
module joins the development, the conventions it follows, the commands that
check it, and how a pull request is reviewed.

## License and citation

The development is licensed under the Apache License 2.0 (`LICENSE`);
`NOTICE` records the attribution it carries from the Agda Universal Algebra
Library.  `CITATION.cff` gives the metadata for citing it; the paper cites
the tagged release, whose archived copy will have a DOI.

## Acknowledgment

The formal development in this repository was produced with the assistance of
large language models used as tools under the author's direction: chiefly
Claude (Anthropic), and models of OpenAI's GPT-6 family, through the Codex
agent, which found and formalized the proof of Theorem H without the infinite
pigeonhole principle (`DeansProblem.NoChain`) and formalized Corollary E1
(`DeansProblem.Shape`).  The models worked against Agda's type checker
through the agda-mcp server of the [Agda-native AIR][agda-native-air]
project.  Every statement in the table above is checked by Agda under
`--safe`; the author takes full responsibility for every definition,
statement and proof.

[Agda]: https://wiki.portal.chalmers.se/agda/
[agda-algebras]: https://github.com/ualib/agda-algebras
[agda-lattices]: https://github.com/ualib/agda-lattices
[agda-native-air]: https://github.com/formalverification/agda-native-air
[algebras-pin]: https://github.com/ualib/agda-algebras/tree/922d138b22c6d0ab6db5245b1760a4c2595d7525
[lattices-pin]: https://github.com/ualib/agda-lattices/tree/bea91e546637d5907dd577d2b987650e9924e87f
[agda/agda]: https://github.com/agda/agda
[agda-pin]: https://github.com/agda/agda/tree/da66a8c75f11d10699a6b38b261efdf244b66f2a
[agda-stdlib]: https://github.com/agda/agda-stdlib
[Cachix]: https://www.cachix.org/
[Nix]: https://nixos.org/
[paper]: https://arxiv.org/abs/YYMM.NNNNN
