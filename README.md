<!-- File: README.md -->

# agda-deans-problem

[![check](https://github.com/ualib/agda-deans-problem/actions/workflows/check.yml/badge.svg?branch=main)](https://github.com/ualib/agda-deans-problem/actions/workflows/check.yml)
[![ci](https://github.com/ualib/agda-deans-problem/actions/workflows/ci.yml/badge.svg?branch=main)](https://github.com/ualib/agda-deans-problem/actions/workflows/ci.yml)
[![License: Apache 2.0](https://img.shields.io/badge/License-Apache_2.0-blue.svg)](./LICENSE)
[![Agda 2.9.0, pre-release](https://img.shields.io/badge/Agda-2.9.0_pre--release-purple.svg)](https://github.com/agda/agda/commit/da66a8c75f11d10699a6b38b261efdf244b66f2a)
[![stdlib 2.3, patched for Agda 2.9.0](https://img.shields.io/badge/stdlib-2.3_patched-orange.svg)](https://github.com/formalverification/agda-stdlib/releases/tag/v2.3-agda-2.9.0)
[![agda-lattices, pinned at v0.2.0](https://img.shields.io/badge/agda--lattices-v0.2.0-teal.svg)](https://github.com/ualib/agda-lattices/releases/tag/v0.2.0)

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

If flakes are not enabled in your Nix configuration, write
`nix --extra-experimental-features 'nix-command flakes' develop` in place of
`nix develop`.  The paper cites the tag `v0.1.0`; to check that state of the
repository, run `git checkout v0.1.0` before `nix develop`.  The tag's
archived copy, a source archive without the git history, checks the same
way from the directory it unpacks to.

`make check` first runs `scripts/check-safety.sh` (below), then generates
`src/EverythingDeansProblem.agda`, which imports every module under `src/`
and the two modules of agda-lattices that the tables below name and no
module here imports (`Lattices.Free.Membership` and `Lattices.Free.Small`),
type-checks it with a heap limit of 6 GiB (`+RTS -M6G -A128M`), the limit
under which the paper's costs are measured, and last runs
`scripts/check-paper.sh` (below).  It exits 0 when every module checks and
the tables agree with the development, and its last line is the following:

    check-paper: 48 results agree with DeansProblem.Paper; 207 names resolve in 40 modules

There is no separate test step: type-checking is the test.

The Agda is a pre-release of Agda 2.9.0, which Nix builds from source in about
an hour unless it can fetch it from the public binary cache
`formalverification` on [Cachix][], where the Agda Universal Algebra Library's
CI puts it.  To fetch it, run `cachix use formalverification` once, or add the
following lines to your Nix configuration (`/etc/nix/nix.conf`, or the
`nix.conf` in your user's Nix configuration directory if you are a trusted
user):

    extra-substituters = https://formalverification.cachix.org
    extra-trusted-public-keys = formalverification.cachix.org-1:KG/AJuuli2F4/bA56rUYC9V8ZE/Zw6iZjxJEf40cQOo=

The cache holds the build for x86_64-linux, the system that the Agda
Universal Algebra Library's CI runs on, as do this repository's CI and the
measurements of [The cost][cost].  The flake also names aarch64-linux and
macOS, where Nix may have to build the Agda, and where the release has not
been checked.  The toolchain takes about 3.2 GiB of the Nix store, 2.5 GiB
of it the GHC 9.10.3 that the Agda environment carries.

The first `make check` also checks the modules of agda-lattices and of the
Agda Universal Algebra Library that the development imports, and keeps their
interface files under `.deps/`.  A later run checks only what has changed;
after `make clean`, which removes this repository's interface files and
leaves `.deps/` alone, it checks this repository's modules alone.

### The toolchain

`flake.lock` pins every input, as follows:

+  [agda-lattices][] at its release [`v0.2.0`][lattices-pin], commit
   `41fb55e4` of its main branch, pinned in `flake.nix` itself by the tag;
+  the [Agda Universal Algebra Library][agda-algebras] at commit
   [`b4d0ab6c`][algebras-pin] of its master branch, the commit agda-lattices
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
   proof.  For Freese's example, whose terms exhausted the build's heap under
   that recursion, the decisions run through the library's table `_≤ᵖ?_`,
   whose verdicts are proved to be the recursion's (`≤ᵖ?-agrees`), on
   smaller terms checked equal to the defined ones, and each statement is
   transported along the equality.
+  Each of the paper's 48 results is one Agda definition whose type is its
   statement, with one proof, defined in the module that proves it (for the
   ten results of Section 2, `DeansProblem.Preliminaries`, from the library's
   statements) and re-exported, in the paper's order, by
   `DeansProblem.Paper`.  No result stays in prose.  A hypothesis beyond the
   paper's is in the statement's type, and said in its module's prose:
   decidable equality on the
   generators, where a decision needs it, and the infinite pigeonhole
   principle.
+  The main theorem, `Theorem-H` in `DeansProblem.NoChain`, has decidable
   equality on the generators as its one hypothesis:

       Theorem-H = ∀ {χ} {X : Type χ} → DecidableEquality X → CopyChain X → ⊥

   says that the free lattice over a type `X` of generators with decidable
   equality contains no infinite strictly ascending chain of sublattices
   isomorphic to `FL(3)`.  Its proof uses finite searches and induction on a
   natural number, and no classical principle.
+  Two results rest on the infinite pigeonhole principle, which is classically
   true and which Agda's constructive logic does not prove, since it decides
   LPO (`pigeonhole→LPO`): the coherent form of Theorem C and Corollary 6.4,
   with the recurrence of Remark 5.1.  They take the principle, the record
   `InfinitePigeonhole` of `DeansProblem.Pigeonhole`, as an explicit argument
   named in their types, never as a postulate.  The converse of the
   coherent form, its second part, takes none; `Corollary-6·4` binds the
   principle before both of its directions, though its converse is proved
   without it (`coherentω→positive`); and the proof of Theorem H takes none.
+  `scripts/check-paper.sh` (`make paper-check`, the last step of
   `make check`) checks that the table of results below and
   `DeansProblem.Paper` list the same results in the same order, and that
   every name in the tables of this section resolves in the module its row
   gives, by an Agda probe whose output it reads for warnings.

## The paper's results and their names

One row per result of the paper, in the paper's order, with the statement
(a type) and its proof, and the module where both are defined.  A module
under `DeansProblem` is this repository's.  The numbering is that of the
paper's full version.

| Result | Statement, proof | Module |
| --- | --- | --- |
| Theorem H | `Theorem-H`, `theorem-H` | `DeansProblem.NoChain` |
| Theorem 2.1 | `Theorem-2·1`, `theorem-2·1` | `DeansProblem.Preliminaries` |
| Lemma 2.2 | `Lemma-2·2`, `lemma-2·2` | `DeansProblem.Preliminaries` |
| Theorem 2.3 | `Theorem-2·3`, `theorem-2·3` | `DeansProblem.Preliminaries` |
| Corollary 2.4 | `Corollary-2·4`, `corollary-2·4` | `DeansProblem.Preliminaries` |
| Corollary 2.5 | `Corollary-2·5`, `corollary-2·5` | `DeansProblem.Preliminaries` |
| Theorem 2.6 | `Theorem-2·6`, `theorem-2·6` | `DeansProblem.Preliminaries` |
| Theorem 2.7 | `Theorem-2·7`, `theorem-2·7` | `DeansProblem.Preliminaries` |
| Lemma 2.8 | `Lemma-2·8`, `lemma-2·8` | `DeansProblem.Preliminaries` |
| Theorem B | `Theorem-B`, `theorem-B` | `DeansProblem.Preliminaries` |
| Lemma 2.9 | `Lemma-2·9`, `lemma-2·9` | `DeansProblem.Preliminaries` |
| Proposition 4.2 | `Proposition-4·2`, `proposition-4·2` | `DeansProblem.Chain.Limit` |
| Proposition 4.3 | `Proposition-4·3`, `proposition-4·3` | `DeansProblem.Chain` |
| Lemma 4.4 | `Lemma-4·4`, `lemma-4·4` | `DeansProblem.Ladder` |
| Theorem 4.5 | `Theorem-4·5`, `theorem-4·5` | `DeansProblem.Examples.ChainCondition` |
| Theorem A | `Theorem-A`, `theorem-A` | `DeansProblem.Chain.Condition` |
| Corollary A1 | `Corollary-A1`, `corollary-A1` | `DeansProblem.SelfSimilar` |
| Corollary A2 | `Corollary-A2`, `corollary-A2` | `DeansProblem.Examples.FreeseEquations` |
| Corollary A3 | `Corollary-A3`, `corollary-A3` | `DeansProblem.Chain.Condition` |
| Corollary A4 | `Corollary-A4`, `corollary-A4` | `DeansProblem.Fixed` |
| Lemma 6.1 | `Lemma-6·1`, `lemma-6·1` | `DeansProblem.Coherent` |
| Theorem C (one step) | `Theorem-C-one-step`, `theorem-C-one-step` | `DeansProblem.Coherent` |
| Lemma 6.3 | `Lemma-6·3`, `lemma-6·3` | `DeansProblem.Coherent.Finite` |
| Theorem C (four links) | `Theorem-C-four-links`, `theorem-C-four-links` | `DeansProblem.Coherent.Finite` |
| Theorem C (length three) | `Theorem-C-length-three`, `theorem-C-length-three` | `DeansProblem.Coherent.Finite` |
| Theorem C (coherent form) | `Theorem-C-coherent`, `theorem-C-coherent` | `DeansProblem.Coherent.Infinite` |
| Corollary 6.4 | `Corollary-6·4`, `corollary-6·4` | `DeansProblem.Coherent.Infinite` |
| Proposition 6.6 | `Proposition-6·6`, `proposition-6·6` | `DeansProblem.Coherent.Finite` |
| Theorem D | `Theorem-D`, `theorem-D` | `DeansProblem.Examples.FixedTriple` |
| Proposition 6.9 | `Proposition-6·9`, `proposition-6·9` | `DeansProblem.Examples.FixedTriple` |
| Lemma 6.10 | `Lemma-6·10`, `lemma-6·10` | `DeansProblem.Partition` |
| Lemma 6.11 | `Lemma-6·11`, `lemma-6·11` | `DeansProblem.Fixed` |
| Lemma 1 | `Lemma-1`, `lemma-1` | `DeansProblem.Inflationary` |
| Lemma 2 | `Lemma-2`, `lemma-2` | `DeansProblem.Inflationary` |
| Lemma 3 | `Lemma-3`, `lemma-3` | `DeansProblem.Inflationary` |
| Lemma 4 | `Lemma-4`, `lemma-4` | `DeansProblem.Inflationary` |
| Proposition 7.2 | `Proposition-7·2`, `proposition-7·2` | `DeansProblem.FixedGenerator` |
| Proposition 7.3 | `Proposition-7·3`, `proposition-7·3` | `DeansProblem.FixedGenerator` |
| Proposition 7.4 | `Proposition-7·4`, `proposition-7·4` | `DeansProblem.FixedGenerator` |
| Theorem E | `Theorem-E`, `theorem-E` | `DeansProblem.FixedGenerator` |
| Corollary 7.5 | `Corollary-7·5`, `corollary-7·5` | `DeansProblem.Examples.SelfEmbedding` |
| Corollary E1 | `Corollary-E1`, `corollary-E1` | `DeansProblem.Shape` |
| Theorem F | `Theorem-F`, `theorem-F` | `DeansProblem.Inflationary` |
| Lemma 5 | `Lemma-5`, `lemma-5` | `DeansProblem.LengthThree` |
| Lemma 8.1 | `Lemma-8·1`, `lemma-8·1` | `DeansProblem.LengthThree` |
| Theorem G | `Theorem-G`, `theorem-G` | `DeansProblem.LengthThree` |
| Theorem 9.1 | `Theorem-9·1`, `theorem-9·1` | `DeansProblem.Truncation` |
| Theorem 9.2 | `Theorem-9·2`, `theorem-9·2` | `DeansProblem.AlmostProof.Links` |

### The definitions

A definition of the paper is named by the Agda definition it is.

| Definition | Names | Module |
| --- | --- | --- |
| Definition 4.1, a chain of sublattices isomorphic to `FL(3)`, and its equivalence with the record by free triples | `CopyChain`, `copyChain→chain`, `chain→copyChain` | `DeansProblem.Chain.Copies` |
| Definition 4.1, the record of a chain by its free triples, and of a step | `Chain`, `Step` | `DeansProblem.Chain` |
| Definition 6.2, coherent chains of length `n`, and infinite ones | `Coherent`, `Coherentω` | `DeansProblem.Coherent.Finite` |
| Definition 7.1, inflationary and deflationary self-embeddings | `Inflationary`, `Deflationary` | `DeansProblem.Inflationary` |

### The remarks and the computations

A remark or a computation is not a result.  The claims of each that are
checked, under its number, are the following.

| Claim | Names | Module |
| --- | --- | --- |
| Computation 4.6: the sublattice `⟨x, y, d⟩` contains every link of the ladder and is infinite | `links⊆⟨x,y,c⟩`, `⟨x,y,c⟩-infinite` | `DeansProblem.Examples.ChainCondition` |
| Computation 4.6: membership in a finitely generated sublattice of a free lattice is decided | `inImage?` | `Lattices.Free.Membership` |
| Remark 5.1: the transitions from the bottom have bounded complexity | `transition-bound` | `DeansProblem.Coherent` |
| Remark 5.1: from the infinite pigeonhole principle, one proper self-embedding expresses the bottom triple, by the same three terms, in infinitely many later triples | `BottomRecurrence`, `bottom-recurrence` | `DeansProblem.Coherent.Infinite` |
| Remark 6.5: the hypothesis of the length-three form | `Recurs` | `DeansProblem.Coherent.Finite` |
| Remark 6.5: the infinite pigeonhole principle supplies it | `some-link-recurs`, `pigeonhole→coherent₃` | `DeansProblem.Coherent.Infinite` |
| Remark 6.5: the infinite pigeonhole principle, which, as this repository adds, decides LPO | `InfinitePigeonhole`, `pigeonhole→LPO` | `DeansProblem.Pigeonhole` |
| Remark 6.8: `Fix(θ₁)` contains a copy of `FL(ω)`, and the sublattice `⟨p, q, z⟩` | `ω-embedding`, `ω-fixed`, `⟨pqz⟩-fixed` | `DeansProblem.Examples.FixedTriple.Remarks` |
| Computation 6.12: the positive facts its counts rest on, that `ρ` fixes the eleven and fixes no free triple | `θ-fixes-T₁₁`, `θ-no-fixed-triple` | `DeansProblem.Examples.SelfEmbedding` |
| Computation 6.12: `θ₁` fixes a free triple | `fixed-triple` | `DeansProblem.Examples.FixedTriple` |
| Remark 8.2: the constructive proof of Theorem H, for the record of a chain | `recurrences-bounded`, `chain-escapes`, `Escapes`, `finite-colors-exhausted`, `no-chain` | `DeansProblem.NoChain` |
| Computation 10.1: the positive facts the searches found, that `θ₂` fixes the free triple of Theorem D, and that `θ₁` and `θ₂` are rigid (that `θ₁` fixes it is the row of Computation 6.12) | `rigid′`, `fixed-triple₂`, `rigid₂` | `DeansProblem.Examples.Rigidity` |

### Other checked claims, by section

| Claim | Names | Module |
| --- | --- | --- |
| Section 1.1(i): a chain in one free lattice gives one in `FL(3)` and in every `FL(X)` with three distinct generators | `reduction`, `copyChain⇔FL₃` | `DeansProblem.Chain.Reduction` |
| Section 1.1(i): `FL(n)` is finite for `n ≤ 2` | `FL₀-enumeration`, `FL₁-enumeration`, `FL₂-enumeration` | `Lattices.Free.Small` |
| Section 1.1: Freese's old generators have complexity 3 and his new ones 4 | `old-complexity`, `new-complexity` | `DeansProblem.Examples.FreeseStep.Complexity` |
| Section 2.3: `FL(X)` has a least and a greatest element exactly when `X` has a finite nonempty enumeration | `FL-bottom⇔enumeration`, `FL-top⇔enumeration` | `Lattices.Free.Extrema` |
| Section 2.3: a self-embedding is proper exactly when some generator is none of its images | `not-onto⇔missed-generator` | `Lattices.Free.Membership` |
| Section 2.5: the requirement of Lemma 2.8 that the joinand not be a generator cannot be dropped | `generator-joinand-not-preserved` | `DeansProblem.Examples.FixedTriple.Remarks` |
| Section 3.3: Freese's example, items (i) to (iv) | `relation-1`, `relation-2`, `relation-3`, `relation-4`, `relation-1ᵇ`, `relation-2ᵇ`, `relation-3ᵇ`, `relation-4ᵇ`, `relation-1ᶜ`, `relation-2ᶜ`, `relation-3ᶜ`, `relation-4ᶜ`, `abc-free`, `abc'-free`, `abc≈`, `a'∉⟨abc⟩` | `DeansProblem.Examples.FreeseStep` |
| Section 3.3: Freese's example, item (v) | `b̄₂≤a`, `c̄₂≤a` | `DeansProblem.Examples.FreeseBox` |
| Section 3.4: Freese's step inside `FL(3)`, and the descending chain | `θ-free`, `x∉θ`, `inside`, `descending` | `DeansProblem.Examples.SelfEmbedding` |
| Section 4.2: the chain condition for `n`-generated sublattices, which contains Theorem H | `StrictlyAscending`, `ChainCondition`, `chainCondition→no-copy-chain` | `DeansProblem.Chain.Condition` |
| Section 4.2: two elements generate at most four, so the chain condition holds for two generators | `two-generate-four`, `chainCondition₂` | `DeansProblem.Chain.TwoGenerated` |
| Section 4.2, after Theorem 4.5: the bottom link's term recurs in every link | `t₀-recurs` | `DeansProblem.Examples.ChainCondition` |
| Section 5: Theorem A for a free sublattice | `self-similar-onto` | `DeansProblem.SelfSimilar` |
| Section 5, after Corollary A2: the three candidates fail | `π-fails`, `π²-fails`, `bar-not-free` | `DeansProblem.Examples.FreeseEquations` |
| Section 5, after Corollary A3: no chain is generated by one embedding, even with a period | `no-periodic-embedding` | `DeansProblem.Chain.Condition` |
| Section 5, after Corollary A3: the steps of a chain are never the powers of one map | `not-powers`, `not-powersᶜ` | `DeansProblem.Chain.Powers` |
| Section 6.4, after Theorem D: `θ₁` fixes `⟨p, q, z⟩`, which holds the triple of Theorem D and is infinite | `⟨pqz⟩-fixed`, `Θ≈μ[pqz]`, `⟨pqz⟩-infinite` | `DeansProblem.Examples.FixedTriple.Remarks` |
| Section 7.1: the dual of a self-embedding | `dualˢ`, `dual-free`, `dual-misses`, `dual-fixed`, `dual-iter`, `dual-inflationary` | `DeansProblem.FixedGenerator` |
| Section 7.2, after Lemma 3: a proper inflationary self-embedding fixes no meet of two generators | `fixes-no-meet`, `fixes-z-no-meetand` | `DeansProblem.Inflationary` |
| Section 7.4, after Corollary 7.5: a proper self-embedding that moves every generator fixes no free triple | `moves→no-fixed-triple` | `DeansProblem.FixedGenerator` |
| Section 8.2: every proper self-embedding with a fixed free triple is rigid | `no-upper-link` | `DeansProblem.LengthThree` |
| Section 8.3: no infinite coherent chain, and no chain with a recurring transition | `no-coherentω`, `no-chain-recurs` | `DeansProblem.LengthThree` |
| Section 9.2: labeled patterns, finitely many on a fixed tree | `Pattern`, `patternOf`, `Enumerate.finitely-many-patterns` | `DeansProblem.Truncation.Pattern` |
| Section 9.3: the box of a labeled pattern holds the triple of every truncation with that pattern | `bound-sound` | `DeansProblem.Truncation.Pattern` |
| Section 9.3: Freese's Lemma 2, in any lattice | `above-or-below`, `lemma-2-at`, `lemma-2` | `DeansProblem.Irredundant` |
| Section 9.3: the gap, as a decidable predicate | `StronglyIrredundant`, `DecideBox.stronglyIrredundant?` | `DeansProblem.AlmostProof` |
| Section 9.3: Freese's `a₁` lies outside his link | `a₁∉⟨a',b',c'⟩` | `DeansProblem.Examples.FreeseGap` |
| Section 9.3: inside a link read as `FL(3)`, the box of a generator that is both a joinand and a meetand is a point | `point-box-in-link` | `DeansProblem.Truncation.Pattern` |
| Section 9.4: Freese's box is strongly irredundant, and his terms express his base in at most one link | `freese-box-irredundant`, `freese-terms-in-box`, `freese-terms-once` | `DeansProblem.Examples.FreeseBox` |
| Section 10.1: `FL(X)` with its universal property | `FL`, `FL-extend` | `Lattices.Free.Universal` |

### The names

+  **The convention**.  The statement of Theorem 4.5 is the type
   `Theorem-4·5`, and its proof is `theorem-4·5 : Theorem-4·5`; likewise
   `Lemma-2·2`, `Corollary-2·4`, `Proposition-4·2`.  The lettered results are
   `Theorem-A` to `Theorem-H`, `Corollary-A1` to `Corollary-A4`,
   `Corollary-E1` and `Lemma-1` to `Lemma-5`, and the four forms of Theorem C
   are `Theorem-C-one-step`, `Theorem-C-four-links`, `Theorem-C-length-three`
   and `Theorem-C-coherent`.  A statement whose parts quantify over universe
   levels separately is a record in `Setω` with fields `part-1`, `part-2`,
   ..., in the paper's order.
+  **The middle dot**.  Agda reserves `.` for qualified names
   (`Theorem-4.5` is a parse error), so the separator is the middle dot `·`
   (U+00B7), which Agda takes inside a name.
+  **The numbering** is that of the paper's full version.  If the paper
   renumbers its results, the names follow, in a commit of their own.
+  **FJN's results**.  agda-lattices names the results of
   [Freese, Ježek and Nation][FJN] that it proves by a standard name where
   the result has one (`WhitmansTheorem` for FJN Theorem 1.11), and otherwise
   by FJN's number (`FJN-1·19`, with its proof `fjn-1·19`); its module
   `Lattices.Free.FJN` lists them in the book's order.  The statements of the
   paper's Section 2 are built from them in `DeansProblem.Preliminaries`.

## The modules

Every module of this repository is under `src/DeansProblem/`, with the barrel
`DeansProblem`, which re-exports the modules below but the worked examples,
`DeansProblem.Irredundant`, `DeansProblem.Ladder` and `DeansProblem.Paper`.

+  **The paper's results**.  `DeansProblem.Paper` (the 48 results in the
   paper's order) and `DeansProblem.Preliminaries` (Section 2).
+  **Chains**.  `DeansProblem.Chain` (steps and chains of free triples,
   Proposition 4.3), `DeansProblem.Chain.Copies` (chains of sublattices
   isomorphic to `FL(3)`, the paper's definition, proved equivalent to the
   record of a chain), `DeansProblem.Chain.Limit` (Proposition 4.2, a chain
   and the direct limit of its self-embeddings),
   `DeansProblem.Chain.Reduction` (the reduction of Section 1.1 to `FL(3)`),
   `DeansProblem.Chain.Condition` (Theorem A and Corollary A3, and the chain
   condition for `n`-generated sublattices), `DeansProblem.Chain.Powers` (the
   steps of a chain are never the powers of one map) and
   `DeansProblem.Chain.TwoGenerated` (the chain condition for two
   generators).
+  **Toward Theorem H**.  `DeansProblem.SelfSimilar` (Corollary A1),
   `DeansProblem.Coherent` and `DeansProblem.Coherent.Finite` (transitions
   and coherent chains, Lemmas 6.1 and 6.3, Theorem C's finite forms and
   Proposition 6.6), `DeansProblem.Pigeonhole` (the infinite pigeonhole
   principle, as a hypothesis), `DeansProblem.Coherent.Infinite` (Theorem C's
   coherent form and Corollary 6.4), `DeansProblem.Partition` (the partition
   lemma, Lemma 6.10), `DeansProblem.Fixed` (periodic and fixed points,
   Corollary A4 and Lemma 6.11), `DeansProblem.Inflationary` (Lemmas 1 to 4
   and Theorem F), `DeansProblem.FixedGenerator` (Propositions 7.2 to 7.4
   and Theorem E), `DeansProblem.Shape` (Corollary E1),
   `DeansProblem.LengthThree` (Lemmas 5 and 8.1 and Theorem G) and
   `DeansProblem.NoChain` (Theorem H).
+  **Without freeness**.  `DeansProblem.Ladder` (Lemma 4.4, in any lattice).
+  **Freese's notes**.  `DeansProblem.Truncation` (Theorem 9.1, the
   truncation theorem), `DeansProblem.Truncation.Pattern` (labeled patterns
   and their boxes), `DeansProblem.Irredundant` (Freese's Lemma 2 in any
   lattice), `DeansProblem.AlmostProof` (boxes, and the gap in Freese's almost
   proof as a predicate) and `DeansProblem.AlmostProof.Links` (Theorem 9.2).
+  **Worked examples**, under `DeansProblem.Examples`: `FreeseStep` (Freese's
   example, on terms over nine generators), `FreeseStep.Complexity` (the
   complexities of its generators), `SelfEmbedding` (Corollary 7.5),
   `FreeseEquations` (Corollary A2), `FreeseBox`, `FreeseGap`, `FixedTriple`
   (Theorem D and Proposition 6.9), `FixedTriple.Remarks`, `Rigidity` and
   `ChainCondition` (the ladder, Theorem 4.5).

## The cost

The cost of the check is stated for the paper's tag, measured as follows:
`make check` from a clean clone, with the Agda already in the Nix store, timed
for wall time and peak resident memory by `/usr/bin/time -v`, the median of
the runs reported with their range; once with the interface files of
agda-lattices and of the Agda Universal Algebra Library built in the same run
(a fresh clone's first check, which checks 173 modules: this repository's 38,
39 of agda-lattices, 95 of the Agda Universal Algebra Library, and the
aggregator), and once with them already built (`make clean`, then the check
again, which checks 39), which is the cost of this repository's modules
alone.  The Agda run, the figure the paper gives, is timed on its own, by a
timing wrapper given to the Makefile as `AGDA`; the rest of `make check` is
`make safety` and `scripts/check-paper.sh`, whose two Agda probes load the
development's interfaces.  The Agda run uses one core: its processor time is
its wall time.

Measured on 9 November 2026 at commit `9f195d3`, whose code the tag has, in
six runs of each kind (two sets of three, from six fresh clones), on a
machine with an Intel Core i9-12900H (6 performance and 8 efficiency cores,
20 threads) and 62 GiB of memory, shared with other work at a load average
of 3.1 to 4.8:

| The libraries' interfaces | `make check` | The Agda run | Peak resident memory |
| --- | --- | --- | --- |
| built in the run | 52.7 s (44.2 to 56.8) | 45.4 s (37.8 to 49.6) | 2.03 to 2.25 GiB |
| already built | 26.3 s (24.1 to 28.5) | 19.1 s (17.6 to 21.2) | 1.74 to 1.77 GiB |

The load is the measurement's, not the release's.  The same commit, with the
same toolchain, measured on 31 October 2026 at a load average of 0.3 to 1.1,
gave the paper's figures: the Agda run took 32.5 seconds from source (32.4
to 32.6, three runs) and 15.0 seconds with the libraries built, and
`make check` from source 37.7 seconds.  The medians above are 27 and 40
percent higher, and a check with the libraries built, pinned to the least
busy performance core, took 16.9 seconds for the Agda run.  The peak
follows the garbage collector's schedule, which depends on timing: each set
of three runs from source peaked at one value, 2.25 GiB in the first and
2.03 GiB in the second, and the runs of 31 October at 2.24, 2.24 and 2.34
GiB.

Pinned to one core, with Agda's per-module profile (every interface file
deleted, then `taskset -c 0 make PROFILE=modules profile`), the check from
source took 43.3 seconds on 9 November, and 32.4 on 31 October.  The
costliest modules of this repository were, both times and in this order,
`DeansProblem.Examples.FreeseStep.Complexity` (3.0 seconds on 9 November),
`DeansProblem.Examples.FreeseBox` (2.4), `DeansProblem.Examples.FreeseStep`
(1.8) and `DeansProblem.FixedGenerator` (1.6); no other module, of this
repository or of the libraries, took a second.  The cost is where the
Whitman decisions are, above all in the worked examples on Freese's terms.

### The counts

At commit `9f195d3`, with the libraries at the commits the flake pins, the
counts the paper states are as follows:

+  this repository's 38 modules have 15,410 lines of literate source, of
   which 9,312 are Agda code;
+  the 39 modules of agda-lattices that the check reads, of the 91 at its
   pin, have 16,435 lines, of which 10,247 are code;
+  the check reads 95 modules of the Agda Universal Algebra Library.

A line of code is one inside a block that Agda reads, by its rules for
literate Markdown: a block opened by a fence that is bare or marked `agda`,
and closed by a bare fence, indented or not.  The modules of agda-lattices
are those that this repository's modules import, directly or not, with the
two that `make check` adds (`TABLE_LIBRARY_MODULES` in the `Makefile`).

## Provenance

The development was first written together with the general modules that
now form agda-lattices, and moved into the namespace `DeansProblem` in October
2026, when those were published as a library of their own.  One module,
`DeansProblem.Examples.FreeseStep` (Freese's example), was first written in
the [Agda Universal Algebra Library][agda-algebras].

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
[algebras-pin]: https://github.com/ualib/agda-algebras/tree/b4d0ab6cd9a6e32f28857bd5014bbacaa284bb35
[lattices-pin]: https://github.com/ualib/agda-lattices/releases/tag/v0.2.0
[agda/agda]: https://github.com/agda/agda
[agda-pin]: https://github.com/agda/agda/tree/da66a8c75f11d10699a6b38b261efdf244b66f2a
[agda-stdlib]: https://github.com/agda/agda-stdlib
[Cachix]: https://www.cachix.org/
[cost]: #the-cost
[Nix]: https://nixos.org/
[paper]: https://arxiv.org/abs/YYMM.NNNNN
[FJN]: https://doi.org/10.1090/surv/042
