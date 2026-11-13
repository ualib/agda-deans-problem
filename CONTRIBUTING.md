<!-- File: CONTRIBUTING.md -->

# Contributing to agda-deans-problem

This repository is the formal development, in Agda, of the paper by William
DeMeo and Ralph Freese, *No free lattice contains an infinite ascending chain
of copies of FL(3)*.  The paper's own Agda is written here, under the
namespace `DeansProblem`: a pull request that adds or changes a module is
opened, reviewed and merged in this repository.  The general lattice theory it
uses comes from the library [agda-lattices][], which the flake pins at one
commit.  This guide says how a module joins the development, the conventions
it follows, the commands that check it, and the review it gets.

## Before you start

+  **The scope**.  A module here proves one of the paper's results, or a step
   of a proof of one, or checks one of its worked examples.  General lattice
   theory, true of free lattices or of lattices at large whatever the paper
   does with it, belongs in [agda-lattices][], and reaches this repository
   only through a release of that library that the flake pins (see "A change
   that needs the library", below).
+  **The map**.  The README's tables, under [The paper's results and their
   names][table], map each result of the paper to its statement in Agda and
   its module, and the checked claims of its definitions, remarks,
   computations and sections to their names.  Read them first: what you want
   to prove may be there, under the paper's numbering.  A new statement joins
   the tables (see "The README", below).
+  **An issue first**.  For anything more than a correction, open an issue
   that names the statement, by the paper's numbering, and the module it
   would go in, before writing the proof.  It lets the authors say whether
   the statement belongs here or in the library, and whether it is already
   under way.

## The environment

The toolchain is the repository's Nix flake: Nix 2.28 or later, with flakes
enabled.  The README's [Checking it][checking] says how to fetch the
pre-release Agda from the binary cache instead of building it (about an hour).
From a clone, the following checks the whole development:

    nix develop --command make check

It runs `make safety` (below), regenerates the aggregator
`src/EverythingDeansProblem.agda`, which imports every module under `src/`,
type-checks it under a heap limit of 6 GiB, and then runs
`scripts/check-paper.sh` (`make paper-check`), which checks the README's
tables against the development (see "The README", below).  It exits 0 when
every module checks and the tables agree; there is no separate test step,
since type-checking is the test.  On 2026-11-09 it ended as follows:

    target: safety
    bash scripts/check-safety.sh src
    safety: 38 modules, each with the pragma and no postulate or unsafe pragma
    target: EverythingDeansProblem.agda
      wrote src/EverythingDeansProblem.agda (40 modules, 2 of them the library's)
    target: check
    agda +RTS -M6G -A128M -RTS  src/EverythingDeansProblem.agda
    AGDA=agda bash scripts/check-paper.sh
    check-paper: 48 results agree with DeansProblem.Paper; 207 names resolve in 40 modules

The aggregator is generated, and found by `find`, so a new module is checked
without any list to edit.  The cases of the safety check run with the
following:

    nix develop --command make safety-test

which ends with `test-check-safety: all cases pass`; its last case runs the
check on `src/`.  `nix develop --command make help` lists the other targets
(`profile` and `clean`, used below).

`nix develop` writes a project-local Agda configuration under `.agda/` and the
wrapper `.agda/bin/agda`, which runs the pinned Agda with the pinned standard
library, Agda Universal Algebra Library and agda-lattices, so nothing in your
own Agda configuration takes part.  Start your editor from inside
`nix develop`, or point it at that wrapper; agda-algebras' guide has an
[Emacs configuration][emacs] that runs each checkout's own wrapper.

## How a module joins

### Where it goes

A module is a literate Markdown file under `src/DeansProblem/`, named for the
mathematics it develops: `DeansProblem.Partition` is
`src/DeansProblem/Partition.lagda.md`.  A worked example, a computation on
explicit terms, goes under `src/DeansProblem/Examples/`.

### The front matter and the prose

Each module opens with the front matter its neighbors carry (the keys
`layout`, `file`, `title`, `date` and `author`; copy them from a neighbor and
set `file`, `title` and `date`), then a heading and prose that states what the
module proves and how, with the paper's numbering.  The code comes in blocks
fenced as `agda`, with prose between them: each block is introduced by the
paragraph above it.  The pragma, the module line and the imports go in a
first block wrapped in an HTML comment (`<!--` and `-->` around the fenced
block), so that the rendered page opens with the mathematics; 35 of the 38
modules do this.  `src/DeansProblem/Partition.lagda.md` is a short module to
copy the layout from.

### The pragma

Every module carries the following pragma, as its one `OPTIONS` pragma, ahead
of its first declaration:

    {-# OPTIONS --without-K --exact-split --safe #-}

A worked example under `Examples/` may add `--lossy-unification` to it, and no
other module may; no module does at present.  A module holds no `postulate`
and no pragma that switches a check off (`TERMINATING`, `NON_TERMINATING`,
`NO_POSITIVITY_CHECK` and the others `scripts/check-safety.sh` names).  The
safety check enforces all of this without running Agda, and `--safe` enforces
it again when Agda runs.  A statement that rests on a principle Agda's logic
does not prove takes the principle as an explicit hypothesis, a record named
in its type, never a postulate: the README's [What is checked][checked] says
how the infinite pigeonhole principle is handled this way.

### Definitions

+  **One lemma per idea**.  Prefer a small named lemma to a long proof term,
   and name the steps a reader of the paper would name.
+  **A comment above each definition**.  Each definition is introduced just
   above it, by a comment saying what it states or by the prose paragraph
   that opens its code block.  A group declared together (several names
   under one signature, or the signatures of a mutual block) shares one.
+  **An explicit type signature on every definition**, the helpers of a
   `where` block included.
+  **Imports name what they use**, with a `using` clause on each
   `open import`; only the barrel `DeansProblem` re-exports whole modules.

### Citations

Cite the paper by its own numbering: its lettered theorems and corollaries
(Theorem C, Corollary A3), and its numbered lemmas, sections and remarks
(Lemma 4.4, Section 9.3, Remark 5.1), written in a module's prose as
`Section 4 of [the paper][]`, with the link `[the paper]` defined near the
top of the module, as the other modules define it.  Cite R. Freese, J. Ježek
and J. B. Nation, *Free Lattices* (1995), by the number of its theorem, lemma
or corollary, as `Corollary 1.13 of [Freese, Ježek, and Nation (1995)][]`,
or in a comment as `FJN Corollary 1.13`.

### Statements that assume a chain

A module that proves a statement assuming a chain of copies of `FL(3)`, or a
coherent chain of length at least three, must not import
`DeansProblem.NoChain` or `DeansProblem.LengthThree`, directly or through
another module: with the theorem that no chain exists in scope, such a
statement would hold vacuously.  Agda's dependency graph settles it.  For
`DeansProblem.Coherent.Infinite`, for example, the following commands print
nothing:

    nix develop --command agda +RTS -M6G -RTS \
      --dependency-graph=closure.dot src/DeansProblem/Coherent/Infinite.lagda.md
    grep -o 'label="[^"]*"' closure.dot | grep -E 'DeansProblem\.(NoChain|LengthThree)"'

The same two commands on `src/DeansProblem.lagda.md`, the barrel, print both
names, which shows that the check can see them.  Delete
`closure.dot` afterward, and say in the pull request how the closure was
checked.

### Names are kept

A module, once published, keeps its name, and so does each definition it
exports.  A change to an interface is a deprecation, never a silent rename:
keep the old name, defined as the new one, with a pragma that warns its users,
as follows:

    -- The old name of new-name, kept for its users.
    old-name : ...
    old-name = new-name
    {-# WARNING_ON_USAGE old-name "Deprecated: use new-name." #-}

The safety check and `--safe` both accept this pragma.

### The cost, and the barrel

The README's [The cost][cost] says how the cost of the whole check is
measured.  A module is heavy when it takes three seconds or more to check on
its own, as the following two commands report (`make clean` removes this
development's interface files and keeps the libraries' under `.deps/`):

    nix develop --command make clean
    nix develop --command make PROFILE=modules profile

A heavy module carries `check-cost: heavy` in its front matter, says in its
prose what it costs and why, and is imported by no barrel: the barrel
`DeansProblem` links to it in its prose instead, as it does for the worked
examples.  No module is heavy at present: measured on 2026-10-30, the largest,
`DeansProblem.Examples.FreeseStep.Complexity`, took 2.4 s of a total of
17.0 s.  `DeansProblem.Examples.FreeseStep` and
`DeansProblem.Examples.FreeseStep.Complexity` say in their prose how they
were brought under the limit.  No script checks the marker; the review does.

### The README

A result of the paper is one definition, whose type is its statement, with
one proof, defined in the module that proves it and named by the README's
convention (`Theorem-4·5` and `theorem-4·5`); it has one row in the README's
table of results and one re-export in `DeansProblem.Paper`, both in the
paper's order.  A checked claim of a definition, a remark, a computation or a
section's prose adds its row to the README's other [tables][table], with the
claim by the paper's numbering, its names, and its module.  `make check` ends
with `scripts/check-paper.sh`, which fails unless the table of results and
`DeansProblem.Paper` list the same results in the same order, and unless every
name of the tables resolves in its module.  A new module joins the
README's list of the modules, and the barrel `DeansProblem` and its guide to
the submodules, unless it is heavy or, like the worked examples, meant to be
imported on its own.  If a row names a module of agda-lattices that no module
here imports, add that module to `TABLE_LIBRARY_MODULES` in the `Makefile`,
so that `make check` checks it.

## A change that needs the library

A proof here imports agda-lattices only at the pinned commit, and never copies
one of its modules.  A statement that needs a new general lemma goes to the
library first: an issue and a pull request on [agda-lattices][], then a
release of the library, then a pull request here that moves the pin (the
`agda-lattices` input's URL in `flake.nix`, then `nix flake lock` to update
`flake.lock`), and then the proof that uses the lemma.  Every library module
this repository imports must check at the new pin, which `make check`
confirms.

## The workflow

1.  Fork the repository, and make a branch named for the issue:
    `NNN-short-description`, where `NNN` is the issue's number.
2.  Make commits that each do one thing, each message a one-line summary and,
    when the change is not trivial, a paragraph saying what and why.
3.  Run `nix develop --command make check` and, if you changed
    `scripts/check-safety.sh`, `nix develop --command make safety-test`.
4.  Open a pull request against `main` that names the issue, and says which
    statements of the paper it proves and, where a statement assumes a chain,
    how its import closure was checked.

Two workflows run on every pull request: `check`
(`.github/workflows/check.yml`), which runs `nix develop --command make check`,
and `ci` (`.github/workflows/ci.yml`), which runs shellcheck over `scripts/`
and the safety check's cases.  Both must pass.

## The review

The authors review every pull request, and merge it once both workflows pass
and the review is done.  The review reads the following:

+  each statement against the paper: that the Agda type says what the paper
   says, under the paper's numbering, with no hypothesis the paper does not
   have (or with the hypothesis named in the type and in the prose);
+  the conventions above: the pragma, the prose and comments, the citations,
   the names kept;
+  for a statement that assumes a chain, the import closure;
+  the cost, for a module that may be heavy;
+  the README's tables and list of modules.

Expect to iterate.  Questions are welcome in the issue or in the pull request.

## License

The development is licensed under the Apache License 2.0 (`LICENSE`).  Under
its section 5, a contribution you submit for inclusion is licensed under the
same terms, unless you state otherwise.

[agda-lattices]: https://github.com/ualib/agda-lattices
[checked]: README.md#what-is-checked
[checking]: README.md#checking-it
[cost]: README.md#the-cost
[emacs]: https://github.com/ualib/agda-algebras/blob/master/CONTRIBUTING.md#emacs-with-several-checkouts
[table]: README.md#the-papers-results-and-their-names
