# =============================================================================
# agda-deans-problem: Makefile
# =============================================================================
#
# Run from the repository root inside `nix develop`, so that `agda` is the
# wrapper that knows the pinned standard library, agda-algebras and
# agda-lattices (see flake.nix).
#
# Agda targets:
#   make check               Check every module's pragma (make safety), then
#                            type-check the development: every module under
#                            src/, with the modules of agda-algebras and
#                            agda-lattices that it imports.
#   make test                Alias for `make check`.
#   make safety              Every module carries the --safe pragma and no
#                            postulate or unsafe pragma (scripts/check-safety.sh).
#   make safety-test         The cases of that check (scripts/test-check-safety.sh).
#   make profile             Type-check with Agda profiling enabled.
#   make clean               Remove this development's interface files and
#                            the aggregator (the copies of agda-algebras and
#                            agda-lattices under .deps/ and their interfaces
#                            are left alone).
#
# The aggregator, EverythingDeansProblem.agda:
#   +  every module under src/, and the library modules of
#      TABLE_LIBRARY_MODULES (below), generated and gitignored, so that one
#      run of Agda checks the whole development and every module the
#      README's table names;
#   +  a PHONY target, always regenerated, so that adding or removing a module
#      is picked up without anyone having to remember; `find` rather than
#      `git ls-tree`, so that untracked files in the working tree are included.
#
# Variables:
#   AGDA           the agda to run        (default: the one on PATH)
#   AGDA_OPTS      extra agda flags
# =============================================================================

.PHONY: help default check test safety safety-test profile clean EverythingDeansProblem.agda

# -- Configuration -----------------------------------------------------------
SRCDIR    := src
AGDA      ?= agda
# A 6 GiB heap limit, the one under which the paper's costs are measured, and
# above the peak of a whole check: the decision modules evaluate Whitman's
# procedure while they are checked.
RTS_OPTS  := +RTS -M6G -A128M -RTS
AGDA_OPTS ?=
# The modules of the pinned agda-lattices that the README's table of the
# paper's statements names and no module under src/ imports.  The aggregator
# imports them too, so that `make check` checks every module the table names.
TABLE_LIBRARY_MODULES := Lattices.Free.Canonical Lattices.Free.Semidistributive

.DEFAULT_GOAL := help

help: ## Show this help
	@grep -hE '^[a-zA-Z][a-zA-Z0-9_-]*:.*## ' $(MAKEFILE_LIST) \
	  | awk 'BEGIN {FS = ":.*## "} {printf "  \033[1m%-14s\033[0m %s\n", $$1, $$2}'

# -- Agda --------------------------------------------------------------------

default: EverythingDeansProblem.agda

# `--exact-split` is deliberately absent from the aggregator's pragma: it
# constrains definitions, and an aggregator contains nothing but imports.
# Each module carries `--exact-split` in its own header and is checked under
# it (make safety).
EverythingDeansProblem.agda: ## Regenerate the aggregator from the current tree
	@echo "target: $@"
	@{ \
	  echo "{-# OPTIONS --without-K --safe #-}"; \
	  echo ""; \
	  echo "module EverythingDeansProblem where"; \
	  echo ""; \
	  find $(SRCDIR) \
	      \( -name '*.lagda.md' -o -name '*.agda' \) \
	      ! -name 'EverythingDeansProblem.agda' \
	    | sed -e 's|^$(SRCDIR)/||' \
	          -e 's|\.lagda\.md$$||' \
	          -e 's|\.agda$$||' \
	          -e 's|/|.|g' \
	          -e 's|^|import |' \
	    | LC_ALL=C sort; \
	  for m in $(TABLE_LIBRARY_MODULES); do echo "import $$m"; done; \
	} > $(SRCDIR)/EverythingDeansProblem.agda
	@echo "  wrote $(SRCDIR)/EverythingDeansProblem.agda ($$(grep -c '^import' $(SRCDIR)/EverythingDeansProblem.agda) modules, $(words $(TABLE_LIBRARY_MODULES)) of them the library's)"

safety: ## Check every module's pragma, and that no postulate or unsafe pragma appears
	@echo "target: $@"
	bash scripts/check-safety.sh $(SRCDIR)

safety-test: ## Run the cases of the safety check
	@echo "target: $@"
	bash scripts/test-check-safety.sh

check test: safety EverythingDeansProblem.agda ## Check the pragmas, then type-check the development
	@echo "target: $@"
	$(AGDA) $(RTS_OPTS) $(AGDA_OPTS) $(SRCDIR)/EverythingDeansProblem.agda

# Profile a whole type-check.  Agda accepts one profiling mode at a
# time, so override PROFILE to choose: internal (phases), modules (per-module
# ranking), definitions (per-definition attribution).  Measure from an empty
# build (`make clean`), or only stale modules are timed.
PROFILE ?= modules

profile: EverythingDeansProblem.agda ## Type-check with Agda profiling (PROFILE=modules|internal|definitions)
	@echo "target: $@"
	$(AGDA) $(RTS_OPTS) --profile=$(PROFILE) $(SRCDIR)/EverythingDeansProblem.agda

clean: ## Remove this development's interface files and the aggregator
	@echo "target: $@"
	rm -rf _build
	find $(SRCDIR) -name '*.agdai' -delete
	rm -f $(SRCDIR)/EverythingDeansProblem.agda
