#!/usr/bin/env bash
# File: scripts/check-paper.sh
#
# The README's tables of names against the development, in two checks.
#
#   bash scripts/check-paper.sh [README.md] [src/DeansProblem/Paper.lagda.md]
#
# 1.  The table of results, the first table of the README's section "The
#     paper's results and their names", and the re-exports of
#     DeansProblem.Paper list the same results in the same order: row by
#     row, the statement, its proof and the module of the README's row are
#     those of the module's line
#
#       open import <Module> public using ( <Statement> ; <proof> )
#
#     with any `module <Statement>` in the using list left aside.
# 2.  Every name in the tables of that section (the results, the
#     definitions, the remarks and computations, and the other checked
#     claims) resolves in the module its row gives.  A probe file imports
#     each row's module with a using clause naming the row's names; a name
#     written Sub.name is opened from the submodule Sub of the module.  In
#     Agda 2.9 a using clause naming what a module does not export is a
#     warning (ModuleDoesntExport), and Agda exits 0, so the check reads
#     Agda's output for warnings, not its exit status.  A control probe
#     that names what DeansProblem.Ladder does not export must draw such a
#     warning first, so that the check is seen to see one.
#
# It runs agda, the dev shell's wrapper, which names this repository's
# library; run it after the development is type-checked (make check does),
# so that the probes load interfaces.  It prints each failure and exits 1,
# or prints a one-line summary and exits 0.
set -u
README=${1:-README.md}
PAPER=${2:-src/DeansProblem/Paper.lagda.md}
AGDA=${AGDA:-agda}
SECTION="## The paper's results and their names"
fail=0

[ -f "$README" ] || { echo "check-paper: no $README" >&2; exit 2; }
[ -f "$PAPER" ] || { echo "check-paper: no $PAPER" >&2; exit 2; }

# The rows of the tables of the section, one per line, as the names of the
# second column (separated by spaces, without backquotes), a tab, and the module
# of the third column; the rows of the first table are marked "R".
rows() {
  awk -v section="$SECTION" '
    $0 == section { on = 1; tables = 0; intable = 0; next }
    on && /^## / { on = 0 }
    on && /^### The names/ { on = 0 }
    !on { next }
    /^\| / {
      if (!intable) { intable = 1; tables++; header = 1; next }
      if (header) { header = 0; next }
      n = split($0, cell, / \| /)
      if (n < 3) { print "BAD\t" $0; next }
      names = cell[2]; module = cell[3]
      gsub(/ *\|$/, "", module)
      out = ""
      while (match(names, /`[^`]*`/)) {
        name = substr(names, RSTART + 1, RLENGTH - 2)
        out = out (out == "" ? "" : " ") name
        names = substr(names, RSTART + RLENGTH)
      }
      gsub(/`/, "", module)
      print (tables == 1 ? "R" : "T") "\t" out "\t" module
      next
    }
    { intable = 0 }
  ' "$README"
}

# The results of DeansProblem.Paper, one per line: statement, proof, module.
paper_results() {
  sed -n 's/^open import \([^ ]*\) *public using ( \(.*\) )$/\1\t\2/p' "$PAPER" |
    awk -F '\t' '{
      n = split($2, item, / ; /); out = ""
      for (i = 1; i <= n; i++) if (item[i] !~ /^module /) out = out (out == "" ? "" : " ") item[i]
      print out "\t" $1
    }'
}

ROWS=$(rows)
if printf '%s\n' "$ROWS" | grep -q '^BAD'; then
  printf '%s\n' "$ROWS" | grep '^BAD' | sed 's/^BAD\t/check-paper: a row with fewer than three columns: /'
  fail=1
fi

# 1. The table of results against DeansProblem.Paper.
table=$(printf '%s\n' "$ROWS" | awk -F '\t' '$1 == "R" { print $2 "\t" $3 }')
paper=$(paper_results)
results=$(printf '%s\n' "$table" | grep -c .)
if [ "$table" != "$paper" ]; then
  echo "check-paper: the README's table of results and $PAPER disagree (README <, Paper >):"
  diff <(printf '%s\n' "$table") <(printf '%s\n' "$paper") | sed 's/^/  /'
  fail=1
fi
if [ "$results" -eq 0 ]; then
  echo "check-paper: no table of results under \"$SECTION\" in $README"
  fail=1
fi

# 2. Every name of the tables, probed in its module.
TMP=$(mktemp -d)
trap 'rm -rf "$TMP"' EXIT

# Write a probe module: its header, then one import per row of the rows given
# on standard input (names, a tab, the module).
probe() {
  {
    echo '{-# OPTIONS --without-K --safe #-}'
    echo
    echo "module $1 where"
    echo
    awk -F '\t' '{
      n = split($1, name, / /); plain = ""; m = $2
      for (i = 1; i <= n; i++) {
        if (name[i] ~ /\./) {
          k = split(name[i], part, /\./)
          sub_ = part[1]; for (j = 2; j < k; j++) sub_ = sub_ "." part[j]
          print "import " m
          print "open " m "." sub_ " using ( " part[k] " )"
        } else plain = plain (plain == "" ? "" : " ; ") name[i]
      }
      if (plain != "") print "open import " m " using ( " plain " )"
    }'
  } > "$TMP/$1.agda"
}

# Run a probe, and print Agda's output if it holds a warning or an error.
run() {
  local out status
  out=$(cd "$TMP" && "$AGDA" -i . "$1.agda" 2>&1); status=$?
  if [ "$status" -ne 0 ] || printf '%s\n' "$out" | grep -qi 'warning'; then
    printf '%s\n' "$out"
    return 1
  fi
}

# The control names what a small module does not export, so that it costs
# the loading of that module alone.
printf 'Lemma-4·4\tDeansProblem.Ladder\nno-such-name-in-the-development\tDeansProblem.Ladder\n' |
  probe Control
if run Control > /dev/null; then
  echo "check-paper: the control probe, which names what DeansProblem.Ladder does not export, drew no warning"
  fail=1
fi

names=$(printf '%s\n' "$ROWS" | awk -F '\t' '$1 != "BAD" { n += split($2, x, / /) } END { print n + 0 }')
printf '%s\n' "$ROWS" | awk -F '\t' '$1 != "BAD" { print $2 "\t" $3 }' | probe Probe
if ! out=$(run Probe); then
  echo "check-paper: a name of the README's tables does not resolve in its module:"
  printf '%s\n' "$out" | sed 's/^/  /'
  fail=1
fi

if [ "$fail" -ne 0 ]; then
  exit 1
fi
modules=$(printf '%s\n' "$ROWS" | awk -F '\t' '{ print $3 }' | sort -u | grep -c .)
echo "check-paper: $results results agree with DeansProblem.Paper; $names names resolve in $modules modules"
