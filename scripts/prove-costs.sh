#!/usr/bin/env bash
# The cost table of scripts/prove.sh's shards, from the output of runs.
#
# Reads the files given, each holding the output of scripts/prove.sh
# (one whole run or any of its shards; a CI log whose lines carry a
# prefix ending in white space will do, and a trailing carriage return
# is ignored), takes every result line
#   NAME: proved P, not proved U, max steps S, exit E, T s
# and prints the table: for each NAME, the mean of its T over every such
# line in every file, rounded to the nearest whole second (halves up),
# at least 1; a comment header, then one "NAME SECONDS" line per name,
# sorted by name (C collation). Save it as scripts/prove-costs.txt.
#
# Usage: scripts/prove-costs.sh LOGFILE...
# Exit status: 0 the table printed; 2 no file given, a file that cannot
# be read, or no result line in any of them.

set -euo pipefail

if [ "$#" -eq 0 ]; then
  echo "usage: scripts/prove-costs.sh LOGFILE..." >&2
  exit 2
fi
files=()
for f in "$@"; do
  if [ ! -f "$f" ] || [ ! -r "$f" ]; then
    echo "prove-costs: a log file cannot be read" >&2
    exit 2
  fi
  # awk takes an operand such as x=y (or x=y/z) as an assignment, and -
  # as standard input: a relative path is given to it as ./PATH.
  case "$f" in
    /* | [A-Za-z]:/* | [A-Za-z]:\\*) files+=("$f") ;;
    *) files+=("./$f") ;;
  esac
done

table=$(awk '
  {
    sub(/\r$/, "")
    if ($0 !~ /(^|[ \t])[^ \t:]+: proved [0-9]+, not proved [0-9]+, max steps [0-9]+, exit [0-9]+, [0-9]+ s$/) { next }
    line = $0
    sub(/: proved [0-9]+, not proved [0-9]+, max steps [0-9]+, exit [0-9]+, [0-9]+ s$/, "", line)
    sub(/^.*[ \t]/, "", line)
    t = $(NF - 1)
    sum[line] += t + 0
    cnt[line]++
  }
  END {
    for (name in cnt) {
      # Rounded to the nearest whole second, halves up, in integers.
      q = 2 * sum[name] + cnt[name]
      mean = (q - q % (2 * cnt[name])) / (2 * cnt[name])
      if (mean < 1) { mean = 1 }
      print name " " mean
    }
  }' "${files[@]}" | LC_ALL=C sort)

if [ -z "$table" ]; then
  echo "prove-costs: no result line (NAME: proved ..., T s) in the files given" >&2
  exit 2
fi
echo "# Seconds per proof command, as measured by scripts/prove.sh: the mean"
echo "# over the runs given to scripts/prove-costs.sh, rounded, at least 1."
echo "# Used only to balance the shards of scripts/prove.sh; a missing or"
echo "# stale entry changes how work is split, never what is proved."
printf '%s\n' "$table"
