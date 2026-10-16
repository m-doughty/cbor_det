#!/usr/bin/env bash
# The differential test: the ghost predicate Det_End and the whole-input
# wrapper Accept_Whole, executed with the library's contracts on (the
# contracts cell of the build matrix), against an independent reference
# decoder written in Python (tests/reference/ref_cbor_det.py; see
# tests/reference/README.md).
#
# Steps, each of which must pass:
#   1. the reference is the recorded one (its SHA-256 below), and its own
#      self-test passes;
#   2. the test runner is built in the contracts cell (-O0, contracts);
#   3. the classifier's self-test, and a check that the runner fails a row
#      the cost model got wrong ("unmodelled") and passes one it got right;
#      then for each seed: the reference writes its corpus, cost_model.py
#      classifies every row by the predicted cost of running Det_End on
#      it, and the runner compares every row of class "run" (ends and
#      whole-input verdicts separately, at index 1 and at the top of
#      Index, and the lemmas on the accepted items); the counts per class
#      are printed, deferred rows included; the measured times are
#      checked against the cost model;
#   4. the reference's head table is compared with the head helpers
#      (run before the corpus, as it is quick);
#   5. every input of 0 to 3 bytes is compared.
#
# Generated files go to tests/obj/differential (ignored by git), never
# into the repository.
#
# A failed build prints only the lines of its log that have a known form
# (see build_failure_lines below), at most 40, and keeps the whole log in
# tests/obj. The limit: a compiler message can quote a value the caller
# gave a project setting (an invalid CBOR_DET_LIBRARY_TYPE or LIBRARY_TYPE
# is printed back), so no private value belongs in one.
#
# Usage: scripts/differential.sh
#   CBOR_DET_SEEDS        seeds of the corpus (default 1): decimal numbers,
#                         separated by spaces, tabs or newlines, taken as
#                         integers;
#                         only 1, 2 and 3, whose corpus row counts are
#                         pinned, are supported. Empty, blank or anything
#                         else is an error. The head table and the
#                         exhaustive run must have their known counts too.
#                         This script never prints this setting's value
#                         (the build-message limit in build_failure_lines
#                         concerns project settings, not this one)
#   CBOR_DET_COST_LIMIT   the most calls a row may be predicted to need to
#                         be run (default 200000000: about 50 s for one
#                         row at the slowest rate validate has measured,
#                         2.5e-7 s per call at -O0); rows above it are
#                         deferred and counted
#   ALR, PYTHON           the alr and python3 to use

set -euo pipefail

# The reference as kept here. It differs from the file as received
# (sha256 aa52b799511abb2676c1e02d7b47d1f48131fa949e6786ae0214e3b2bd88d696)
# only in three display labels of RFC examples, written with Python \u
# escapes instead of non-ASCII characters (the same strings at run time),
# and in its argument errors, which never print the arguments given: the
# same output (see tests/reference/README.md).
REFERENCE_SHA256=36f1d76b9cf4a96a10104ecbb5e108624a7d1d0f34b4eb3f365f2daf893edd89

ALR=${ALR:-alr}
PYTHON=${PYTHON:-python3}
limit=${CBOR_DET_COST_LIMIT:-200000000}

# Settings are checked before anything runs. A message says what kind
# of setting is wrong, never its value; a tool that cannot start is
# reported by its role and exit status, never by what the shell said.
if ! command -v "$ALR" > /dev/null 2>&1; then
  echo "differential: alr (ALR) cannot be run"
  exit 2
fi
status=0
"$ALR" --version > /dev/null 2>&1 || status=$?
if [ "$status" -ne 0 ]; then
  echo "differential: could not start alr (ALR), exit $status"
  exit 2
fi
if ! command -v "$PYTHON" > /dev/null 2>&1; then
  echo "differential: the Python interpreter (PYTHON) cannot be run"
  exit 2
fi
status=0
"$PYTHON" -c 'import sys; sys.exit(0 if sys.version_info >= (3, 10) else 3)' \
  > /dev/null 2>&1 || status=$?
if [ "$status" -eq 3 ]; then
  echo "differential: the Python interpreter (PYTHON) is not Python 3.10 or later"
  exit 2
elif [ "$status" -ne 0 ]; then
  echo "differential: could not start the Python interpreter (PYTHON), exit $status"
  exit 2
fi
case "$limit" in
  ''|*[!0-9]*)
    echo "differential: CBOR_DET_COST_LIMIT is not a decimal number"
    exit 2 ;;
esac
# The seeds: split on spaces, tabs and newlines; each a decimal
# number, taken as an integer (01 is 1), and one of the seeds whose row
# counts are pinned below.
seeds=
set -f
for token in ${CBOR_DET_SEEDS-1}; do
  case "$token" in
    *[!0-9]*)
      echo "differential: a seed in CBOR_DET_SEEDS is not a decimal number"
      exit 2 ;;
  esac
  token=$(printf '%s' "$token" | sed 's/^0*//')
  case "$token" in
    1|2|3) seeds="$seeds $token" ;;
    *) echo "differential: only the supported seeds 1, 2 and 3 can be run (their row counts are pinned)"
       exit 2 ;;
  esac
done
set +f
if [ -z "$seeds" ]; then
  echo "differential: no seeds (CBOR_DET_SEEDS is set but empty or blank): nothing would be compared"
  exit 2
fi

# The row counts the generated files must have, so that a truncated one
# fails: the corpus of each supported seed, the head table and the
# exhaustive file's verdicts.
corpus_rows () {
  case "$1" in
    1) echo 87814 ;;
    2) echo 87160 ;;
    3) echo 87646 ;;
  esac
}
HEADS_ROWS=67705
# Of those rows, the heads compared and the inputs both refuse (the rest,
# empty or of major types 6 and 7, are counted but not compared).
HEADS_COMPARED="heads compared 38664, refused by both 12114"
EXHAUSTIVE_COUNTS="inputs of 0 to 3 bytes 16843009, accepted whole by the reference 269799, failures 0"

# rows_are FILE N WHAT: FILE has exactly N lines, or the run fails.
rows_are () {
  local n
  n=$(wc -l < "$1" | tr -d ' ')
  if [ "$n" != "$2" ]; then
    echo "differential: FAILED: $3 has $n rows, expected $2 rows"
    exit 1
  fi
}

# Python, printing nothing of an exception but its type: no traceback
# (its file names are absolute paths) and no message (which can hold a
# path, or a value read from a file).
py () {
  "$PYTHON" -B -I -c 'import runpy, sys
sys.argv = sys.argv[1:]
try:
    runpy.run_path(sys.argv[0], run_name="__main__")
except SystemExit:
    raise
except BaseException as e:
    sys.stderr.write("python: " + type(e).__name__ + "\n")
    sys.exit(1)' "$@"
}

cd "$(dirname "$0")"
cd ..
cd tests

"$PYTHON" -B -I - reference/ref_cbor_det.py "$REFERENCE_SHA256" <<'PY'
import hashlib, sys
sys.tracebacklimit = 0
sys.excepthook = lambda t, v, b: sys.stderr.write("python: " + t.__name__ + "\n")
if sys.version_info < (3, 10):
    sys.exit("differential: Python 3.10 or later is needed")
path, expected = sys.argv[1], sys.argv[2]
with open(path, "rb") as f:
    actual = hashlib.sha256(f.read()).hexdigest()
if actual != expected:
    sys.exit("differential: the reference is not the recorded one")
print("reference: sha256 " + actual)
PY
py reference/ref_cbor_det.py selftest

out=obj/differential
mkdir -p "$out"
# --- build_failure_lines: begin (the same in matrix.sh, decoder-measure.sh,
# decoder-tests.sh and differential.sh; scripts/test-runner.sh checks it) ---
# build_failure_lines LOG: what a failed build said, without paths. Only
# lines of a known form are kept, at most the first 40 (the cause comes
# first):
#   - a message on one of the crate's own files (its name exactly as in
#     src, tests/src, the configuration directories or a project file):
#     unit.adb:12:4: text;
#   - "compilation of unit.adb failed", with the same rule for the name;
#   - gprbuild's "processing failed" on the crate's own project files,
#     and its and alr's fixed lines for a failed compilation or link.
# A line holding a slash or a backslash, or any character other than
# printable ASCII, is dropped whatever its form; so is every other line.
# The limit: a message can quote a value the caller gave a project setting
# (an invalid CBOR_DET_LIBRARY_TYPE or LIBRARY_TYPE is printed back), so
# no private value belongs in one.
build_failure_lines () {
  local LC_ALL=C
  local names=$'\n' root d f line name shown=0
  root=$(cd .. && pwd -P)
  for d in "$root/src" src "$root/config" config; do
    if [ -d "$d" ]; then
      for f in "$d"/*; do
        if [ -f "$f" ]; then names+="${f##*/}"$'\n'; fi
      done
    fi
  done
  for f in "$root"/*.gpr ./*.gpr; do
    if [ -f "$f" ]; then names+="${f##*/}"$'\n'; fi
  done
  local diag='^([A-Za-z0-9_.+-]+\.(ads|adb|gpr)):[0-9]+:[0-9]+: [ -~]+$'
  local comp='^ *compilation of ([A-Za-z0-9_.+-]+\.(ads|adb)) failed$'
  local proc='^gprbuild: "([A-Za-z0-9_.+-]+\.gpr)" processing failed$'
  echo "  the build's messages (lines of a known form only, without paths):"
  while IFS= read -r line || [ -n "$line" ]; do
    line=${line%$'\r'}
    case $line in
      */* | *\\* | *[!\ -~]*) continue ;;
    esac
    name=
    if [[ $line =~ $diag ]] || [[ $line =~ $comp ]] \
       || [[ $line =~ $proc ]]; then
      name=${BASH_REMATCH[1]}
      case $names in
        *$'\n'"$name"$'\n'*) ;;
        *) continue ;;
      esac
    else
      case $line in
        "gprbuild: *** compilation phase failed" \
          | "gprbuild: *** post compilation phase failed" \
          | "gprbuild: *** link phase failed" \
          | "ERROR: Compilation failed.") ;;
        *) continue ;;
      esac
    fi
    echo "    $line"
    shown=$((shown + 1))
    if [ "$shown" -ge 40 ]; then break; fi
  done < "$1"
  if [ "$shown" -eq 0 ]; then
    echo "    (none: the whole output is in the log)"
  fi
}
# --- build_failure_lines: end ---

# The build's output is kept in obj/differential; on a failure only its
# lines of a known form are printed, without paths (a message from a
# tool that cannot start can hold its path).
status=0
"$ALR" -n build -- -XCBOR_DET_OPT=O0 -XCBOR_DET_CHECKS=contracts \
  > "$out/build-contracts.txt" 2>&1 || status=$?
if [ "$status" -ne 0 ]; then
  echo "differential: the build of the contracts cell failed, exit $status (its output is in tests/$out/build-contracts.txt)"
  build_failure_lines "$out/build-contracts.txt"
  exit 1
fi
runner=bin/O0-contracts/test_main

echo "== the classifier and the runner fail a row the cost model gets wrong"
py reference/cost_model.py selftest
check="$out/runner-check"
mkdir -p "$check"
printf '00\t1\t1\trun\t1\n' > "$check/agree.tsv"
printf '00\t1\t1\tunmodelled\t1\n' > "$check/unmodelled.tsv"
if ! "$runner" corpus "$check/agree.tsv" > "$check/agree.txt" 2>&1; then
  cat "$check/agree.txt"
  echo "differential: FAILED: the runner fails a row it should pass"
  exit 1
fi
if "$runner" corpus "$check/unmodelled.tsv" > "$check/unmodelled.txt" 2>&1; then
  cat "$check/unmodelled.txt"
  echo "differential: FAILED: the runner passes an unmodelled row"
  exit 1
fi
echo "runner: an agreeing row passes, an unmodelled row fails"

echo "== head table"
py reference/ref_cbor_det.py heads --out "$out/heads.tsv"
rows_are "$out/heads.tsv" "$HEADS_ROWS" "the head table"
"$runner" heads "$out/heads.tsv" | tee "$out/heads.txt"
if ! grep -q "^heads: rows $HEADS_ROWS, $HEADS_COMPARED," "$out/heads.txt"; then
  echo "differential: FAILED: the runner did not compare the pinned heads ($HEADS_COMPARED)"
  exit 1
fi

for seed in $seeds; do
  echo "== corpus, seed $seed"
  py reference/ref_cbor_det.py corpus --seed "$seed" \
    --out "$out/corpus-$seed.tsv"
  py reference/cost_model.py classify \
    --in "$out/corpus-$seed.tsv" --out "$out/classified-$seed.tsv" \
    --limit "$limit"
  rows_are "$out/corpus-$seed.tsv" "$(corpus_rows "$seed")" "the corpus for seed $seed"
  "$runner" corpus "$out/classified-$seed.tsv" "$out/timings-$seed.txt" \
    | tee "$out/corpus-$seed.txt"
  if ! grep -q "^corpus: rows $(corpus_rows "$seed")," "$out/corpus-$seed.txt"; then
    echo "differential: FAILED: the runner did not read the pinned rows of seed $seed"
    exit 1
  fi
  py reference/cost_model.py validate \
    --timings "$out/timings-$seed.txt"
done


echo "== every input of up to 3 bytes"
py reference/exhaustive.py --out "$out/exhaustive.bin"
"$runner" exhaustive "$out/exhaustive.bin" | tee "$out/exhaustive.txt"
if ! grep -qF "$EXHAUSTIVE_COUNTS" "$out/exhaustive.txt"; then
  echo "differential: FAILED: the exhaustive run did not compare the known counts"
  exit 1
fi

echo "differential: passed"
