#!/usr/bin/env bash
# The decoder's tests: Cbor_Det.Decoder.Check against two independent
# references in tests/reference, written without access to this crate's
# code: the reference decoder (ref_cbor_det.py, for the verdict) and the
# status oracle (ref_status.py, for the Status and Where of a rejection,
# from the precedence table of the decoder's contract).
#
# Steps, each of which must pass:
#   1. both references are the recorded ones (their SHA-256 below), and
#      their own self-tests pass;
#   2. the test runner is built in a plain cell (-O2, language checks, no
#      contracts) and in the contracts cell (-O0, contracts: Check's
#      postcondition, the ghost Det_End, runs on every call);
#   3. the runner's vectors in both cells (RFC 8949 Appendix A, a
#      rejection per Status with shifted bounds, the overlapping-rule and
#      owed-member examples, null bounds) and, in the contracts cell, the
#      operation counts against their envelope;
#   4. VERDICT: every input of the reference's head table, with the
#      reference's whole-input verdict, in both cells (its row count and
#      its number of accepted inputs pinned below; a cell that fails, or
#      compares other counts, fails the stage after both cells ran); for
#      each seed, the reference's corpus, classified by the cost model:
#      every row in the plain cell, and in the contracts cell every row
#      the cost model allows (the rest are counted, never skipped
#      silently); every input of 0 to 3 bytes in both cells. The contracts
#      cell's limit is lower than the differential test's: there the
#      decoder also executes its lemma calls and loop invariants, which
#      re-evaluate the ghost Members_End and Keys_Ascending at every
#      member, so a row costs more than its Det_End alone;
#   5. STATUS (plain cell): the oracle's corpus (seed 1), the oracle's
#      answers on every row of the reference's corpora, and the boundary
#      inputs (wide arrays and maps, nested container keys, maximum
#      lengths and counts, map counts around half the bytes left), each
#      at index 1, at index 1000 and ending at Index'Last, the empty
#      input also with null bounds.
#
# Generated files go to tests/obj/decoder (ignored by git).
#
# A failed build prints only the lines of its log that have a known form
# (see build_failure_lines below), at most 40, and keeps the whole log in
# tests/obj. The limit: a compiler message can quote a value the caller
# gave a project setting (an invalid CBOR_DET_LIBRARY_TYPE or LIBRARY_TYPE
# is printed back), so no private value belongs in one.
#
# Usage: scripts/decoder-tests.sh
#   CBOR_DET_SEEDS        seeds of the reference's corpus (default "1 2 3"):
#                         decimal numbers separated by spaces, tabs or
#                         newlines,
#                         taken as integers; only 1, 2 and 3, whose
#                         corpus row counts are pinned, are supported.
#                         Empty, blank or anything else is an error. The
#                         oracle's seed-1 corpus, the head table, the
#                         boundary inputs and the exhaustive run must
#                         have their known counts too, so that a
#                         truncated corpus fails.
#                         This script never prints this setting's value
#                         (the build-message limit in build_failure_lines
#                         concerns project settings, not this one)
#   CBOR_DET_DECODER_COST_LIMIT  the most Det_End calls the cost model may
#                         predict for a row run in the contracts cell
#                         (default 1000000: about a minute a seed)
#   CBOR_DET_NO_HUGE      set to leave out the 1 000 000-member array
#   ALR, PYTHON           the alr and python3 to use

set -euo pipefail

# The references as kept here (tests/reference/README.md says how each
# differs from the file as received).
REFERENCE_SHA256=36f1d76b9cf4a96a10104ecbb5e108624a7d1d0f34b4eb3f365f2daf893edd89
ORACLE_SHA256=6dc6f3064139acdc6fbf3f139a94bf59062fb68f3b71edccff9acf1231fdcb9f

ALR=${ALR:-alr}
PYTHON=${PYTHON:-python3}
limit=${CBOR_DET_DECODER_COST_LIMIT:-1000000}

# Settings are checked before anything runs. A message says what kind
# of setting is wrong, never its value; a tool that cannot start is
# reported by its role and exit status, never by what the shell said.
if ! command -v "$ALR" > /dev/null 2>&1; then
  echo "decoder-tests: alr (ALR) cannot be run"
  exit 2
fi
status=0
"$ALR" --version > /dev/null 2>&1 || status=$?
if [ "$status" -ne 0 ]; then
  echo "decoder-tests: could not start alr (ALR), exit $status"
  exit 2
fi
if ! command -v "$PYTHON" > /dev/null 2>&1; then
  echo "decoder-tests: the Python interpreter (PYTHON) cannot be run"
  exit 2
fi
status=0
"$PYTHON" -c 'import sys; sys.exit(0 if sys.version_info >= (3, 10) else 3)' \
  > /dev/null 2>&1 || status=$?
if [ "$status" -eq 3 ]; then
  echo "decoder-tests: the Python interpreter (PYTHON) is not Python 3.10 or later"
  exit 2
elif [ "$status" -ne 0 ]; then
  echo "decoder-tests: could not start the Python interpreter (PYTHON), exit $status"
  exit 2
fi
case "$limit" in
  ''|*[!0-9]*)
    echo "decoder-tests: CBOR_DET_DECODER_COST_LIMIT is not a decimal number"
    exit 2 ;;
esac
# The seeds: split on spaces, tabs and newlines; each a decimal
# number, taken as an integer (01 is 1), and one of the seeds whose row
# counts are pinned below.
seeds=
set -f
for token in ${CBOR_DET_SEEDS-1 2 3}; do
  case "$token" in
    *[!0-9]*)
      echo "decoder-tests: a seed in CBOR_DET_SEEDS is not a decimal number"
      exit 2 ;;
  esac
  token=$(printf '%s' "$token" | sed 's/^0*//')
  case "$token" in
    1|2|3) seeds="$seeds $token" ;;
    *) echo "decoder-tests: only the supported seeds 1, 2 and 3 can be run (their row counts are pinned)"
       exit 2 ;;
  esac
done
set +f
if [ -z "$seeds" ]; then
  echo "decoder-tests: no seeds (CBOR_DET_SEEDS is set but empty or blank): nothing would be compared"
  exit 2
fi

# The row counts the corpora must have, so that a truncated one fails:
# the reference's corpus for the seeds known here, and the oracle's.
reference_rows () {
  case "$1" in
    1) echo 87814 ;;
    2) echo 87160 ;;
    3) echo 87646 ;;
  esac
}
ORACLE_ROWS_SEED_1=87039
# The reference's head table: its rows, and the line each cell's verdict
# run must print (every row run, and the inputs accepted).
HEAD_TABLE_ROWS=67705
HEAD_TABLE_COUNTS="verdict: rows 67705, run 67705 (Ok 1104)"
EXHAUSTIVE_COUNTS="inputs of 0 to 3 bytes 16843009, Ok 269799, disagreements 0"
BOUNDARY_ROWS=230
BOUNDARY_ROWS_NO_HUGE=228

cd "$(dirname "$0")"
cd ..
cd tests

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

start=$SECONDS
stamp () {
  echo "-- $1 ($((SECONDS - start)) s so far)"
}

"$PYTHON" -B -I - reference/ref_cbor_det.py "$REFERENCE_SHA256" \
  reference/ref_status.py "$ORACLE_SHA256" <<'PY'
import hashlib, sys
sys.tracebacklimit = 0
sys.excepthook = lambda t, v, b: sys.stderr.write("python: " + t.__name__ + "\n")
if sys.version_info < (3, 10):
    sys.exit("decoder-tests: Python 3.10 or later is needed")
args = sys.argv[1:]
for path, expected in zip(args[0::2], args[1::2]):
    with open(path, "rb") as f:
        actual = hashlib.sha256(f.read()).hexdigest()
    if actual != expected:
        sys.exit("decoder-tests: " + path + " is not the recorded one")
    print(path + ": sha256 " + actual)
PY
py reference/ref_cbor_det.py selftest
py reference/ref_status.py selftest
stamp "references checked"

out=obj/decoder
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

# build CELL OPT CHECKS: its output kept in obj/decoder; on a failure
# only its lines of a known form are printed, without paths (a message
# from a tool that cannot start can hold its path).
build () {
  local status=0
  "$ALR" -n build -- "-XCBOR_DET_OPT=$2" "-XCBOR_DET_CHECKS=$3" \
    > "$out/build-$1.txt" 2>&1 || status=$?
  if [ "$status" -ne 0 ]; then
    echo "decoder-tests: the build of the $1 cell failed, exit $status (its output is in tests/$out/build-$1.txt)"
    build_failure_lines "$out/build-$1.txt"
    exit 1
  fi
}
build plain O2 lang
build contracts O0 contracts
plain=bin/O2-lang/test_main
contracts=bin/O0-contracts/test_main
stamp "runners built"

echo "== vectors, plain cell"
"$plain"
echo "== vectors and operation counts, contracts cell"
"$contracts"
stamp "vectors"

# The head table, in the corpus's row format (the bytes, item_end at 0,
# whole), from the reference's own functions; then classified by the cost
# model like a corpus. Both cells run before the stage's result is known.
echo "== verdict, the head table"
"$PYTHON" -B -I - reference "$out/head-table.tsv" <<'PY'
import sys
sys.tracebacklimit = 0
sys.excepthook = lambda t, v, b: sys.stderr.write("python: " + t.__name__ + "\n")
sys.path.insert(0, sys.argv[1])
import ref_cbor_det as ref
count = 0
with open(sys.argv[2], "w", encoding="ascii", newline="\n") as out:
    for data in ref.head_cases():
        out.write(f"{data.hex()}\t{ref.item_end(data, 0, 16)}"
                  f"\t{int(ref.whole(data))}\n")
        count += 1
print(f"head table: {count} rows")
PY
py reference/cost_model.py classify \
  --in "$out/head-table.tsv" --out "$out/classified-head-table.tsv" \
  --limit "$limit"
head_table_failed=0
for cell in plain contracts; do
  if [ "$cell" = plain ]; then runner=$plain; else runner=$contracts; fi
  echo "$cell cell:"
  status=0
  "$runner" verdict "$out/classified-head-table.tsv" "$HEAD_TABLE_ROWS" \
    | tee "$out/head-table-$cell.txt" || status=$?
  if [ "$status" -ne 0 ]; then
    echo "decoder-tests: FAILED: the head table in the $cell cell (exit $status)"
    head_table_failed=1
  elif ! grep -qF "$HEAD_TABLE_COUNTS" "$out/head-table-$cell.txt"; then
    echo "decoder-tests: FAILED: the head table in the $cell cell did not compare the known counts ($HEAD_TABLE_COUNTS)"
    head_table_failed=1
  fi
done
if [ "$head_table_failed" -ne 0 ]; then
  exit 1
fi
stamp "verdict, head table"

for seed in $seeds; do
  echo "== verdict, corpus seed $seed"
  py reference/ref_cbor_det.py corpus --seed "$seed" \
    --out "$out/corpus-$seed.tsv"
  py reference/cost_model.py classify \
    --in "$out/corpus-$seed.tsv" --out "$out/classified-$seed.tsv" \
    --limit "$limit"
  rows=$(reference_rows "$seed")
  echo "plain cell:"
  "$plain" verdict "$out/classified-$seed.tsv" $rows
  echo "contracts cell:"
  "$contracts" verdict "$out/classified-$seed.tsv" $rows
  stamp "verdict, seed $seed"
done

echo "== verdict, every input of up to 3 bytes"
py reference/exhaustive.py --out "$out/exhaustive.bin"
for runner in "$plain" "$contracts"; do
  "$runner" verdict-exhaustive "$out/exhaustive.bin" | tee "$out/exhaustive.txt"
  if ! grep -qF "$EXHAUSTIVE_COUNTS" "$out/exhaustive.txt"; then
    echo "decoder-tests: FAILED: the exhaustive run did not compare the known counts ($EXHAUSTIVE_COUNTS)"
    exit 1
  fi
done
stamp "verdict, exhaustive"

echo "== status, the oracle's corpus (seed 1)"
py reference/ref_status.py corpus --seed 1 \
  --out "$out/status-corpus-1.tsv"
"$plain" status "$out/status-corpus-1.tsv" "$ORACLE_ROWS_SEED_1"
stamp "status, oracle corpus"

for seed in $seeds; do
  echo "== status, the reference's corpus seed $seed"
  py reference/ref_status.py classify \
    --in "$out/corpus-$seed.tsv" --out "$out/status-reference-$seed.tsv"
  "$plain" status "$out/status-reference-$seed.tsv" $(reference_rows "$seed")
done
stamp "status, reference corpora"

echo "== status, boundary inputs"
if [ -n "${CBOR_DET_NO_HUGE:-}" ]; then
  py reference/boundary.py --out "$out/boundary.txt" --no-huge
  boundary_rows=$BOUNDARY_ROWS_NO_HUGE
else
  py reference/boundary.py --out "$out/boundary.txt"
  boundary_rows=$BOUNDARY_ROWS
fi
py reference/ref_status.py classify \
  --in "$out/boundary.txt" --out "$out/status-boundary.tsv"
"$plain" status "$out/status-boundary.tsv" "$boundary_rows"
stamp "status, boundary"

echo "decoder-tests: passed"
