#!/usr/bin/env bash
# The value relation's tests: the ghost relation Same (the value an
# accepted item denotes, Cbor_Det.Proof.Model) against the denotation
# oracle in tests/reference (ref_denotation.py), written without access
# to this crate's code.
#
# Steps, each of which must pass:
#   1. the oracle is the recorded one (its SHA-256 below), and its own
#      self-test and exhaustive check pass;
#   2. the oracle writes its two pair files (tests/obj/model, ignored by
#      git): the main file (22 000 pairs of accepted inputs, from its
#      seeded corpus) and the small file (every ordered pair of the 1 086
#      accepted inputs of up to 2 bytes); each must be the recorded one
#      (its SHA-256 below), so a pair file that changed in any way fails
#      before anything is compared;
#   3. the test runner is built with the library's contracts at -O2
#      (language checks and -gnata: the ghost code and every contract
#      run); at -O0 the same run takes about fifteen times as long;
#   4. SAME: for every pair of each file, the runner checks that both
#      inputs are accepted whole, that Same agrees with the oracle's label
#      (S: the same value, D: different values), also with the second
#      input rebased, and runs the uniqueness lemmas on the rebased pair
#      (Lemma_CU_Whole and Lemma_Same_Of_Bytes_Whole on an S pair,
#      Lemma_Same_Iff_Bytes_Whole on a D pair), so that their contracts
#      execute. The line of counts it prints must be the pinned one below:
#      every row compared and agreeing, none malformed, no failure. A
#      file with no pair, or another number of pairs, fails.
#
# Usage: scripts/model-tests.sh
#   ALR, PYTHON   the alr and python3 to use

set -euo pipefail

# The oracle as kept here (tests/reference/README.md), and the pair files
# it writes.
DENOTATION_SHA256=9067be6cf0bfc67b126942409b184609dcfb7f03ccc3aaa1825026dd61f9d4ff
PAIRS_SHA256=c46e87b889e0e3805ce21ff1df118ed4b94be5543cdbd785432460450635fb43
SMALL_PAIRS_SHA256=bcc969eab765fec25ea35583a647207022cc9f87803b18a95c1c5f2cc982a2b6

# The counts each file must give: its pairs, and its S pairs.
PAIRS_ROWS=22000
PAIRS_S=4398
SMALL_ROWS=1179396
SMALL_S=1086
counts_line () {
  echo "same: rows $1, accepted $1, S $2, D $(($1 - $2)), agreeing $1, lemmas on S rows $2, malformed 0, failures 0"
}

ALR=${ALR:-alr}
PYTHON=${PYTHON:-python3}

# Settings are checked before anything runs. A tool that cannot start is
# reported by its role and exit status, never by what the shell said.
if ! command -v "$ALR" > /dev/null 2>&1; then
  echo "model-tests: alr (ALR) cannot be run"
  exit 2
fi
status=0
"$ALR" --version > /dev/null 2>&1 || status=$?
if [ "$status" -ne 0 ]; then
  echo "model-tests: could not start alr (ALR), exit $status"
  exit 2
fi
if ! command -v "$PYTHON" > /dev/null 2>&1; then
  echo "model-tests: the Python interpreter (PYTHON) cannot be run"
  exit 2
fi
status=0
"$PYTHON" -c 'import sys; sys.exit(0 if sys.version_info >= (3, 10) else 3)' \
  > /dev/null 2>&1 || status=$?
if [ "$status" -eq 3 ]; then
  echo "model-tests: the Python interpreter (PYTHON) is not Python 3.10 or later"
  exit 2
elif [ "$status" -ne 0 ]; then
  echo "model-tests: could not start the Python interpreter (PYTHON), exit $status"
  exit 2
fi

cd "$(dirname "$0")"
cd ..
cd tests

# Python, printing nothing of an exception but its type: no traceback
# (its file names are absolute paths) and no message.
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

# sha256 WHAT FILE EXPECTED: FILE is the recorded one, or the run fails.
sha256 () {
  "$PYTHON" -B -I - "$1" "$2" "$3" <<'PY'
import hashlib, sys
sys.tracebacklimit = 0
sys.excepthook = lambda t, v, b: sys.stderr.write("python: " + t.__name__ + "\n")
what, path, expected = sys.argv[1:]
with open(path, "rb") as f:
    actual = hashlib.sha256(f.read()).hexdigest()
if actual != expected:
    sys.exit("model-tests: " + what + " is not the recorded one")
print(what + ": sha256 " + actual)
PY
}

start=$SECONDS
stamp () {
  echo "-- $1 ($((SECONDS - start)) s so far)"
}

sha256 "the oracle (reference/ref_denotation.py)" \
  reference/ref_denotation.py "$DENOTATION_SHA256"
py reference/ref_denotation.py selftest
py reference/ref_denotation.py check
stamp "oracle checked"

out=obj/model
mkdir -p "$out"
rm -f "$out/pairs.txt" "$out/pairs.txt.small"
py reference/ref_denotation.py pairs "$out/pairs.txt"
sha256 "the main pair file" "$out/pairs.txt" "$PAIRS_SHA256"
sha256 "the small pair file" "$out/pairs.txt.small" "$SMALL_PAIRS_SHA256"
stamp "pair files written"

status=0
"$ALR" -n build -- -XCBOR_DET_OPT=O2 -XCBOR_DET_CHECKS=contracts \
  > "$out/build-contracts.txt" 2>&1 || status=$?
if [ "$status" -ne 0 ]; then
  echo "model-tests: the build with contracts failed, exit $status (its output is in tests/$out/build-contracts.txt)"
  exit 1
fi
runner=bin/O2-contracts/test_main
stamp "runner built"

# same NAME FILE ROWS S: one pair file, with its pinned counts.
same () {
  local status=0 want
  want=$(counts_line "$3" "$4")
  echo "== same, the $1 pair file"
  "$runner" same "$2" "$3" "$4" | tee "$out/same-$1.txt" || status=$?
  if [ "$status" -ne 0 ]; then
    echo "model-tests: FAILED: the $1 pair file (exit $status)"
    exit 1
  fi
  if ! grep -qF "$want" "$out/same-$1.txt"; then
    echo "model-tests: FAILED: the $1 pair file did not give the pinned counts ($want)"
    exit 1
  fi
  stamp "same, the $1 pair file"
}
same main "$out/pairs.txt" "$PAIRS_ROWS" "$PAIRS_S"
same small "$out/pairs.txt.small" "$SMALL_ROWS" "$SMALL_S"

echo "model-tests: passed"
