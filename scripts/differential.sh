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
#   4. the reference's head table is compared with the head helpers;
#   5. every input of 0 to 3 bytes is compared.
#
# Generated files go to tests/obj/differential (ignored by git), never
# into the repository.
#
# Usage: scripts/differential.sh
#   CBOR_DET_SEEDS        seeds of the corpus, space separated (default 1)
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
# escapes instead of non-ASCII characters: the same strings at run time,
# and the same output (see tests/reference/README.md).
REFERENCE_SHA256=287a37add851d40c2dd980f7ce17d6dadae7ba1d657927658816eaea9ba597fe

ALR=${ALR:-alr}
PYTHON=${PYTHON:-python3}
seeds=${CBOR_DET_SEEDS:-1}
limit=${CBOR_DET_COST_LIMIT:-200000000}

cd "$(dirname "$0")"
cd ..
cd tests

"$PYTHON" -B -I - reference/ref_cbor_det.py "$REFERENCE_SHA256" <<'PY'
import hashlib, sys
if sys.version_info < (3, 10):
    sys.exit("differential: Python 3.10 or later is needed")
path, expected = sys.argv[1], sys.argv[2]
with open(path, "rb") as f:
    actual = hashlib.sha256(f.read()).hexdigest()
if actual != expected:
    sys.exit("differential: the reference is not the recorded one")
print("reference: sha256 " + actual)
PY
"$PYTHON" -B -I reference/ref_cbor_det.py selftest

"$ALR" -n build -- -XCBOR_DET_OPT=O0 -XCBOR_DET_CHECKS=contracts
runner=bin/O0-contracts/test_main
out=obj/differential
mkdir -p "$out"

echo "== the classifier and the runner fail a row the cost model gets wrong"
"$PYTHON" -B -I reference/cost_model.py selftest
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

for seed in $seeds; do
  echo "== corpus, seed $seed"
  "$PYTHON" -B -I reference/ref_cbor_det.py corpus --seed "$seed" \
    --out "$out/corpus-$seed.tsv"
  "$PYTHON" -B -I reference/cost_model.py classify \
    --in "$out/corpus-$seed.tsv" --out "$out/classified-$seed.tsv" \
    --limit "$limit"
  "$runner" corpus "$out/classified-$seed.tsv" "$out/timings-$seed.txt"
  "$PYTHON" -B -I reference/cost_model.py validate \
    --timings "$out/timings-$seed.txt"
done

echo "== head table"
"$PYTHON" -B -I reference/ref_cbor_det.py heads --out "$out/heads.tsv"
"$runner" heads "$out/heads.tsv"

echo "== every input of up to 3 bytes"
"$PYTHON" -B -I reference/exhaustive.py --out "$out/exhaustive.bin"
"$runner" exhaustive "$out/exhaustive.bin"

echo "differential: passed"
