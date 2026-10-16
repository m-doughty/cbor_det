#!/usr/bin/env bash
# Exercise scripts/windows-check.sh with stand-ins for every check it runs
# (the gates, the proof, the matrix, the differential, the test runner's
# self-test, the decoder's tests and measurements), alr and Python,
# so that its exit status is seen to follow its results: 0 only when every
# step was selected, ran and passed; 1 when any step failed (every
# selected step still runs and the summary is printed); 2 when nothing
# failed but a selected step could not run (alr missing, or Python 3.10
# or later for the differential, the test runner's self-test and the
# decoder tests), each reported as INCOMPLETE; 3 (PARTIAL) when every
# selected step passed but --only or --skip left a step out, each reported
# as NOT SELECTED and not run; 4 for an unknown option or step name, an
# empty list, or --only with --skip, with nothing run.
# Runs under /bin/bash by default (Bash 3.2 on macOS).
#
# Usage: scripts/test-windows-check.sh
#        TEST_BASH=/path/to/bash scripts/test-windows-check.sh

set -euo pipefail
cd "$(dirname "$0")"
cd ..
TEST_BASH=${TEST_BASH:-/bin/bash}

tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT
mkdir -p "$tmp/crate/scripts" "$tmp/crate/tests" "$tmp/bin"
cp scripts/windows-check.sh "$tmp/crate/scripts/"
for s in check-sources check-leakage check-version test-version test-prove \
         prove test-matrix matrix differential test-runner decoder-tests \
         decoder-measure; do
  printf '#!/usr/bin/env bash\necho "stand-in %s $*"\ncase " ${MOCK_FAIL:-} " in *" %s "*) exit 1 ;; esac\nexit 0\n' \
    "$s" "$s" > "$tmp/crate/scripts/$s.sh"
done
printf '#!/usr/bin/env bash\necho "alr 2.1.1"\n' > "$tmp/bin/alr"
printf '#!/usr/bin/env bash\nif [ "$1" = --version ]; then echo "Python 3.12.0"; exit 0; fi\nexit 0\n' \
  > "$tmp/bin/python-good"
printf '#!/usr/bin/env bash\nif [ "$1" = --version ]; then echo "Python 3.9.0"; exit 0; fi\nexit 1\n' \
  > "$tmp/bin/python-old"
chmod +x "$tmp/bin/"*
mkdir -p "$tmp/dir with spaces"
cp "$tmp/bin/alr" "$tmp/dir with spaces/alr tool"

pass=0
fail=0
# check NAME EXPECTED_STATUS EXPECTED_TEXT [--absent TEXT] [ENV...]
#       [-- ARGUMENTS...]
# Runs windows-check.sh with the ENV settings and ARGUMENTS; passes if it
# exits EXPECTED_STATUS, prints EXPECTED_TEXT and does not print TEXT.
check () {
  local name=$1 want=$2 text=$3 absent= status=0 ok=1
  local env_args=()
  shift 3
  if [ "${1:-}" = --absent ]; then
    absent=$2
    shift 2
  fi
  # ENV settings up to "--"; what follows it is the arguments.
  while [ $# -gt 0 ] && [ "$1" != -- ]; do
    env_args+=("$1")
    shift
  done
  if [ $# -gt 0 ]; then
    shift
  fi
  (cd "$tmp/crate" && env ALR="$tmp/bin/alr" PYTHON="$tmp/bin/python-good" \
     MOCK_FAIL= ${env_args[@]+"${env_args[@]}"} \
     "$TEST_BASH" scripts/windows-check.sh "$@") \
    > "$tmp/$name.out" 2>&1 || status=$?
  [ "$status" -eq "$want" ] || ok=0
  grep -qF -- "$text" "$tmp/$name.out" || ok=0
  if [ -n "$absent" ] && grep -qF -- "$absent" "$tmp/$name.out"; then
    ok=0
  fi
  if [ "$ok" -eq 1 ]; then
    pass=$((pass + 1))
  else
    fail=$((fail + 1))
    echo "test-windows-check FAILED: $name (exit $status, expected $want and \"$text\"${absent:+, and not \"$absent\"}):"
    sed 's/^/    /' "$tmp/$name.out"
  fi
}

check all-pass 0 "windows-check: PASSED"
check one-fails 1 "matrix: exit 1" MOCK_FAIL="matrix"
check one-fails-summary 1 "windows-check: FAILED" MOCK_FAIL="matrix"
check later-steps-still-run 1 "differential: exit 0" MOCK_FAIL="check-sources"
check all-fail 1 "windows-check: FAILED" \
  MOCK_FAIL="check-sources check-leakage check-version test-version test-prove prove test-matrix matrix differential test-runner decoder-tests decoder-measure"
check no-python 2 "differential: INCOMPLETE" PYTHON="$tmp/bin/python-old"
check no-python-decoder 2 "decoder-tests: INCOMPLETE" PYTHON="$tmp/bin/python-old"
# The test runner's self-test needs Python too: without it, that step is
# INCOMPLETE and not run, alone or among the others.
check no-python-test-runner 2 "test-runner: INCOMPLETE" \
  --absent "stand-in test-runner" PYTHON="$tmp/bin/python-old" \
  -- --only test-runner
check no-python-test-runner-all 2 "test-runner: INCOMPLETE" \
  --absent "stand-in test-runner" PYTHON="$tmp/bin/python-old"
check decoder-tests-fail 1 "decoder-tests: exit 1" MOCK_FAIL="decoder-tests"
check decoder-measure-runs 0 "decoder-measure: exit 0"
check test-runner-fail 1 "test-runner: exit 1" MOCK_FAIL="test-runner"
check no-python-summary 2 "windows-check: INCOMPLETE" PYTHON="$tmp/bin/python-old"
check no-alr 2 "prove: INCOMPLETE" ALR="$tmp/bin/no-such-alr"
check failure-beats-incomplete 1 "windows-check: FAILED" \
  PYTHON="$tmp/bin/python-old" MOCK_FAIL="matrix"
# An alr whose path holds spaces is one executable, found and run.
check alr-path-with-spaces 0 "windows-check: PASSED" \
  ALR="$tmp/dir with spaces/alr tool"
check alr-path-with-spaces-runs 0 "prove: exit 0" \
  ALR="$tmp/dir with spaces/alr tool"
# The summary records which find comes first on the PATH, and whether the
# copy is a git work tree.
check summary-find 0 "find #1 on PATH:"
check summary-find-version 0 "find --version:"
check summary-no-git 0 "git work tree: no"
# Step selection. The summary names every step; a step left out by --only
# or --skip is reported NOT SELECTED and not run, and the result is
# PARTIAL (3), never PASSED; a failure or an INCOMPLETE step still wins.
every="environment,sources-self-test,leakage-self-test,test-version,sources,leakage,version,test-prove,prove,test-matrix,matrix,differential,test-runner,decoder-tests,decoder-measure"
check summary-step-names 0 "steps: environment sources-self-test leakage-self-test test-version sources leakage version test-prove prove test-matrix matrix differential test-runner decoder-tests decoder-measure"
check summary-none-unselected 0 "not selected: none"
check only-one-partial 3 "windows-check: PARTIAL" --absent "stand-in prove" \
  -- --only matrix
check only-one-runs 3 "stand-in matrix" -- --only matrix
check only-one-runs-status 3 "matrix: exit 0" -- --only matrix
check only-others-not-selected 3 "prove: NOT SELECTED (not run)" \
  -- --only matrix
check only-lists-unselected 3 "not selected: environment sources-self-test leakage-self-test test-version sources leakage version test-prove prove test-matrix differential test-runner decoder-tests decoder-measure" \
  -- --only matrix
check only-equals-form 3 "windows-check: PARTIAL" -- --only=matrix,prove
check only-repeated 3 "prove: exit 0" -- --only matrix --only prove
check only-every-step 0 "windows-check: PASSED" -- --only "$every"
check only-every-step-none-unselected 0 "not selected: none" \
  -- --only "$every"
check skip-failing-step 3 "windows-check: PARTIAL" --absent "stand-in matrix" \
  MOCK_FAIL="matrix" -- --skip matrix
check skip-reported 3 "matrix: NOT SELECTED (not run)" -- --skip matrix
check skip-differential-without-python 3 "differential: NOT SELECTED" \
  PYTHON="$tmp/bin/python-old" -- --skip differential,test-runner,decoder-tests
check skip-test-runner-without-python 3 "test-runner: NOT SELECTED" \
  PYTHON="$tmp/bin/python-old" -- --skip differential,test-runner,decoder-tests
check skip-environment 3 "environment: NOT SELECTED" \
  --absent "stand-in" -- --skip "$every"
check failure-beats-partial 1 "windows-check: FAILED" MOCK_FAIL="matrix" \
  -- --only matrix,prove
check failure-beats-partial-listed 1 "sources: NOT SELECTED" \
  MOCK_FAIL="matrix" -- --only matrix,prove
check incomplete-beats-partial 2 "windows-check: INCOMPLETE" \
  ALR="$tmp/bin/no-such-alr" -- --only prove
check incomplete-beats-partial-listed 2 "matrix: NOT SELECTED" \
  ALR="$tmp/bin/no-such-alr" -- --only prove
# A bad selection is a usage error (4), and nothing runs.
check unknown-only 4 "an unknown step name" --absent "== environment" \
  -- --only matrx
check unknown-skip 4 "an unknown step name" --absent "== environment" \
  -- --skip prove,proof
check unknown-option 4 "an unknown argument" --absent "== environment" \
  -- --all
check only-and-skip 4 "cannot be combined" --absent "== environment" \
  -- --only matrix --skip prove
check missing-list 4 "needs a list of steps" --absent "== environment" \
  -- --only
check empty-list 4 "an empty step name" --absent "== environment" \
  -- --only ""
check empty-name 4 "an empty step name" --absent "== environment" \
  -- --skip "matrix,,prove"
check space-in-list 4 "a space in" --absent "== environment" \
  -- --only "matrix prove"
check glob-name 4 "an unknown step name" --absent "== environment" -- --only "*"
# Nothing a caller supplies is printed back: canaries in a step name, an
# argument, ALR and PYTHON.
check canary-step 4 "an unknown step name" --absent "QQ-STEP-CANARY" \
  -- --only "/zz-dir/QQ-STEP-CANARY"
check canary-skip 4 "an unknown step name" --absent "QQ-STEP-CANARY" \
  -- --skip "matrix,/zz-dir/QQ-STEP-CANARY"
check canary-argument 4 "an unknown argument" --absent "QQ-ARG-CANARY" \
  -- "--QQ-ARG-CANARY"
check canary-empty-name 4 "an empty step name" --absent "QQ-LIST-CANARY" \
  -- --only "QQ-LIST-CANARY,,matrix"
check canary-alr 2 "INCOMPLETE" --absent "QQ-ALR-CANARY" \
  ALR="/zz-dir/QQ-ALR-CANARY/alr"
check canary-python 2 "INCOMPLETE" --absent "QQ-PY-CANARY" \
  PYTHON="/zz-dir/QQ-PY-CANARY/python3"
# The finds on the PATH are reported by kind and order, never by their
# directories: a find first on the PATH in a relative and in an absolute
# directory named after a canary.
mkdir -p "$tmp/crate/QQ-REL-FIND-CANARY" "$tmp/QQ-ABS-FIND-CANARY"
printf '#!/bin/sh\nexec "%s" "$@"\n' "$(command -v find)" \
  > "$tmp/crate/QQ-REL-FIND-CANARY/find"
cp "$tmp/crate/QQ-REL-FIND-CANARY/find" "$tmp/QQ-ABS-FIND-CANARY/find"
chmod +x "$tmp/crate/QQ-REL-FIND-CANARY/find" "$tmp/QQ-ABS-FIND-CANARY/find"
check canary-find-relative 0 "find #1 on PATH: other" \
  --absent "QQ-REL-FIND-CANARY" PATH="QQ-REL-FIND-CANARY:$PATH"
check canary-find-absolute 0 "find #1 on PATH: other" \
  --absent "QQ-ABS-FIND-CANARY" PATH="$tmp/QQ-ABS-FIND-CANARY:$PATH"
check help 0 "--only LIST" --absent "== environment" -- --help

mkdir -p "$tmp/crate/.git"
check summary-stray-git 0 "git work tree: yes"

echo "test-windows-check: $pass passed, $fail failed"
[ "$fail" -eq 0 ]
