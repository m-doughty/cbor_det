#!/usr/bin/env bash
# Adapted from the scripts of the blake2b crate; to be replaced by the shared gates when that repository exists.
# Builds and runs the test runner in every cell of the build matrix:
#
#   optimisation  -O0 / -O2 / -O3
#   checks        off  (-gnatp: the release setting)
#                 lang (every language check: overflow, range, index, ...)
#
# plus one cell with contracts enabled (-gnata), where every precondition,
# postcondition, loop invariant and assertion runs.
#
# Every cell must pass. A miscompilation at one optimisation level, or a
# gap between what the proof covers and what the checks enforce, shows up
# as a failing cell.
#
# A failed build prints only the lines of its log that have a known form
# (see build_failure_lines below), at most 40, and keeps the whole log in
# tests/obj. The limit: a compiler message can quote a value the caller
# gave a project setting (an invalid CBOR_DET_LIBRARY_TYPE or LIBRARY_TYPE
# is printed back), so no private value belongs in one.
#
# Usage: scripts/matrix.sh            (from anywhere in the crate)
#        ALR=/path/to/alr scripts/matrix.sh

set -euo pipefail

ALR=${ALR:-alr}
# Never print the value of ALR, nor what the shell says when it cannot
# start it: say what is wrong, and the exit status.
if ! command -v "$ALR" > /dev/null 2>&1; then
  echo "matrix: alr (ALR) cannot be run"
  exit 2
fi
status=0
"$ALR" --version > /dev/null 2>&1 || status=$?
if [ "$status" -ne 0 ]; then
  echo "matrix: could not start alr (ALR), exit $status"
  exit 2
fi
cd "$(dirname "$0")/../tests"

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

cells=(
  "O0 off" "O0 lang"
  "O2 off" "O2 lang"
  "O3 off" "O3 lang"
  "O0 contracts"
)

failed=()
for cell in "${cells[@]}"; do
  read -r opt checks <<< "$cell"
  echo "=================================================================="
  echo "cell: -$opt, checks=$checks"
  echo "=================================================================="
  # The build's output is kept in a file; on a failure only its lines
  # of a known form are printed, without paths (a tool that cannot start
  # is described by the shell with its path). A failed build stops the
  # run with its exit status.
  mkdir -p obj
  status=0
  "$ALR" -n build -- "-XCBOR_DET_OPT=$opt" "-XCBOR_DET_CHECKS=$checks" \
    > "obj/matrix-build-$opt-$checks.txt" 2>&1 || status=$?
  if [ "$status" -ne 0 ]; then
    echo "cell -$opt/$checks: the build failed, exit $status (its output is in tests/obj/matrix-build-$opt-$checks.txt)"
    build_failure_lines "obj/matrix-build-$opt-$checks.txt"
    exit "$status"
  fi

  if "./bin/$opt-$checks/test_main"; then
    echo "cell -$opt/$checks: PASS"
  else
    echo "cell -$opt/$checks: FAIL"
    failed+=("-$opt/$checks")
  fi
done

echo
if [ "${#failed[@]}" -eq 0 ]; then
  echo "matrix: all ${#cells[@]} cells passed"
else
  echo "matrix: FAILED cells: ${failed[*]}"
  exit 1
fi
