#!/usr/bin/env bash
# Measurements of the decoder, as information, never a gate: no limit or
# ratio is set from them, here or in CI.
#
#   1. throughput: bytes per second of Check on a small message (a map of
#      6 pairs), a 1 MB byte string, a 16-deep nest and a map of 65 536
#      pairs: minimum, median and maximum of 11 samples;
#   2. stack: the bytes of stack Check used on a 16-deep nest, arrays of
#      65 536 and 1 000 000 members and a map of 65 536 pairs, by stack
#      painting (the overhead of the measurement is the "none" line): it
#      must not grow with width.
#
# Both in a production cell: -O3, run-time checks off, no contracts (so
# no ghost code). The figures depend on the machine and the platform.
#
# A failed build prints only the lines of its log that have a known form
# (see build_failure_lines below), at most 40, and keeps the whole log in
# tests/obj. The limit: a compiler message can quote a value the caller
# gave a project setting (an invalid CBOR_DET_LIBRARY_TYPE or LIBRARY_TYPE
# is printed back), so no private value belongs in one.
#
# Usage: scripts/decoder-measure.sh
#   ALR   the alr to use

set -euo pipefail
ALR=${ALR:-alr}
# Never print the value of ALR, nor what the shell says when it cannot
# start it: say what is wrong, and the exit status.
if ! command -v "$ALR" > /dev/null 2>&1; then
  echo "decoder-measure: alr (ALR) cannot be run"
  exit 2
fi
status=0
"$ALR" --version > /dev/null 2>&1 || status=$?
if [ "$status" -ne 0 ]; then
  echo "decoder-measure: could not start alr (ALR), exit $status"
  exit 2
fi
cd "$(dirname "$0")"
cd ..
cd tests

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

# The build's output is kept in obj/measure; on a failure only its lines of
# a known form are printed, without paths.
mkdir -p obj/measure
status=0
"$ALR" -n build -- -XCBOR_DET_OPT=O3 -XCBOR_DET_CHECKS=off \
  > obj/measure/build-production.txt 2>&1 || status=$?
if [ "$status" -ne 0 ]; then
  echo "decoder-measure: the build of the production cell failed, exit $status (its output is in tests/obj/measure/build-production.txt)"
  build_failure_lines obj/measure/build-production.txt
  exit 1
fi
bench=bin/O3-off/bench_main

echo "== throughput (production cell O3, checks off; information only)"
"$bench" throughput

echo "== stack (bytes Check used, by stack painting; information only)"
for w in none deep16 wide65536 wide1000000 widemap65536; do
  "$bench" stack "$w"
done
