#!/usr/bin/env bash
# Every local check of the crate in one run, for Windows x86_64 under Git
# Bash, with Alire 2.1.1 on the PATH (GNAT 16.1.0, gprbuild 26.0.1 and
# GNATprove 16.1.0 come from the crate's own manifests) and, for the
# differential test, the test runner's self-test and the decoder tests,
# Python 3.10 or later. It runs on any platform, but it exists so that
# the Windows results are gathered the same way each time.
#
# Run it from a copy of the crate, so that nothing in the working tree is
# disturbed:
#
#   bash scripts/windows-check.sh
#
# Steps, in order, each with its full output in tests/obj/windows/:
#   environment   uname, git, bash, perl, python and alr versions, and
#                 git config core.symlinks; and, in the summary too, the
#                 finds on the PATH, find --version, and whether this copy
#                 is a git work tree (none is needed; the gates run in find
#                 mode; if Windows' own find comes first and no POSIX find
#                 follows, run with PATH=/usr/bin:$PATH)
#   gates         the self-tests of the source and leakage gates and the
#                 version gate's test (scripts/test-version.sh), then the
#                 three gates (find mode)
#   prove         scripts/test-prove.sh (the proof driver's own test),
#                 then scripts/prove.sh --jobs 2: cold, per unit and per
#                 subprogram, steps only; no --memlimit, which makes the
#                 provers fail at once on Windows; no wall-clock guard,
#                 because none has been measured
#   matrix        scripts/test-matrix.sh, then scripts/matrix.sh
#   differential  scripts/differential.sh (seed 1), only if Python 3.10
#                 or later is found; otherwise INCOMPLETE
#   test-runner   scripts/test-runner.sh: the test runner's own failure
#                 modes (a missing file reported without its path; no
#                 pass when nothing was compared); Python 3.10 or later,
#                 as the differential
#   decoder-tests scripts/decoder-tests.sh: the decoder against the two
#                 references (Python 3.10 or later, as the differential)
#   decoder-measure  scripts/decoder-measure.sh: throughput and stack of
#                 the decoder, as information (no pass or fail of its own
#                 beyond running)
#
# Nothing the caller supplies (an argument, a step name, ALR, PYTHON) is
# printed back: a message says what kind of thing was wrong.
#
# Every selected step runs even if an earlier one fails. At the end it
# prints the step names in order, one line per step with its exit status
# (or INCOMPLETE, or NOT SELECTED), the steps not selected, and then the
# result, the first of these that applies:
#   1  FAILED        a step failed (or the script could not set up)
#   2  INCOMPLETE    nothing failed, but a selected step could not run (a
#                    tool it needs, such as alr or Python 3.10 or later,
#                    is missing)
#   3  PARTIAL       every selected step ran and passed, but not every
#                    step was selected (--only or --skip)
#   0  PASSED        every step was selected, ran and passed
#   4  usage error   an unknown option or step name, an empty list, or
#                    --only with --skip; nothing is run
# Only 0 is a pass. Send back that summary and the directory
# tests/obj/windows. scripts/test-windows-check.sh tests these exit
# statuses with stand-ins.
#
# Usage: scripts/windows-check.sh [--only LIST | --skip LIST]
#   --only LIST   run only the steps named in LIST (STEP[,STEP...])
#   --skip LIST   run every step except those named in LIST
#                 Either may be given more than once; the lists add up.
#                 The step names are: environment sources-self-test
#                 leakage-self-test test-version sources leakage version
#                 test-prove prove test-matrix matrix differential
#                 test-runner decoder-tests decoder-measure.
#   ALR, PYTHON   the alr and python to use (default alr, and the first of
#                 python3 and python that is 3.10 or later); a PYTHON
#                 that is set is the only one tried

set -u

# Every step, in the order run.
all_steps="environment sources-self-test leakage-self-test test-version \
sources leakage version test-prove prove test-matrix matrix differential \
test-runner decoder-tests decoder-measure"

usage () {
  echo "Usage: scripts/windows-check.sh [--only LIST | --skip LIST]"
  echo "  LIST is STEP[,STEP...]; --only runs only those steps, --skip all"
  echo "  but those. Steps:" $all_steps
}

usage_error () {
  echo "windows-check: $1" >&2
  usage >&2
  exit 4
}

# The step selection is read and checked before anything runs (with
# globbing off, so that a name is never matched against files).
set -f
only=
skip=
while [ $# -gt 0 ]; do
  case "$1" in
    --only|--skip)
      [ $# -ge 2 ] || usage_error "--only or --skip needs a list of steps"
      list=$2
      option=$1
      shift 2
      ;;
    --only=*|--skip=*)
      list=${1#*=}
      option=${1%%=*}
      shift
      ;;
    -h|--help)
      usage
      exit 0
      ;;
    *)
      usage_error "an unknown argument"
      ;;
  esac
  case ",$list," in
    *,,*) usage_error "$option: an empty step name in the list" ;;
  esac
  case "$list" in
    *[[:space:]]*) usage_error "$option: a space in the list" ;;
  esac
  names=$(printf '%s' "$list" | tr ',' ' ')
  for n in $names; do
    case " $all_steps " in
      *" $n "*) ;;
      *) usage_error "$option: an unknown step name (the names are listed below)" ;;
    esac
  done
  if [ "$option" = --only ]; then
    only="$only $names"
  else
    skip="$skip $names"
  fi
done
if [ -n "$only" ] && [ -n "$skip" ]; then
  usage_error "--only and --skip cannot be combined"
fi
set +f

# selected NAME: whether the step NAME is to run.
selected () {
  if [ -n "$only" ]; then
    case " $only " in *" $1 "*) return 0 ;; esac
    return 1
  fi
  case " $skip " in *" $1 "*) return 1 ;; esac
  return 0
}

cd "$(dirname "$0")" || exit 1
cd .. || exit 1
out=tests/obj/windows
mkdir -p "$out" || exit 1
ALR=${ALR:-alr}
export ALR
summary="$out/summary.txt"
: > "$summary"

failed=0
incomplete=0
partial=0
unselected=

# not_selected NAME: record that the step NAME was not selected.
not_selected () {
  echo "$1: NOT SELECTED (not run)" | tee -a "$summary"
  unselected="$unselected $1"
  partial=1
}

# step NAME NEEDS CMD...: run CMD unless a tool it needs is missing, in
# which case the step is INCOMPLETE. NEEDS is a space-separated list of
# the words perl and alr (not of paths): alr means the executable named by
# ALR, checked as one quoted name, so a path with spaces in it is found.
have () {
  case "$1" in
    perl) command -v perl > /dev/null 2>&1 ;;
    alr) command -v "$ALR" > /dev/null 2>&1 ;;
    *) return 1 ;;
  esac
}

step () {
  local name=$1 needs=$2 status t
  shift 2
  if ! selected "$name"; then
    not_selected "$name"
    return 0
  fi
  echo "== $name"
  for t in $needs; do
    if ! have "$t"; then
      if [ "$t" = alr ]; then
        echo "$name: INCOMPLETE (not run: alr (ALR) not found)" | tee -a "$summary"
      else
        echo "$name: INCOMPLETE (not run: $t not found)" | tee -a "$summary"
      fi
      incomplete=1
      return 0
    fi
  done
  "$@" > "$out/$name.txt" 2>&1
  status=$?
  tail -n 3 "$out/$name.txt"
  echo "$name: exit $status" | tee -a "$summary"
  if [ "$status" -ne 0 ]; then
    failed=1
  fi
}

environment () {
  echo "uname -s: $(uname -s)"
  echo "uname -m: $(uname -m)"
  git --version
  bash --version | head -n 1
  perl -v | sed -n 2p
  if [ -n "${PYTHON:-}" ]; then
    echo "python: $("$PYTHON" --version 2>&1)"
  else
    echo "python: not found"
  fi
  if ! command -v "$ALR" > /dev/null 2>&1; then
    echo "alr: not found (ALR)"
  elif ! "$ALR" --version 2> /dev/null; then
    echo "alr: could not start (ALR)"
  fi
  echo "core.symlinks: $(git config core.symlinks)"
  return 0
}

# Python 3.10 or later: PYTHON if it is set (and then only it), else the
# first of python3 and python that qualifies; none means the differential,
# test-runner and decoder-tests steps are INCOMPLETE.
python_ok () {
  "$1" -c 'import sys; sys.exit(0 if sys.version_info >= (3, 10) else 1)' \
    > /dev/null 2>&1
}
if [ -n "${PYTHON:-}" ]; then
  if ! python_ok "$PYTHON"; then
    echo "python: PYTHON is not Python 3.10 or later"
    PYTHON=
  fi
else
  for p in python3 python; do
    if python_ok "$p"; then
      PYTHON=$p
      break
    fi
  done
fi
export PYTHON

echo "steps:" $all_steps | tee -a "$summary"
step environment "" environment

# What the summary must show so that a PATH or copy problem is visible:
# the finds on the PATH in order (the gates use the first that behaves as
# a POSIX find; Windows' own find is a text search), the first line of
# find --version, and whether this copy is a git work tree (it need not
# be: the gates run in find mode, which leaves .git out). A find is shown
# by its kind, never by its directory, which could name a user or a
# private place.
find_kind () {
  case "$1" in
    /usr/bin/find|/bin/find)
      echo "usr/bin (Git Bash, MSYS or the system's own POSIX find)" ;;
    */[Ww][Ii][Nn][Dd][Oo][Ww][Ss]/[Ss][Yy][Ss][Tt][Ee][Mm]32/[Ff][Ii][Nn][Dd]*)
      echo "Windows System32 (a text search, not a POSIX find)" ;;
    *) echo "other" ;;
  esac
}
{
  n=0
  while IFS= read -r f; do
    n=$((n + 1))
    [ "$n" -le 3 ] || break
    echo "find #$n on PATH: $(find_kind "$f")"
  done < <(type -a -p find 2> /dev/null)
  if [ "$n" -eq 0 ]; then
    echo "find #1 on PATH: none"
  fi
  case "$(find --version 2>&1 | head -n 1)" in
    "find (GNU findutils)"*)
      echo "find --version: $(find --version 2>&1 | head -n 1)" ;;
    *) echo "find --version: not GNU findutils" ;;
  esac
  if [ -e .git ]; then
    echo "git work tree: yes (a .git exists in this copy; none is needed)"
  else
    echo "git work tree: no"
  fi
} | tee -a "$summary"
step sources-self-test "perl" bash scripts/check-sources.sh --self-test
step leakage-self-test "perl" bash scripts/check-leakage.sh --self-test
step test-version "" bash scripts/test-version.sh
step sources "perl" bash scripts/check-sources.sh
step leakage "perl" bash scripts/check-leakage.sh
step version "" bash scripts/check-version.sh
step test-prove "perl" bash scripts/test-prove.sh
step prove "perl alr" bash scripts/prove.sh --jobs 2
step test-matrix "" bash scripts/test-matrix.sh
step matrix "alr" bash scripts/matrix.sh
if ! selected differential; then
  not_selected differential
elif [ -n "${PYTHON:-}" ]; then
  step differential "alr" bash scripts/differential.sh
else
  echo "differential: INCOMPLETE (not run: no Python 3.10 or later found)" \
    | tee -a "$summary"
  incomplete=1
fi
if ! selected test-runner; then
  not_selected test-runner
elif [ -n "${PYTHON:-}" ]; then
  step test-runner "alr" bash scripts/test-runner.sh
else
  echo "test-runner: INCOMPLETE (not run: no Python 3.10 or later found)" \
    | tee -a "$summary"
  incomplete=1
fi
if ! selected decoder-tests; then
  not_selected decoder-tests
elif [ -n "${PYTHON:-}" ]; then
  step decoder-tests "alr" bash scripts/decoder-tests.sh
else
  echo "decoder-tests: INCOMPLETE (not run: no Python 3.10 or later found)" \
    | tee -a "$summary"
  incomplete=1
fi
step decoder-measure "alr" bash scripts/decoder-measure.sh
echo "not selected:${unselected:- none}" | tee -a "$summary" > /dev/null

echo
echo "== summary (also in $summary)"
cat "$summary"
if [ "$failed" -ne 0 ]; then
  echo "windows-check: FAILED"
  exit 1
elif [ "$incomplete" -ne 0 ]; then
  echo "windows-check: INCOMPLETE (a step could not run; this is not a pass)"
  exit 2
elif [ "$partial" -ne 0 ]; then
  echo "windows-check: PARTIAL (the selected steps passed, but not every" \
    "step was selected; this is not a pass)"
  exit 3
fi
echo "windows-check: PASSED"
