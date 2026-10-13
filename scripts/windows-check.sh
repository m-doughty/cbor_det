#!/usr/bin/env bash
# Every local check of the crate in one run, for Windows x86_64 under Git
# Bash, with Alire 2.1.1 on the PATH (GNAT 16.1.0, gprbuild 26.0.1 and
# GNATprove 16.1.0 come from the crate's own manifests) and, for the
# differential test, Python 3.10 or later. It runs on any platform, but
# it exists so that the Windows results are gathered the same way each
# time.
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
#                 test-prove prove test-matrix matrix differential.
#   ALR, PYTHON   the alr and python to use (default alr, and the first of
#                 python3 and python that is 3.10 or later); a PYTHON
#                 that is set is the only one tried

set -u

# Every step, in the order run.
all_steps="environment sources-self-test leakage-self-test test-version \
sources leakage version test-prove prove test-matrix matrix differential"

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
      [ $# -ge 2 ] || usage_error "$1 needs a list of steps"
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
      usage_error "unknown argument: $1"
      ;;
  esac
  case ",$list," in
    *,,*) usage_error "$option: an empty step name in \"$list\"" ;;
  esac
  case "$list" in
    *[[:space:]]*) usage_error "$option: a space in \"$list\"" ;;
  esac
  names=$(printf '%s' "$list" | tr ',' ' ')
  for n in $names; do
    case " $all_steps " in
      *" $n "*) ;;
      *) usage_error "$option: unknown step: $n" ;;
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
        echo "$name: INCOMPLETE (not run: alr ($ALR) not found)" | tee -a "$summary"
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
  echo "python: ${PYTHON:-not found} $("${PYTHON:-false}" --version 2>&1)"
  "$ALR" --version
  echo "core.symlinks: $(git config core.symlinks)"
  return 0
}

# Python 3.10 or later: PYTHON if it is set (and then only it), else the
# first of python3 and python that qualifies; none means the differential
# is INCOMPLETE.
python_ok () {
  "$1" -c 'import sys; sys.exit(0 if sys.version_info >= (3, 10) else 1)' \
    > /dev/null 2>&1
}
if [ -n "${PYTHON:-}" ]; then
  if ! python_ok "$PYTHON"; then
    echo "python: $PYTHON is not Python 3.10 or later"
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
# be: the gates run in find mode, which leaves .git out). A path under the
# home directory is shown as ~.
home_tilde () {
  if [ -n "${HOME:-}" ]; then
    sed "s|$HOME|~|g"
  else
    cat
  fi
}
{
  first=$(type -a -p find 2> /dev/null | head -n 1 | home_tilde)
  echo "find first on PATH: ${first:-none}"
  type -a -p find 2> /dev/null | sed -n '2,3p' | home_tilde \
    | sed 's/^/find later on PATH: /'
  echo "find --version: $(find --version 2>&1 | head -n 1 | home_tilde)"
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
