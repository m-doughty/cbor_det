#!/usr/bin/env bash
# The proof of the crate, per unit and per subprogram, from cold.
#
# For every unit in src/ (spec and body together), then for every
# subprogram declared at the top level of every spec, one gnatprove
# command, each from cold: every proof session of the crate (the
# directories obj/*/gnatprove and lib/*/gnatprove) is deleted before it.
# The provers' limits are those of cbor_det.gpr: steps only (--steps), no
# time limit (--timeout=0), three provers, every check an error. The
# number of parallel proof jobs is explicit (--jobs, default 2).
#
# For each command it prints the checks proved, the checks not proved and
# the largest number of steps any check took (from --report=statistics).
# It fails if any check is not proved; if gnatprove fails or is killed by
# a signal; if the command wrote no summary (gnatprove.out), or one
# without a well-formed Total line; if the summary does not show the unit
# (all of its subprograms) or the subprogram as analysed; if the number
# of checks the summary counts is not the number the output reports
# proved or not proved (so a command that proved nothing while there was
# something to prove fails); or if the summary shows a justified check or
# a pragma Assume. GNATprove's exit status and its "Success" line are not
# taken as evidence on their own. scripts/test-prove.sh shows each of
# these failures failing the run.
#
# Wall-clock guard. --guard SECONDS stops a command that runs longer and
# reports "GUARD TRIPPED": an error to rerun, never a failed proof (exit
# status 2, not 1). Its value is a safeguard, not a result, and is not
# known yet: it is to be set from measurements on the CI runners, after
# their first runs. Until then it is UNMEASURED and the default is no
# guard (0); a local run may pass one, as a local safeguard only.
#
# Usage: scripts/prove.sh [--jobs N] [--guard SECONDS] [--units-only]
#   ALR   the alr to use (default alr)
# Exit status: 0 all proved; 1 a check not proved or a proof run failed;
# 2 a guard tripped, or the script could not run.

set -euo pipefail

ALR=${ALR:-alr}
jobs=2
guard=0
units_only=no
while [ "$#" -gt 0 ]; do
  case "$1" in
    --jobs) jobs=$2; shift 2 ;;
    --guard) guard=$2; shift 2 ;;
    --units-only) units_only=yes; shift ;;
    *) echo "usage: scripts/prove.sh [--jobs N] [--guard SECONDS] [--units-only]"; exit 2 ;;
  esac
done
case "$jobs" in ''|*[!0-9]*|0) echo "prove: --jobs must be a positive number"; exit 2 ;; esac
case "$guard" in ''|*[!0-9]*) echo "prove: --guard must be a number of seconds"; exit 2 ;; esac

cd "$(dirname "$0")"
cd ..
crate=$(pwd -P)
logs="$crate/tests/obj/prove"
mkdir -p "$logs"
cd tests
"$ALR" -n build > "$logs/build.txt" 2>&1 \
  || { echo "prove: the tests crate does not build (see tests/obj/prove/build.txt)"; exit 2; }

if [ "$guard" -eq 0 ]; then
  echo "guard: UNMEASURED (none)"
else
  echo "guard: $guard s per command (a safeguard; a trip is an error to rerun)"
fi
echo "jobs: $jobs"

failed=0
tripped=0

# run NAME ARGS...: one cold gnatprove command; its output in
# tests/obj/prove/NAME.txt.
run () {
  local name=$1 kind=$2 target=$3 out status steps proved unproved summary
  local verdict total
  shift 3
  out="$logs/$name.txt"
  for d in "$crate"/obj/*/gnatprove "$crate"/lib/*/gnatprove; do
    if [ -d "$d" ]; then rm -rf "$d"; fi
  done
  status=0
  # The command in its own process group; a guard kills the whole group.
  # A command killed by a signal is reported as such, never as its exit
  # status (which would be 0).
  perl -e '
    my ($guard, @cmd) = @ARGV;
    my $pid = fork;
    die "fork\n" unless defined $pid;
    if ($pid == 0) { setpgrp(0, 0); exec @cmd; exit 127; }
    my $timed_out = 0;
    local $SIG{ALRM} = sub { $timed_out = 1; kill "KILL", -$pid; };
    alarm $guard if $guard > 0;
    waitpid $pid, 0;
    my $st = $?;
    alarm 0;
    exit 124 if $timed_out;
    if ($st & 127) {
      print STDERR "prove.sh: the command was killed by signal ", $st & 127, "\n";
      exit 1;
    }
    exit($st >> 8);
  ' "$guard" "$ALR" -n exec -- gnatprove -P "$crate/cbor_det.gpr" \
      -j"$jobs" --report=statistics "$@" > "$out" 2>&1 || status=$?
  if [ "$status" -eq 124 ]; then
    echo "$name: GUARD TRIPPED after $guard s (an error to rerun, not a proof result)"
    tripped=1
    return 0
  fi
  steps=$(perl -ne '$m = $1 if /and (\d+) steps?\)/ && $1 > ($m // 0); END { print $m // 0 }' "$out")
  proved=$(grep -c '^ *info: .* proved' "$out" || true)
  unproved=$(grep -cE '^ *(medium|high|low): ' "$out" || true)
  echo "$name: proved $proved, not proved $unproved, max steps $steps, exit $status"
  if [ "$status" -ne 0 ] || [ "$unproved" -ne 0 ]; then
    failed=1
  fi
  if grep -q '^prove.sh: the command was killed by signal' "$out"; then
    echo "$name: the command was killed by a signal"
    failed=1
  fi
  # The summary must exist, have a well-formed Total line, show the unit
  # or subprogram as analysed, and count exactly the checks the output
  # reports, proved or not.
  summary=$(ls "$crate"/obj/*/gnatprove/gnatprove.out 2> /dev/null | head -n 1 || true)
  if [ -z "$summary" ]; then
    echo "$name: no summary (gnatprove.out) was written"
    failed=1
    return 0
  fi
  verdict=$(KIND=$kind TARGET=$target perl -ne '
      BEGIN { $total = ""; $analysed = 0; $assume = 0; $just = ""; $unpr = "" }
      if (/^Total\s/ && $total eq "") {
        chomp;
        my @f = split /\s{2,}/;
        s/^\s+|\s+$//g for @f;
        if (@f == 6 && $f[1] =~ /^(\d+|\.)$/ && $f[2] =~ /^(\.|\d+ \(.*\))$/
            && $f[3] =~ /^(\.|\d+ \(.*\))$/ && $f[4] =~ /^(\d+|\.)$/
            && $f[5] =~ /^(\d+|\.)$/) {
          ($total, $just, $unpr) = ($f[1], $f[4], $f[5]);
        } else { $total = "bad" }
      }
      $assume = 1 if /and (\d+) pragma Assume statements/ && $1 > 0;
      if ($ENV{KIND} eq "unit") {
        $analysed = 1 if /^in unit \Q$ENV{TARGET}\E, (\d+) subprograms and packages out of (\d+) analyzed/
                         && $1 == $2 && $2 >= 1;
      } else {
        $analysed = 1 if / at \Q$ENV{TARGET}\E flow analyzed/;
      }
      END {
        if ($total eq "" || $total eq "bad") { print "malformed"; exit }
        my @v;
        push @v, "notanalysed" unless $analysed;
        push @v, "justified" if $just ne ".";
        push @v, "unproved" if $unpr ne ".";
        push @v, "assume" if $assume;
        push @v, "total=" . ($total eq "." ? 0 : $total);
        print join " ", @v;
      }' "$summary")
  case "$verdict" in
    malformed)
      echo "$name: malformed summary (no well-formed Total line)"
      failed=1
      return 0 ;;
  esac
  total=${verdict##*total=}
  case "$verdict" in
    *notanalysed*)
      echo "$name: the unit or subprogram was not analysed"
      failed=1 ;;
  esac
  case "$verdict" in
    *unproved*)
      echo "$name: the summary shows unproved checks"
      failed=1 ;;
  esac
  case "$verdict" in
    *justified*|*assume*)
      echo "$name: a justified check or a pragma Assume in the summary"
      failed=1 ;;
  esac
  if [ "$((proved + unproved))" -ne "$total" ]; then
    echo "$name: the summary counts $total checks but $proved were proved and $unproved not proved"
    failed=1
  fi
}

specs=$(cd "$crate/src" && ls *.ads)
for spec in $specs; do
  unit=${spec%.ads}
  files=("$spec")
  if [ -f "$crate/src/$unit.adb" ]; then files+=("$unit.adb"); fi
  run "unit-$unit" unit "$unit" -u "${files[@]}"
done

if [ "$units_only" = no ]; then
  for spec in $specs; do
    unit=${spec%.ads}
    # The first declaration line of each subprogram declared at the top
    # level (three spaces in), as --limit-subp needs.
    while read -r line name; do
      run "subp-$unit-$name" subp "$spec:$line" --limit-subp="$spec:$line"
    done < <(grep -n -E '^   (procedure|function) [A-Za-z_0-9]+' "$crate/src/$spec" \
             | sed -E 's/^([0-9]+):   (procedure|function) ([A-Za-z_0-9]+).*/\1 \3/' \
             | awk '!seen[$2]++')
  done
fi

if [ "$tripped" -ne 0 ]; then
  echo "prove: a guard tripped: rerun; this is not a proof result"
  exit 2
fi
if [ "$failed" -ne 0 ]; then
  echo "prove: FAILED"
  exit 1
fi
echo "prove: all checks proved"
