#!/usr/bin/env bash
# The proof of the crate, per unit and per subprogram, from cold.
#
# For every unit in src/ (spec and body together), then for every
# subprogram declared at the top level of every spec, and for every one
# declared at the top level of a body and not in its spec (at its first
# declaration), one gnatprove command, each from cold: every proof session of the crate (the
# directories obj/*/gnatprove and lib/*/gnatprove) is deleted before it.
# The provers' limits are those of cbor_det.gpr: steps only (--steps), no
# time limit (--timeout=0), three provers, every check an error. The
# number of parallel proof jobs is explicit (--jobs, default 2).
#
# For each command it prints the checks proved, the checks not proved and
# the largest number of steps any check took: the largest over every
# prover on every line of the output (--report=statistics lists each
# prover that worked on a check, the largest not necessarily last) and
# the summary's own "max steps used for successful proof".
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
# Shards. The commands are numbered 0 to T-1 in the order above (units,
# then the subprograms of the specs, then those declared only in a body;
# the files in C collation order, so the same on every platform), and
# --shard K/N (1 <= K <= N <= 999) runs those whose number leaves K-1
# when divided by N. Before any proof, a sharded run checks that the N
# shards of that rule, together, list every command exactly once, and
# that its own shard lists at least one; it prints "shard K/N: M of T
# commands", or fails (exit status 2) without proving anything. Each
# command is the same as in a run without --shard, and is judged the
# same way. A run, sharded or not, that started fewer or more commands
# than it listed fails ("prove: INTERNAL", exit status 2).
# --list prints the names of the commands, one per line, in that order
# (with --shard, those of the shard, after the same check), and runs
# nothing: no alr is needed.
#
# Usage: scripts/prove.sh [--jobs N] [--guard SECONDS] [--units-only]
#                         [--shard K/N] [--list]
#   ALR   the alr to use (default alr)
# Exit status: 0 all proved (or listed); 1 a check not proved or a proof
# run failed; 2 a guard tripped, a shard check failed, not every command
# listed was started, or the script could not run.

set -euo pipefail

ALR=${ALR:-alr}
jobs=2
guard=0
units_only=no
shard=""
list=no
usage="usage: scripts/prove.sh [--jobs N] [--guard SECONDS] [--units-only] [--shard K/N] [--list]"
while [ "$#" -gt 0 ]; do
  case "$1" in
    --jobs) jobs=$2; shift 2 ;;
    --guard) guard=$2; shift 2 ;;
    --units-only) units_only=yes; shift ;;
    --shard)
      if [ "$#" -lt 2 ]; then echo "$usage"; exit 2; fi
      shard=$2; shard_given=yes; shift 2 ;;
    --list) list=yes; shift ;;
    *) echo "$usage"; exit 2 ;;
  esac
done

# say TEXT: a message; on standard error with --list, whose standard
# output is the list alone.
say () {
  if [ "$list" = yes ]; then echo "$1" >&2; else echo "$1"; fi
}

case "$jobs" in ''|*[!0-9]*|0) echo "prove: --jobs must be a positive number"; exit 2 ;; esac
case "$guard" in ''|*[!0-9]*) echo "prove: --guard must be a number of seconds"; exit 2 ;; esac
shard_k=0
shard_n=0
if [ "${shard_given:-no}" = yes ]; then
  # K/N: two decimal numbers without leading zeros, with
  # 1 <= K <= N <= 999 (the check below starts one process per shard).
  case "$shard" in
    */*/*) shard_k=0 ;;
    [1-9]*/[1-9]*)
      shard_k=${shard%/*}
      shard_n=${shard#*/}
      case "$shard_k$shard_n" in *[!0-9]*) shard_k=0 ;; esac
      if [ "${#shard_k}" -gt 3 ] || [ "${#shard_n}" -gt 3 ]; then shard_k=0; fi ;;
    *) shard_k=0 ;;
  esac
  if [ "$shard_k" -eq 0 ] || [ "$shard_k" -gt "$shard_n" ]; then
    say "prove: --shard must be K/N, two whole numbers with 1 <= K <= N <= 999"
    exit 2
  fi
fi

cd "$(dirname "$0")"
cd ..
crate=$(pwd -P)

# The commands, one record per line: NAME KIND TARGET ARGS..., in the
# order they run without --shard (the files in C collation order, so the
# order is the same on every platform). No name or argument holds a space.
specs=$(cd "$crate/src" && LC_ALL=C ls *.ads)
records=""
add () {
  records="$records$*
"
}
for spec in $specs; do
  unit=${spec%.ads}
  files="$spec"
  if [ -f "$crate/src/$unit.adb" ]; then files="$files $unit.adb"; fi
  add "unit-$unit" unit "$unit" -u $files
done
if [ "$units_only" = no ]; then
  for spec in $specs; do
    unit=${spec%.ads}
    # The first declaration line of each subprogram declared at the top
    # level (three spaces in), as --limit-subp needs.
    while read -r line name; do
      add "subp-$unit-$name" subp "$spec:$line" --limit-subp="$spec:$line"
    done < <(grep -n -E '^   (procedure|function) [A-Za-z_0-9]+' "$crate/src/$spec" \
             | sed -E 's/^([0-9]+):   (procedure|function) ([A-Za-z_0-9]+).*/\1 \3/' \
             | awk '!seen[$2]++')
  done
  # Subprograms declared at the top level of a body and not in its spec,
  # at their first declaration in the body.
  for spec in $specs; do
    unit=${spec%.ads}
    body="$unit.adb"
    [ -f "$crate/src/$body" ] || continue
    while read -r line name; do
      if ! grep -q -E "^   (procedure|function) $name([^A-Za-z_0-9]|\$)" "$crate/src/$spec"; then
        add "subp-$unit-$name" subp "$body:$line" --limit-subp="$body:$line"
      fi
    done < <(grep -n -E '^   (procedure|function) [A-Za-z_0-9]+' "$crate/src/$body" \
             | sed -E 's/^([0-9]+):   (procedure|function) ([A-Za-z_0-9]+).*/\1 \3/' \
             | awk '!seen[$2]++')
  done
fi
commands=$(printf '%s' "$records" | awk 'END { print NR }')

# select_shard K N: the records of shard K of N, in order: those whose
# number (0 to T-1) leaves K-1 when divided by N.
select_shard () {
  printf '%s' "$records" | awk -v k="$1" -v n="$2" '(NR - 1) % n == k - 1'
}

if [ "$shard_n" -gt 0 ]; then
  # The coverage check, for this N: the shards 1 to N, together, hold
  # every command exactly once, and this shard at least one.
  all=$(printf '%s' "$records" | LC_ALL=C sort)
  twice=$(printf '%s\n' "$all" | uniq -d)
  union=$(k=1; while [ "$k" -le "$shard_n" ]; do select_shard "$k" "$shard_n"; k=$((k + 1)); done \
          | LC_ALL=C sort)
  if [ -n "$twice" ]; then
    say "prove: SHARD CHECK FAILED: a command is listed twice"
    exit 2
  fi
  if [ "$union" != "$all" ]; then
    if [ -n "$(printf '%s\n' "$union" | uniq -d)" ]; then
      say "prove: SHARD CHECK FAILED: the $shard_n shards overlap"
    else
      say "prove: SHARD CHECK FAILED: the $shard_n shards do not cover the $commands commands"
    fi
    exit 2
  fi
  records=$(select_shard "$shard_k" "$shard_n")
  if [ -n "$records" ]; then
    records="$records
"
  fi
  count=$(printf '%s' "$records" | awk 'END { print NR }')
  if [ "$count" -lt 1 ]; then
    say "prove: SHARD CHECK FAILED: shard $shard_k/$shard_n has no commands (of $commands)"
    exit 2
  fi
  shard_line="shard $shard_k/$shard_n: $count of $commands commands"
fi

if [ "$list" = yes ]; then
  if [ "$shard_n" -gt 0 ]; then say "$shard_line"; fi
  printf '%s' "$records" | awk '{ print $1 }'
  exit 0
fi

logs="$crate/tests/obj/prove"
mkdir -p "$logs"
cd tests
if ! command -v "$ALR" > /dev/null 2>&1; then
  echo "prove: alr (ALR) cannot be run"
  exit 2
fi
"$ALR" -n build > "$logs/build.txt" 2>&1 \
  || { echo "prove: the tests crate does not build (see tests/obj/prove/build.txt)"; exit 2; }

if [ "$guard" -eq 0 ]; then
  echo "guard: UNMEASURED (none)"
else
  echo "guard: $guard s per command (a safeguard; a trip is an error to rerun)"
fi
echo "jobs: $jobs"
if [ "$shard_n" -gt 0 ]; then echo "$shard_line"; fi

failed=0
tripped=0
started=0

# run NAME ARGS...: one cold gnatprove command; its output in
# tests/obj/prove/NAME.txt.
run () {
  local name=$1 kind=$2 target=$3 out status steps proved unproved summary
  local verdict total
  shift 3
  started=$((started + 1))
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
  summary=$(ls "$crate"/obj/*/gnatprove/gnatprove.out 2> /dev/null | head -n 1 || true)
  steps=$(perl -ne '
      while (/and (\d+) steps?\b/g) { $m = $1 if $1 > ($m // 0) }
      $m = $1 if /^max steps used for successful proof: (\d+)/ && $1 > ($m // 0);
      END { print $m // 0 }' "$out" ${summary:+"$summary"})
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

# Each command of the run (of the shard, with --shard), in order. The
# records are read on descriptor 3, which is closed for each command, so
# that no command reads them.
while read -r name kind target args <&3; do
  # shellcheck disable=SC2086
  run "$name" "$kind" "$target" $args 3<&-
done 3< <(printf '%s' "$records")

# Every command of the run was started: a record stream that ended early
# (or yielded nothing) is an error, never a pass.
if [ "$shard_n" -gt 0 ]; then expected=$count; else expected=$commands; fi
if [ "$started" -ne "$expected" ]; then
  echo "prove: INTERNAL: ran $started of $expected commands"
  exit 2
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
