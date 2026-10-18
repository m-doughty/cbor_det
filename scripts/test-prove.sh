#!/usr/bin/env bash
# Exercise scripts/prove.sh with a stand-in alr that plays gnatprove, so
# that each way a proof run can fail is seen to fail it:
#   a check not proved; a failing exit status with nothing printed; a
#   justified check or a pragma Assume in the summary; unproved checks
#   shown only in the summary; a command killed by a signal; a command
#   that exits 0 with no output and no summary; a malformed summary; a
#   truncated summary (no Total line); a summary that counts checks the
#   output never proved; a subprogram command that analysed nothing; and
#   a tripped wall-clock guard (an error, exit status 2, not a failed
#   proof). And that the largest step count it reports is the largest of
#   every prover on every line and of the summary's own figure, and that
#   a subprogram declared only in a body gets its own command.
# Shards and the list, on a crate of 11 commands: --list prints the
#   commands in the order a run executes them, without alr (with
#   --units-only, the units); a run without --shard prints no shard
#   line; with no cost table, for N = 1, 2, 3, 4 and 11 the N shards
#   (each with its count) are round robin and list every command exactly
#   once; a shard with no commands fails; the runs
#   of the shards of 3 pass and together execute exactly the commands,
#   with the same arguments, of a run without --shard; a shard fails on a
#   check not proved and on a tripped guard; a bad --shard is refused,
#   N above 999 too; and a broken rule (a gap or an overlap, in a test
#   copy of the script) is caught by the shard check before anything
#   runs. A command that reads the driver's list on descriptor 3 cannot
#   cut a run short, and a run whose list stops early or yields nothing
#   (in test copies of the script) fails, never passes. Every result
#   line ends with the command's time in whole seconds.
# Shards by measured time, with a cost table: the exact shards of 3 and
#   of 2 (worked out below), their loads within the largest cost; a
#   command not in the table at the median; names that are not commands
#   ignored; the runs of the shards execute the commands --list gives
#   them, and together exactly those of a run without --shard; an empty,
#   flat, zero or stale table gives round robin; a table in CR LF or
#   CR CR LF reads as in LF; a malformed table, a name listed twice or an unreadable
#   table fails before anything runs (with --shard only). scripts/prove-costs.sh: its means, rounding,
#   minimum, order and header, a table prove.sh reads, logs named like
#   awk assignments (x=y), and its refusals, each with its reason.
# Runs under /bin/bash by default (Bash 3.2 on macOS).
#
# Usage: scripts/test-prove.sh
#        TEST_BASH=/path/to/bash scripts/test-prove.sh

set -euo pipefail
cd "$(dirname "$0")"
cd ..
here=$(pwd)
TEST_BASH=${TEST_BASH:-/bin/bash}

tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT
mkdir -p "$tmp/crate/scripts" "$tmp/crate/src" "$tmp/crate/tests" "$tmp/mocks"
cp scripts/prove.sh "$tmp/crate/scripts/"
printf 'package A with SPARK_Mode is\n   procedure P;\n   function F return Boolean;\nend A;\n' \
  > "$tmp/crate/src/a.ads"
printf 'package body A with SPARK_Mode is\n   procedure Inner;\n   procedure Inner is null;\nend A;\n' \
  > "$tmp/crate/src/a.adb"

# The stand-in prints what gnatprove prints with --report=statistics and
# writes the summary file gnatprove.out, as MOCK_MODE says.
cat > "$tmp/mocks/alr" <<'EOF'
#!/usr/bin/env bash
set -euo pipefail
if [ "$1 $2" = "-n build" ]; then exit 0; fi
[ "$1 $2 $3 $4" = "-n exec -- gnatprove" ]
crate=${6%/cbor_det.gpr}
printf '%s\n' "$*" >> "$MOCK_DIR/calls"
subp=""
unit=a
prev=""
for a in "$@"; do
  case "$a" in --limit-subp=*) subp=${a#--limit-subp=} ;; esac
  if [ "$prev" = -u ]; then unit=${a%.ads}; fi
  prev=$a
done
summary="$crate/obj/x/gnatprove/gnatprove.out"
mkdir -p "$crate/obj/x/gnatprove"
total=1 justified=. unproved=. assume=0 code=0 proved_lines=1
case "$MOCK_MODE" in
  pass) ;;
  unproved) echo ' medium: postcondition might fail'; total=2; unproved=1; code=1 ;;
  silent-exit) code=1 ;;
  justified) total=2; justified=1 ;;
  assume) assume=1 ;;
  summary-only) total=2; unproved=1 ;;
  slow) sleep 30 ;;
  killed) kill -KILL $$ ;;
  empty) exit 0 ;;
  proved-zero) total=3; proved_lines=0 ;;
  drain-fd3) cat <&3 > /dev/null 2>&1 || true ;;
esac
if [ "$proved_lines" -eq 1 ]; then
  case "$MOCK_MODE" in
    multi-prover)
      echo ' info: postcondition proved (CVC5: 5 VC in max 0.1 seconds and 866 steps; Trivial: 1 VC in max 0.0 seconds and 2 steps; Z3: 5 VC in max 0.0 seconds and 21 steps)' ;;
    *) echo ' info: precondition proved (Z3: 1 VC in max 0.0 seconds and 42 steps)' ;;
  esac
fi
{
  echo 'SPARK Analysis results        Total        Flow   Provers   Justified   Unproved'
  case "$MOCK_MODE" in
    malformed) echo 'Total             x    garbled' ;;
    truncated) ;;
    *) printf 'Total             %s           .    %s (100%%)           %s          %s\n' \
         "$total" "$total" "$justified" "$unproved" ;;
  esac
  if [ "$MOCK_MODE" = summary-max ]; then
    echo 'max steps used for successful proof: 5000'
  fi
  echo 'Analyzed 1 unit'
  if [ -n "$subp" ]; then
    if [ "$MOCK_MODE" = not-analysed ]; then
      echo 'in unit a, 0 subprograms and packages out of 0 analyzed'
    else
      echo 'in unit a, 1 subprograms and packages out of 1 analyzed'
      printf '  A.X at %s flow analyzed (0 errors, 0 checks, 0 warnings and %s pragma Assume statements) and proved (1 checks)\n' \
        "$subp" "$assume"
    fi
  else
    echo "in unit $unit, 3 subprograms and packages out of 3 analyzed"
    printf '  A at a.ads:1 flow analyzed (0 errors, 0 checks, 0 warnings and %s pragma Assume statements) and proved (1 checks)\n' \
      "$assume"
  fi
} > "$summary"
exit "$code"
EOF
chmod +x "$tmp/mocks/alr"

pass=0
fail=0
# check NAME MODE ARGS EXPECTED_STATUS EXPECTED_TEXT
check () {
  local name=$1 mode=$2 args=$3 want=$4 text=$5 status=0
  export MOCK_MODE=$mode MOCK_DIR="$tmp/$name"
  mkdir -p "$MOCK_DIR"
  # shellcheck disable=SC2086
  (cd "$tmp/crate" && ALR="$tmp/mocks/alr" "$TEST_BASH" scripts/prove.sh $args) \
    > "$MOCK_DIR/output" 2>&1 || status=$?
  if [ "$status" -eq "$want" ] && grep -qF -- "$text" "$MOCK_DIR/output"; then
    pass=$((pass + 1))
  else
    fail=$((fail + 1))
    echo "test-prove FAILED: $name (exit $status, expected $want and \"$text\"):"
    sed 's/^/    /' "$MOCK_DIR/output"
  fi
}

check pass pass "" 0 "prove: all checks proved"
check steps pass "" 0 "max steps 42"
check unproved unproved "" 1 "not proved 1"
check silent-exit silent-exit "" 1 "prove: FAILED"
check justified justified "" 1 "a justified check or a pragma Assume"
check assume assume "" 1 "a justified check or a pragma Assume"
check summary-only summary-only "" 1 "the summary shows unproved checks"
check killed killed "--units-only" 1 "killed by a signal"
check empty empty "--units-only" 1 "no summary"
check malformed malformed "--units-only" 1 "malformed summary"
check truncated truncated "--units-only" 1 "malformed summary"
check proved-zero proved-zero "--units-only" 1 "the summary counts 3 checks but 0 were proved"
check not-analysed not-analysed "" 1 "not analysed"
check guard slow "--guard 1 --units-only" 2 "GUARD TRIPPED"
check jobs pass "--jobs 0" 2 "--jobs must be a positive number"
# The largest step count: of every prover on a line, not the last one
# listed; and the summary's own figure where that is larger.
check steps-every-prover multi-prover "--units-only" 0 "max steps 866,"
check steps-summary summary-max "--units-only" 0 "max steps 5000,"

# One command per unit, then one per subprogram declaration (P and F in
# the spec, Inner declared only in the body, at its declaration), each
# with the job cap.
if [ "$(grep -c -- '-j2 --report=statistics -u a.ads a.adb' "$tmp/pass/calls")" -eq 1 ] \
   && [ "$(grep -c -- '--limit-subp=a.ads:2' "$tmp/pass/calls")" -eq 1 ] \
   && [ "$(grep -c -- '--limit-subp=a.ads:3' "$tmp/pass/calls")" -eq 1 ] \
   && [ "$(grep -c -- '--limit-subp=a.adb:2' "$tmp/pass/calls")" -eq 1 ] \
   && [ "$(wc -l < "$tmp/pass/calls")" -eq 4 ]; then
  pass=$((pass + 1))
else
  fail=$((fail + 1))
  echo "test-prove FAILED: commands:"
  sed 's/^/    /' "$tmp/pass/calls"
fi

# Shards and the list, on a crate of three units: a (spec and body, one
# subprogram declared only in the body), b (spec only) and c (spec and
# body, one subprogram declared only in the body, one declared in both).
# Its 11 commands, in the order a run without --shard has them:
mkdir -p "$tmp/multi/scripts" "$tmp/multi/src" "$tmp/multi/tests"
cp scripts/prove.sh "$tmp/multi/scripts/"
cp "$tmp/crate/src/a.ads" "$tmp/crate/src/a.adb" "$tmp/multi/src/"
printf 'package B with SPARK_Mode is\n   procedure G;\nend B;\n' > "$tmp/multi/src/b.ads"
printf 'package C with SPARK_Mode is\n   procedure H1;\n   procedure H2;\n   function H3 return Boolean;\nend C;\n' \
  > "$tmp/multi/src/c.ads"
printf 'package body C with SPARK_Mode is\n   procedure Hidden is null;\n   procedure H1 is null;\nend C;\n' \
  > "$tmp/multi/src/c.adb"
printf '%s\n' unit-a unit-b unit-c subp-a-P subp-a-F subp-b-G subp-c-H1 \
  subp-c-H2 subp-c-H3 subp-a-Inner subp-c-Hidden > "$tmp/want-list"

# prove DIR OUT MODE ARGS...: scripts/prove.sh of DIR, with the stand-in
# in mode MODE; its standard output in OUT/stdout, its standard error in
# OUT/stderr, the commands it ran in OUT/calls, its exit status in st.
prove () {
  local dir=$1 out=$2
  export MOCK_MODE=$3 MOCK_DIR=$out
  shift 3
  mkdir -p "$out"
  : > "$out/calls"
  st=0
  (cd "$dir" && ALR="${PROVE_ALR:-$tmp/mocks/alr}" "$TEST_BASH" scripts/prove.sh "$@") \
    > "$out/stdout" 2> "$out/stderr" || st=$?
}
# verdict NAME CONDITION...: a case passes if the command CONDITION does;
# a failure shows the output of the last run, in o.
verdict () {
  local name=$1
  shift
  if "$@"; then
    pass=$((pass + 1))
  else
    fail=$((fail + 1))
    echo "test-prove FAILED: $name (exit $st; the last run's output follows):"
    for f in "$o/stdout" "$o/stderr"; do
      if [ -f "$f" ]; then sed 's/^/    /' "$f"; fi
    done
  fi
}
same () { cmp -s "$1" "$2"; }
# The commands' names in a run's output, in order.
names_run () { sed -n -E 's/^((unit|subp)-[^:]*): proved .*/\1/p' "$1"; }

# --list prints the commands in order, and needs no alr.
o="$tmp/v/list-no-alr"
PROVE_ALR="$tmp/no-such-alr" prove "$tmp/multi" "$o" pass --list
list_ok () { [ "$st" -eq 0 ] && same "$o/stdout" "$tmp/want-list" && [ ! -s "$o/calls" ]; }
verdict list-no-alr list_ok
cp "$o/stdout" "$tmp/list"
o="$tmp/v/list-units-only"
PROVE_ALR="$tmp/no-such-alr" prove "$tmp/multi" "$o" pass --list --units-only
units_list_ok () {
  [ "$st" -eq 0 ] && [ "$(cat "$o/stdout")" = "$(head -n 3 "$tmp/want-list")" ]
}
verdict list-units-only units_list_ok

# --list is the sequence of commands a run without --shard executes; that
# run prints no shard line, nothing but the commands between its header
# and its verdict.
o="$tmp/v/list-is-run"
prove "$tmp/multi" "$o" pass
names_run "$o/stdout" > "$o/names"
printf '%s\n' "guard: UNMEASURED (none)" "jobs: 2" "prove: all checks proved" > "$o/frame"
run_ok () {
  [ "$st" -eq 0 ] && same "$o/names" "$tmp/list" && same "$o/names" "$tmp/want-list" \
    && [ "$(wc -l < "$o/calls")" -eq 11 ] \
    && grep -v -E '^(unit|subp)-[^:]*: proved ' "$o/stdout" | cmp -s - "$o/frame"
}
verdict list-is-run run_ok
cp "$o/calls" "$tmp/full-calls"

# The partition: for N = 1, 2, 3, 4 and 11 (one command a shard), shard K
# of N lists exactly the commands whose number leaves K-1 divided by N,
# with its count; the N shards together list every command once.
partition_ok () {
  local n=$1 k=1 m
  : > "$tmp/v/union-$n"
  while [ "$k" -le "$n" ]; do
    o="$tmp/v/partition-$n-$k"
    prove "$tmp/multi" "$o" pass --list --shard "$k/$n"
    awk -v k="$k" -v n="$n" '(NR - 1) % n == k - 1' "$tmp/want-list" > "$o/want"
    m=$(wc -l < "$o/want" | tr -d ' ')
    [ "$st" -eq 0 ] && same "$o/stdout" "$o/want" && [ ! -s "$o/calls" ] \
      && [ "$(cat "$o/stderr")" = "shard $k/$n: $m of 11 commands" ] || return 1
    cat "$o/stdout" >> "$tmp/v/union-$n"
    k=$((k + 1))
  done
  [ "$(LC_ALL=C sort "$tmp/v/union-$n")" = "$(LC_ALL=C sort "$tmp/want-list")" ] \
    && [ -z "$(LC_ALL=C sort "$tmp/v/union-$n" | uniq -d)" ]
}
for n in 1 2 3 4 11; do
  verdict "partition-$n" partition_ok "$n"
done

# With more shards than commands, a shard with no commands fails, in a
# run (before any proof) and in a list.
o="$tmp/v/empty-shard"
prove "$tmp/multi" "$o" pass --shard 12/12
empty_ok () {
  [ "$st" -eq 2 ] && [ ! -s "$o/calls" ] \
    && grep -qF "prove: SHARD CHECK FAILED: shard 12/12 has no commands (of 11)" "$o/stdout"
}
verdict empty-shard empty_ok
o="$tmp/v/empty-shard-list"
prove "$tmp/multi" "$o" pass --list --shard 12/12
empty_list_ok () {
  [ "$st" -eq 2 ] && [ ! -s "$o/stdout" ] \
    && grep -qF "prove: SHARD CHECK FAILED: shard 12/12 has no commands (of 11)" "$o/stderr"
}
verdict empty-shard-list empty_list_ok

# The runs of the three shards of 3 each pass, say how many commands they
# ran, and together execute exactly the commands, with the same
# arguments, of the run without --shard: shard K those numbered K-1, K+2,
# ..., in order.
shards_ok () {
  local k=1 m
  : > "$tmp/v/shard-calls"
  while [ "$k" -le 3 ]; do
    o="$tmp/v/shard-run-$k"
    prove "$tmp/multi" "$o" pass --shard "$k/3"
    awk -v k="$k" '(NR - 1) % 3 == k - 1' "$tmp/full-calls" > "$o/want"
    m=$(wc -l < "$o/want" | tr -d ' ')
    [ "$st" -eq 0 ] && same "$o/calls" "$o/want" \
      && grep -qx "shard $k/3: $m of 11 commands" "$o/stdout" \
      && [ "$(tail -n 1 "$o/stdout")" = "prove: all checks proved" ] || return 1
    cat "$o/calls" >> "$tmp/v/shard-calls"
    k=$((k + 1))
  done
  [ "$(LC_ALL=C sort "$tmp/v/shard-calls")" = "$(LC_ALL=C sort "$tmp/full-calls")" ]
}
verdict shard-runs shards_ok

# A shard fails as a whole run does: on a check not proved, and on a
# tripped guard.
o="$tmp/v/shard-unproved"
prove "$tmp/multi" "$o" unproved --shard 2/3
shard_unproved_ok () {
  [ "$st" -eq 1 ] && grep -q '^shard 2/3: 4 of 11 commands$' "$o/stdout" \
    && [ "$(tail -n 1 "$o/stdout")" = "prove: FAILED" ]
}
verdict shard-unproved shard_unproved_ok
o="$tmp/v/shard-guard"
prove "$tmp/multi" "$o" slow --units-only --guard 1 --shard 3/3
shard_guard_ok () {
  [ "$st" -eq 2 ] && grep -qF "unit-c: GUARD TRIPPED" "$o/stdout" \
    && [ "$(wc -l < "$o/calls")" -eq 1 ]
}
verdict shard-guard shard_guard_ok

# A bad --shard is refused (exit status 2) before anything runs.
bad_ok () {
  [ "$st" -eq 2 ] && [ ! -s "$o/calls" ] && [ ! -s "$o/stderr" ] \
    && grep -qx "prove: --shard must be K/N, two whole numbers with 1 <= K <= N <= 999" "$o/stdout"
}
i=0
for v in 0/0 0/3 4/3 1/0 x/3 1/2/3 "" 01/3 3 /3 1/ 1/3x 1234567890/1234567890 1/1000 1000/1000; do
  i=$((i + 1))
  o="$tmp/v/bad-shard-$i"
  prove "$tmp/multi" "$o" pass --shard "$v"
  verdict "bad-shard-$i" bad_ok
done
o="$tmp/v/bad-shard-missing"
prove "$tmp/multi" "$o" pass --shard
missing_ok () { [ "$st" -eq 2 ] && [ ! -s "$o/calls" ] && grep -q '^usage: scripts/prove.sh ' "$o/stdout"; }
verdict bad-shard-missing missing_ok
# N up to 999 is accepted: shard 1 of 999 holds the first command.
o="$tmp/v/shard-999"
PROVE_ALR="$tmp/no-such-alr" prove "$tmp/multi" "$o" pass --list --shard 1/999
n999_ok () {
  [ "$st" -eq 0 ] && [ "$(cat "$o/stdout")" = unit-a ] \
    && [ "$(cat "$o/stderr")" = "shard 1/999: 1 of 11 commands" ]
}
verdict shard-999 n999_ok

# A command that reads descriptor 3 (where the driver reads its list)
# cannot take the commands after it: every command of the shard runs.
o="$tmp/v/drain-fd3"
prove "$tmp/multi" "$o" drain-fd3 --shard 1/3
drain_ok () {
  [ "$st" -eq 0 ] && [ "$(wc -l < "$o/calls")" -eq 4 ] \
    && [ "$(tail -n 1 "$o/stdout")" = "prove: all checks proved" ]
}
verdict drain-fd3 drain_ok

# A run that starts fewer commands than it listed fails (exit status 2),
# never passes: in test copies of the script whose list feeds the loop
# nothing, or only its first command.
feed () {
  local name=$1 to=$2
  mkdir -p "$tmp/$name/scripts"
  cp -R "$tmp/multi/src" "$tmp/multi/tests" "$tmp/$name/"
  sed "s/^done 3< <(printf '%s' \"\$records\")\$/done 3< <($to)/" scripts/prove.sh \
    > "$tmp/$name/scripts/prove.sh"
}
feed feed-empty ':'
feed feed-one "printf '%s' \"\$records\" | head -n 1"
o="$tmp/v/feed-empty"
prove "$tmp/feed-empty" "$o" pass
feed_empty_ok () {
  ! cmp -s scripts/prove.sh "$tmp/feed-empty/scripts/prove.sh" \
    && [ "$st" -eq 2 ] && [ ! -s "$o/calls" ] \
    && [ "$(tail -n 1 "$o/stdout")" = "prove: INTERNAL: ran 0 of 11 commands" ] \
    && ! grep -q 'all checks proved' "$o/stdout"
}
verdict feed-empty feed_empty_ok
o="$tmp/v/feed-one"
prove "$tmp/feed-one" "$o" pass --shard 2/3
feed_one_ok () {
  ! cmp -s scripts/prove.sh "$tmp/feed-one/scripts/prove.sh" \
    && [ "$st" -eq 2 ] && [ "$(wc -l < "$o/calls")" -eq 1 ] \
    && [ "$(tail -n 1 "$o/stdout")" = "prove: INTERNAL: ran 1 of 4 commands" ] \
    && ! grep -q 'all checks proved' "$o/stdout"
}
verdict feed-one feed_one_ok

# The shard check catches a broken rule: in test copies of the script,
# shard K takes the commands given shard K+1 (a gap: those given shard 1
# are in no shard), or those given shard K or less (an overlap), or every
# command is given the shard after its own (a gap: shard N+1 is never
# run). No copy runs a command.
fault () {
  local name=$1 from=$2 to=$3
  mkdir -p "$tmp/$name/scripts"
  cp -R "$tmp/multi/src" "$tmp/multi/tests" "$tmp/$name/"
  sed "s/$from/$to/" scripts/prove.sh > "$tmp/$name/scripts/prove.sh"
}
fault gap "'\$1 == k + 0 {" "'\$1 == k + 1 {"
fault overlap "'\$1 == k + 0 {" "'\$1 <= k + 0 {"
fault label "lab\[i\] = best;" "lab[i] = best + 1;"
o="$tmp/v/fault-gap"
prove "$tmp/gap" "$o" pass --shard 1/3
gap_ok () {
  ! cmp -s scripts/prove.sh "$tmp/gap/scripts/prove.sh" \
    && [ "$st" -eq 2 ] && [ ! -s "$o/calls" ] \
    && grep -qF "prove: SHARD CHECK FAILED: the 3 shards do not cover the 11 commands" "$o/stdout"
}
verdict fault-gap gap_ok
o="$tmp/v/fault-overlap"
prove "$tmp/overlap" "$o" pass --shard 1/3
overlap_ok () {
  ! cmp -s scripts/prove.sh "$tmp/overlap/scripts/prove.sh" \
    && [ "$st" -eq 2 ] && [ ! -s "$o/calls" ] \
    && grep -qF "prove: SHARD CHECK FAILED: the 3 shards overlap" "$o/stdout"
}
verdict fault-overlap overlap_ok
o="$tmp/v/fault-label"
prove "$tmp/label" "$o" pass --list --shard 2/3
label_ok () {
  ! cmp -s scripts/prove.sh "$tmp/label/scripts/prove.sh" \
    && [ "$st" -eq 2 ] && [ ! -s "$o/stdout" ] \
    && grep -qF "prove: SHARD CHECK FAILED: the 3 shards do not cover the 11 commands" "$o/stderr"
}
verdict fault-label label_ok

# Every result line ends with the command's wall-clock time, in whole
# seconds: ", T s".
time_ok () {
  local f=$1 n
  n=$(grep -c -E '^(unit|subp)-[^:]*: proved ' "$f" || true)
  [ "$n" -ge 1 ] \
    && [ "$(grep -c -E '^(unit|subp)-[^:]*: proved [0-9]+, not proved [0-9]+, max steps [0-9]+, exit [0-9]+, [0-9]+ s$' "$f")" -eq "$n" ]
}
o="$tmp/v/time-suffix"
verdict time-suffix time_ok "$tmp/v/list-is-run/stdout"
verdict time-suffix-shard time_ok "$tmp/v/shard-run-2/stdout"

# Shards split by measured time: the crate above with a cost table
# (scripts/prove-costs.txt beside the script). Its costs, with comments,
# a blank line and two names that are not commands (ignored, also in the
# median: counted, they would make it 6):
#   unit-a 10, unit-b 3, unit-c 8, subp-a-P 7, subp-a-F 2, subp-b-G 9,
#   subp-c-H1 5, subp-c-H2 1, subp-c-H3 4, subp-c-Hidden 6;
#   subp-a-Inner is not in the table: it costs the lower median of the
#   ten costs (1 2 3 4 5 6 7 8 9 10), 5.
# By cost, largest first, then by number (in brackets):
#   10 unit-a (0), 9 G (5), 8 unit-c (2), 7 P (3), 6 Hidden (10),
#   5 H1 (6), 5 Inner (9), 4 H3 (8), 3 unit-b (1), 2 F (4), 1 H2 (7).
# Three shards, each command to the least loaded (the lowest of equals):
#   unit-a 1 (10 0 0), G 2 (10 9 0), unit-c 3 (10 9 8), P 3 (10 9 15),
#   Hidden 2 (10 15 15), H1 1 (15 15 15), Inner 1 (20 15 15),
#   H3 2 (20 19 15), unit-b 3 (20 19 18), F 3 (20 19 20),
#   H2 2 (20 20 20).
# Two shards: unit-a 1 (10 0), G 2 (10 9), unit-c 2 (10 17),
#   P 1 (17 17), Hidden 1 (23 17), H1 2 (23 22), Inner 2 (23 27),
#   H3 1 (27 27), unit-b 1 (30 27), F 2 (30 29), H2 2 (30 30).
# Each shard lists its commands in the order a run has them.
mkdir -p "$tmp/wt/scripts"
cp -R "$tmp/multi/src" "$tmp/multi/tests" "$tmp/wt/"
cp scripts/prove.sh "$tmp/wt/scripts/"
cat > "$tmp/wt/scripts/prove-costs.txt" <<'EOF'
# A cost table for the test.
unit-a 10
unit-b 3
unit-c 8

  # an indented comment
subp-a-P 7
subp-a-F 2
subp-b-G	9
subp-c-H1 5
subp-c-H2 1
subp-c-H3 4
subp-c-Hidden 6
subp-z-Gone 1000
unit-z 900
EOF
printf '%s\n' unit-a subp-c-H1 subp-a-Inner > "$tmp/want-w3-1"
printf '%s\n' subp-b-G subp-c-H2 subp-c-H3 subp-c-Hidden > "$tmp/want-w3-2"
printf '%s\n' unit-b unit-c subp-a-P subp-a-F > "$tmp/want-w3-3"
printf '%s\n' unit-a unit-b subp-a-P subp-c-H3 subp-c-Hidden > "$tmp/want-w2-1"
printf '%s\n' unit-c subp-a-F subp-b-G subp-c-H1 subp-c-H2 subp-a-Inner > "$tmp/want-w2-2"
# load FILE: the cost of the commands named in FILE (subp-a-Inner 5).
load () {
  awk 'NR == FNR { if ($0 !~ /^ *#/ && NF == 2) c[$1] = $2; next }
       { s += ($1 in c) ? c[$1] : 5 } END { print s + 0 }' \
    "$tmp/wt/scripts/prove-costs.txt" "$1"
}
weighted_ok () {
  local n=$1 k=1 m lo=0 hi=0 l
  : > "$tmp/v/wunion-$n"
  while [ "$k" -le "$n" ]; do
    o="$tmp/v/weighted-$n-$k"
    PROVE_ALR="$tmp/no-such-alr" prove "$tmp/wt" "$o" pass --list --shard "$k/$n"
    m=$(wc -l < "$tmp/want-w$n-$k" | tr -d ' ')
    [ "$st" -eq 0 ] && same "$o/stdout" "$tmp/want-w$n-$k" \
      && [ "$(cat "$o/stderr")" = "shard $k/$n: $m of 11 commands" ] || return 1
    l=$(load "$o/stdout")
    if [ "$k" -eq 1 ] || [ "$l" -lt "$lo" ]; then lo=$l; fi
    if [ "$k" -eq 1 ] || [ "$l" -gt "$hi" ]; then hi=$l; fi
    cat "$o/stdout" >> "$tmp/v/wunion-$n"
    k=$((k + 1))
  done
  # The loads differ by no more than the largest cost (10), and together
  # the shards list every command once.
  [ "$((hi - lo))" -le 10 ] \
    && [ "$(LC_ALL=C sort "$tmp/v/wunion-$n")" = "$(LC_ALL=C sort "$tmp/want-list")" ]
}
verdict weighted-3 weighted_ok 3
verdict weighted-2 weighted_ok 2

# The table changes no command: the runs of the three weighted shards
# pass, each executes the commands --list gives it, in that order, and
# together they execute exactly the commands, with the same arguments,
# of a run without --shard.
wruns_ok () {
  local k=1
  o="$tmp/v/wfull-run"
  prove "$tmp/wt" "$o" pass
  names_run "$o/stdout" > "$o/names"
  same "$o/names" "$tmp/want-list" && [ "$st" -eq 0 ] || return 1
  cp "$o/calls" "$tmp/wfull-calls"
  : > "$tmp/v/wshard-calls"
  while [ "$k" -le 3 ]; do
    o="$tmp/v/wshard-run-$k"
    prove "$tmp/wt" "$o" pass --shard "$k/3"
    names_run "$o/stdout" > "$o/names"
    # The calls of the run without --shard, of the commands of shard K.
    awk 'NR == FNR { want[$0] = 1; next }
         FNR == 1 { i = 0 } { i++ }
         FILENAME ~ /want-list$/ { name[i] = $0; next }
         (name[i] in want) { print }' \
      "$tmp/want-w3-$k" "$tmp/want-list" "$tmp/wfull-calls" > "$o/want-calls"
    [ "$st" -eq 0 ] && same "$o/names" "$tmp/want-w3-$k" && same "$o/calls" "$o/want-calls" \
      && [ "$(tail -n 1 "$o/stdout")" = "prove: all checks proved" ] || return 1
    cat "$o/calls" >> "$tmp/v/wshard-calls"
    k=$((k + 1))
  done
  [ "$(LC_ALL=C sort "$tmp/v/wshard-calls")" = "$(LC_ALL=C sort "$tmp/wfull-calls")" ]
}
verdict weighted-runs wruns_ok

# With a table of no use (comments only; equal costs; costs of 0, which
# count as 1; or only names that are not commands), every cost is the
# same and the shards are round robin: shard K of 3 gets the commands
# whose number leaves K-1 when divided by 3.
flat () {
  local name=$1
  mkdir -p "$tmp/$name/scripts"
  cp -R "$tmp/multi/src" "$tmp/multi/tests" "$tmp/$name/"
  cp scripts/prove.sh "$tmp/$name/scripts/"
  cat > "$tmp/$name/scripts/prove-costs.txt"
}
printf '# nothing measured\n\n' | flat flat-empty
sed 's/$/ 7/' "$tmp/want-list" | flat flat-equal
sed 's/$/ 0/' "$tmp/want-list" | flat flat-zero
printf 'unit-z 50\nsubp-z-Gone 3\n' | flat flat-stale
flat_ok () {
  local dir=$1 k=1
  while [ "$k" -le 3 ]; do
    o="$tmp/v/$dir-$k"
    PROVE_ALR="$tmp/no-such-alr" prove "$tmp/$dir" "$o" pass --list --shard "$k/3"
    awk -v k="$k" '(NR - 1) % 3 == k - 1' "$tmp/want-list" > "$o/want"
    [ "$st" -eq 0 ] && same "$o/stdout" "$o/want" || return 1
    k=$((k + 1))
  done
}
for d in flat-empty flat-equal flat-zero flat-stale; do
  verdict "$d" flat_ok "$d"
done

# A malformed table line, a name listed twice, or a table that cannot be
# read fails (exit status 2) before anything runs, in a run and in a
# list. Without --shard the table is not read.
i=0
for t in 'unit-a' 'unit-a -3' 'unit-a 1.5' 'unit-a 5 x' 'unit-a x' 'unit-a 1234567890' \
         ' unit-a 5' '5' 'unit-a +5' 'unit-a 5\r7'; do
  i=$((i + 1))
  printf "$t\\n" | flat "bad-table-$i"
  o="$tmp/v/bad-table-$i"
  prove "$tmp/bad-table-$i" "$o" pass --shard 1/3
  bad_table_ok () {
    [ "$st" -eq 2 ] && [ ! -s "$o/calls" ] \
      && grep -qE '^prove: scripts/prove-costs.txt: line [0-9]+(: | is not NAME SECONDS)' "$o/stdout"
  }
  verdict "bad-table-$i" bad_table_ok
done
o="$tmp/v/bad-table-list"
PROVE_ALR="$tmp/no-such-alr" prove "$tmp/bad-table-1" "$o" pass --list --shard 1/3
bad_table_list_ok () {
  [ "$st" -eq 2 ] && [ ! -s "$o/stdout" ] \
    && [ "$(cat "$o/stderr")" = "prove: scripts/prove-costs.txt: line 1 is not NAME SECONDS" ]
}
verdict bad-table-list bad_table_list_ok
printf '#c\nunit-a 5\nunit-a 6\n' | flat bad-table-twice
o="$tmp/v/bad-table-twice"
prove "$tmp/bad-table-twice" "$o" pass --shard 1/3
bad_twice_ok () {
  [ "$st" -eq 2 ] && [ ! -s "$o/calls" ] \
    && grep -qx "prove: scripts/prove-costs.txt: line 3: unit-a is listed twice" "$o/stdout"
}
verdict bad-table-twice bad_twice_ok

# A table whose lines end in CR LF, or in CR CR LF, reads as the same
# table in LF: the weighted table above (not round robin), every line so
# ended, blank and comment lines too, gives the same shards. A malformed
# line in such a table is still refused, at its own line number.
# (Written by the shell's printf: an awk might write its "\r\n" in
# text mode, doubling the CR.)
# ends CRS: standard input with CRS (\r or \r\r) before each LF.
ends () { local e=$1 l; while IFS= read -r l; do printf '%s' "$l"; printf "$e"'\n'; done; }
crlf () { ends '\r'; }
crlf < "$tmp/wt/scripts/prove-costs.txt" | flat table-crlf
crlf_ok () {
  local k
  [ "$(tr -d -c '\r' < "$tmp/table-crlf/scripts/prove-costs.txt" | wc -c | tr -d ' ')" \
    -eq "$(wc -l < "$tmp/table-crlf/scripts/prove-costs.txt" | tr -d ' ')" ] || return 1
  for k in 1 2 3; do
    o="$tmp/v/table-crlf-$k"
    PROVE_ALR="$tmp/no-such-alr" prove "$tmp/table-crlf" "$o" pass --list --shard "$k/3"
    [ "$st" -eq 0 ] && same "$o/stdout" "$tmp/want-w3-$k" \
      && same "$o/stdout" "$tmp/v/weighted-3-$k/stdout" || return 1
  done
}
verdict table-crlf crlf_ok
printf '# c\nunit-a 5\nunit-b x\nunit-c 4\n' | crlf | flat table-crlf-bad
o="$tmp/v/table-crlf-bad"
prove "$tmp/table-crlf-bad" "$o" pass --shard 1/3
crlf_bad_ok () {
  [ "$st" -eq 2 ] && [ ! -s "$o/calls" ] \
    && grep -qx "prove: scripts/prove-costs.txt: line 3 is not NAME SECONDS" "$o/stdout"
}
verdict table-crlf-bad crlf_bad_ok
ends '\r\r' < "$tmp/wt/scripts/prove-costs.txt" | flat table-crcrlf
crcrlf_ok () {
  local k
  [ "$(tr -d -c '\r' < "$tmp/table-crcrlf/scripts/prove-costs.txt" | wc -c | tr -d ' ')" \
    -eq "$((2 * $(wc -l < "$tmp/table-crcrlf/scripts/prove-costs.txt")))" ] || return 1
  for k in 1 2 3; do
    o="$tmp/v/table-crcrlf-$k"
    PROVE_ALR="$tmp/no-such-alr" prove "$tmp/table-crcrlf" "$o" pass --list --shard "$k/3"
    [ "$st" -eq 0 ] && same "$o/stdout" "$tmp/want-w3-$k" || return 1
  done
}
verdict table-crcrlf crcrlf_ok
printf '# c\n\nunit-a 5\nunit-b x\nunit-c 4\n' | ends '\r\r' | flat table-crcrlf-bad
o="$tmp/v/table-crcrlf-bad"
prove "$tmp/table-crcrlf-bad" "$o" pass --shard 1/3
crcrlf_bad_ok () {
  [ "$st" -eq 2 ] && [ ! -s "$o/calls" ] \
    && grep -qx "prove: scripts/prove-costs.txt: line 4 is not NAME SECONDS" "$o/stdout"
}
verdict table-crcrlf-bad crcrlf_bad_ok
# Mixed endings (CR LF, then CR CR LF) read as the same table in LF.
printf '# c\r\n\r\nunit-a 10\r\r\n' | flat table-mixed-cr
printf '# c\n\nunit-a 10\n' | flat table-mixed-lf
mixed_ok () {
  local k
  for k in 1 2 3; do
    o="$tmp/v/table-mixed-lf-$k"
    PROVE_ALR="$tmp/no-such-alr" prove "$tmp/table-mixed-lf" "$o" pass --list --shard "$k/3"
    [ "$st" -eq 0 ] || return 1
    o="$tmp/v/table-mixed-cr-$k"
    PROVE_ALR="$tmp/no-such-alr" prove "$tmp/table-mixed-cr" "$o" pass --list --shard "$k/3"
    [ "$st" -eq 0 ] && same "$o/stdout" "$tmp/v/table-mixed-lf-$k/stdout" || return 1
  done
}
verdict table-mixed-cr mixed_ok
mkdir -p "$tmp/table-dir/scripts/prove-costs.txt"
cp -R "$tmp/multi/src" "$tmp/multi/tests" "$tmp/table-dir/"
cp scripts/prove.sh "$tmp/table-dir/scripts/"
o="$tmp/v/table-unreadable"
prove "$tmp/table-dir" "$o" pass --shard 1/3
unreadable_ok () {
  [ "$st" -eq 2 ] && [ ! -s "$o/calls" ] \
    && grep -qx "prove: scripts/prove-costs.txt cannot be read" "$o/stdout"
}
verdict table-unreadable unreadable_ok
o="$tmp/v/table-unsharded"
prove "$tmp/bad-table-1" "$o" pass
unsharded_ok () {
  [ "$st" -eq 0 ] && [ "$(wc -l < "$o/calls")" -eq 11 ] \
    && [ "$(tail -n 1 "$o/stdout")" = "prove: all checks proved" ]
}
verdict table-unsharded unsharded_ok

# scripts/prove-costs.sh: the mean per name over every result line of
# every file, rounded to the nearest second (halves up), at least 1;
# lines with a prefix (as in a CI log) or a carriage return count, other
# lines do not; sorted by name, after a comment header. A file that
# cannot be read, no file, or no result line: exit status 2.
r=', not proved 0, max steps 1, exit 0'
printf '%s\n' "unit-a: proved 1$r, 10 s" "subp-a-P: proved 2$r, 3 s" \
  "unit-b: proved 1$r, 0 s" "subp-c-H2: proved 1$r, 2 s" "subp-c-H2: proved 1$r, 3 s" \
  "subp-c-H3: proved 1$r, 1 s" "subp-c-H3: proved 1$r, 1 s" "noise" \
  "subp-c-H1: GUARD TRIPPED after 5 s (an error to rerun, not a proof result)" \
  "subp-a-F: proved 1, not proved 0, max steps 1, exit 0" > "$tmp/log1"
printf 'job\tstep\tat 2026-01-01T00:00:00Z %s\r\n' "unit-a: proved 1$r, 11 s" \
  "subp-a-P: proved 2$r, 4 s" "unit-b: proved 1$r, 0 s" "subp-c-H2: proved 1$r, 3 s" \
  "subp-c-H3: proved 1$r, 2 s" > "$tmp/log2"
printf '%s\n' subp-a-P subp-c-H2 subp-c-H3 unit-a unit-b > "$tmp/want-cost-names"
printf '%s\n' "subp-a-P 4" "subp-c-H2 3" "subp-c-H3 1" "unit-a 11" "unit-b 1" > "$tmp/want-costs"
o="$tmp/v/costs-mean"
mkdir -p "$o"
st=0
"$TEST_BASH" scripts/prove-costs.sh "$tmp/log1" "$tmp/log2" > "$o/stdout" 2> "$o/stderr" || st=$?
costs_ok () {
  [ "$st" -eq 0 ] && [ ! -s "$o/stderr" ] \
    && grep -v '^#' "$o/stdout" | cmp -s - "$tmp/want-costs" \
    && [ "$(head -n 4 "$o/stdout" | grep -c '^# ')" -eq 4 ] \
    && [ "$(grep -c '^#' "$o/stdout")" -eq 4 ]
}
verdict costs-mean costs_ok
# Result lines ending in CR CR LF read as the same lines in LF.
ends '\r\r' < "$tmp/log1" > "$tmp/log1-crcr"
o="$tmp/v/costs-crcrlf"
mkdir -p "$o"
st=0
"$TEST_BASH" scripts/prove-costs.sh "$tmp/log1-crcr" > "$o/stdout" 2> "$o/stderr" || st=$?
st_crcr=$st
st=0
"$TEST_BASH" scripts/prove-costs.sh "$tmp/log1" > "$o/want" 2> /dev/null || st=$?
costs_crcr_ok () {
  [ "$st_crcr" -eq 0 ] && [ "$st" -eq 0 ] && [ ! -s "$o/stderr" ] \
    && [ "$(grep -vc '^#' "$o/want")" -eq 5 ] && same "$o/stdout" "$o/want"
}
verdict costs-crcrlf costs_crcr_ok
# Its table is one prove.sh reads and uses. Costs: unit-a 11, subp-a-P 4,
# unit-b 1, subp-c-H3 1, subp-c-H2 3, and the rest the median, 3. Two
# shards: unit-a 1 (11 0), P 2 (11 4), unit-c 2 (11 7), F 2 (11 10),
# G 2 (11 13), H1 1 (14 13), H2 2 (14 16), Inner 1 (17 16),
# Hidden 2 (17 19), unit-b 1 (18 19), H3 1 (19 19).
flat costs-roundtrip < "$tmp/v/costs-mean/stdout"
printf '%s\n' unit-a unit-b subp-c-H1 subp-c-H3 subp-a-Inner > "$tmp/want-rt-1"
printf '%s\n' unit-c subp-a-P subp-a-F subp-b-G subp-c-H2 subp-c-Hidden > "$tmp/want-rt-2"
roundtrip_ok () {
  local k
  for k in 1 2; do
    o="$tmp/v/costs-roundtrip-$k"
    PROVE_ALR="$tmp/no-such-alr" prove "$tmp/costs-roundtrip" "$o" pass --list --shard "$k/2"
    [ "$st" -eq 0 ] && same "$o/stdout" "$tmp/want-rt-$k" || return 1
  done
}
verdict costs-roundtrip roundtrip_ok
# Logs given by relative paths that awk would take for an assignment
# (x=y, d=e/z.log) count as files, as an ordinary one does.
mkdir -p "$tmp/rel/d=e"
printf '%s\n' "unit-a: proved 1$r, 7 s" > "$tmp/rel/x=y"
printf '%s\n' "unit-b: proved 1$r, 9 s" > "$tmp/rel/d=e/z.log"
printf '%s\n' "unit-c: proved 1$r, 3 s" > "$tmp/rel/plain.log"
o="$tmp/v/costs-assignment-names"
mkdir -p "$o"
st=0
(cd "$tmp/rel" && "$TEST_BASH" "$here/scripts/prove-costs.sh" x=y d=e/z.log plain.log) \
  > "$o/stdout" 2> "$o/stderr" || st=$?
assign_ok () {
  [ "$st" -eq 0 ] && [ ! -s "$o/stderr" ] \
    && [ "$(grep -v '^#' "$o/stdout")" = "$(printf '%s\n' "unit-a 7" "unit-b 9" "unit-c 3")" ]
}
verdict costs-assignment-names assign_ok

# Its refusals (exit status 2, nothing on standard output, the reason on
# standard error): no file; a file that does not exist; a directory; a
# file with no result line; a good file and one that does not exist.
# costs_bad NAME MESSAGE ARGS...: a case of prove-costs.sh ARGS.
costs_bad () {
  local name=$1 msg=$2
  shift 2
  o="$tmp/v/$name"
  mkdir -p "$o"
  st=0
  "$TEST_BASH" scripts/prove-costs.sh "$@" > "$o/stdout" 2> "$o/stderr" || st=$?
  costs_bad_ok () {
    [ "$st" -eq 2 ] && [ ! -s "$o/stdout" ] && [ "$(cat "$o/stderr")" = "$msg" ]
  }
  verdict "$name" costs_bad_ok
}
printf 'no result here\nunit-a: proved 1, not proved 0, max steps 1, exit 0\n' > "$tmp/log-none"
mkdir -p "$tmp/log-dir"
unreadable="prove-costs: a log file cannot be read"
costs_bad costs-bad-1 "usage: scripts/prove-costs.sh LOGFILE..."
costs_bad costs-bad-2 "$unreadable" "$tmp/no-such-log"
costs_bad costs-bad-3 "$unreadable" "$tmp/log-dir"
costs_bad costs-bad-4 "prove-costs: no result line (NAME: proved ..., T s) in the files given" \
  "$tmp/log-none"
costs_bad costs-bad-5 "$unreadable" "$tmp/log1" "$tmp/no-such-log"

echo "test-prove: $pass passed, $fail failed"
[ "$fail" -eq 0 ]
