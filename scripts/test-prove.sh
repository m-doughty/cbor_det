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
#   line; for N = 1, 2,
#   3, 4 and 11 the N shards (each with its count) list every command
#   exactly once, by the rule; a shard with no commands fails; the runs
#   of the shards of 3 pass and together execute exactly the commands,
#   with the same arguments, of a run without --shard; a shard fails on a
#   check not proved and on a tripped guard; a bad --shard is refused,
#   N above 999 too; and a broken rule (a gap or an overlap, in a test
#   copy of the script) is caught by the shard check before anything
#   runs. A command that reads the driver's list on descriptor 3 cannot
#   cut a run short, and a run whose list stops early or yields nothing
#   (in test copies of the script) fails, never passes.
# Runs under /bin/bash by default (Bash 3.2 on macOS).
#
# Usage: scripts/test-prove.sh
#        TEST_BASH=/path/to/bash scripts/test-prove.sh

set -euo pipefail
cd "$(dirname "$0")"
cd ..
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

# The shard check catches a broken rule: in a test copy of the script,
# shard K takes the commands that leave K (a gap: those that leave 0 are
# in no shard), or those that leave at most K-1 (an overlap). Neither
# copy runs a command.
fault () {
  local name=$1 to=$2
  mkdir -p "$tmp/$name/scripts"
  cp -R "$tmp/multi/src" "$tmp/multi/tests" "$tmp/$name/"
  sed "s/'(NR - 1) % n == k - 1'/'$to'/" scripts/prove.sh > "$tmp/$name/scripts/prove.sh"
}
fault gap '(NR - 1) % n == k'
fault overlap '(NR - 1) % n <= k - 1'
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

echo "test-prove: $pass passed, $fail failed"
[ "$fail" -eq 0 ]
