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
for a in "$@"; do
  case "$a" in --limit-subp=*) subp=${a#--limit-subp=} ;; esac
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
    echo 'in unit a, 3 subprograms and packages out of 3 analyzed'
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

echo "test-prove: $pass passed, $fail failed"
[ "$fail" -eq 0 ]
