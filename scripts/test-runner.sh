#!/usr/bin/env bash
# The test runner's and the decoder scripts' own failure modes, with the
# real runner:
#
#   1. privacy: nothing a caller supplies is printed back. Each mode of
#      tests/bin/<cell>/test_main is given an absolute path to a missing
#      file under a directory named after a secret, with short (two and
#      three character) synthetic components too, and must fail without
#      printing the path or any component under the temporary directory
#      (components of the temporary directory itself only from four
#      characters, since one-letter system names such as "T" occur in
#      ordinary text); a corpus row with an unknown class is reported
#      without its text; scripts/decoder-tests.sh and
#      scripts/differential.sh print no canary from a path-valued seed
#      list, cost limit or missing interpreter, and no absolute path when
#      a file they generate cannot be written (no traceback); the four
#      build scripts show a failed build's messages without paths; the
#      benchmark prints back no unknown workload; the Python tools print
#      back no argument that is not valid and no field of a malformed row,
#      and the cost model's self-test no traceback of a crashing child;
#   2. no vacuous pass: verdict and status on an empty file, corpus and
#      heads with nothing to compare (empty, or only rows that are not
#      compared), corpus outside the contracts cell (populated with an
#      agreeing row), and an exhaustive file with one byte too many all
#      fail; status with an expected row count fails on a file one row
#      short; both scripts refuse a seed list that is empty after
#      splitting (spaces, tabs, newlines), a seed that is not a decimal
#      number, and a seed whose row counts are not pinned, and fail on a
#      truncated generated corpus whatever the seed's spelling (01);
#      scripts/decoder-tests.sh fails its head-table stage in both cells
#      on a head table cut to one row, and on one with the pinned number
#      of rows but not the pinned number of accepted inputs.
#
# When a case detects a leak it says only "leak detected in <case>" and
# prints nothing of what it captured.
#
# Builds the runner in a plain cell (-O2, language checks) and in the
# contracts cell, where the ghost modes (corpus, exhaustive) run.
#
# Usage: scripts/test-runner.sh
#   ALR, PYTHON   the alr and python3 to use

set -euo pipefail
ALR=${ALR:-alr}
PYTHON=${PYTHON:-python3}
if ! command -v "$ALR" > /dev/null 2>&1; then
  echo "test-runner: alr (ALR) cannot be run"
  exit 2
fi
if ! command -v "$PYTHON" > /dev/null 2>&1; then
  echo "test-runner: the Python interpreter (PYTHON) cannot be run"
  exit 2
fi
python_path=$(command -v "$PYTHON")
cd "$(dirname "$0")"
cd ..
crate=$(pwd -P)
crate_name=${crate##*/}
cd tests
"$ALR" -n build -- -XCBOR_DET_OPT=O2 -XCBOR_DET_CHECKS=lang > /dev/null 2>&1
"$ALR" -n build -- -XCBOR_DET_OPT=O0 -XCBOR_DET_CHECKS=contracts > /dev/null 2>&1
plain=$(pwd -P)/bin/O2-lang/test_main
contracts=$(pwd -P)/bin/O0-contracts/test_main

# The temporary directory has a synthetic name of its own, so that the leak
# check (which looks for every component from it down) cannot mistake an
# ordinary word for a leak.
tmp=$(mktemp -d "${TMPDIR:-/tmp}/zqrunner.XXXXXXXX")
trap 'rm -rf "$tmp"; rm -rf "$crate/tests/obj/decoder/corpus-1.tsv" "$crate/tests/obj/differential/corpus-1.tsv"' EXIT
tmp=$(cd "$tmp" && pwd -P)
tmp_parent=${tmp%/*}
secret_dir="$tmp/zz-secret-dir-$$/Q7z/kQ"
mkdir -p "$secret_dir"
missing="$secret_dir/missing-input-file.tsv"

pass=0
fail=0
ok () { pass=$((pass + 1)); }
# bad CASE: a failure; the first lines of what the case printed follow,
# except any line holding a slash (a path could be in it) or the
# checkout's or the temporary directory's name.
bad () {
  fail=$((fail + 1))
  echo "test-runner FAILED: $1"
  grep -v -e / -e "$crate_name" -e "${tmp##*/}" "$tmp/out" \
    | sed 's/^/    /' | head -n 20 || true
}
# leaked CASE: a failure that printed something private; nothing of the
# capture is shown.
leaked () {
  fail=$((fail + 1))
  echo "test-runner FAILED: leak detected in $1"
}

# leaks_path OUT: OUT holds the missing path, the system's temporary
# directory, or any component from the synthetic temporary directory down
# (of any length: zqrunner.*, zz-secret-dir-*, Q7z, kQ, the file name).
# The system's own components (such as "T" or "tmp") are not looked for
# on their own: they are ordinary words; only as part of a path.
leaks_path () {
  local c rest
  if grep -qF -- "$missing" "$1"; then return 0; fi
  if grep -qF -- "$tmp_parent/" "$1"; then return 0; fi
  rest=${missing#"$tmp_parent"/}
  local IFS=/
  for c in $rest; do
    if [ -n "$c" ] && grep -qF -- "$c" "$1"; then return 0; fi
  done
  return 1
}
# holds OUT TEXT...: OUT holds one of the texts.
holds () {
  local f=$1 t
  shift
  for t in "$@"; do
    if grep -qF -- "$t" "$f"; then return 0; fi
  done
  return 1
}

# why_leak OUT: after a leak is reported, the lines of OUT that hold a
# synthetic canary, the temporary directory or the checkout (at most 8, 200
# characters each), so that a failure on another platform can be read from
# its log. They hold test values only, or the runner's own checkout path.
why_leak () {
  local line shown=0
  while IFS= read -r line || [ -n "$line" ]; do
    case $line in
      *QQ_* | *QQ-BUILD-CANARY* | *"$tmp_parent/"* | *"$crate"*)
        echo "    | ${line:0:200}"
        shown=$((shown + 1))
        if [ "$shown" -ge 8 ]; then break; fi ;;
    esac
  done < "$1"
  if [ "$shown" -eq 0 ]; then echo "    | (no such line)"; fi
}

# why_leak shows the lines that hold a canary (and the temporary directory,
# and the checkout), at most 8, and says when there is none.
{
  for i in 1 2 3 4 5 6 7 8 9 10; do echo "QQ_LOGIN line $i"; done
  echo "unrelated"
} > "$tmp/out"
if [ "$(why_leak "$tmp/out" | grep -c 'QQ_LOGIN line')" -eq 8 ] \
   && ! why_leak "$tmp/out" | grep -q unrelated; then ok; else
  bad "why_leak: not the first 8 lines that hold a canary"
fi
printf 'nothing here\n' > "$tmp/out"
if why_leak "$tmp/out" | grep -qF "(no such line)"; then ok; else
  bad "why_leak: no note that no line holds a canary"
fi

# The leak check itself catches a short component: a stand-in output
# holding only "kQ" is a leak.
printf 'some output\nkQ\n' > "$tmp/out"
if leaks_path "$tmp/out"; then ok; else
  fail=$((fail + 1)); echo "test-runner FAILED: the leak check misses a short component"
fi

# 1. Each mode on a missing file: non-zero, and nothing of the path.
# missing_file RUNNER MODE
missing_file () {
  status=0
  (cd "$tmp" && "$1" "$2" "$missing") > "$tmp/out" 2>&1 || status=$?
  if leaks_path "$tmp/out"; then
    leaked "$2 on a missing file"
  elif [ "$status" -eq 0 ]; then
    bad "$2 on a missing file exits 0"
  else
    ok
  fi
}
missing_file "$plain" verdict
missing_file "$plain" verdict-exhaustive
missing_file "$plain" status
missing_file "$plain" heads
missing_file "$contracts" corpus
missing_file "$contracts" exhaustive

# A corpus row whose predicted count is not a number: a failure, and it
# is written neither to the output nor to the timings file.
printf '00\t1\t1\trun\t/zz-dir/QQ-COUNT-CANARY\n' > "$tmp/count.tsv"
status=0
(cd "$tmp" && "$contracts" corpus "$tmp/count.tsv" "$tmp/times.txt") \
  > "$tmp/out" 2>&1 || status=$?
if holds "$tmp/out" QQ-COUNT-CANARY zz-dir \
   || { [ -f "$tmp/times.txt" ] && holds "$tmp/times.txt" QQ-COUNT-CANARY; }; then
  leaked "corpus with a count that is not a number"
elif [ "$status" -ne 0 ] && grep -q "not a decimal number" "$tmp/out"; then
  ok
else
  bad "corpus with a count that is not a number (exit $status)"
fi

# A corpus row of an unknown class: a failure that does not print it.
printf '00\t1\t1\t/zz-dir/QQ-CLASS-CANARY\t1\n' > "$tmp/class.tsv"
status=0
(cd "$tmp" && "$contracts" corpus "$tmp/class.tsv") > "$tmp/out" 2>&1 || status=$?
if holds "$tmp/out" QQ-CLASS-CANARY zz-dir; then
  leaked "corpus with an unknown class"
elif [ "$status" -ne 0 ] && grep -q "unknown class" "$tmp/out"; then
  ok
else
  bad "corpus with an unknown class (exit $status)"
fi

# 2. Nothing to compare is a failure, saying so.
: > "$tmp/empty.tsv"
printf '\tNONE\nc0\tNONE\nf4\tNONE\n' > "$tmp/heads-none.tsv"
printf '00\t1\t1\trun\t1\n' > "$tmp/agree.tsv"
# A runner whose path holds spaces (a checkout in such a directory) runs:
# every case passes runner, mode and file as separate quoted arguments.
mkdir -p "$tmp/QQ space dir"
cp "$plain" "$tmp/QQ space dir/test_main"
spaced="$tmp/QQ space dir/test_main"
# nothing_compared CELL RUNNER MODE FIXTURE
nothing_compared () {
  status=0
  (cd "$tmp" && "$2" "$3" "$tmp/$4.tsv") > "$tmp/out" 2>&1 || status=$?
  if leaks_path "$tmp/out" || holds "$tmp/out" "QQ space dir"; then
    leaked "$3 ($1) on $4"
  elif [ "$status" -ne 0 ] && grep -q "nothing was compared" "$tmp/out"; then
    ok
  else
    bad "$3 ($1) on $4 (exit $status)"
  fi
}
nothing_compared plain "$plain" verdict empty
nothing_compared plain "$plain" status empty
nothing_compared contracts "$contracts" corpus empty
nothing_compared plain "$plain" heads empty
nothing_compared plain "$plain" heads heads-none
nothing_compared contracts "$contracts" heads heads-none
nothing_compared "plain, path with spaces" "$spaced" verdict empty
# corpus outside the contracts cell, on an agreeing row: refused, naming
# the cell it needs.
status=0
(cd "$tmp" && "$plain" corpus "$tmp/agree.tsv") > "$tmp/out" 2>&1 || status=$?
if [ "$status" -ne 0 ] && grep -q "needs the library's contracts" "$tmp/out"; then
  ok
else
  bad "corpus (O2-lang) on an agreeing row (exit $status)"
fi

# An exhaustive file with one byte too many. Nothing of Python's output is
# shown if it fails (a traceback names files by their absolute path).
if ! "$PYTHON" -B -I reference/exhaustive.py --out "$tmp/exhaustive.bin" \
     > /dev/null 2>&1; then
  echo "test-runner: the exhaustive input file could not be made"
  exit 1
fi
printf '\000' >> "$tmp/exhaustive.bin"
# too_long CELL RUNNER MODE
too_long () {
  status=0
  (cd "$tmp" && "$2" "$3" "$tmp/exhaustive.bin") > "$tmp/out" 2>&1 || status=$?
  if [ "$status" -ne 0 ] && grep -q "more bytes than" "$tmp/out"; then
    ok
  else
    bad "$3 ($1) with one byte too many (exit $status)"
  fi
}
too_long plain "$plain" verdict-exhaustive
too_long contracts "$contracts" verdict-exhaustive
too_long contracts "$contracts" exhaustive

# A status file one row short of the expected count fails.
printf '00\tOk\t1\n01\tOk\t1\n' > "$tmp/short.tsv"
status=0
(cd "$tmp" && "$plain" status "$tmp/short.tsv" 3) > "$tmp/out" 2>&1 || status=$?
if [ "$status" -ne 0 ] && grep -q "expected 3 rows" "$tmp/out"; then
  ok
else
  bad "status with 2 rows where 3 are expected (exit $status)"
fi
status=0
(cd "$tmp" && "$plain" status "$tmp/short.tsv" 2) > "$tmp/out" 2>&1 || status=$?
if [ "$status" -eq 0 ]; then
  ok
else
  bad "status with the expected 2 rows (exit $status)"
fi

# The scripts: bad settings are refused before anything runs, saying what
# kind of setting is wrong and never its value.
# run_script NAME SCRIPT ENV...: runs SCRIPT with the settings; STATUS.
run_script () {
  local script=$2
  shift 2
  status=0
  (cd "$crate" && env "$@" bash "scripts/$script.sh") > "$tmp/out" 2>&1 \
    || status=$?
}
for script in decoder-tests differential; do
  for label in empty blank newline mixed; do
    case $label in
      empty) seeds="" ;;
      blank) seeds="  	 " ;;
      newline) seeds=$'\n' ;;
      mixed) seeds=$' \n\t' ;;
    esac
    run_script "$label" "$script" "CBOR_DET_SEEDS=$seeds"
    if [ "$status" -eq 2 ] && grep -q "no seeds" "$tmp/out" \
       && ! grep -q "sha256" "$tmp/out"; then
      ok
    else
      bad "$script.sh with a seed list that is $label (exit $status)"
    fi
  done
  run_script canary "$script" "CBOR_DET_SEEDS=/zz-dir/QQ-SEED-CANARY"
  if holds "$tmp/out" QQ-SEED-CANARY zz-dir; then
    leaked "$script.sh with a path-valued seed"
  elif [ "$status" -eq 2 ] && grep -q "not a decimal number" "$tmp/out"; then
    ok
  else
    bad "$script.sh with a path-valued seed (exit $status)"
  fi
  run_script unpinned "$script" "CBOR_DET_SEEDS=1 4"
  if [ "$status" -eq 2 ] && grep -q "supported seeds" "$tmp/out" \
     && ! grep -q "sha256" "$tmp/out"; then
    ok
  else
    bad "$script.sh with a seed whose counts are not pinned (exit $status)"
  fi
  run_script python "$script" "PYTHON=/zz-dir/QQ-PY-CANARY/python3"
  if holds "$tmp/out" QQ-PY-CANARY zz-dir; then
    leaked "$script.sh with a missing PYTHON"
  elif [ "$status" -eq 2 ] && grep -q "PYTHON" "$tmp/out"; then
    ok
  else
    bad "$script.sh with a missing PYTHON (exit $status)"
  fi
  run_script alr "$script" "ALR=/zz-dir/QQ-ALR-CANARY/alr"
  if holds "$tmp/out" QQ-ALR-CANARY zz-dir; then
    leaked "$script.sh with a missing ALR"
  elif [ "$status" -eq 2 ] && grep -q "ALR" "$tmp/out"; then
    ok
  else
    bad "$script.sh with a missing ALR (exit $status)"
  fi
done
for script in matrix decoder-measure prove; do
  run_script alr "$script" "ALR=/zz-dir/QQ-ALR-CANARY/alr"
  if holds "$tmp/out" QQ-ALR-CANARY zz-dir; then
    leaked "$script.sh with a missing ALR"
  elif [ "$status" -eq 2 ] && grep -q "ALR" "$tmp/out"; then
    ok
  else
    bad "$script.sh with a missing ALR (exit $status)"
  fi
done
for limit in CBOR_DET_DECODER_COST_LIMIT:decoder-tests \
             CBOR_DET_COST_LIMIT:differential; do
  run_script limit "${limit#*:}" "${limit%%:*}=/zz-dir/QQ-LIMIT-CANARY"
  if holds "$tmp/out" QQ-LIMIT-CANARY zz-dir; then
    leaked "${limit#*:}.sh with a path-valued cost limit"
  elif [ "$status" -eq 2 ] && grep -q "not a decimal number" "$tmp/out"; then
    ok
  else
    bad "${limit#*:}.sh with a path-valued cost limit (exit $status)"
  fi
done

# A generated file that cannot be written (its name is a directory): the
# script fails, printing no absolute path and no traceback.
for case in decoder-tests:decoder differential:differential; do
  script=${case%%:*}
  dir="$crate/tests/obj/${case#*:}"
  rm -rf "$dir/corpus-1.tsv"
  mkdir -p "$dir/corpus-1.tsv"
  run_script directory "$script" "CBOR_DET_SEEDS=1" "CBOR_DET_NO_HUGE=1"
  rm -rf "$dir/corpus-1.tsv"
  if holds "$tmp/out" "$crate" "$HOME" "Traceback" 'File "/'; then
    leaked "$script.sh with an unwritable generated file"
  elif [ "$status" -ne 0 ]; then
    ok
  else
    bad "$script.sh with an unwritable generated file (exit $status)"
  fi
done

# A truncated generated corpus fails whatever the seed's spelling: a
# Python stand-in that runs the real one, then cuts the reference's
# corpus to one row.
cat > "$tmp/truncating-python" <<EOF
#!/bin/sh
"$python_path" "\$@" || exit \$?
for a in "\$@"; do
  case "\$a" in reference/ref_cbor_det.py) seen=yes ;; esac
done
if [ "\${seen:-}" = yes ]; then
  out=""
  prev=""
  for a in "\$@"; do
    if [ "\$prev" = --out ]; then out=\$a; fi
    prev=\$a
  done
  case " \$* " in *" corpus "*) printf '00\t1\t1\n' > "\$out" ;; esac
fi
EOF
chmod +x "$tmp/truncating-python"
for script in decoder-tests differential; do
  run_script truncated "$script" "CBOR_DET_SEEDS=01" \
    "PYTHON=$tmp/truncating-python" "CBOR_DET_NO_HUGE=1"
  if [ "$status" -ne 0 ] && grep -q "rows, expected" "$tmp/out"; then
    ok
  else
    bad "$script.sh with seed 01 and a truncated corpus (exit $status)"
  fi
done

# The decoder tests' head table: cut to one row, and with its 67 705 rows
# all one accepted input (the row count as pinned, the count of accepted
# inputs not), it fails the stage in both cells. A Python stand-in runs
# the real one, then rewrites the generated table as HEAD_TABLE_FORM says.
cat > "$tmp/head-table-python" <<EOF
#!/bin/sh
"$python_path" "\$@" || exit \$?
for a in "\$@"; do
  case "\$a" in
    */head-table.tsv)
      if [ "\$HEAD_TABLE_FORM" = one-row ]; then
        printf '00\t1\t1\n' > "\$a"
      else
        i=0
        while [ \$i -lt 67705 ]; do printf '00\t1\t1\n'; i=\$((i + 1)); done > "\$a"
      fi ;;
  esac
done
EOF
chmod +x "$tmp/head-table-python"
for form in one-row all-accepted; do
  run_script "head-table-$form" decoder-tests "CBOR_DET_SEEDS=1" \
    "PYTHON=$tmp/head-table-python" "CBOR_DET_NO_HUGE=1" \
    "HEAD_TABLE_FORM=$form"
  if [ "$form" = one-row ]; then
    want="rows, expected 67705 rows"
  else
    want="did not compare the known counts"
  fi
  if [ "$status" -ne 0 ] && grep -q "$want" "$tmp/out" \
     && grep -q "FAILED: the head table in the plain cell" "$tmp/out" \
     && grep -q "FAILED: the head table in the contracts cell" "$tmp/out"; then
    ok
  else
    bad "decoder-tests.sh with a head table $form: not failed in both cells (exit $status)"
  fi
done

# A tool that passes "command -v" but cannot start (its interpreter is
# missing): the scripts say which tool could not start and its exit
# status, and print nothing of what the shell said about it.
mkdir -p "$tmp/QQ-SHEBANG-CANARY"
printf '#!/zz-dir/QQ-INTERP-CANARY/sh\n' > "$tmp/QQ-SHEBANG-CANARY/tool"
chmod +x "$tmp/QQ-SHEBANG-CANARY/tool"
for case in matrix:ALR decoder-measure:ALR decoder-tests:ALR differential:ALR \
            decoder-tests:PYTHON differential:PYTHON; do
  script=${case%%:*}
  var=${case#*:}
  run_script shebang "$script" "$var=$tmp/QQ-SHEBANG-CANARY/tool"
  if holds "$tmp/out" QQ-SHEBANG-CANARY QQ-INTERP-CANARY zz-dir "$tmp_parent/"; then
    leaked "$script.sh with an $var that cannot start"
  elif [ "$status" -ne 0 ] && grep -q "could not start" "$tmp/out"; then
    ok
  else
    bad "$script.sh with an $var that cannot start (exit $status)"
  fi
done

# A copy of the crate, in a directory whose name holds spaces and a
# canary, with a reference file missing: the scripts fail, and print no
# absolute path, no canary and no Python exception message (only its
# type).
copy="$tmp/QQ-COPY-CANARY dir/cbor_det"
mkdir -p "$copy"
(cd "$crate" && tar cf - --exclude ./.git --exclude ./obj --exclude ./lib \
   --exclude ./bin --exclude ./tests/obj --exclude ./tests/lib \
   --exclude ./tests/bin .) | (cd "$copy" && tar xf -)
mv "$copy/tests/reference/cost_model.py" "$copy/tests/reference/cost_model.away"
for script in differential decoder-tests; do
  status=0
  (cd "$copy" && env CBOR_DET_SEEDS=1 CBOR_DET_NO_HUGE=1 \
     bash "scripts/$script.sh") > "$tmp/out" 2>&1 || status=$?
  if holds "$tmp/out" QQ-COPY-CANARY "$tmp_parent/" "$crate" "cost_model.py'" \
       "No such file"; then
    leaked "$script.sh with a reference file missing"
  elif [ "$status" -ne 0 ] && grep -q "^python: FileNotFoundError" "$tmp/out"; then
    ok
  else
    bad "$script.sh with a reference file missing (exit $status)"
  fi
done

# A build that fails: each script shows the compiler's messages (the
# build log's lines of a known form, none holding a path), from
# a copy of the crate in a directory named after a canary, with a test
# unit broken.
broken="$tmp/QQ-BUILD-CANARY dir/cbor_det"
mkdir -p "$broken"
(cd "$crate" && tar cf - --exclude ./.git --exclude ./obj --exclude ./lib \
   --exclude ./bin --exclude ./tests/obj --exclude ./tests/lib \
   --exclude ./tests/bin .) | (cd "$broken" && tar xf -)
printf 'procedure Broken_Unit is\nbegin\n   Undefined_Name_QQ;\nend Broken_Unit;\n' \
  > "$broken/tests/src/broken_unit.adb"
printf 'with Broken_Unit;\n' | cat - "$broken/tests/src/test_main.adb" \
  > "$broken/tests/src/test_main.new"
mv "$broken/tests/src/test_main.new" "$broken/tests/src/test_main.adb"
# The same with a unit of the library broken, in a second copy: its file
# name carries the crate's name, which is also the checkout's.
broken_src="$tmp/QQ-BUILD-CANARY dir/src-case/cbor_det"
mkdir -p "$broken_src"
(cd "$broken" && tar cf - --exclude ./tests/src/broken_unit.adb .) \
  | (cd "$broken_src" && tar xf -)
cp "$crate/tests/src/test_main.adb" "$broken_src/tests/src/test_main.adb"
printf 'Undefined_Name_QQ;\n' >> "$broken_src/src/cbor_det-decoder.adb"
for case in "$broken|broken_unit.adb" "$broken_src|cbor_det-decoder.adb"; do
  copy=${case%|*}
  unit=${case#*|}
  for script in matrix decoder-measure decoder-tests differential; do
    status=0
    (cd "$copy" && env CBOR_DET_SEEDS=1 bash "scripts/$script.sh") \
      > "$tmp/out" 2>&1 || status=$?
    if holds "$tmp/out" QQ-BUILD-CANARY "$tmp_parent/" "$crate"; then
      leaked "$script.sh with $unit broken"
    elif [ "$status" -ne 0 ] && grep -q "error" "$tmp/out" \
         && grep -qF "$unit" "$tmp/out"; then
      ok
    else
      bad "$script.sh with $unit broken: no compiler message shown (exit $status)"
    fi
  done
done

# The build-log filter is the same function in the four scripts.
: > "$tmp/out"
same=yes
for script in matrix decoder-measure decoder-tests differential; do
  sed -n '/^# --- build_failure_lines: begin/,/^# --- build_failure_lines: end ---$/p' \
    "$crate/scripts/$script.sh" > "$tmp/filter-$script.sh"
  if ! grep -q '^build_failure_lines () {$' "$tmp/filter-$script.sh" \
     || ! cmp -s "$tmp/filter-matrix.sh" "$tmp/filter-$script.sh"; then
    same=no
  fi
done
if [ "$same" = yes ]; then ok; else
  bad "the build-log filter differs between the four scripts"
fi

# filter_case DIR LOG: the filter (matrix.sh's copy) on LOG, run from
# DIR/tests of a stand-in checkout, into $tmp/out.
filter_case () {
  (cd "$1/tests" && bash -c 'source "$1"; build_failure_lines "$2"' \
     filter "$tmp/filter-matrix.sh" "$2") > "$tmp/out" 2>&1 || true
}
# kept_lines: the number of log lines the filter printed.
kept_lines () {
  grep '^    ' "$tmp/out" | grep -vc '^    (none: ' || true
}
# A stand-in checkout per name: the crate's own file names, empty.
stand_in () {
  local d="$tmp/fc/$1" f
  mkdir -p "$d/src" "$d/tests/src"
  for f in "$crate"/src/*; do : > "$d/src/${f##*/}"; done
  for f in "$crate"/tests/src/*; do : > "$d/tests/src/${f##*/}"; done
  : > "$d/cbor_det.gpr"
  : > "$d/tests/cbor_det_tests.gpr"
}

# Every injected form below, in checkouts named cbor_det, cbor, det,
# cbor_det_PRIVATE, PRIVATE_cbor_det and CBOR_DET: no line is kept but
# the public library unit's message, which is kept in every one.
# Drive letter and UNC paths are spelt with variables, so that this file
# holds none.
colon=:
bs='\'
filter_payloads=(
  'posix|error: "/QQ_PARENT/cbor_det/unit.adb": missing'
  "drive|error: \"C${colon}\\QQ_PARENT\\cbor_det\\unit.adb\": missing"
  'rooted|error: "\QQ_PARENT\cbor_det\unit.adb": missing'
  "unc|error: \"${bs}${bs}QQ_HOST${bs}QQ_SHARE${bs}unit.adb\": missing"
  'relative|error: "QQ_PARENT\unit.adb": missing'
  'bare|error: "QQ_LOGIN" not found'
  'host|connection to QQ_HOST failed'
  'fileline|QQ_LOGIN.adb:12:3: error: missing declaration'
  'public|cbor_det-decoder.adb:12:3: error: missing declaration'
  'split|error at /QQ_PARENT/'
  'long|'
  'case|CBOR_DET_PRIVATE.adb:12:3: error: missing'
  'prefix|cbor_det_PRIVATE.adb:12:3: error: missing'
  'suffix|PRIVATE_cbor_det.adb:12:3: error: missing'
  'cause-slash|unit.adb:1:1: error: operator "/" is not visible'
)
for name in cbor_det cbor det cbor_det_PRIVATE PRIVATE_cbor_det CBOR_DET; do
  stand_in "$name"
  for entry in "${filter_payloads[@]}"; do
    label=${entry%%|*}
    payload=${entry#*|}
    log="$tmp/fc/$name/tests/log.txt"
    case $label in
      split) printf '%s\nQQ_LOGIN\nunit.adb\n' "$payload" > "$log" ;;
      long)
        { printf '/QQ_PARENT/'
          printf '%*s' 100000 '' | tr ' ' x
          printf 'QQ_LOGIN\n'; } > "$log" ;;
      *) printf '%s\n' "$payload" > "$log" ;;
    esac
    filter_case "$tmp/fc/$name" "$log"
    if [ "$label" = public ]; then
      if grep -qxF "    $payload" "$tmp/out" && [ "$(kept_lines)" -eq 1 ]; then
        ok
      else
        bad "filter, checkout $name: the library unit's message is not shown"
      fi
    elif holds "$tmp/out" QQ_ PRIVATE CBOR_DET unit.adb xxxxxxxxxx \
         || [ "$(kept_lines)" -ne 0 ]; then
      leaked "filter, checkout $name, form $label"
    else
      ok
    fi
  done
done

# Forms of the filter itself, in the checkout named cbor_det.
fc="$tmp/fc/cbor_det"
log="$fc/tests/log.txt"
# The cause first, then 300 progress lines: the cause is shown.
{ echo "cbor_det-decoder.adb:309:01: error: end of file expected"
  for i in $(seq 1 300); do echo "   [Ada]          cbor_det-decoder.adb"; done
} > "$log"
filter_case "$fc" "$log"
if grep -qF "cbor_det-decoder.adb:309:01: error: end of file expected" "$tmp/out"
then ok; else
  bad "filter: a cause followed by 300 progress lines is not shown"
fi
# 45 messages: the first 40 only.
for i in $(seq 1 45); do echo "support.adb:$i:1: error: message $i"; done > "$log"
filter_case "$fc" "$log"
if [ "$(kept_lines)" -eq 40 ] && grep -qx "    support.adb:1:1: error: message 1" "$tmp/out" \
   && grep -qx "    support.adb:40:1: error: message 40" "$tmp/out" \
   && ! grep -q "message 41" "$tmp/out"; then
  ok
else
  bad "filter: not the first 40 of 45 messages"
fi
# Windows line ends: the message is kept, without its carriage return.
printf 'support.adb:3:1: error: crlf\r\n' > "$log"
filter_case "$fc" "$log"
if grep -qx "    support.adb:3:1: error: crlf" "$tmp/out"; then ok; else
  bad "filter: a message with a Windows line end is not shown"
fi
# Kept forms: compilation of a unit, processing of a project, fixed lines.
printf '%s\n' "   compilation of support.adb failed" \
  'gprbuild: "cbor_det_tests.gpr" processing failed' \
  "gprbuild: *** compilation phase failed" \
  "gprbuild: *** post compilation phase failed" \
  "gprbuild: *** link phase failed" "ERROR: Compilation failed." > "$log"
filter_case "$fc" "$log"
if [ "$(kept_lines)" -eq 6 ]; then ok; else
  bad "filter: a fixed failure line is not shown"
fi
# Dropped forms: names that are not the crate's own (also by case only),
# a control character, a tab, a message on a line of its own.
printf '%s\n' "   compilation of QQ_LOGIN.adb failed" \
  'gprbuild: "QQ_LOGIN.gpr" processing failed' \
  "SUPPORT.adb:1:1: error: QQ_LOGIN" "support.ads.adb:1:1: error: QQ_LOGIN" \
  "support.adb:1:1: error: $(printf '\033')[31mQQ_LOGIN" \
  "support.adb:1:1: error: $(printf '\t')QQ_LOGIN" \
  "error: QQ_LOGIN" "gprbuild: *** QQ_LOGIN failed" "QQ_LOGIN" > "$log"
filter_case "$fc" "$log"
if holds "$tmp/out" QQ_LOGIN || [ "$(kept_lines)" -ne 0 ]; then
  leaked "filter: a line of no known form"
elif grep -q "(none: " "$tmp/out"; then
  ok
else
  bad "filter: no note that nothing was kept"
fi

# The real tools, in a copy under a canary directory, with a value a caller
# gave a project setting. The one form that prints it back (the known
# limit, in the scripts' headers and the README) is gprbuild's message on
# a typed string; a message holding a slash or a backslash is not shown,
# and alr's fixed line on the failure is.
real="$tmp/QQ-BUILD-CANARY dir/real/cbor_det"
mkdir -p "$real"
(cd "$crate" && tar cf - --exclude ./.git --exclude ./obj --exclude ./lib \
   --exclude ./bin --exclude ./tests/obj --exclude ./tests/lib \
   --exclude ./tests/bin .) | (cd "$real" && tar xf -)
# gprbuild words the echo by platform: an "error: " prefix, the name's
# case, and a second line about the library kind (seen on Windows).
residual='^ *cbor_det\.gpr:[0-9]+:[0-9]+: (error: )?(value "QQ_LOGIN" is illegal for typed string "[Ll]ibrary_[Tt]ype"|[Vv]alue QQ_LOGIN is invalid for attribute [Ll]ibrary_[Kk]ind)$'
printf '%s\n' \
  '    cbor_det.gpr:13:04: value "QQ_LOGIN" is illegal for typed string "library_type"' \
  '    cbor_det.gpr:13:04: error: value "QQ_LOGIN" is illegal for typed string "Library_Type"' \
  '    cbor_det.gpr:16:08: error: Value QQ_LOGIN is invalid for attribute Library_Kind' > "$tmp/forms"
if [ "$(grep -cE "$residual" "$tmp/forms")" -eq 3 ]; then ok; else
  bad "the known gprbuild forms are not all accepted"
fi
printf '%s\n' \
  'cbor_det.gpr:13:04: value "QQ_LOGIN" is illegal for typed string "other"' \
  'other.gpr:13:04: value "QQ_LOGIN" is illegal for typed string "library_type"' \
  'cbor_det.gpr:13:04: error: Value QQ_LOGIN is invalid for attribute Library_Kind in /QQ_PARENT/x' \
  'cbor_det.gpr:13:04: value "QQ_LOGIN/x" is illegal for typed string "library_type"' > "$tmp/forms"
if [ "$(grep -cE "$residual" "$tmp/forms")" -eq 0 ]; then ok; else
  bad "a form other than the known ones is accepted"
fi
for setting in CBOR_DET_LIBRARY_TYPE LIBRARY_TYPE; do
  for script in matrix decoder-measure decoder-tests differential; do
    if [ "$setting" = LIBRARY_TYPE ] && [ "$script" != matrix ]; then
      continue
    fi
    status=0
    (cd "$real" && env -u CBOR_DET_LIBRARY_TYPE -u LIBRARY_TYPE \
       "$setting=QQ_LOGIN" CBOR_DET_SEEDS=1 bash "scripts/$script.sh") \
      > "$tmp/out" 2>&1 || status=$?
    if holds "$tmp/out" QQ-BUILD-CANARY "$tmp_parent/" "$crate" \
       || grep "QQ_LOGIN" "$tmp/out" | grep -qvE "$residual"; then
      leaked "$script.sh with $setting set: a form other than the known one"
      why_leak "$tmp/out"
    elif [ "$status" -ne 0 ] && grep -qE "$residual" "$tmp/out"; then
      ok
    else
      bad "$script.sh with $setting set: not the known message (exit $status)"
    fi
  done
done
for value in '\QQ_PARENT\cbor_det\unit.adb' \
             "${bs}${bs}QQ_HOST${bs}QQ_SHARE${bs}unit.adb" \
             "C${colon}\\QQ_PARENT\\cbor_det" '/QQ_PARENT/QQ_LOGIN' \
             'cbor_det_QQ_LOGIN/x'; do
  status=0
  (cd "$real" && env -u LIBRARY_TYPE "CBOR_DET_LIBRARY_TYPE=$value" \
     bash scripts/matrix.sh) > "$tmp/out" 2>&1 || status=$?
  if holds "$tmp/out" QQ_ QQ-BUILD-CANARY "$tmp_parent/" "$crate"; then
    leaked "matrix.sh with a path in CBOR_DET_LIBRARY_TYPE"
    why_leak "$tmp/out"
  elif [ "$status" -ne 0 ] \
       && grep -qx "    ERROR: Compilation failed." "$tmp/out"; then
    ok
  else
    bad "matrix.sh with a path in CBOR_DET_LIBRARY_TYPE (exit $status)"
  fi
done

# The benchmark's stack mode given an unknown workload: a fixed message.
status=0
"${plain%/*}/bench_main" stack "$missing" > "$tmp/out" 2>&1 || status=$?
if leaks_path "$tmp/out"; then
  leaked "bench_main stack with an unknown workload"
elif [ "$status" -ne 0 ] && grep -qx "bench: unknown workload" "$tmp/out"; then
  ok
else
  bad "bench_main stack with an unknown workload (exit $status)"
fi

# The Python tools. The cost model's self-test with its classifier made to
# crash (a message of two lines), in a copy under a canary directory: it
# fails, and names the child's exception only, never its traceback (which
# names files by their absolute path) or its message.
pycopy="$tmp/QQ-COST-CANARY dir/kq"
mkdir -p "$pycopy"
awk '{ print } /^def classify\(/ { print "    raise ValueError(\"boom\\nQQ_WORD\")" }' \
  "$crate/tests/reference/cost_model.py" > "$pycopy/cost_model.py"
status=0
"$PYTHON" -B -I "$pycopy/cost_model.py" selftest > "$tmp/out" 2>&1 \
  || status=$?
if holds "$tmp/out" QQ- QQ_WORD "kq/" "$tmp_parent/" "${tmp##*/}" "$crate"
then
  leaked "cost_model.py selftest with a crashing child"
elif [ "$status" -ne 0 ] && grep -qx "    its exception: ValueError" "$tmp/out"
then
  ok
else
  bad "cost_model.py selftest with a crashing child (exit $status)"
fi

# A row whose first field is a path: the status oracle's classify names
# the line, never the field (which it would print in lower case).
printf '/QQ_PARENT/QQ_LOGIN\t1\t1\n' > "$tmp/bad-row.tsv"
status=0
"$PYTHON" -B -I reference/ref_status.py classify --in "$tmp/bad-row.tsv" \
  --out "$tmp/bad-row.out" > "$tmp/out" 2>&1 || status=$?
if grep -qi "qq_" "$tmp/out"; then
  leaked "ref_status.py classify on a row that is not hex"
elif [ "$status" -ne 0 ] && grep -q "^line 1: " "$tmp/out"; then
  ok
else
  bad "ref_status.py classify on a row that is not hex (exit $status)"
fi

# The cost model on a malformed corpus row and a malformed timing row: the
# row's number, never its text.
printf '00\t/QQ_PARENT/QQ_LOGIN\t1\n' > "$tmp/bad-corpus.tsv"
printf '/QQ_PARENT/QQ_LOGIN\t0.2\n10\t0.1\n' > "$tmp/bad-timings.txt"
for mode in classify validate; do
  status=0
  if [ "$mode" = classify ]; then
    "$PYTHON" -B -I reference/cost_model.py classify \
      --in "$tmp/bad-corpus.tsv" --out "$tmp/bad-corpus.out" --limit 10 \
      > "$tmp/out" 2>&1 || status=$?
    want="cost_model: malformed corpus row 1"
  else
    "$PYTHON" -B -I reference/cost_model.py validate \
      --timings "$tmp/bad-timings.txt" > "$tmp/out" 2>&1 || status=$?
    want="cost_model: malformed timing row 1"
  fi
  if holds "$tmp/out" QQ_ "$tmp_parent/" "$crate"; then
    leaked "cost_model.py $mode on a malformed row"
  elif [ "$status" -ne 0 ] && grep -qx "$want" "$tmp/out"; then
    ok
  else
    bad "cost_model.py $mode on a malformed row (exit $status)"
  fi
done

# Arguments that are not valid, holding a path: every tool fails with a
# fixed message.
canary=/QQ_PARENT/QQ_LOGIN
py_arguments () {
  local tool=$1
  shift
  status=0
  "$PYTHON" -B -I "reference/$tool" "$@" > "$tmp/out" 2>&1 || status=$?
  if holds "$tmp/out" QQ_; then
    leaked "$tool with arguments that are not valid"
  elif [ "$status" -eq 2 ] \
       && grep -qx "$tool: the arguments are not valid (see --help)" "$tmp/out"
  then
    ok
  else
    bad "$tool with arguments that are not valid (exit $status)"
  fi
}
py_arguments ref_cbor_det.py corpus --seed "$canary" --out "$tmp/unused"
py_arguments ref_cbor_det.py "$canary"
py_arguments ref_status.py corpus --seed "$canary" --out "$tmp/unused"
py_arguments ref_status.py classify --in "$tmp/unused" "$canary"
py_arguments cost_model.py classify --in "$tmp/unused" --out "$tmp/unused" \
  --limit "$canary"
py_arguments boundary.py --out "$tmp/unused" "$canary"
py_arguments exhaustive.py --out "$tmp/unused" "$canary"

# A head table of one comparable head among rows that are not compared
# (67 705 rows, as pinned): the differential's count of comparisons fails
# it. A Python stand-in rewrites the table after the real one is made.
cat > "$tmp/heads-python" <<EOF
#!/bin/sh
"$python_path" "\$@" || exit \$?
case " \$* " in
  *" reference/ref_cbor_det.py heads "*)
    prev=""
    for a in "\$@"; do
      if [ "\$prev" = --out ]; then out=\$a; fi
      prev=\$a
    done
    { printf '00\t0\t0\t1\n'; i=1
      while [ \$i -lt 67705 ]; do printf 'c0\tNONE\n'; i=\$((i + 1)); done
    } > "\$out" ;;
esac
EOF
chmod +x "$tmp/heads-python"
run_script heads-one differential "CBOR_DET_SEEDS=1" "PYTHON=$tmp/heads-python"
if [ "$status" -ne 0 ] && grep -q "heads compared" "$tmp/out"; then
  ok
else
  bad "differential.sh with a head table of one comparable head (exit $status)"
fi

echo "test-runner: $pass passed, $fail failed"
[ "$fail" -eq 0 ]
