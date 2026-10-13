#!/usr/bin/env bash
# Exercise scripts/check-version.sh on small crates: versions that agree
# with a dated release heading in ASCII pass; an em dash (or any other
# separator) in the heading, versions that disagree, a missing date, and
# a development version without "## Unreleased" are each refused with a
# message saying what is expected. A trailing comment after the version
# is ignored, even one holding a quoted string.
#
# Usage: scripts/test-version.sh
#        TEST_BASH=/path/to/bash scripts/test-version.sh

set -euo pipefail
cd "$(dirname "$0")"
cd ..
TEST_BASH=${TEST_BASH:-/bin/bash}

tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT
emdash=$(printf '\342\200\224')

pass=0
fail=0
# check NAME LIB_VERSION TESTS_VERSION HEADING EXPECTED_STATUS EXPECTED_TEXT
# A version given as a bare value is written as version = "VALUE"; one
# given with a leading = is written as the rest of the line, as is.
version_line () {
  case "$1" in
    =*) printf 'version %s\n' "$1" ;;
    *) printf 'version = "%s"\n' "$1" ;;
  esac
}

check () {
  local name=$1 lib=$2 tests=$3 heading=$4 want=$5 text=$6 status=0
  local d="$tmp/$name"
  mkdir -p "$d/scripts" "$d/tests"
  cp scripts/check-version.sh "$d/scripts/"
  { printf 'name = "x"\n'; version_line "$lib"; } > "$d/alire.toml"
  { printf 'name = "x_tests"\n'; version_line "$tests"; } > "$d/tests/alire.toml"
  printf '# Changelog\n\n%s\n\n- a change\n' "$heading" > "$d/CHANGELOG.md"
  "$TEST_BASH" "$d/scripts/check-version.sh" > "$d/output" 2>&1 || status=$?
  if [ "$status" -eq "$want" ] && grep -qF -- "$text" "$d/output"; then
    pass=$((pass + 1))
  else
    fail=$((fail + 1))
    echo "test-version FAILED: $name (exit $status, expected $want and \"$text\"):"
    sed 's/^/    /' "$d/output"
  fi
}

check ascii-heading 1.2.3 1.2.3 "## 1.2.3 - 2026-01-02" 0 "version: 1.2.3 consistent"
check em-dash-heading 1.2.3 1.2.3 "## 1.2.3 $emdash 2026-01-02" 1 \
  "must start with \"## 1.2.3 - YYYY-MM-DD\" (an ASCII hyphen)"
check no-date 1.2.3 1.2.3 "## 1.2.3" 1 "must start with \"## 1.2.3 - YYYY-MM-DD\""
check other-version 1.2.3 1.2.3 "## 1.2.4 - 2026-01-02" 1 "must start with"
check versions-differ 1.2.3 1.2.4 "## 1.2.3 - 2026-01-02" 1 \
  "alire.toml is 1.2.3 but tests/alire.toml is 1.2.4"
check dev-unreleased 1.3.0-dev 1.3.0-dev "## Unreleased" 0 "version: 1.3.0-dev consistent"
check dev-dated 1.3.0-dev 1.3.0-dev "## 1.3.0-dev - 2026-01-02" 1 "with \"## Unreleased\""
# A trailing TOML comment holding a quoted string is not the version.
check comment-is-not-the-version '= "1.2.3" # "2.0.0"' '= "9.9.9" # "2.0.0"' \
  "## 2.0.0 - 2026-01-02" 1 "alire.toml is 1.2.3 but tests/alire.toml is 9.9.9"
check trailing-comment-tolerated '= "1.2.3"   # the release' '= "1.2.3" # x' \
  "## 1.2.3 - 2026-01-02" 0 "version: 1.2.3 consistent"

echo "test-version: $pass passed, $fail failed"
[ "$fail" -eq 0 ]
