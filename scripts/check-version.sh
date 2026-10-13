#!/usr/bin/env bash
# Adapted from the scripts of the blake2b crate; to be replaced by the shared gates when that repository exists.
# Version consistency: alire.toml, tests/alire.toml and CHANGELOG.md agree.
#
#   x.y.z-dev  CHANGELOG.md's first section is "## Unreleased"
#   x.y.z      CHANGELOG.md's first section is "## x.y.z - YYYY-MM-DD",
#              with an ASCII hyphen (the crate's files are ASCII; an em
#              dash is refused)
#
# scripts/test-version.sh tests it.
# Usage: scripts/check-version.sh

set -euo pipefail
cd "$(dirname "$0")/.."

# The first quoted value of the version assignment; anything after it (a
# trailing comment, even one holding a quoted string) is ignored.
version_of () {
  grep -m1 -E '^version *= *"' "$1" | sed -E 's/^version *= *"([^"]*)".*/\1/'
}

lib=$(version_of alire.toml)
tests=$(version_of tests/alire.toml)
top=$(grep -m1 -E '^## ' CHANGELOG.md)

fail=0
if [ "$lib" != "$tests" ]; then
  echo "alire.toml is $lib but tests/alire.toml is $tests"
  fail=1
fi
case "$lib" in
  *-dev)
    if [ "$top" != "## Unreleased" ]; then
      echo "version $lib is a development version; CHANGELOG.md must start"
      echo "with \"## Unreleased\", not \"$top\""
      fail=1
    fi
    ;;
  *)
    if ! grep -qE "^## ${lib//./\\.} - [0-9]{4}-[0-9]{2}-[0-9]{2}$" <<< "$top"
    then
      echo "version $lib: CHANGELOG.md must start with \"## $lib - YYYY-MM-DD\" (an ASCII hyphen),"
      echo "not \"$top\""
      fail=1
    fi
    ;;
esac

if [ "$fail" -eq 0 ]; then
  echo "version: $lib consistent"
else
  exit 1
fi
