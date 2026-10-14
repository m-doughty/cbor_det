#!/usr/bin/env bash
# Leakage gate: nothing in the repository may name the machine it was
# written on, or the private workspace around it. Every file of the crate
# is scanned (see gate-common.sh for the inventory, the modes and the
# checks every file passes first: no links, known kinds only, no names
# Windows cannot hold, UTF-8 only), file names included, and this script
# with them. Refused, in every file unless stated:
#
#   absolute paths, every family in any case: macOS and Linux home
#       directories (with slashes, or rooted with backslashes and no
#       drive), macOS volumes, the process file system, Cygwin and WSL
#       drive mounts, MSYS drive paths (a slash, one letter from c to z,
#       a slash and any non-space character, after a boundary or a
#       colon), forward-slash UNC paths (two slashes, a host, a slash and
#       a share, after a boundary or a colon that does not end a URL
#       scheme), file URLs, any drive-qualified Windows path (a drive
#       letter, a colon, then a slash or backslash), Windows UNC paths
#       (two backslashes, a server, a backslash, a share; $ allowed, so
#       WSL paths are caught) and Windows extended-length and device
#       prefixes. A boundary is the start of a line or any character that
#       is not a letter, a digit, /, ., +, - or :, so Markdown emphasis,
#       tables, links and code spans are covered while a URL and a/b are
#       not;
#   per-user paths: macOS private and per-user temporary directories, a
#       temporary directory whose first component ends in a numeric user
#       id, and absolute paths under run/user/N, media/NAME,
#       run/media/NAME and the root user's home directory (each starting
#       with a slash not preceded by a letter, digit, dot, hyphen or
#       underscore);
#   references to private notes: the bare word naming their vault (any
#       case, as a whole word), record names (t or d and four digits, as
#       a word or followed by a hyphen and a letter), question ids (a
#       name, a slash, Q and digits), ticket and decision numbers (T or D
#       followed by any digits) in prose only, and Obsidian wikilinks.
#       Prose is the whole of Markdown, text, LICENSE, YAML, git
#       configuration, shell and Python files (shell and Python files are
#       not parsed: a T or D number anywhere in one is refused, in code
#       as in comments and strings), the comments of Ada-family
#       files (an Ada identifier of T or D and digits passes in code;
#       string literals in Ada are not prose for this rule), and the
#       comments and string literals of TOML and JSON files. One
#       exemption: a T or D and a single digit, one space from another
#       two-character upper-case hex token, is a hex byte as RFC 8949
#       writes CBOR (D9 D9 F7 passes; a lone D and digit, or one followed
#       by a full stop, does not; lower-case hex neighbours do not
#       exempt). A wikilink is two
#       opening square brackets, one or more characters that are not
#       square brackets and include a letter, two closing square
#       brackets; it is looked for in the same prose, plus Ada string
#       literals, so a TOML table header or a JSON array in code passes.
#       In Markdown code spans and fenced blocks, where [[ is usually
#       code, only a wikilink whose target looks like a note name is
#       refused: a letter, then letters, digits, hyphens or underscores,
#       then optionally | or # and any text. So in code a link to a
#       note, with or without an alias or a heading, is refused, and so
#       is a single bare word in double brackets, such as the boolean
#       true (a stated limit); a nested list of numbers, a list of quoted
#       strings, a nested CBOR array and a shell test pass. In shell
#       files, where [[ starts a test and [[: a POSIX class, and in
#       Python files, where [[ opens a nested list or a subscript, only
#       the plain form is caught: a letter, digit, hyphen or underscore
#       right after the brackets and no white space before the closing
#       ones; a wikilink written with spaces inside, in a shell or Python
#       file, is not caught;
#   zero-width and format characters (U+200B, U+200C, U+200D, U+2060, any
#       other format character, and U+FEFF anywhere but as the byte order
#       mark at the start). An emoji joined with U+200D (a zero-width
#       joiner sequence) is refused too: a stated limit. Look-alike
#       letters from other scripts in prose are out of scope;
#   a parent-directory step (two dots, then a slash or backslash), except
#       for the exact references listed in the scanner, each in the one
#       file it belongs to; so no committed file holds a path to a
#       directory beside the crate;
#   an inventory with no file to scan, in every mode.
#
# File names get the path rules, the private-reference rules (the vault
# word, wikilinks, record names, ticket and decision numbers of two or
# more digits) and the format-character rule, after decoding them as
# UTF-8 (a name that is not valid UTF-8 is refused).
#
# The gate holds no list of names (of people, machines or the
# directories around the crate): what it refuses is fixed by the rules
# above, so a path into a directory beside the crate is caught as a
# parent-directory step or an absolute path, and a bare name is not.
#
# Nothing the gate prints contains matched text or the line: a finding is
# the class, the file and the line number, and a file name that would
# itself leak is withheld (see gate-common.sh).
#
# Limits. The gate stops accidents and a careless author; it cannot stop
# someone trying to beat a shell scanner. Escaped or encoded forms (JSON
# \u escapes, percent-encoding, base64, HTML entities, compression) are
# not decoded and are an unsupported representation. Find mode (no git)
# is a convenience before git init, not the shipping check: CI runs
# --require-git, the pre-commit hook --staged. Nothing in this round has
# been run on Windows (see gate-common.sh).
#
# The patterns are built from fragments, so the script passes its own
# scan; the self-test shows that each class is still detected.
#
# Usage: scripts/check-leakage.sh               check the crate
#        scripts/check-leakage.sh --require-git refuse to run outside
#                                               git (as CI runs it)
#        scripts/check-leakage.sh --staged      check what git commit
#                                               would record (the
#                                               pre-commit hook)
#        scripts/check-leakage.sh --self-test   check the gate itself,
#                                               end to end
#        SELF_TEST_ONLY=TEXT scripts/check-leakage.sh --self-test
#                                               only the self-test cases
#                                               whose names contain TEXT
#                                               (as their FAILED and
#                                               SKIPPED lines show them);
#                                               ends "self-test: PARTIAL"
#                                               with the counts run and
#                                               not selected, exits 0
#                                               only if every case run
#                                               passed, and fails if no
#                                               name contains TEXT

set -euo pipefail
# The crate is the parent of this script's directory, found without
# dirname, so that no tool's diagnostic can print the path.
case "$0" in
  */*) gate_dir=${0%/*} ;;
  *) gate_dir=. ;;
esac
cd "$gate_dir/.." 2> /dev/null || { echo "ERROR: cannot enter the crate"; exit 2; }
if [ ! -f scripts/gate-common.sh ] || ! . scripts/gate-common.sh 2> /dev/null; then
  echo "ERROR: the gate library is missing"
  exit 2
fi

leakage_perl () {
  cat <<'PERL'
my $u = "." . "./";
# The parent-directory references that exist, as exact text, each in the
# one file it belongs to: the proof command, which runs from tests/, and
# the matrix driver, which goes from scripts/ to tests/.
my %up_ok = (
  "README.md"                => ["alr -n exec -- gnatprove -P ${u}cbor_det.gpr -j2"],
  ".github/workflows/ci.yml" => ["run: alr -n exec -- gnatprove -P ${u}cbor_det.gpr -j0"],
  "cbor_det.gpr"             => ["--    alr exec -- gnatprove -P ${u}cbor_det.gpr"],
  "tests/alire.toml"         => ["run as `alr exec -- gnatprove -P ${u}cbor_det.gpr`"],
  "scripts/matrix.sh"        => ["cd \"\$(dirname \"\$0\")/${u}tests\""],
);
# In shell, where [[ starts a test and [[: a POSIX class, and in Python,
# where [[ opens a nested list or a subscript of a list, a wikilink is
# caught only in its plain form: a letter, digit, hyphen or underscore
# right after the brackets, and no white space before the closing ones.
my $shell_wikilink = qr{\[\[[A-Za-z0-9_-][^\s\[\]]*\]\]};

# The views of a file, line by line: the prose the wikilink rule reads,
# the prose the ticket and decision rule reads, and (Markdown) the code
# the note-name wikilink rule reads. Markdown, text, LICENSE, YAML,
# git configuration, shell and Python files are prose throughout (Python
# is not parsed: its code is read as prose too); Ada files are
# read for their comments (both rules) and string literals (wikilinks
# only); TOML and JSON files for their comments and string literals.
# In Markdown code (code spans and fenced blocks), where [[ is usually
# code, a wikilink is refused only when its target looks like a note
# name: a letter, then letters, digits, hyphens or underscores, then
# optionally | or # and any text.
my $note_wikilink = qr{\[\[[A-Za-z][A-Za-z0-9_-]*(?:[|#][^\[\]\n]*)?\]\]};

# Markdown, line by line: the prose (code spans and fenced blocks
# removed) and the code.
my $markdown = sub {
  my (@lines) = @_;
  my (@prose, @code);
  my $fence = "";
  for my $l (@lines) {
    if ($fence ne "") {
      push @prose, "";
      push @code, $l;
      $fence = "" if $l =~ /\A {0,3}(\Q$fence\E+)\s*\z/;
      next;
    }
    if ($l =~ /\A {0,3}(`{3,}|~{3,})/) {
      $fence = $1;
      push @prose, "";
      push @code, $l;
      next;
    }
    my ($p, $c) = ($l, "");
    $p =~ s{(`+)(.+?)\1}{$c .= " $2"; " "}ge;
    push @prose, $p;
    push @code, $c;
  }
  return (\@prose, \@code);
};

my $views = sub {
  my ($kind, @lines) = @_;
  if ($kind eq "markdown") {
    my ($prose, $code) = $markdown->(@lines);
    return ($prose, \@lines, $code);
  }
  return (\@lines, \@lines, [])
    if $kind =~ /\A(?:text|license|yaml|gitconfig|shell|python)\z/;
  my @wiki = ("") x @lines;
  my @td = ("") x @lines;
  if ($kind eq "ada") {
    for my $s (ada_segments(join "\n", @lines)) {
      my ($type, $text, $n) = @$s;
      if ($type eq "comment") {
        $wiki[$n] .= " $text";
        $td[$n] .= " $text";
      } elsif ($type eq "string") {
        $wiki[$n] .= " $text";
      }
    }
    return (\@wiki, \@td, []);
  }
  my $state = "";
  for my $n (0 .. $#lines) {
    my $l = $lines[$n];
    my $t = "";
    my ($i, $len) = (0, length $l);
    while ($i < $len) {
      my $rest = substr $l, $i;
      if ($state ne "") {
        if (($state eq '"' || $state eq '"""') && $rest =~ /\A\\./s) {
          $t .= substr $rest, 0, 2;
          $i += 2;
          next;
        }
        if (substr($rest, 0, length $state) eq $state) {
          $i += length $state;
          $state = "";
          next;
        }
        $t .= substr $rest, 0, 1;
        $i++;
        next;
      }
      if ($kind eq "toml") {
        if ($rest =~ /\A#/) { $t .= " " . substr($rest, 1); last; }
        if ($rest =~ /\A("""|''')/) {
          $state = $1;
          $i += 3;
          next;
        }
        if ($rest =~ /\A(['"])/) { $state = $1; $i++; next; }
      } elsif ($kind eq "json") {
        if ($rest =~ m{\A//}) { $t .= " " . substr($rest, 2); last; }
        if ($rest =~ m{\A/\*}) { $state = "*/"; $i += 2; next; }
        if ($rest =~ /\A"/) { $state = '"'; $i++; next; }
      }
      $i++;
    }
    # Only TOML multi-line strings and JSON block comments continue on
    # the next line.
    $state = "" if $state eq '"' || $state eq "'";
    $wiki[$n] = $t;
    $td[$n] = $t;
  }
  return (\@wiki, \@td, []);
};

# The ticket and decision rule, with one exemption: a T or D and one
# digit next to (one space from) another two-digit upper-case hex token
# is a hex byte, as RFC 8949 writes CBOR (D9 D9 F7).
my $tickets = sub {
  my ($text) = @_;
  while ($text =~ /\b([TD][0-9]+)\b/g) {
    my ($token, $start, $end) = ($1, $-[0], $+[0]);
    if ($token =~ /\A[TD][0-9]\z/) {
      my $before = substr $text, 0, $start;
      my $after = substr $text, $end;
      next if $before =~ /(?<![0-9A-Za-z])[0-9A-F]{2} \z/
           || $after =~ /\A [0-9A-F]{2}(?![0-9A-Za-z])/;
    }
    return 1;
  }
  return 0;
};

my $check = sub {
  my ($path, $where, $line, $kind, $wiki, $td, $code) = @_;
  for my $r (@RULES) {
    refuse($r->[0], $where) if $line =~ $r->[1];
  }
  my $rest = $line;
  if (defined $kind) {
    $rest =~ s/\Q$_\E/ /g for @{ $up_ok{$path} // [] };
  }
  refuse("parent-directory path", $where) if $rest =~ /\.\.[\/\\]/;
  refuse("zero-width or format character", $where) if $line =~ $FORMAT;
  my $wikilink = defined $kind && ($kind eq "shell" || $kind eq "python")
    ? $shell_wikilink : $WIKILINK;
  refuse("wikilink", $where) if defined $wiki && $wiki =~ $wikilink
                            || defined $code && $code =~ $note_wikilink;
  if (defined $kind) {
    refuse("ticket or decision", $where) if defined $td && $tickets->($td);
  } else {
    refuse("ticket or decision", $where) if $line =~ /\b[TD][0-9]{2,}\b/;
  }
};

my $scanned = 0;
for my $file (@FILES) {
  my ($path, $kind, $bytes, $chars, $bom, $shown, $name) = @$file;
  $scanned++;
  if (defined $name) {
    $check->($path, "$shown (file name)", $name, undef, $name, undef);
  } else {
    refuse("file name not valid UTF-8", $shown);
  }
  my @lines = split /\r\n|[\n\r\f\x0B\x{85}\x{2028}\x{2029}]/, $chars, -1;
  my ($wiki, $td, $code) = $views->($kind, @lines);
  for my $i (0 .. $#lines) {
    $check->($path, "$shown:" . ($i + 1), $lines[$i], $kind,
             $wiki->[$i], $td->[$i], $code->[$i]);
  }
}
refuse("no file scanned", "the inventory") if $scanned == 0;
print "files scanned: $scanned\n";
exit $BAD;
PERL
}

# ---------------------------------------------------------------------
# Self-test. Texts the gate refuses are built from fragments, so that this
# file does not contain them; no case may print them.

ST_LEAK_ABSENT="/Us""ers/
$ST_SECRET"

st_leak_base () {
  st_put README.md 'clean\n' && ST_ABSENT=$ST_LEAK_ABSENT
}

st_leak_hostile () {
  st_put "$1" '--  see /Us\x{65}rs/alice/x\n'
}

# Every file untracked and ignored: nothing to scan.
st_leak_nothing () {
  st_put .gitignore '*\n' && ST_NO_ADD=yes
}

# A home path naming a secret, and a file whose name holds the secret and
# a record id: the output must contain neither.
st_leak_no_echo () {
  st_leak_base \
    && st_put README.md "See /Us\\x{65}rs/$ST_SECRET/x.\\n" \
    && st_put "docs/$ST_SECRET-d""0019-notes.md" 'clean\n' \
    && ST_ABSENT="$ST_LEAK_ABSENT
$ST_SECRET-d""0019-notes.md"
}

# st_hook_step NAME EXPECT_STATUS EXPECT_TEXT ENV...: one commit attempt in
# the hook fixture; EXPECT_STATUS is fail or pass. Nothing withheld may be
# printed. A step SELF_TEST_ONLY leaves out still makes its commit attempt,
# silently, so that the steps after it see the same repository; in the
# dry run (ST_HOOK_DRY) a step is only counted. A failed step is followed
# by a diagnosis (st_hook_diagnose).
st_hook_step () {
  local name=$1 want=$2 text=$3 status ok=yes
  shift 3
  if [ "$ST_HOOK_DRY" = yes ]; then
    ST_HOOK_ALL=$((ST_HOOK_ALL + 1))
    if st_matches "hook: $name"; then ST_HOOK_WANTED=$((ST_HOOK_WANTED + 1)); fi
    return 0
  fi
  (cd "$ST_DIR/hook" && { [ "$#" -eq 0 ] || export "$@"; } \
     && st_git commit -q -m "$name") \
    > "$ST_DIR/hook.out" 2>&1
  status=$?
  st_select "hook: $name" || return 0
  if [ "$want" = fail ] && [ "$status" -eq 0 ]; then ok=no; fi
  if [ "$want" = pass ] && [ "$status" -ne 0 ]; then ok=no; fi
  if [ -n "$text" ] && ! grep -qF -- "$text" "$ST_DIR/hook.out"; then ok=no; fi
  ST_ABSENT=$ST_LEAK_ABSENT
  if ! st_absent "$ST_DIR/hook.out"; then ok=no; fi
  if [ "$ok" = yes ]; then
    ST_PASS=$((ST_PASS + 1))
  else
    st_failed "hook: $name (exit $status):"
    sed 's/^/    /' "$ST_DIR/hook.out"
    st_hook_diagnose "$@"
  fi
}

# st_hook_diagnose ENV...: after a failed step, what the hook saw, with
# the same ENV: the exit status of git rev-parse --show-toplevel in the
# fixture, then a commit attempt through a stand-in hook that reports the
# PATH, the git it finds and that git's rev-parse, and runs the real hook
# under bash -x (the attempt is always refused, so nothing is committed).
# The last 30 lines are shown, scrubbed (st_scrub): no fixture or home
# path, no user name, and never a line holding the canary.
st_hook_diagnose () {
  local trace="$ST_DIR/hook-trace" out="$ST_DIR/hook-diagnosis.out"
  mkdir -p "$trace" 2> /dev/null
  printf '%s\n' '#!/usr/bin/env bash' \
    'echo "diagnosis: PATH in the hook: $PATH"' \
    'echo "diagnosis: git in the hook: $(command -v git 2>&1)"' \
    'top=$(git rev-parse --show-toplevel 2>&1)' \
    'echo "diagnosis: git rev-parse --show-toplevel in the hook: exit $?: $top"' \
    'bash -x .githooks/pre-commit "$@"' \
    'echo "diagnosis: the hook exited $?"' \
    'exit 1' > "$trace/pre-commit" 2> /dev/null
  chmod +x "$trace/pre-commit" 2> /dev/null
  {
    echo "diagnosis: ENV: $*"
    (cd "$ST_DIR/hook" && { [ "$#" -eq 0 ] || export "$@"; } \
       && st_git rev-parse --show-toplevel)
    echo "diagnosis: git rev-parse --show-toplevel in the fixture: exit $?"
    (cd "$ST_DIR/hook" && { [ "$#" -eq 0 ] || export "$@"; } \
       && st_git -c core.hooksPath="$trace" commit -q -m diagnosis)
    echo "diagnosis: the commit through the tracing hook exited $?"
  } > "$out" 2>&1
  echo "    diagnosis (last 30 lines, scrubbed):"
  st_scrub < "$out" | tail -n 30 | sed 's/^/      /'
}

# The pre-commit hook, end to end, in a temporary git repository. A dry
# run of the steps first counts them and, under SELF_TEST_ONLY, finds
# whether any is selected; if none is, the fixture is not built.
st_hook_cases () {
  local d="$ST_DIR/hook" w="$ST_DIR/hook-bin"
  ST_HOOK_DRY=yes ST_HOOK_ALL=0 ST_HOOK_WANTED=0
  st_hook_steps "$w"
  ST_HOOK_DRY=no
  if [ "$ST_HOOK_WANTED" -eq 0 ]; then
    ST_UNSELECTED=$((ST_UNSELECTED + ST_HOOK_ALL))
    return 0
  fi
  if [ "$ST_GIT" = no ]; then
    ST_SKIP=$((ST_SKIP + ST_HOOK_WANTED))
    ST_UNSELECTED=$((ST_UNSELECTED + ST_HOOK_ALL - ST_HOOK_WANTED))
    return 0
  fi
  if ! { st_fixture "$d" && mkdir -p "$w" \
         && printf '#!/bin/sh\necho "warning: harmless advice" >&2\nexec "%s" "$@"\n' \
              "$ST_REAL_GIT" > "$w/git" && chmod +x "$w/git" \
         && (cd "$d" && st_git init -q --template= \
             && st_git config core.hooksPath .githooks \
             && st_put src/c.ads 'package C with SPARK_Mode is\nend C;\n' \
             && st_put README.md 'clean\n' && st_git add -A); } \
       > /dev/null 2>&1; then
    st_failed "hook: cannot build the fixture"
    return 0
  fi
  st_hook_steps "$w"
}

# st_hook_steps W: the steps, in order; W holds the git that warns.
st_hook_steps () {
  local w=$1
  st_hook_step "a clean commit passes" pass "leakage: clean"
  st_hook_do st_put notes.md "Copied from /Us\\x{65}rs/$ST_SECRET/x\\n" \
    && st_hook_do st_git add -A
  st_hook_step "a path is refused, and not printed" fail \
    "FORBIDDEN (absolute home path) at notes.md:1"
  st_hook_do st_put notes.md 'clean\n' \
    && st_hook_do st_put src/c.adb 'pragma Assume (True);\n' \
    && st_hook_do st_git add -A
  st_hook_step "the source gate runs too" fail \
    "FORBIDDEN (Assume) at src/c.adb"
  st_hook_do st_git rm -q --cached src/c.adb && st_hook_do rm src/c.adb
  st_hook_step "a clean commit passes after a refusal" pass "sources: clean"
  st_hook_change scripts/check-sources.sh v1
  st_hook_step "an unstaged change to a gate script is refused" fail \
    "differs from its staged copy (restore with: git checkout -- "
  st_hook_do st_git checkout -q -- scripts/check-sources.sh
  st_hook_do st_git update-index --assume-unchanged scripts/gate-common.sh \
    && st_hook_change scripts/gate-common.sh v2
  st_hook_step "a change hidden by assume-unchanged is refused" fail \
    "differs from its staged copy (restore with: git checkout -- "
  st_hook_do st_git update-index --no-assume-unchanged scripts/gate-common.sh \
    && st_hook_do st_git checkout -q -- scripts/gate-common.sh
  st_hook_do st_git update-index --skip-worktree .githooks/pre-commit \
    && st_hook_change .githooks/pre-commit v3
  st_hook_step "a change hidden by skip-worktree is refused" fail \
    "differs from its staged copy (restore with: git checkout -- "
  st_hook_do st_git update-index --no-skip-worktree .githooks/pre-commit \
    && st_hook_do st_git checkout -q -- .githooks/pre-commit
  st_hook_do st_put .gitattributes 'scripts/check-leakage.sh filter=hide\n' \
    && st_hook_do st_git config filter.hide.clean "sed -e '/^# changed\$/d'" \
    && st_hook_do st_git add .gitattributes \
    && st_hook_change scripts/check-leakage.sh v4
  st_hook_step "a change hidden by a clean filter is refused" fail \
    "differs from its staged copy (restore with: git checkout -- "
  st_hook_do st_git checkout -q -- scripts/check-leakage.sh \
    && st_hook_do st_git rm -q --cached .gitattributes \
    && st_hook_do rm .gitattributes \
    && st_hook_do st_git config --unset filter.hide.clean
  st_hook_do st_git rm -q --cached scripts/check-sources.sh \
    && st_hook_do st_put notes.md 'v5\n' && st_hook_do st_git add notes.md
  st_hook_step "a gate script removed from the index is refused" fail \
    "REFUSED: pre-commit: a gate file is not in the index"
  st_hook_do st_git add scripts/check-sources.sh
  st_hook_step "a git that warns on stderr does not break the hook" pass \
    "sources: clean" "PATH=$w:$PATH"
  st_hook_do st_put notes.md 'v6\n' && st_hook_do st_git add notes.md
  st_hook_step "a broken locale does not break the hook" pass \
    "sources: clean" LC_ALL=xx_INVALID.UTF-8 LANG=xx_INVALID.UTF-8
  st_hook_do st_put .gitattributes '* text=auto eol=lf\n' \
    && st_hook_do st_git add .gitattributes \
    && st_hook_do perl -pi -e 's/\n/\r\n/' scripts/gate-common.sh \
    && st_hook_do st_git add -A
  st_hook_step "a gate file with CRLF in the working tree names the fix" fail \
    "REFUSED: pre-commit: scripts/gate-common.sh differs from its staged copy (restore with: git checkout -- scripts/gate-common.sh)"
  st_hook_do st_git checkout -q -- scripts/gate-common.sh \
    && st_hook_do st_git rm -q --cached .gitattributes \
    && st_hook_do rm .gitattributes
  st_hook_cmp_cases
}

# Without cmp the hook refuses. The PATH holds only the tools the hook and
# the gates use (st_hook_tools_without_cmp). Then the same refusal where
# the git in git's own directory (exec-path, which git puts first on a
# hook's PATH) cannot start under that PATH, as on MSYS, where that copy
# of git needs msys-2.0.dll from a directory the PATH no longer holds: a
# stand-in exec-path whose git starts only while the directory of the
# real git is on the PATH. The first step shows the stand-in trips the
# hook as MSYS did; the second, that the tool directory then gives git
# its own exec-path and the refusal is the one expected.
st_hook_cmp_cases () {
  local cmp_name="a missing cmp is refused with a fixed message"
  local sim="$ST_DIR/msys-exec-path" sim_bin="$ST_DIR/msys-no-cmp-bin"
  local sim_trips="a git that cannot start from its exec-path under that PATH trips the hook"
  local sim_name="a missing cmp is refused when git cannot start from its exec-path"
  if [ "$ST_HOOK_DRY" = yes ]; then
    st_hook_step "$cmp_name" fail ""
    st_hook_step "$sim_trips" fail ""
    st_hook_step "$sim_name" fail ""
    return 0
  fi
  if ! st_matches "hook: $cmp_name"; then
    st_select "hook: $cmp_name"
  elif st_hook_tools_without_cmp "$ST_DIR/no-cmp-bin"; then
    st_hook_do st_put notes.md 'v7\n' && st_hook_do st_git add notes.md
    # shellcheck disable=SC2086
    st_hook_step "$cmp_name" fail \
      "REFUSED: pre-commit: cmp is not available" "PATH=$ST_DIR/no-cmp-bin" \
      $ST_HOOK_CMP_ENV
  else
    st_skipped "hook: $cmp_name" "$ST_TOOL_DIR_REASON"
  fi
  if ! st_matches "hook: $sim_trips" && ! st_matches "hook: $sim_name"; then
    st_select "hook: $sim_trips"
    st_select "hook: $sim_name"
    return 0
  fi
  if ! { mkdir -p "$sim" \
         && printf '#!/bin/sh\ncase ":$PATH:" in\n  *":%s:"*) exec "%s" "$@" ;;\nesac\necho "git: error while loading shared libraries: msys-2.0.dll: cannot open shared object file: No such file or directory" >&2\nexit 127\n' \
              "${ST_REAL_GIT%/*}" "$ST_REAL_GIT" > "$sim/git" \
         && chmod +x "$sim/git"; } > /dev/null 2>&1; then
    st_failed "hook: cannot build the exec-path stand-in"
    return 0
  fi
  # The stand-in shows something only where git, unaided, works in a hook
  # with a PATH of only the tools; elsewhere both steps are skipped.
  local why=""
  if ! ST_HOOK_QUIET=yes st_hook_tools_without_cmp "$sim_bin"; then
    why=$ST_TOOL_DIR_REASON
  elif [ -n "$ST_HOOK_CMP_ENV" ]; then
    why="git here needs its exec-path set to work in a hook with a PATH of only the tools, so a stand-in exec-path shows nothing more"
  fi
  if [ -n "$why" ]; then
    st_skipped "hook: $sim_trips" "$why"
    st_skipped "hook: $sim_name" "$why"
    return 0
  fi
  st_hook_do st_put notes.md 'v8\n' && st_hook_do st_git add notes.md
  st_hook_step "$sim_trips" fail "ERROR: pre-commit: not in a git work tree" \
    "PATH=$sim_bin" "GIT_EXEC_PATH=$sim"
  if GIT_EXEC_PATH="$sim" ST_HOOK_QUIET=yes st_hook_tools_without_cmp "$sim_bin" \
     && [ "$ST_HOOK_CMP_ENV" = "GIT_EXEC_PATH=$sim_bin" ]; then
    # shellcheck disable=SC2086
    st_hook_step "$sim_name" fail "REFUSED: pre-commit: cmp is not available" \
      "PATH=$sim_bin" "GIT_EXEC_PATH=$sim" $ST_HOOK_CMP_ENV
  elif [ -n "$ST_TOOL_DIR_REASON" ]; then
    st_skipped "hook: $sim_name" "$ST_TOOL_DIR_REASON"
  else
    st_failed "hook: $sim_name: the tool directory did not give git its own exec-path"
  fi
}

# st_hook_tools_without_cmp DIR: a directory of the tools the hook and the
# gates use, without cmp (st_tool_dir: links, else wrapper scripts, else a
# skip), in which git works inside a hook: a commit in a throwaway
# repository, with PATH=DIR, runs a hook that needs git rev-parse
# --show-toplevel to work (st_hook_git_works). If it does not, and git
# does with GIT_EXEC_PATH=DIR (so that git's own directory, which it puts
# first on a hook's PATH, is DIR), ST_HOOK_CMP_ENV holds that setting for
# the step, and a NOTE says so (unless ST_HOOK_QUIET is yes). Otherwise fails, with the reason in
# ST_TOOL_DIR_REASON.
st_hook_tools_without_cmp () {
  local dir=$1 first
  ST_HOOK_CMP_ENV=""
  st_tool_dir "$dir" git bash sh env mktemp rm cat grep perl find id \
    basename uname tr dirname sed cut printf mkdir chmod ls cygpath \
    || return 1
  if st_hook_git_works "$dir"; then
    return 0
  fi
  first=$ST_HOOK_PROBE
  if st_hook_git_works "$dir" "GIT_EXEC_PATH=$dir"; then
    ST_HOOK_CMP_ENV="GIT_EXEC_PATH=$dir"
    [ "${ST_HOOK_QUIET:-}" = yes ] || echo "self-test NOTE: hook: with a PATH of the tools only, git in a hook fails ($first); with git's exec-path set to those tools it works, so the case runs with GIT_EXEC_PATH set to them"
    return 0
  fi
  ST_TOOL_DIR_REASON="git does not work inside a hook with a PATH of only these tools ($first), nor with its exec-path set to them ($ST_HOOK_PROBE)"
  return 1
}

# st_hook_git_works DIR [ENV...]: a commit in a throwaway repository, with
# PATH=DIR and ENV, whose hook (started as the real one is) needs git
# rev-parse --show-toplevel to give the work tree. On failure
# ST_HOOK_PROBE says how it failed (scrubbed, one line).
st_hook_git_works () {
  local dir=$1 p="$ST_DIR/hook-probe" status
  shift
  rm -rf "$p" 2> /dev/null
  if ! { mkdir -p "$p/.githooks" \
         && printf '%s\n' '#!/usr/bin/env bash' \
              'top=$(git rev-parse --show-toplevel) || exit 3' \
              '[ -n "$top" ] && cd "$top" || exit 4' \
              'exit 0' > "$p/.githooks/pre-commit" \
         && chmod +x "$p/.githooks/pre-commit" \
         && (cd "$p" && st_git init -q --template= \
             && st_git config core.hooksPath .githooks \
             && st_put probe.txt 'probe\n' && st_git add probe.txt); } \
       > /dev/null 2>&1; then
    ST_HOOK_PROBE="the probe repository could not be made"
    return 1
  fi
  (cd "$p" && export PATH="$dir" && { [ "$#" -eq 0 ] || export "$@"; } \
     && st_git commit -q -m probe) > "$ST_DIR/hook-probe.out" 2>&1
  status=$?
  [ "$status" -eq 0 ] && return 0
  ST_HOOK_PROBE="exit $status: $(st_scrub < "$ST_DIR/hook-probe.out" \
    | tr '\n' ' ' | sed 's/ *$//' | cut -c1-200)"
  return 1
}

# st_hook_do COMMAND...: a setup step in the hook fixture, silently (in
# the dry run, nothing).
st_hook_do () {
  [ "$ST_HOOK_DRY" = yes ] && return 0
  (cd "$ST_DIR/hook" && "$@") > /dev/null 2>&1
}

# st_hook_change PATH TAG: an unstaged change to PATH, and a staged
# change elsewhere so that there is something to commit.
st_hook_change () {
  st_hook_do sh -c "printf '# changed\\n' >> '$1'" \
    && st_hook_do st_put notes.md "$2\\n" && st_hook_do st_git add notes.md
}

st_leak_odd_file_name () {
  local path
  st_leak_base && path=$(st_decode "$1") && st_odd_put "$path" 'clean\n'
}

self_test () {
  st_begin check-leakage.sh || return 2
  local up='.\x{2E}'
  local proof="alr -n exec -- gnatprove -P $up/cbor_det.gpr -j0"
  local readme_proof="alr -n exec -- gnatprove -P $up/cbor_det.gpr -j2"
  st_shared_cases st_leak_base st_leak_hostile \
    "FORBIDDEN (absolute home path) at "
  st_hook_cases
  st_bootstrap_cases
  st_both "nothing matched is printed" \
    "FORBIDDEN (absolute home path) at README.md:1" st_leak_no_echo
  st_case3 "nothing to scan" - "FORBIDDEN (no file scanned)" \
    "FORBIDDEN (no file scanned)" st_leak_nothing
  st_both "record name in a file name" \
    "FORBIDDEN (private record name) at <file name withheld: inventory entry" \
    st_table_setup st_leak_base "notes/d""0019-crate-names.txt" clean
  st_both "file name with a wikilink" \
    "FORBIDDEN (wikilink) at <file name withheld: inventory entry" \
    st_leak_odd_file_name 'docs/\x{5B}[private-note]].txt'
  st_both "file name with a zero-width space in the vault word" \
    "FORBIDDEN (zero-width or format character) at <file name withheld: inventory entry" \
    st_leak_odd_file_name 'docs/bra\u{200B}in.md'
  st_table st_leak_base \
    "users-path|FORBIDDEN (absolute home path) at a.md|a.md|see /Us\\x{65}rs/someone/x" \
    "home-path|FORBIDDEN (absolute home path) at a.sh|a.sh|cd /h\\x{6F}me/someone/work" \
    "windows-users-path|FORBIDDEN (absolute Windows path) at a.txt|a.txt|C\\x{3A}\\x{5C}Users\\x{5C}someone" \
    "windows-slash-path|FORBIDDEN (absolute Windows path) at a.txt|a.txt|c\\x{3A}/us\\x{65}rs/someone" \
    "windows-work-path|FORBIDDEN (absolute Windows path) at README.md|README.md|Build directory: C\\x{3A}\\x{5C}work\\x{5C}ada\\x{5C}cbor_det" \
    "windows-drive-forward|FORBIDDEN (absolute Windows path) at a.txt|a.txt|output in d\\x{3A}/build/x" \
    "windows-drive-in-workflow|FORBIDDEN (absolute Windows path) at .github/workflows/ci.yml|.github/workflows/ci.yml|        run: cd C\\x{3A}\\x{5C}x" \
    "windows-drive-bare|FORBIDDEN (absolute Windows path) at src/x.adb|src/x.adb|--  see E\\x{3A}\\x{5C}" \
    "unc-path|FORBIDDEN (Windows UNC path) at README.md|README.md|copied from \\x{5C}\\x{5C}server\\x{5C}share\\x{5C}x" \
    "unc-path-in-code|FORBIDDEN (Windows UNC path) at src/x.adb|src/x.adb|S : constant String := \"\\x{5C}\\x{5C}host\\x{5C}c\";" \
    "file-url|FORBIDDEN (file URL) at README.md|README.md|see fil\\x{65}:///etc/x" \
    "file-url-upper|FORBIDDEN (file URL) at a.txt|a.txt|FIL\\x{45}:/\\x{2F}server/x" \
    "volumes|FORBIDDEN (absolute volume path) at a.sh|a.sh|cp x /Vol\\x{75}mes/Disk/x" \
    "extended-length|FORBIDDEN (extended-length path) at a.txt|a.txt|\\x{5C}\\x{5C}?\\x{5C}UNC\\x{5C}server" \
    "device-path|FORBIDDEN (extended-length path) at a.txt|a.txt|\\x{5C}\\x{5C}.\\x{5C}pipe\\x{5C}x" \
    "nt-object-path|FORBIDDEN (extended-length path) at a.txt|a.txt|\\x{5C}??\\x{5C}UNC\\x{5C}x" \
    "proc|FORBIDDEN (process file system path) at a.sh|a.sh|cat /pr\\x{6F}c/self/environ" \
    "cygdrive|FORBIDDEN (Cygwin drive path) at a.sh|a.sh|cd /cyg\\x{64}rive/c/x" \
    "mnt-drive|FORBIDDEN (mounted drive path) at a.sh|a.sh|cd /mn\\x{74}\\x{2F}c/work" \
    "msys-after-space|FORBIDDEN (MSYS drive path) at a.sh|a.sh|cd /\\x{64}/work" \
    "msys-after-quote|FORBIDDEN (MSYS drive path) at a.sh|a.sh|x=\"/\\x{65}/data\"" \
    "msys-after-equals|FORBIDDEN (MSYS drive path) at a.txt|a.txt|dir=/\\x{63}/x" \
    "msys-after-colon|FORBIDDEN (MSYS drive path) at a.yml|a.yml|path:/\\x{7A}/x" \
    "msys-after-bracket|FORBIDDEN (MSYS drive path) at a.md|a.md|(see /\\x{63}/x)" \
    "msys-line-start|FORBIDDEN (MSYS drive path) at a.txt|a.txt|/\\x{63}/x" \
    "benign-paths|pass|README.md|a/b and/or ./c/x https://alire.ada.dev/c/x \$HOME/.cache ~/x .github/c/x" \
    "private-tmp|FORBIDDEN (per-user temporary path) at a.txt|a.txt|/pri\\x{76}ate/tmp/x" \
    "var-folders|FORBIDDEN (per-user temporary path) at a.txt|a.txt|/var/fo\\x{6C}ders/ab/x" \
    "tmp-uid|FORBIDDEN (per-user temporary path) at a.txt|a.txt|/tmp/build-\\x{35}01/x" \
    "plain-tmp|pass|.github/workflows/ci.yml|/tmp/vectors.json" \
    "notes-word|FORBIDDEN (private notes) at README.md|README.md|See the bra\\x{69}n for the private design." \
    "notes-word-upper|FORBIDDEN (private notes) at a.md|a.md|BRA\\x{49}N" \
    "notes-dir-backslash|FORBIDDEN (private notes) at a.md|a.md|see bra\\x{69}n\\x{5C}specs\\x{5C}x" \
    "notes-word-in-code|FORBIDDEN (private notes) at src/x.adb|src/x.adb|X : constant String := \"bra\\x{69}n\";" \
    "brainstorm|pass|a.md|brainstorm" \
    "record-ticket-name|FORBIDDEN (private record name) at README.md|README.md|see t\\x{30}041-create-the-member" \
    "record-decision-name|FORBIDDEN (private record name) at src/x.adb|src/x.adb|X : Integer;  --  d\\x{30}019-crate-names" \
    "wikilink|FORBIDDEN (wikilink) at a.md|a.md|see \\x{5B}[some-note]]" \
    "wikilink-alias|FORBIDDEN (wikilink) at a.md|a.md|see \\x{5B}[some-note|text]]" \
    "wikilink-dot|FORBIDDEN (wikilink) at a.md|a.md|\\x{5B}[.x]]" \
    "wikilink-equals|FORBIDDEN (wikilink) at a.md|a.md|\\x{5B}[=x]]" \
    "wikilink-space|FORBIDDEN (wikilink) at a.md|a.md|\\x{5B}[ x]]" \
    "wikilink-colon|FORBIDDEN (wikilink) at a.md|a.md|\\x{5B}[:x]]" \
    "wikilink-text-unclosed|pass|a.txt|see \\x{5B}[x" \
    "json-array|pass|a.json|\\x{5B}[1,2],[3,4]]" \
    "toml-array-of-arrays|pass|a.toml|x = \\x{5B}[\"name\"]]" \
    "toml-table|pass|a.toml|\\x{5B}[depends-on]]" \
    "toml-table-quoted|pass|a.toml|  \\x{5B}[\"quoted\".key]]" \
    "bash-test|pass|a.sh|if \\x{5B}[ -n \"\$x\" ]]; then :; fi" \
    "python-classified|pass|tests/t.py|import sys  # a Python file is scanned" \
    "python-nested-list|pass|t.py|x = \\x{5B}[1, 2], [3, 4]]" \
    "python-subscript|pass|t.py|y = x\\x{5B}[i][j]]" \
    "python-home-path|FORBIDDEN (absolute home path) at t.py|t.py|p = \"/h\\x{6F}me/someone/x\"" \
    "python-ticket-in-code|FORBIDDEN (ticket or decision) at t.py|t.py|x = T\\x{31}2" \
    "python-ticket-in-comment|FORBIDDEN (ticket or decision) at t.py|t.py|x = 1  # see D\\x{30}19" \
    "python-ticket-in-docstring|FORBIDDEN (ticket or decision) at t.py:2|t.py|\"\"\"Doc.\\nFrom T\\x{34}9.\"\"\"" \
    "python-wikilink-comment|FORBIDDEN (wikilink) at t.py|t.py|x = 1  # see \\x{5B}[note]]" \
    "python-wikilink-string|FORBIDDEN (wikilink) at t.py|t.py|s = \"\\x{5B}[private-note]]\"" \
    "python-parent-path|FORBIDDEN (parent-directory path) at t.py|t.py|open(\"$up/other/x\")" \
    "posix-class-in-shell-code|pass|a.sh|if \\x{5B}[ \$x == \\x{5B}[:space:]]* ]]; then :; fi" \
    "posix-class-in-shell-string|pass|a.sh|grep -E '^\\x{5B}[:space:]]*version'" \
    "markdown-nested-list|pass|a.md|\\x{5B}[1], [2]]" \
    "wikilink-spaces|FORBIDDEN (wikilink) at a.md|a.md|\\x{5B}[ note ]]" \
    "wikilink-ada-comment|FORBIDDEN (wikilink) at src/x.ads|src/x.ads|--  see \\x{5B}[private-note]]" \
    "wikilink-ada-string|FORBIDDEN (wikilink) at src/x.adb|src/x.adb|S : constant String := \"\\x{5B}[private-note]]\";" \
    "wikilink-adc-comment|FORBIDDEN (wikilink) at src/gnat.adc|src/gnat.adc|--  \\x{5B}[note]]" \
    "wikilink-gpr-comment|FORBIDDEN (wikilink) at p.gpr|p.gpr|--  \\x{5B}[note]]" \
    "wikilink-gpr-string|FORBIDDEN (wikilink) at p.gpr|p.gpr|   for Main use (\"\\x{5B}[note]]\");" \
    "wikilink-shell-comment|FORBIDDEN (wikilink) at a.sh|a.sh|x=1  # see \\x{5B}[note]]" \
    "wikilink-shell-string|FORBIDDEN (wikilink) at a.sh|a.sh|echo \"\\x{5B}[note]]\"" \
    "wikilink-shell-single|FORBIDDEN (wikilink) at a.sh|a.sh|echo '\\x{5B}[a|b]]'" \
    "wikilink-shell-heredoc|FORBIDDEN (wikilink) at a.sh:2|a.sh|cat <<EOT\\n\\x{5B}[note]]\\nEOT" \
    "wikilink-shell-multiline-string|FORBIDDEN (wikilink) at a.sh:2|a.sh|x=\"first\\n\\x{5B}[note]]\"" \
    "wikilink-hook-comment|FORBIDDEN (wikilink) at .githooks/pre-commit|.githooks/pre-commit|# \\x{5B}[note]]" \
    "wikilink-toml-comment|FORBIDDEN (wikilink) at a.toml|a.toml|# \\x{5B}[note]]" \
    "wikilink-toml-string|FORBIDDEN (wikilink) at a.toml|a.toml|x = \"\\x{5B}[note]]\"" \
    "wikilink-toml-literal|FORBIDDEN (wikilink) at a.toml|a.toml|x = '\\x{5B}[note]]'" \
    "wikilink-toml-multiline|FORBIDDEN (wikilink) at a.toml:2|a.toml|x = \"\"\"\\n\\x{5B}[note]]\\n\"\"\"" \
    "wikilink-yaml-comment|FORBIDDEN (wikilink) at a.yml|a.yml|# \\x{5B}[note]]" \
    "wikilink-yaml-string|FORBIDDEN (wikilink) at a.yml|a.yml|name: \"\\x{5B}[note]]\"" \
    "wikilink-json-string|FORBIDDEN (wikilink) at a.json|a.json|{\"a\": \"\\x{5B}[note]]\"}" \
    "wikilink-json-comment|FORBIDDEN (wikilink) at a.json|a.json|// \\x{5B}[note]]" \
    "json-string-of-arrays|pass|a.json|{\"a\": \"\\x{5B}[1], [2]]\"}" \
    "shell-wikilink-after-comment|FORBIDDEN (wikilink) at a.sh|a.sh|:;#\\x{5B}[private-note]]" \
    "shell-wikilink-in-numbered-heredoc|FORBIDDEN (wikilink) at a.sh:2|a.sh|cat <<1\\n\\x{5B}[private-note]]\\n1" \
    "shell-wikilink-in-second-heredoc|FORBIDDEN (wikilink) at a.sh:4|a.sh|cat <<A <<B\\nx\\nA\\n\\x{5B}[private-note]]\\nB" \
    "shell-tests-and-classes|pass|a.sh|if \\x{5B}[ -n \"\$x\" ]] && \\x{5B}[ \$a == b ]]; then grep -E '\\x{5B}[:space:]]' x; fi" \
    "markdown-msys-in-brackets|FORBIDDEN (MSYS drive path) at a.md|a.md|see \\x{5B}/\\x{63}/work/cbor_det]" \
    "markdown-unc-in-brackets|FORBIDDEN (forward-slash UNC path) at a.md|a.md|see \\x{5B}/\\x{2F}server/share/file]" \
    "markdown-msys-in-backticks|FORBIDDEN (MSYS drive path) at a.md|a.md|see \`/\\x{63}/work/cbor_det\`" \
    "markdown-unc-in-backticks|FORBIDDEN (forward-slash UNC path) at a.md|a.md|see \`/\\x{2F}server/share/file\`" \
    "markdown-msys-in-angle-brackets|FORBIDDEN (MSYS drive path) at a.md|a.md|see </\\x{63}/work/x>" \
    "markdown-msys-in-braces|FORBIDDEN (MSYS drive path) at a.md|a.md|see {/\\x{63}/work/x}" \
    "markdown-msys-after-comma|FORBIDDEN (MSYS drive path) at a.md|a.md|a,/\\x{63}/work/x" \
    "volumes-lower-case|FORBIDDEN (absolute volume path) at a.md|a.md|/vol\\x{75}mes/PrivateDisk/cbor_det" \
    "proc-upper-case|FORBIDDEN (process file system path) at a.md|a.md|/PR\\x{4F}C/self" \
    "cygdrive-upper-case|FORBIDDEN (Cygwin drive path) at a.md|a.md|/CYG\\x{44}RIVE/c/x" \
    "mnt-upper-case|FORBIDDEN (mounted drive path) at a.md|a.md|/MN\\x{54}\\x{2F}C/x" \
    "markdown-benign-punctuation|pass|a.md|\\x{5B}a link](https://alire.ada.dev/c/x), \`a/b\`, (./c/x), {x}/y, <a/b>, see [docs](docs/x.md)" \
    "decision-in-code|pass|src/x.adb|X : constant := D\\x{31}9;" \
    "review-modular-type|pass|src/review.ads|package Review is\\n   type T\\x{33}2 is mod 2 ** 32;\\n   D\\x{31}6 : constant := 16;\\nend Review;" \
    "ticket-in-ada-comment|FORBIDDEN (ticket or decision) at src/review.ads|src/review.ads|--  see T\\x{33}2" \
    "ticket-in-json-string|FORBIDDEN (ticket or decision) at a.json|a.json|{\"a\": \"see T\\x{31}\"}" \
    "ticket-in-toml-string|FORBIDDEN (ticket or decision) at a.toml|a.toml|x = \"see D\\x{32}\"" \
    "backslash-users|FORBIDDEN (absolute home path) at README.md|README.md|Copied from \\x{5C}Us\\x{65}rs\\x{5C}someone\\x{5C}Code\\x{5C}x" \
    "backslash-home|FORBIDDEN (absolute home path) at README.md|README.md|and \\x{5C}ho\\x{6D}e\\x{5C}someone\\x{5C}x." \
    "wsl-unc|FORBIDDEN (Windows UNC path) at README.md|README.md|See \\x{5C}\\x{5C}wsl\$\\x{5C}Ubuntu\\x{5C}x" \
    "forward-unc-with-dollar|FORBIDDEN (forward-slash UNC path) at a.md|a.md|see /\\x{2F}wsl\$/Ubuntu/x" \
    "msys-after-bold|FORBIDDEN (MSYS drive path) at a.md|a.md|**/\\x{63}/work/cbor_det**" \
    "msys-in-table-cell|FORBIDDEN (MSYS drive path) at a.md|a.md||/\\x{64}/work/x|" \
    "msys-after-semicolon|FORBIDDEN (MSYS drive path) at a.md|a.md|x;/\\x{65}/work/y" \
    "msys-after-star|FORBIDDEN (MSYS drive path) at a.md|a.md|*/\\x{66}/work/z*" \
    "unc-after-bold|FORBIDDEN (forward-slash UNC path) at a.md|a.md|**/\\x{2F}server/share/x**" \
    "boundary-benign|pass|a.md|https://alire.ada.dev/c/x a/b/c ./c/x x+/c/y v1.2/c/d" \
    "bare-record-ids|FORBIDDEN (private record name) at README.md|README.md|See t\\x{30}041 and d\\x{30}019 for the design." \
    "cbor-hex-bytes|pass|README.md|The self-described CBOR tag is \`D\\x{39} D\\x{39} F7\`; a date is \`C0 74\`." \
    "cbor-hex-vector|pass|tests/vectors/magic.txt|D\\x{39} D\\x{39} F7 A1 01 02" \
    "lone-d0|FORBIDDEN (ticket or decision) at a.md|a.md|the byte D\\x{30} alone" \
    "t32-is|FORBIDDEN (ticket or decision) at a.md|a.md|T\\x{33}2 is the type" \
    "hex-pair-two-spaces|FORBIDDEN (ticket or decision) at a.md|a.md|D\\x{39}  D\\x{39}" \
    "hex-lower-case-neighbour|FORBIDDEN (ticket or decision) at a.md|a.md|See D\\x{32} be careful" \
    "fenced-code-bash-test|pass|README.md|\`\`\`sh\\n\\x{5B}[ -n \"\$x\" ]]\\n\`\`\`" \
    "tilde-fenced-bash-test|pass|README.md|~~~\\n\\x{5B}[ -n \"\$x\" ]]\\n~~~" \
    "code-span-bash-test|pass|README.md|Run \`if \\x{5B}[ -n \"\$x\" ]]; then :; fi\` first." \
    "code-span-diagnostic|pass|README.md|Diagnostic notation: \`\\x{5B}[true, \"a\"], 1]\` and \`\\x{5B}[\"a\"]]\` and \`\\x{5B}[1, [2]]]\`." \
    "code-span-note-name|FORBIDDEN (wikilink) at README.md|README.md|see \`\\x{5B}[note-name]]\`" \
    "code-span-note-alias|FORBIDDEN (wikilink) at README.md|README.md|see \`\\x{5B}[note_name|the text]]\`" \
    "code-span-note-heading|FORBIDDEN (wikilink) at README.md|README.md|see \`\\x{5B}[note-name#heading]]\`" \
    "code-span-true|FORBIDDEN (wikilink) at README.md|README.md|see \`\\x{5B}[true]]\`" \
    "fenced-code-note|FORBIDDEN (wikilink) at README.md:2|README.md|\`\`\`\\n\\x{5B}[note-name]]\\n\`\`\`" \
    "fenced-code-diagnostic|pass|README.md|\`\`\`\\n\\x{5B}[1, [2]]]\\n\`\`\`\\ntext" \
    "tilde-fenced-code-note|FORBIDDEN (wikilink) at README.md:2|README.md|~~~\\n\\x{5B}[note]]\\n~~~" \
    "emoji-zwj-sequence|FORBIDDEN (zero-width or format character) at README.md|README.md|Maintained with care \\u{1F469}\\u{200D}\\u{1F4BB} by the team." \
    "run-user|FORBIDDEN (per-user path) at a.md|a.md|see /ru\\x{6E}/user/501/x" \
    "media|FORBIDDEN (per-user path) at a.md|a.md|see /medi\\x{61}/someone/USB/x" \
    "run-media|FORBIDDEN (per-user path) at a.md|a.md|see /ru\\x{6E}/medi\\x{61}/someone/x" \
    "root-home|FORBIDDEN (per-user path) at a.md|a.md|see /roo\\x{74}/work/x" \
    "per-user-benign|pass|a.md|src/roo\\x{74}/x and the media/ folder and /ru\\x{6E}/lock" \
    "users-upper|FORBIDDEN (absolute home path) at a.txt|a.txt|see /US\\x{45}RS/someone/x" \
    "home-mixed-case|FORBIDDEN (absolute home path) at a.md|a.md|cd /Ho\\x{6D}e/someone" \
    "unc-forward-line-start|FORBIDDEN (forward-slash UNC path) at a.txt|a.txt|/\\x{2F}server/share/x" \
    "unc-forward-quote|FORBIDDEN (forward-slash UNC path) at a.sh|a.sh|x=\"/\\x{2F}server/share\"" \
    "unc-forward-equals|FORBIDDEN (forward-slash UNC path) at a.txt|a.txt|dir=/\\x{2F}server/share" \
    "unc-forward-bracket|FORBIDDEN (forward-slash UNC path) at a.md|a.md|(/\\x{2F}host/share)" \
    "unc-forward-colon|FORBIDDEN (forward-slash UNC path) at a.yml|a.yml|path: /\\x{2F}host/share" \
    "unc-forward-after-colon|FORBIDDEN (forward-slash UNC path) at a.txt|a.txt|x=1;:/\\x{2F}host/share" \
    "unc-forward-benign|pass|README.md|/\\x{2F} a comment, https://alire.ada.dev/x, a/\\x{2F}b/c and /\\x{2F}x alone" \
    "msys-non-ascii|FORBIDDEN (MSYS drive path) at a.sh|a.sh|cd /\\x{64}/\\u{E9}t\\u{E9}" \
    "ticket|FORBIDDEN (ticket or decision) at a.md|a.md|fixed in T\\x{34}1" \
    "decision|FORBIDDEN (ticket or decision) at src/x.ads|src/x.ads|--  (D\\x{31}9)" \
    "question|FORBIDDEN (question id) at a.md|a.md|as workspace/Q\\x{31}7 says" \
    "short-decision-markdown|FORBIDDEN (ticket or decision) at CHANGELOG.md|CHANGELOG.md|See D\\x{32}." \
    "short-decision-uppercase-md|FORBIDDEN (ticket or decision) at probe.MD|probe.MD|See D\\x{32}." \
    "short-ticket-markdown|FORBIDDEN (ticket or decision) at a.md|a.md|T\\x{31}" \
    "short-ticket-text|FORBIDDEN (ticket or decision) at a.txt|a.txt|See T\\x{31}" \
    "short-decision-ada-comment|FORBIDDEN (ticket or decision) at src/x.adb|src/x.adb|X := 1;  --  see D\\x{32}" \
    "short-decision-adc-comment|FORBIDDEN (ticket or decision) at src/gnat.adc|src/gnat.adc|-- see D\\x{32}" \
    "short-decision-gpr-comment|FORBIDDEN (ticket or decision) at p.gpr|p.gpr|--  see D\\x{32}" \
    "short-ticket-shell-comment|FORBIDDEN (ticket or decision) at a.sh|a.sh|x=1  # see T\\x{31}" \
    "short-ticket-toml-comment|FORBIDDEN (ticket or decision) at tests/alire.toml|tests/alire.toml|# T\\x{31}" \
    "short-decision-workflow|FORBIDDEN (ticket or decision) at .github/workflows/ci.yml|.github/workflows/ci.yml|      - name: step for D\\x{32}" \
    'short-ids-in-ada-code|pass|src/x.adb|   X : constant := T\x{31} + D\x{32} + Text1;' \
    'short-ids-in-ada-string|pass|src/x.adb|   S : constant String := "T\x{31} and D\x{32}";' \
    'short-id-after-dashes-in-string|pass|src/x.adb|   S : constant String := "-- T\x{31}";' \
    'short-id-in-shell-code|FORBIDDEN (ticket or decision) at a.sh|a.sh|n=${#T\x{31}[@]}' \
    'short-ids-in-json-code|pass|a.json|[1, 2]' \
    'short-ids-in-words|pass|README.md|Text1, T1x and xD2' \
    "zero-width-space|FORBIDDEN (zero-width or format character) at a.md|a.md|a\\u{200B}b" \
    "zero-width-non-joiner|FORBIDDEN (zero-width or format character) at a.md|a.md|a\\u{200C}b" \
    "zero-width-joiner|FORBIDDEN (zero-width or format character) at a.sh|a.sh|a\\u{200D}b" \
    "word-joiner|FORBIDDEN (zero-width or format character) at a.txt|a.txt|a\\u{2060}b" \
    "byte-order-mark-inside|FORBIDDEN (zero-width or format character) at a.md|a.md|clean\\n\\u{FEFF}b" \
    "sibling|FORBIDDEN (parent-directory path) at a.sh|a.sh|cp $up/other-crate/x ." \
    "sibling-windows|FORBIDDEN (parent-directory path) at a.txt|a.txt|$up\\x{5C}other-crate\\x{5C}x" \
    "grandparent|FORBIDDEN (parent-directory path) at a.sh|a.sh|cd $up/$up/x" \
    "parent-hidden|FORBIDDEN (parent-directory path) at a.txt|a.txt|$up/.hidden" \
    "root-workflow-parent|FORBIDDEN (parent-directory path) at .github/workflows/ci.yml|.github/workflows/ci.yml|      - run: cat $up/src/private.txt" \
    "readme-parent|FORBIDDEN (parent-directory path) at README.md|README.md|cat $up/src/private.txt" \
    "crate-dirs-elsewhere|FORBIDDEN (parent-directory path) at scripts/other.sh|scripts/other.sh|cd $up/src && cat $up/tests/x" \
    "exemption-in-other-file|FORBIDDEN (parent-directory path) at CHANGELOG.md|CHANGELOG.md|$proof" \
    "exemption-plus-extra|FORBIDDEN (parent-directory path) at README.md|README.md|$readme_proof && cat $up/src/x" \
    "matrix-path-in-other-script|FORBIDDEN (parent-directory path) at scripts/other.sh|scripts/other.sh|cd \"\$(dirname \"\$0\")/$up/tests\"" \
    "readme-proof|pass|README.md|$readme_proof" \
    "readme-old-proof|FORBIDDEN (parent-directory path) at README.md|README.md|$proof" \
    "workflow-proof|pass|.github/workflows/ci.yml|        run: $proof" \
    "gpr-proof|pass|cbor_det.gpr|   --    alr exec -- gnatprove -P $up/cbor_det.gpr" \
    "tests-toml-proof|pass|tests/alire.toml|# manifest: GNATprove, run as \`alr exec -- gnatprove -P $up/cbor_det.gpr\`" \
    "matrix-path|pass|scripts/matrix.sh|cd \"\$(dirname \"\$0\")/$up/tests\"" \
    "tests-pin|pass|tests/alire.toml|cbor_det = { path = \"$up\" }" \
    "dirname-up|pass|a.sh|cd \"\$(dirname \"\$0\")/$up\"" \
    "sha256|pass|a.txt|e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855" \
    "ordinary|pass|README.md|Ada2022 RFC 8949 BSD-3-Clause ubuntu-24.04 -gnatW8 -O3 x86_64 2026-10-11"
  st_end
}

gate_main leakage leakage_perl self_test "$@"
exit $?
