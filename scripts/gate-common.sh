# Shared by scripts/check-sources.sh and scripts/check-leakage.sh, which
# source it; never run on its own. Needs bash 3.2 or later, perl 5.16 or
# later (core modules only), and git for the git and staged modes.
#
# What the gates are for: they stop accidents and a careless author. They
# cannot stop someone trying to beat a shell scanner: escaped or encoded
# representations (JSON \u escapes, percent-encoding, base64, HTML
# entities, compressed data) are not decoded, and are an unsupported way
# to write anything the gates look for.
#
# It holds four things:
#
#   gate_inventory   every file of the crate, in one of three modes:
#                    git     the crate directory is the root of a git work
#                            tree: the index (git ls-files -s, with each
#                            entry's mode) plus the untracked files that
#                            are not ignored, read from the working tree.
#                            This is the shipping check (with
#                            --require-git, as CI runs it).
#                    staged  with --staged: what git commit would record,
#                            the index, each file read from its blob. It
#                            needs the crate to be the root of a git
#                            repository, a non-empty index, and the gate
#                            files (scripts/check-sources.sh,
#                            scripts/check-leakage.sh,
#                            scripts/gate-common.sh, .githooks/pre-commit)
#                            in it as regular files. The pre-commit hook
#                            runs this mode.
#                    find    a convenience before git init, not the
#                            shipping check: the crate is not a git
#                            repository (or git is not installed and there
#                            is no .git): find, hidden files and nested
#                            directories included, leaving out only what
#                            .gitignore ignores: the directories obj, lib,
#                            bin, alire, config, tests/obj, tests/lib,
#                            tests/bin, tests/alire and tests/config (and
#                            only when they are real directories), and
#                            .DS_Store files; and anything named .git,
#                            which git never records (so a stray .git is
#                            not scanned). It uses the first find on the
#                            PATH that behaves as a POSIX find, so the
#                            find of Windows' System32 (a text search) is
#                            passed over; with none, the gate refuses.
#                            --require-git refuses to run in this mode.
#                    Any other git failure is an error.
#   gate_run         runs a gate: the common perl below, then the gate's
#                    own perl, over the inventory. Every file must first
#                    pass the common checks; a file that fails one is
#                    refused, never skipped:
#                      - it is a regular file: a symbolic link, a
#                        submodule, a fifo, a missing tracked file or an
#                        unmerged entry is refused. Symbolic links are
#                        refused from the index mode (120000) in git and
#                        staged mode, so the rule does not depend on the
#                        checkout's symbolic link support (Git for Windows
#                        with core.symlinks=false checks a link out as a
#                        plain file holding its target), and from the
#                        working tree as well; a working-tree directory on
#                        the way to a file that is a symbolic link, or
#                        whose real path differs from its path (a Windows
#                        junction), is refused too;
#                      - its kind is known: the extensions ads, adb, adc,
#                        ada and gpr (Ada), toml, json, yml, yaml, md, txt,
#                        sh and py, in any case, or one of the exact names
#                        LICENSE, CODEOWNERS, .editorconfig, .gitignore and
#                        .gitattributes (anywhere), and
#                        .githooks/pre-commit (at the crate root);
#                      - Windows can hold its name: no component is a
#                        reserved device name (CON, PRN, AUX, NUL, CONIN$,
#                        CONOUT$, COM0-9, LPT0-9, and COM or LPT with a
#                        superscript one, two or three; any case, with or
#                        without an extension) or ends in a dot or a space, no
#                        character is one of < > : " | ? * \ or a control
#                        character, and no two paths are equal under case
#                        folding (and NFC), since macOS and Windows
#                        checkouts cannot hold both;
#                      - it can be read, has no NUL byte and is valid
#                        UTF-8 (a UTF-8 byte order mark at the start is
#                        allowed, so UTF-16 in any form is refused).
#                    Exit status: 0 clean, 1 something refused, 2 the gate
#                    could not run. No child process may write to the
#                    terminal: the standard error of git, find, mktemp,
#                    uname, cygpath and perl is captured and discarded,
#                    and a child is judged by its exit status alone (a
#                    failure is an error with a fixed message). Every
#                    child runs with LC_ALL=C, so a broken locale in the
#                    environment cannot break a run; the perl decodes
#                    UTF-8 itself where the rules need it.
#   output           nothing a gate prints contains matched text: a
#                    finding is the class, the file and the line number
#                    only. A file name that itself matches a leakage rule
#                    (or is not plain printable ASCII) is not printed
#                    either: it is shown as its position in the inventory.
#   st_*             the end-to-end self-test harness: each case builds a
#                    small crate in a temporary directory, with copies of
#                    the gates, of this file and of the pre-commit hook,
#                    and runs a gate's real entry point on it, in find,
#                    git and staged mode (git init only inside that
#                    temporary directory; without git, the git and staged
#                    runs are counted as skipped). The harness prints only
#                    fixed messages and fixture output, never a path,
#                    except in the diagnosis of a failed hook case, which
#                    is scrubbed (st_scrub). SELF_TEST_ONLY selects the
#                    cases whose names contain it (st_matches); the run
#                    then ends "self-test: PARTIAL".
#                    Where the system cannot make a symbolic link (Git
#                    Bash copies instead), link cases in git and staged
#                    mode use what Git for Windows checks out: a 120000
#                    index entry and a plain file holding the target;
#                    cases the system cannot build (a link in find mode,
#                    a directory link, an unreadable file, a fifo) are
#                    skipped, each with a printed reason, and counted.
#                    ST_FAKE_NO_LINKS=1 forces the no-link path.
#
# Path identity. The git and staged modes compare git's top-level
# directory with the crate's physical directory, and the junction check
# compares each directory's real path with its path. On Windows under
# MSYS, Git Bash or Cygwin (uname -s starting MINGW, MSYS or CYGWIN, with
# cygpath on the PATH) both sides go through cygpath -m, drive letter
# lower-cased, before they are compared; elsewhere they are compared as
# they are. The self-test exercises that Windows path with a stand-in
# uname and cygpath; git mode and the cygpath comparison on Windows are
# verified by the CI gates job on the Windows runner (--require-git), not
# by a local run. A local Windows check needs no git: in Git Bash, in a
# plain copy of the crate, scripts/windows-check.sh runs the gates in find
# mode (if Windows' own find comes first on the PATH and no POSIX find
# follows it, export PATH=/usr/bin:$PATH first).

# Every child runs in the C locale.
export LC_ALL=C
unset LANG LANGUAGE LC_CTYPE LC_COLLATE LC_MESSAGES LC_MONETARY LC_NUMERIC \
  LC_TIME LC_ADDRESS LC_IDENTIFICATION LC_MEASUREMENT LC_NAME LC_PAPER \
  LC_TELEPHONE 2> /dev/null || true

# The gate files the staged mode requires in the index.
GATE_FILES="scripts/check-sources.sh scripts/check-leakage.sh scripts/gate-common.sh .githooks/pre-commit"

# gate_windows: succeeds on MSYS, Git Bash or Cygwin with cygpath.
gate_windows () {
  case "$(uname -s 2> /dev/null)" in
    MINGW*|MSYS*|CYGWIN*) command -v cygpath > /dev/null 2>&1 ;;
    *) return 1 ;;
  esac
}

# gate_identity PATH: PATH in the form paths are compared in.
gate_identity () {
  local p
  if gate_windows; then
    if ! p=$(cygpath -m "$1" 2> /dev/null) || [ -z "$p" ]; then
      return 1
    fi
    case "$p" in
      [A-Za-z]:*) p="$(printf '%s' "${p%%:*}" | tr 'A-Z' 'a-z'):${p#*:}" ;;
    esac
    printf '%s\n' "$p"
  else
    printf '%s\n' "$1"
  fi
}

# gate_same_path A B: succeeds when A and B name the same directory.
gate_same_path () {
  local a b
  a=$(gate_identity "$1") && b=$(gate_identity "$2") && [ "$a" = "$b" ]
}

# gate_inventory DIR STAGED: writes the crate's files, NUL-separated, to
# DIR/list (git and staged mode: git ls-files -s records; find mode:
# paths) and DIR/others (git mode: untracked paths), and sets GATE_MODE.
# Returns 2, after printing an ERROR line, on any failure.
gate_inventory () {
  local dir=$1 staged=$2 err="$1/err" top here status gate_find
  : > "$dir/others" 2> /dev/null || { echo "ERROR: cannot write a temporary file"; return 2; }
  if ! here=$(pwd -P 2> /dev/null); then
    echo "ERROR: cannot resolve the crate directory"
    return 2
  fi
  if [ "$staged" = yes ]; then
    GATE_MODE=staged
    if ! command -v git > /dev/null 2>&1; then
      echo "ERROR: --staged needs git"
      return 2
    fi
    if ! top=$(git rev-parse --show-toplevel 2> /dev/null); then
      echo "ERROR: --staged needs a git repository"
      return 2
    fi
    if ! gate_same_path "$top" "$here"; then
      echo "ERROR: --staged needs the crate to be the root of its git repository"
      return 2
    fi
    if ! git ls-files -z -s > "$dir/list" 2> /dev/null; then
      echo "ERROR: git ls-files failed"
      return 2
    fi
    return 0
  fi
  GATE_MODE=find
  if command -v git > /dev/null 2>&1; then
    top=$(git rev-parse --show-toplevel 2> "$err")
    status=$?
    if [ "$status" -eq 0 ]; then
      if gate_same_path "$top" "$here"; then
        GATE_MODE=git
      fi
    elif grep -q 'not a git repository' "$err" 2> /dev/null; then
      GATE_MODE=find
    else
      echo "ERROR: git failed (status $status)"
      return 2
    fi
  elif [ -e .git ]; then
    echo "ERROR: .git exists but git is not installed"
    return 2
  fi
  if [ "$GATE_MODE" = git ]; then
    if ! git ls-files -z -s > "$dir/list" 2> /dev/null \
       || ! git ls-files -z --others --exclude-standard > "$dir/others" 2> /dev/null; then
      echo "ERROR: git ls-files failed"
      return 2
    fi
  else
    if ! gate_find=$(gate_pick_find); then
      echo "ERROR: no usable find on PATH: find mode needs a POSIX find."
      echo "On Windows, the find of System32 is a text search; put Git's"
      echo "tools first: export PATH=/usr/bin:\$PATH"
      return 2
    fi
    status=0
    "$gate_find" . \( \( -path ./obj -o -path ./lib -o -path ./bin -o -path ./alire \
                     -o -path ./config -o -path ./tests/obj -o -path ./tests/lib \
                     -o -path ./tests/bin -o -path ./tests/alire \
                     -o -path ./tests/config \) -type d \) -prune \
              -o \( -name .DS_Store -type f \) -prune \
              -o -name .git -prune \
              -o ! -type d -print0 > "$dir/list" 2> /dev/null || status=$?
    if [ "$status" -ne 0 ]; then
      echo "ERROR: find failed (status $status)"
      return 2
    fi
  fi
  return 0
}

# gate_pick_find: prints the first find on PATH that behaves as a POSIX
# find (it lists "." for "find . -maxdepth 0 -print0"), whatever comes
# before it: on Windows the find of System32, a text search, can come
# first. Only absolute PATH entries are tried. Fails if there is none.
gate_pick_find () {
  local d old_ifs=$IFS
  IFS=:
  set -f
  for d in $PATH; do
    case "$d" in /*) ;; *) continue ;; esac
    if [ -f "$d/find" ] && [ -x "$d/find" ] \
       && [ "$("$d/find" . -maxdepth 0 -print0 2> /dev/null | tr '\000' '\n')" = "." ]; then
      set +f
      IFS=$old_ifs
      printf '%s\n' "$d/find"
      return 0
    fi
  done
  set +f
  IFS=$old_ifs
  return 1
}

# The perl every gate starts with. After it:
#   @RULES   [class, pattern] of the path and reference rules;
#   $FORMAT, $WIKILINK   format characters, and a wikilink;
#   ada_segments()   the Ada tokenizer;
#   %SCANNED  path => kind of every file that passed the common checks;
#   @FILES   one entry per file that passed the common checks:
#            [path, kind, bytes (byte order mark removed), characters,
#             byte order mark flag, the path as it may be printed, the
#             path as characters].
gate_common_perl () {
  cat <<'PERL'
use strict;
use warnings;
use feature qw(fc);
use Encode ();
use Cwd ();
use Unicode::Normalize ();

our ($LIST, $OTHERS, $MODE) = @ARGV;
our $BAD = 0;
our (@FILES, %ENTRY, %SCANNED);
our $FORMAT = qr{[\x{200B}\x{200C}\x{200D}\x{2060}\x{FEFF}\p{Cf}]};
our $WIKILINK = qr{\[\[[^\[\]]*\p{L}[^\[\]]*\]\]};
binmode STDOUT;

sub refuse {
  my ($what, $where) = @_;
  print "FORBIDDEN ($what) at $where\n";
  $BAD = 1;
}

# Ends the run as an error, with a fixed message.
sub fail_run {
  my ($message) = @_;
  print "ERROR: $message\n";
  exit 2;
}

sub decode_strict {
  my ($bytes) = @_;
  return eval {
    Encode::decode("UTF-8", $bytes, Encode::FB_CROAK | Encode::LEAVE_SRC)
  };
}

# The Ada 2022 reserved words.
our %ADA_RESERVED = map { $_ => 1 } qw(abort abs abstract accept access
  aliased all and array at begin body case constant declare delay delta
  digits do else elsif end entry exception exit for function generic goto
  if in interface is limited loop mod new not null of or others out
  overriding package parallel pragma private procedure protected raise
  range record rem renames requeue return reverse select separate some
  subtype synchronized tagged task terminate then type until use when
  while with xor);

# Ada text (line ends already LF) as [type, text, line] segments: code,
# string (its contents), char (the character), comment (after "--"). A
# quote after an identifier that is not a reserved word, after ")" or
# "]", or after an attribute name is an attribute tick; anywhere else it
# starts a character literal.
sub ada_segments {
  my ($text) = @_;
  my (@seg, $prev);
  my $line = 0;
  $prev = "";
  pos($text) = 0;
  while (pos($text) < length $text) {
    if ($text =~ /\G\n/gc) {
      push @seg, ["code", "\n", $line];
      $line++;
    } elsif ($text =~ /\G([ \t]+)/gc) {
      push @seg, ["code", $1, $line];
    } elsif ($text =~ /\G--([^\n]*)/gc) {
      push @seg, ["comment", $1, $line];
    } elsif ($text =~ /\G"((?:[^"\n]|"")*)"/gc) {
      push @seg, ["string", $1, $line];
      $prev = "other";
    } elsif ($text =~ /\G'/gc) {
      if ($prev =~ /\A(?:id|attr|close)\z/) {
        push @seg, ["code", "'", $line];
        $prev = "tick";
      } elsif ($text =~ /\G([^\n])'/gc) {
        push @seg, ["char", $1, $line];
        $prev = "other";
      } else {
        push @seg, ["code", "'", $line];
        $prev = "tick";
      }
    } elsif ($text =~ /\G([\p{L}\p{N}_]+)/gc) {
      my $word = $1;
      push @seg, ["code", $word, $line];
      $prev = $prev eq "tick" ? "attr"
            : $ADA_RESERVED{lc $word} ? "reserved" : "id";
    } elsif ($text =~ /\G(.)/gcs) {
      push @seg, ["code", $1, $line];
      $prev = ($1 eq ")" || $1 eq "]") ? "close" : "other";
    }
  }
  return @seg;
}

# The kind of a file from its name, or undef.
sub classify {
  my ($path) = @_;
  my $base = $path =~ s{.*/}{}r;
  return "license" if $base eq "LICENSE";
  return "text" if $base eq "CODEOWNERS" || $base eq ".editorconfig";
  return "gitconfig" if $base eq ".gitignore" || $base eq ".gitattributes";
  return "shell" if $path eq ".githooks/pre-commit";
  return undef unless $base =~ /.\.([^.]+)\z/s || $base =~ /\A\.([^.]+)\z/s;
  my $ext = lc $1;
  return "ada"      if $ext =~ /\A(?:ads|adb|adc|ada|gpr)\z/;
  return "markdown" if $ext eq "md";
  return "text"     if $ext eq "txt";
  return "toml"     if $ext eq "toml";
  return "shell"    if $ext eq "sh";
  return "python"   if $ext eq "py";
  return "yaml"     if $ext =~ /\A(?:yml|yaml)\z/;
  return "json"     if $ext eq "json";
  return undef;
}

# Why Windows cannot hold a path, or "".
sub windows_problem {
  my ($path) = @_;
  my $chars = decode_strict($path) // $path;
  for my $c (split m{/}, $chars) {
    return "Windows-invalid file name" if $c =~ /[<>:"|?*\\\x00-\x1F]/;
    return "Windows-reserved name, or a name ending in a dot or space"
      if $c =~ /\A(?:con|prn|aux|nul|conin\$|conout\$|com[0-9\x{B9}\x{B2}\x{B3}]|lpt[0-9\x{B9}\x{B2}\x{B3}])(?:\..*)?\z/is
      || $c =~ /[. ]\z/;
  }
  return "";
}

# The path and reference rules, built from fragments so that this file
# passes its own scan. A path family is matched in any case; a path that
# starts after a boundary may follow the start of a line, white space,
# quotes, a backtick, =, :, a comma, or any bracket.
my $bs = chr 92;
my ($us, $ho, $vo, $pc, $cy, $pr, $vf, $nd) = ("Us" . "ers", "ho" . "me",
  "Vol" . "umes", "pr" . "oc", "cyg" . "drive", "pri" . "vate",
  "fol" . "ders", "bra" . "in");
my $furl = "fi" . "le:" . "//";
my $edge = qr{(?:^|(?<=[^A-Za-z0-9/.+:-]))};
my $pre = qr{(?:$edge|(?<![A-Za-z0-9+.-]):)};
my $per_user = qr{(?<![A-Za-z0-9._-])};
our @RULES = (
  ["absolute home path",        qr{/(?:$us|$ho)/}i],
  ["absolute home path",        qr{(?<![A-Za-z0-9_])\Q$bs\E(?:$us|$ho)\Q$bs\E}i],
  ["absolute volume path",      qr{/$vo/}i],
  ["process file system path",  qr{/$pc/}i],
  ["Cygwin drive path",         qr{/$cy/}i],
  ["mounted drive path",        qr{/mnt/[A-Za-z]/}i],
  ["MSYS drive path",           qr{(?:$edge|:)/[c-zC-Z]/[^\s/]}],
  ["forward-slash UNC path",    qr{$pre//[A-Za-z0-9._\$-]+/[^\s/]}],
  ["file URL",                  qr{\Q$furl\E}i],
  ["extended-length path",      qr{\Q$bs$bs\E[?.]\Q$bs\E|\Q$bs\E[?][?]\Q$bs\E}],
  ["absolute Windows path",     qr{(?<![A-Za-z0-9_])[A-Za-z]:[\\/]}],
  ["Windows UNC path",          qr{(?<!\Q$bs\E)\Q$bs$bs\E[A-Za-z0-9._\$-]+\Q$bs\E[A-Za-z0-9._\$-]}],
  ["per-user temporary path",   qr{/$pr/(?:tmp|var)\b}i],
  ["per-user temporary path",   qr{/var/$vf/}i],
  ["per-user temporary path",   qr{/tmp/[^/\s]*-[0-9]+(?:/|\b)}i],
  ["per-user path",             qr{$per_user/run/user/[0-9]+/}i],
  ["per-user path",             qr{$per_user/(?:run/)?media/[^/\s]+/}i],
  ["per-user path",             qr{$per_user/root/}i],
  ["private notes",             qr{\b$nd\b}i],
  ["private record name",       qr{\b[tdTD][0-9]{4}-[A-Za-z]}],
  ["private record name",       qr{\b[tdTD][0-9]{4}\b}],
  ["question id",               qr{\b[A-Za-z0-9_-]+/Q[0-9]+\b}],
);

# Reads a file of the working tree: returns its bytes, or nothing after
# refusing it.
sub read_file {
  my ($path, $shown) = @_;
  my @st = lstat $path;
  unless (@st) { refuse("missing or unreadable entry", $shown); return; }
  if (-l _) { refuse("symbolic link", $shown); return; }
  unless (-f _) { refuse("not a regular file", $shown); return; }
  my $fh;
  unless (open $fh, "<:raw", $path) {
    refuse("cannot read", $shown);
    return;
  }
  my $bytes = do { local $/; <$fh> };
  unless (close $fh && defined $bytes) { refuse("cannot read", $shown); return; }
  return $bytes;
}

# Reads a blob of the index: returns its bytes, or nothing after refusing.
sub read_blob {
  my ($sha, $shown) = @_;
  my $fh;
  unless (open $fh, "-|", "git", "cat-file", "blob", $sha) {
    refuse("cannot read", $shown);
    return;
  }
  binmode $fh;
  my $bytes = do { local $/; <$fh> };
  unless (close $fh && defined $bytes) { refuse("cannot read", $shown); return; }
  return $bytes;
}

# Checks the bytes of a file: returns (bytes without a byte order mark,
# characters, byte order mark flag), or nothing after refusing.
sub check_bytes {
  my ($bytes, $shown) = @_;
  if ($bytes =~ /\0/) { refuse("NUL byte", $shown); return; }
  my $bom = $bytes =~ s/\A\xEF\xBB\xBF// ? 1 : 0;
  my $chars = decode_strict($bytes);
  unless (defined $chars) { refuse("not valid UTF-8", $shown); return; }
  return ($bytes, $chars, $bom);
}

# A path in the form paths are compared in (see the header).
sub identity {
  my ($p) = @_;
  return $p unless $ENV{GATE_WINDOWS};
  my $fh;
  open $fh, "-|", "cygpath", "-m", $p or return undef;
  my $out = do { local $/; <$fh> };
  close $fh or return undef;
  return undef unless defined $out;
  chomp $out;
  $out =~ s/\A([A-Za-z]):/lc($1) . ":"/e;
  return $out;
}

# A working-tree directory on the way to PATH that is a symbolic link, or
# whose real path is not its path (a junction): returns the reason.
my $CWD = Cwd::getcwd();
my %ANCESTOR;
sub ancestor_problem {
  my ($path) = @_;
  my @parts = split m{/}, $path;
  pop @parts;
  my $prefix = "";
  for my $part (@parts) {
    $prefix = $prefix eq "" ? $part : "$prefix/$part";
    unless (exists $ANCESTOR{$prefix}) {
      my $problem = "";
      if (-l $prefix) {
        $problem = "symbolic link in the path";
      } elsif (-d $prefix) {
        my $real = Cwd::realpath($prefix);
        my ($a, $b) = defined $real && defined $CWD
          ? (identity($real), identity("$CWD/$prefix")) : (undef, undef);
        $problem = "symbolic link or junction in the path"
          unless defined $a && defined $b && $a eq $b;
      }
      $ANCESTOR{$prefix} = $problem;
    }
    return $ANCESTOR{$prefix} if $ANCESTOR{$prefix} ne "";
  }
  return "";
}

# The path as it may be printed: withheld when it is not plain printable
# ASCII, or matches a rule.
sub shown {
  my ($path) = @_;
  my $withheld = $path =~ /[^\x21-\x7E]/ || $path =~ /\.\.[\/\\]/
              || $path =~ $WIKILINK || $path =~ /\b[TD][0-9]{2,}\b/
              || windows_problem($path) ne "";
  for my $r (@RULES) { $withheld ||= $path =~ $r->[1]; }
  return $withheld ? "<file name withheld: inventory entry $ENTRY{$path}>"
                   : $path;
}

{
  my $read_list = sub {
    my ($file) = @_;
    open my $lf, "<:raw", $file or fail_run("cannot read the inventory");
    my @entries = do { local $/ = "\0"; <$lf> };
    close $lf or fail_run("cannot read the inventory");
    return grep { $_ ne "" } map { s/\0\z//r } @entries;
  };
  my @items;
  for my $e ($read_list->($LIST)) {
    if ($MODE eq "find") {
      push @items, [$e =~ s{\A\./}{}r];
    } else {
      $e =~ /\A([0-7]{6}) ([0-9a-f]+) ([0-3])\t(.+)\z/s
        or fail_run("unexpected git ls-files output");
      push @items, [$4, $1, $2, $3];
    }
  }
  push @items, [$_] for $read_list->($OTHERS);
  @items = sort { $a->[0] cmp $b->[0] } @items;
  $ENTRY{$items[$_][0]} //= $_ + 1 for 0 .. $#items;
  print "inventory: $MODE mode, ", scalar(@items), " files\n";
  if ($MODE eq "staged") {
    refuse("empty index", "the index") unless @items;
    my %regular = map { $_->[0] => 1 }
                  grep { ($_->[1] // "") =~ /\A100(?:644|755)\z/ && ($_->[3] // "") eq "0" } @items;
    for my $g (qw(scripts/check-sources.sh scripts/check-leakage.sh
                  scripts/gate-common.sh .githooks/pre-commit)) {
      refuse("gate file not in the index as a regular file", $g) unless $regular{$g};
    }
  }
  my %folded;
  for my $item (@items) {
    my $chars = decode_strict($item->[0]) // $item->[0];
    my $key = fc(Unicode::Normalize::NFC($chars));
    push @{ $folded{$key} }, $item->[0];
  }
  for my $paths (values %folded) {
    next unless @$paths > 1;
    my %distinct = map { $_ => 1 } @$paths;
    next unless keys %distinct > 1;
    refuse("case-folding collision", shown($_)) for sort keys %distinct;
  }
  for my $item (@items) {
    my ($path, $mode, $sha, $stage) = @$item;
    my $shown = shown($path);
    my $windows = windows_problem($path);
    if ($windows ne "") {
      refuse($windows, $shown);
      next;
    }
    my $kind = classify($path);
    my $bytes;
    if (defined $mode) {
      if ($stage ne "0") { refuse("unmerged index entry", $shown); next; }
      if ($mode eq "120000") { refuse("symbolic link", $shown); next; }
      unless ($mode eq "100644" || $mode eq "100755") {
        refuse("not a regular file", $shown);
        next;
      }
    }
    if ($MODE eq "staged") {
      unless (defined $kind) { refuse("unclassified file", $shown); next; }
      $bytes = read_blob($sha, $shown);
    } else {
      my $problem = ancestor_problem($path);
      if ($problem ne "") { refuse($problem, $shown); next; }
      my @st = lstat $path;
      if (@st && -l _) { refuse("symbolic link", $shown); next; }
      unless (defined $kind) { refuse("unclassified file", $shown); next; }
      $bytes = read_file($path, $shown);
    }
    next unless defined $bytes;
    my ($clean, $chars, $bom) = check_bytes($bytes, $shown);
    next unless defined $clean;
    $SCANNED{$path} = $kind;
    push @FILES, [$path, $kind, $clean, $chars, $bom, $shown,
                  decode_strict($path)];
  }
}
PERL
}

# gate_main NAME GATE_PERL_FUNCTION SELF_TEST_FUNCTION [ARG]: the entry
# point of a gate. ARG is nothing, --require-git, --staged or --self-test.
gate_main () {
  local name=$1 gate_perl=$2 self_test=$3
  shift 3
  set +e
  case "${1:-}:$#" in
    :0) gate_run "$name" "$gate_perl" no no ;;
    --require-git:1) gate_run "$name" "$gate_perl" no yes ;;
    --staged:1) gate_run "$name" "$gate_perl" yes yes ;;
    --self-test:1) "$self_test" ;;
    *) echo "usage: scripts/check-$name.sh [--require-git | --staged | --self-test]"; return 2 ;;
  esac
}

# gate_run NAME GATE_PERL_FUNCTION STAGED REQUIRE_GIT: the whole gate.
# Prints the result and returns its status (0, 1 or 2).
gate_run () {
  local name=$1 gate_perl=$2 staged=$3 require_git=$4 tmp status
  # Some mktemp implementations fall back silently when TMPDIR is wrong;
  # a wrong TMPDIR is an error here, on every platform.
  if { [ -n "${TMPDIR:-}" ] && [ ! -d "$TMPDIR" ]; } \
     || ! tmp=$(mktemp -d 2> /dev/null) || [ -z "$tmp" ]; then
    echo "ERROR: cannot create a temporary directory"
    return 2
  fi
  if ! gate_inventory "$tmp" "$staged"; then
    rm -rf "$tmp" 2> /dev/null
    return 2
  fi
  if [ "$require_git" = yes ] && [ "$GATE_MODE" = find ]; then
    echo "ERROR: --require-git: the crate is not the root of a git work tree"
    rm -rf "$tmp" 2> /dev/null
    return 2
  fi
  if gate_windows; then GATE_WINDOWS=1; else GATE_WINDOWS=; fi
  export GATE_WINDOWS
  if ! { gate_common_perl && "$gate_perl"; } > "$tmp/gate.pl" 2> /dev/null; then
    echo "ERROR: cannot write the gate program"
    rm -rf "$tmp" 2> /dev/null
    return 2
  fi
  perl "$tmp/gate.pl" "$tmp/list" "$tmp/others" "$GATE_MODE" 2> /dev/null
  status=$?
  rm -rf "$tmp" 2> /dev/null
  case "$status" in
    0) echo "$name: clean"; return 0 ;;
    1) echo "$name: REFUSED"; return 1 ;;
    2) return 2 ;;
    *) echo "ERROR: $name: the scanner failed"; return 2 ;;
  esac
}

# ---------------------------------------------------------------------
# Self-test harness.

# A name used to check that nothing is echoed; built from fragments.
ST_SECRET="zz-secret""-dir"

# st_begin GATE_SCRIPT
st_begin () {
  ST_GATE=$1
  ST_PASS=0 ST_FAIL=0 ST_SKIP=0 ST_N=0 ST_UNSELECTED=0
  # SELF_TEST_ONLY: run only the cases whose names contain it (see
  # st_select); read here only, so it changes nothing outside a self-test.
  ST_ONLY=${SELF_TEST_ONLY:-}
  if { [ -n "${TMPDIR:-}" ] && [ ! -d "$TMPDIR" ]; } \
     || ! ST_HOME=$(pwd -P 2> /dev/null) || ! ST_DIR=$(mktemp -d 2> /dev/null) \
     || [ -z "$ST_DIR" ] || ! mkdir "$ST_DIR/home" "$ST_DIR/bin" 2> /dev/null; then
    echo "ERROR: cannot set up the self-test"
    return 2
  fi
  # The bootstrap case runs a self-test inside a self-test; that inner run
  # must stop here.
  if [ -n "${ST_NESTED:-}" ]; then
    rm -rf "$ST_DIR" 2> /dev/null
    echo "self-test: refusing to run inside a self-test"
    return 2
  fi
  if command -v git > /dev/null 2>&1; then
    ST_GIT=yes
    ST_REAL_GIT=$(command -v git)
  else
    ST_GIT=no
    ST_REAL_GIT=
  fi
  if [ "$(id -u 2> /dev/null)" = 0 ]; then ST_ROOT=yes; else ST_ROOT=no; fi
  return 0
}

# Git for fixtures only: no user or system configuration.
st_git () {
  HOME="$ST_DIR/home" GIT_CONFIG_NOSYSTEM=1 git -c core.autocrlf=false \
    -c core.symlinks=true -c init.defaultBranch=main \
    -c user.name=fixture -c user.email=fixture@example.org "$@"
}

# st_put PATH CONTENT: writes CONTENT, with the escapes \n \r \t \f \v \0
# \\, \x{HH} (one byte) and \u{HHHH} (one character, as UTF-8).
st_put () {
  mkdir -p "$(dirname "$1")" && perl -e '
    my $s = shift;
    $s =~ s{\\(?:x\{([0-9A-Fa-f]{1,2})\}|u\{([0-9A-Fa-f]{1,6})\}|(.))}{
      defined $1 ? chr(hex $1)
      : defined $2 ? do { my $c = chr(hex $2); utf8::encode($c); $c }
      : $3 eq "n" ? "\n" : $3 eq "r" ? "\r" : $3 eq "t" ? "\t"
      : $3 eq "f" ? "\f" : $3 eq "v" ? "\x0B" : $3 eq "0" ? "\0" : $3
    }gse;
    binmode STDOUT;
    print $s or die;
    close STDOUT or die;' -- "$2" > "$1"
}

# st_decode TEXT: TEXT with the escapes of st_put, on standard output.
st_decode () {
  perl -e '$_ = shift; s/\\x\{([0-9A-Fa-f]{2})\}/chr hex $1/ge;
    s/\\u\{([0-9A-Fa-f]{1,6})\}/do { my $c = chr hex $1; utf8::encode($c); $c }/ge;
    binmode STDOUT; print' -- "$1"
}

# st_track PATH: in git and staged mode, tracks PATH even if ignored.
st_track () {
  if [ "$ST_MODE" != find ]; then
    st_git add -f -- "$1"
  fi
}

# st_fixture DIR: a crate with copies of the gates, of this file and of
# the pre-commit hook.
st_fixture () {
  { mkdir -p "$1/scripts" "$1/.githooks" \
    && cp "$ST_HOME/scripts/check-sources.sh" "$ST_HOME/scripts/check-leakage.sh" \
          "$ST_HOME/scripts/gate-common.sh" "$1/scripts/" \
    && cp "$ST_HOME/.githooks/pre-commit" "$1/.githooks/pre-commit" \
    && chmod +x "$1/.githooks/pre-commit"; } 2> /dev/null
}

st_failed () {
  echo "self-test FAILED: $1"
  ST_FAIL=$((ST_FAIL + 1))
}

# st_matches NAME: whether the case NAME is selected: always, unless
# SELF_TEST_ONLY is set, and then only if NAME contains it (a plain
# substring, case sensitive; a case's name is the text its FAILED or
# SKIPPED line shows, mode included, such as "fifo (find)" or "hook: a
# clean commit passes").
st_matches () {
  [ -z "$ST_ONLY" ] && return 0
  case "$1" in
    *"$ST_ONLY"*) return 0 ;;
  esac
  return 1
}

# st_select NAME: st_matches, counting the case as not selected if not.
st_select () {
  st_matches "$1" && return 0
  ST_UNSELECTED=$((ST_UNSELECTED + 1))
  return 1
}

# st_scrub: standard input to standard output with the fixture directory
# shown as <fixtures>, the home directory as ~, the user's name as <user>,
# any user's home directory (under /Users, /home or a drive's Users
# folder) as <a home directory>, and any line holding the canary
# (ST_SECRET, in any case) withheld. Each path is replaced in its MSYS,
# mixed and Windows forms where cygpath exists. For the diagnosis of a
# failed case, which shows paths and commands.
st_scrub () {
  local pairs="" f to physical
  physical=$(cd "$ST_DIR" 2> /dev/null && pwd -P)
  for f in "$ST_DIR" "$physical" "${HOME:-}" "${USERPROFILE:-}"; do
    [ -n "$f" ] || continue
    case "$f" in
      "$ST_DIR"|"$physical") to="<fixtures>" ;;
      *) to="~" ;;
    esac
    pairs="$pairs$to $f
"
    if command -v cygpath > /dev/null 2>&1; then
      pairs="$pairs$to $(cygpath -m "$f" 2> /dev/null)
$to $(cygpath -w "$f" 2> /dev/null)
"
    fi
  done
  ST_SCRUB_PAIRS=$pairs ST_SCRUB_SECRET=$ST_SECRET \
    ST_SCRUB_USERS="${USER:-}
${USERNAME:-}
${LOGNAME:-}" perl -ne '
    BEGIN {
      @pairs = sort { length $b->[1] <=> length $a->[1] }
               grep { defined $_->[1] && length $_->[1] > 1 }
               map { [split / /, $_, 2] } split /\n/, $ENV{ST_SCRUB_PAIRS};
      @users = grep { length > 1 } split /\n/, $ENV{ST_SCRUB_USERS};
      $secret = lc $ENV{ST_SCRUB_SECRET};
    }
    if (index(lc $_, $secret) >= 0) { print "<a line withheld>\n"; next; }
    for my $p (@pairs) { my ($to, $f) = @$p; s/\Q$f\E/$to/gi; }
    s{[A-Za-z]:[\\/]+Users[\\/]+[^\\/\s]+}{<a home directory>}gi;
    s{/(?:Users|home)/[^/\s]+}{<a home directory>}g;
    for my $u (@users) { s/\b\Q$u\E\b/<user>/gi; }
    print;'
}

# st_absent OUT: fails if OUT contains any line of ST_ABSENT (any case).
st_absent () {
  local out=$1 a found=no
  local IFS='
'
  set -f
  for a in $ST_ABSENT; do
    if [ -n "$a" ] && grep -qiF -- "$a" "$out"; then found=yes; fi
  done
  set +f
  [ "$found" = no ]
}

# st_run NAME MODE EXPECT SETUP [ARGS...]. MODE is find, git or staged.
# EXPECT is "-" (not run in this mode), "skip" (counted as skipped),
# "pass", "pass:TEXT" (exit 0 and TEXT in the output), "ERROR..." (exit 2
# and that text in the output) or TEXT (exit 1 and TEXT in the output).
# In every case the output must contain no line of ST_ABSENT. SETUP runs
# inside the fixture crate and may set ST_ENV (extra environment
# assignments for the gate, no spaces), ST_PREPATH (a directory, with a
# trailing colon, put first on the gate's PATH), ST_ABSENT (texts that
# must not be printed, one per line), ST_NO_ADD (yes: keep the index the
# setup made), ST_ARGS (an argument for the gate in find and git mode) and
# ST_PATH (the gate's whole PATH, after ST_PREPATH, instead of the
# harness's), or ST_SKIP_REASON (the case cannot run here: it is skipped,
# with that reason printed).
st_run () {
  local name=$1 mode=$2 expect=$3 crate out status ok
  shift 3
  case "$expect" in
    -) return 0 ;;
  esac
  st_select "$name ($mode)" || return 0
  case "$expect" in
    skip) ST_SKIP=$((ST_SKIP + 1)); return 0 ;;
  esac
  if [ "$mode" != find ] && [ "$ST_GIT" = no ]; then
    ST_SKIP=$((ST_SKIP + 1))
    return 0
  fi
  ST_N=$((ST_N + 1))
  crate="$ST_DIR/c$ST_N"
  out="$ST_DIR/c$ST_N.out"
  ST_MODE=$mode ST_ENV="" ST_PREPATH="" ST_PATH="" ST_ABSENT="" ST_NO_ADD=no ST_ARGS=""
  ST_SKIP_REASON="" ST_INDEX_LINKS=""
  if ! st_fixture "$crate"; then
    st_failed "$name ($mode): cannot build the fixture"
    return 0
  fi
  if [ "$mode" != find ] \
     && ! (cd "$crate" && st_git init -q --template=) > /dev/null 2>&1; then
    st_failed "$name ($mode): git init failed"
    return 0
  fi
  if ! cd "$crate" 2> /dev/null; then
    st_failed "$name ($mode): cannot enter the fixture"
    return 0
  fi
  "$@" 2> /dev/null
  status=$?
  if ! cd "$ST_HOME" 2> /dev/null; then
    echo "ERROR: cannot return to the crate"
    exit 2
  fi
  if [ "$status" -ne 0 ]; then
    st_failed "$name ($mode): setup failed"
    return 0
  fi
  if [ -n "$ST_SKIP_REASON" ]; then
    echo "self-test SKIPPED: $name ($mode): $ST_SKIP_REASON"
    ST_SKIP=$((ST_SKIP + 1))
    return 0
  fi
  if [ "$mode" != find ] && [ "$ST_NO_ADD" != yes ] \
     && ! (cd "$crate" && st_git add -A && st_relink) > /dev/null 2>&1; then
    st_failed "$name ($mode): git add failed"
    return 0
  fi
  set --
  if [ "$mode" = staged ]; then
    set -- --staged
  elif [ -n "$ST_ARGS" ]; then
    set -- "$ST_ARGS"
  fi
  # shellcheck disable=SC2086
  (cd "$crate" && env HOME="$ST_DIR/home" \
     GIT_CONFIG_NOSYSTEM=1 PATH="$ST_PREPATH${ST_PATH:-$PATH}" \
     $ST_ENV bash "scripts/$ST_GATE" "$@") > "$out" 2>&1
  status=$?
  ok=no
  case "$expect" in
    pass)
      if [ "$status" -eq 0 ]; then ok=yes; fi ;;
    pass:*)
      if [ "$status" -eq 0 ] && grep -qF -- "${expect#pass:}" "$out"; then
        ok=yes
      fi ;;
    ERROR*)
      if [ "$status" -eq 2 ] && grep -qF -- "$expect" "$out"; then
        ok=yes
      fi ;;
    *)
      if [ "$status" -eq 1 ] && grep -qF -- "$expect" "$out"; then
        ok=yes
      fi ;;
  esac
  if ! st_absent "$out"; then
    ok=no
    expect="$expect, and nothing withheld printed"
  fi
  if [ "$ok" = yes ]; then
    ST_PASS=$((ST_PASS + 1))
  else
    st_failed "$name ($mode): expected [$expect], exit $status:"
    sed 's/^/    /' "$out"
  fi
  return 0
}

# st_case NAME FIND_EXPECT GIT_EXPECT SETUP [ARGS...]: staged mode
# expects what git mode does.
st_case () {
  local name=$1 find_expect=$2 git_expect=$3
  shift 3
  st_case3 "$name" "$find_expect" "$git_expect" "$git_expect" "$@"
}

# st_case3 NAME FIND_EXPECT GIT_EXPECT STAGED_EXPECT SETUP [ARGS...]
st_case3 () {
  local name=$1 find_expect=$2 git_expect=$3 staged_expect=$4
  shift 4
  st_run "$name" find "$find_expect" "$@"
  st_run "$name" git "$git_expect" "$@"
  st_run "$name" staged "$staged_expect" "$@"
}

# st_both NAME EXPECT SETUP [ARGS...]: the same expectation in every mode.
st_both () {
  local name=$1 expect=$2
  shift 2
  st_case3 "$name" "$expect" "$expect" "$expect" "$@"
}

# st_table SETUP_BASE ENTRY...: each ENTRY is "name|expect|path|content";
# the fixture is SETUP_BASE plus that one file (content gets a final
# line feed). EXPECT may be "find-expect~git-and-staged-expect".
st_table () {
  local base=$1 entry name expect path content fx gx
  shift
  for entry in "$@"; do
    IFS='|' read -r name expect path content <<< "$entry"
    case "$expect" in
      *~*) fx=${expect%%~*}; gx=${expect#*~} ;;
      *) fx=$expect; gx=$expect ;;
    esac
    st_case "$name" "$fx" "$gx" "${ST_TABLE_SETUP:-st_table_setup}" "$base" \
      "$path" "$content"
  done
}

st_table_setup () {
  "$1" && st_put "$2" "$3\\n"
}

# The cases every gate shares: inventory, kinds, links, encodings,
# failures and the staged mode. BASE builds a clean crate for the gate;
# HOSTILE PATH writes an Ada file there that the gate refuses with the
# message REFUSAL followed by the path.
st_shared_cases () {
  local base=$1 hostile=$2 refusal=$3
  st_shared_base=$base
  st_shared_hostile=$hostile
  st_case3 "mode printed" "pass:inventory: find mode" \
    "pass:inventory: git mode" "pass:inventory: staged mode" "$base"
  st_case3 "staged mode outside git" "ERROR: --staged needs a git repository" \
    - - st_shared_args --staged
  st_case3 "--require-git outside git" "ERROR: --require-git" \
    "pass:inventory: git mode" - st_shared_args --require-git
  st_both "unclassified file" "FORBIDDEN (unclassified file) at notes.rst" \
    st_shared_put notes.rst 'x\n'
  st_both "unclassified dotfile" "FORBIDDEN (unclassified file) at .envrc" \
    st_shared_put .envrc 'x\n'
  st_both "nested hook path is unclassified" \
    "FORBIDDEN (unclassified file) at docs/.githooks/pre-commit" \
    st_shared_put docs/.githooks/pre-commit 'x\n'
  st_both "uppercase extension" "pass" st_shared_put NOTES.MD 'clean\n'
  st_both "Windows device name" \
    "FORBIDDEN (Windows-reserved name, or a name ending in a dot or space) at <file name withheld" \
    st_shared_put docs/con.txt 'clean\n'
  st_both "Windows device name, upper case, no extension" \
    "FORBIDDEN (Windows-reserved name, or a name ending in a dot or space) at <file name withheld" \
    st_shared_put AUX 'clean\n'
  st_both "Windows device name, numbered" \
    "FORBIDDEN (Windows-reserved name, or a name ending in a dot or space) at <file name withheld" \
    st_shared_put lpt9.md 'clean\n'
  st_both "Windows device name as a directory" \
    "FORBIDDEN (Windows-reserved name, or a name ending in a dot or space) at <file name withheld" \
    st_shared_put Com1/x.md 'clean\n'
  st_both "name ending in a dot" \
    "FORBIDDEN (Windows-reserved name, or a name ending in a dot or space) at <file name withheld" \
    st_shared_put x.md. 'clean\n'
  st_both "name ending in a space" \
    "FORBIDDEN (Windows-reserved name, or a name ending in a dot or space) at <file name withheld" \
    st_shared_put 'y.md ' 'clean\n'
  st_both "names close to device names" "pass" st_shared_device_like
  st_case3 "case-folding collision in the index" - \
    "FORBIDDEN (case-folding collision) at docs/note.md" \
    "FORBIDDEN (case-folding collision) at docs/note.md" st_shared_collision
  st_both "symbolic link to a file" "FORBIDDEN (symbolic link) at link.md" \
    st_shared_link README.md link.md
  st_both "symbolic link out of the crate" \
    "FORBIDDEN (symbolic link) at private.md" \
    st_shared_link "/ho\x{6D}e/alice/private" private.md
  st_both "broken symbolic link beside a hostile file" \
    "FORBIDDEN (symbolic link) at src/broken.ads" \
    st_shared_broken_link
  st_both "symbolic link named like a generated directory" \
    "FORBIDDEN (symbolic link) at obj" st_shared_obj_link
  st_case3 "directory replaced by a symbolic link after staging" \
    "FORBIDDEN (symbolic link) at docs" \
    "FORBIDDEN (symbolic link in the path) at docs/x.md" "pass" \
    st_shared_ancestor_link
  st_case3 "link in the index, plain file in the working tree" - \
    "FORBIDDEN (symbolic link) at link.md" \
    "FORBIDDEN (symbolic link) at link.md" st_shared_index_link
  st_case3 "plain file in the index, link in the working tree" - \
    "FORBIDDEN (symbolic link) at a.md" "pass" st_shared_worktree_link
  st_case3 "fifo" "FORBIDDEN (not a regular file) at pipe.txt" - - \
    st_shared_fifo
  st_case3 "submodule entry in the index" - \
    "FORBIDDEN (not a regular file) at sub" \
    "FORBIDDEN (not a regular file) at sub" st_shared_gitlink
  st_both "NUL byte" "FORBIDDEN (NUL byte) at zero.md" \
    st_shared_put zero.md 'a\0b\n'
  st_both "invalid UTF-8" "FORBIDDEN (not valid UTF-8) at bad.md" \
    st_shared_put bad.md 'a\x{FF}b\n'
  st_both "UTF-8 byte order mark" "pass" \
    st_shared_put bom.md '\x{EF}\x{BB}\x{BF}clean\n'
  st_both "UTF-16LE with byte order mark" "FORBIDDEN (NUL byte) at u16.txt" \
    st_shared_utf16 u16.txt le-bom
  st_both "UTF-16BE without byte order mark" \
    "FORBIDDEN (NUL byte) at u16be.txt" st_shared_utf16 u16be.txt be
  st_case3 "unreadable file" "FORBIDDEN (cannot read) at locked.md" - - \
    st_shared_unreadable
  st_both "Windows device names COM0, LPT0, CONIN\$, CONOUT\$" \
    "FORBIDDEN (Windows-reserved name, or a name ending in a dot or space) at <file name withheld" \
    st_shared_console_names
  st_both "code owners and editor configuration files" "pass" \
    st_shared_project_files
  st_both "ignored Finder and library files" "pass" st_shared_ignored_files
  st_both "git ls-files fails" "ERROR: git ls-files failed" \
    st_shared_fake_git ls-files
  st_both "temporary directory missing, named after a secret" \
    "ERROR: cannot create a temporary directory" st_shared_missing_tmp
  st_case3 "alternate object directory missing, named after a secret" - - \
    "pass:inventory: staged mode" st_shared_missing_alternates
  st_both "git that warns on stderr" "pass" st_shared_fake_git warn
  st_case3 "git that exits 128" "ERROR: git failed" "ERROR: git failed" \
    "ERROR: --staged needs a git repository" st_shared_fake_git fail
  st_both "broken locale in the environment" "pass" st_shared_bad_locale
  st_case3 "localised git messages in the environment" \
    "pass:inventory: find mode" "pass:inventory: git mode" \
    "pass:inventory: staged mode" st_shared_german_locale
  st_both "Windows-invalid character, colon" \
    "FORBIDDEN (Windows-invalid file name) at <file name withheld" \
    st_shared_put safe:stream.txt 'clean\n'
  st_both "Windows-invalid character, question mark" \
    "FORBIDDEN (Windows-invalid file name) at <file name withheld" \
    st_shared_put 'safe?.txt' 'clean\n'
  st_both "Windows device name with a superscript digit" \
    "FORBIDDEN (Windows-reserved name, or a name ending in a dot or space) at <file name withheld" \
    st_shared_decoded_name 'COM\u{B9}.txt'
  st_case3 "Windows path identity through cygpath" - \
    "pass:inventory: git mode" "pass:inventory: staged mode" \
    st_shared_windows_identity yes
  # Without cygpath the paths cannot be compared, so the gate falls back
  # to find mode, which leaves .git out (so the crate passes).
  st_case3 "Windows path identity without cygpath" - \
    "pass:inventory: find mode" \
    "ERROR: --staged needs the crate to be the root of its git repository" \
    st_shared_windows_identity no
  st_case "tracked file in a generated directory" \
    "pass:inventory: find mode" "${refusal}obj/generated.ads" \
    st_shared_tracked_obj
  st_both "hidden nested file" "${refusal}.hidden/deep/h.ads" st_shared_hidden
  # Find mode leaves out anything named .git, as git never records it: a
  # stray, unusable .git (no HEAD, so git says this is not a repository)
  # is not scanned; names that only start with .git still are.
  st_run "stray .git in find mode" find "pass:inventory: find mode" \
    st_shared_stray_git
  st_run "a name starting with .git is scanned" find \
    "${refusal}docs/.git-note.ads" st_shared_dot_git_like docs/.git-note.ads
  st_run "a directory starting with .git is scanned" find \
    "${refusal}.github-x/h.ads" st_shared_dot_git_like .github-x/h.ads
  st_case3 "hostile in the index, clean in the working tree" - - \
    "${refusal}src/h.ads" st_shared_staged hostile-index
  st_case3 "clean in the index, hostile in the working tree" - - \
    "pass:inventory: staged mode" st_shared_staged clean-index
  st_case3 "empty index" - - "FORBIDDEN (empty index)" st_shared_empty_index
  st_case3 "gate script removed from the index" - - \
    "FORBIDDEN (gate file not in the index as a regular file) at scripts/check-sources.sh" \
    st_shared_unstage scripts/check-sources.sh
  st_case3 "hook removed from the index" - - \
    "FORBIDDEN (gate file not in the index as a regular file) at .githooks/pre-commit" \
    st_shared_unstage .githooks/pre-commit
}

st_shared_put () { "$st_shared_base" && st_put "$1" "$2"; }

st_shared_args () { "$st_shared_base" && ST_ARGS=$1; }

st_shared_device_like () {
  "$st_shared_base" && st_put console.md 'clean\n' && st_put nullable.md 'clean\n' \
    && st_put com10.md 'clean\n' && st_put docs/auxiliary.txt 'clean\n'
}

st_shared_collision () {
  local sha
  "$st_shared_base" && st_put docs/Note.md 'clean\n' && st_git add -A \
    && sha=$(st_git rev-parse :docs/Note.md) \
    && st_git update-index --add --cacheinfo "100644,$sha,docs/note.md" \
    && ST_NO_ADD=yes
}

# st_make_link TARGET NAME: a symbolic link. Where the system cannot make
# one (Git Bash without symbolic link support copies instead), git and
# staged mode get what Git for Windows checks out: a 120000 entry in the
# index and a plain file holding the target; find mode, which has no
# index, is skipped with a reason. ST_FAKE_NO_LINKS=1 forces that path.
st_make_link () {
  local sha
  if [ -z "${ST_FAKE_NO_LINKS:-}" ] && ln -s "$1" "$2" 2> /dev/null && [ -L "$2" ]; then
    return 0
  fi
  rm -rf "$2" 2> /dev/null
  if [ "$ST_MODE" = find ]; then
    ST_SKIP_REASON="symbolic links are not available here, and find mode has no index"
    return 0
  fi
  mkdir -p "$(dirname "$2")" && sha=$(printf '%s' "$1" | st_git hash-object -w --stdin) \
    && printf '%s' "$1" > "$2" \
    && ST_INDEX_LINKS="$ST_INDEX_LINKS
$sha $2" && st_relink
}

# st_relink: puts the emulated links back in the index (git add replaces
# them with regular files).
st_relink () {
  local line sha path
  local IFS='
'
  for line in $ST_INDEX_LINKS; do
    [ -n "$line" ] || continue
    sha=${line%% *}
    path=${line#* }
    st_git update-index --add --cacheinfo "120000,$sha,$path" || return 1
  done
  return 0
}

# st_need_links: skips the case (with a reason) where real links cannot
# be made.
st_need_links () {
  if [ -n "${ST_FAKE_NO_LINKS:-}" ] || ! ln -s x "$ST_DIR/link-probe-$ST_N" 2> /dev/null \
     || [ ! -L "$ST_DIR/link-probe-$ST_N" ]; then
    rm -rf "$ST_DIR/link-probe-$ST_N" 2> /dev/null
    ST_SKIP_REASON="this case needs a real symbolic link in the working tree"
    return 0
  fi
  rm -f "$ST_DIR/link-probe-$ST_N"
  return 0
}

st_shared_link () {
  local target
  "$st_shared_base" && st_put README.md 'clean\n' \
    && target=$(st_decode "$1") && st_make_link "$target" "$2"
}

st_shared_broken_link () {
  "$st_shared_base" && mkdir -p src && st_make_link nowhere.ads src/broken.ads \
    && "$st_shared_hostile" src/z.ads
}

st_shared_obj_link () {
  "$st_shared_base" && st_put real/x.md 'clean\n' && st_make_link real obj
}

# A tracked directory replaced by a link after staging (in find mode the
# link is there from the start).
st_shared_ancestor_link () {
  "$st_shared_base" && st_need_links || return 1
  [ -z "$ST_SKIP_REASON" ] || return 0
  if [ "$ST_MODE" = find ]; then
    st_put real/x.md 'clean\n' && ln -s real docs
  else
    st_put docs/x.md 'clean\n' && st_git add -A && mv docs real \
      && ln -s real docs && ST_NO_ADD=yes
  fi
}

# The Windows case: a link in the index (mode 120000), checked out as a
# plain file holding the target, as Git for Windows does with
# core.symlinks=false.
st_shared_index_link () {
  local sha
  "$st_shared_base" && st_git add -A \
    && sha=$(printf 'README.md' | st_git hash-object -w --stdin) \
    && st_git update-index --add --cacheinfo "120000,$sha,link.md" \
    && printf 'README.md' > link.md && ST_NO_ADD=yes
}

st_shared_worktree_link () {
  "$st_shared_base" && st_need_links || return 1
  [ -z "$ST_SKIP_REASON" ] || return 0
  st_put README.md 'clean\n' && st_put a.md 'clean\n' \
    && st_git add -A && rm a.md && ln -s README.md a.md && ST_NO_ADD=yes
}

st_shared_fifo () {
  "$st_shared_base" || return 1
  mkfifo pipe.txt 2> /dev/null || ST_SKIP_REASON="mkfifo is not available here"
  return 0
}

st_shared_gitlink () {
  "$st_shared_base" && st_git add -A \
    && st_git update-index --add --cacheinfo \
         160000,1111111111111111111111111111111111111111,sub \
    && ST_NO_ADD=yes
}

st_shared_utf16 () {
  "$st_shared_base" && perl -e '
    my ($order) = @ARGV;
    my $s = "/Us" . "ers/alice/private\n";
    my $u = join "", map { $order eq "be" ? "\0$_" : "$_\0" } split //, $s;
    $u = "\xFF\xFE$u" if $order eq "le-bom";
    binmode STDOUT; print $u or die; close STDOUT or die;' -- "$2" > "$1"
}

st_shared_unreadable () {
  "$st_shared_base" && st_put locked.md 'clean\n' && chmod 000 locked.md || return 1
  if [ -r locked.md ]; then
    ST_SKIP_REASON="chmod cannot make a file unreadable here"
  fi
  return 0
}

st_shared_fake_git () {
  "$st_shared_base" && mkdir -p "$ST_DIR/bin/$ST_N" || return 1
  if [ "$1" = warn ]; then
    printf '#!/bin/sh\necho "warning: harmless advice" >&2\nexec "%s" "$@"\n' \
      "$ST_REAL_GIT" > "$ST_DIR/bin/$ST_N/git"
  elif [ "$1" = fail ]; then
    printf '#!/bin/sh\necho "fatal: something else broke" >&2\nexit 128\n' \
      > "$ST_DIR/bin/$ST_N/git"
  else
    printf '#!/bin/sh\nif [ "$1" = rev-parse ]; then pwd -P; exit 0; fi\nexit 1\n' \
      > "$ST_DIR/bin/$ST_N/git"
  fi
  chmod +x "$ST_DIR/bin/$ST_N/git" && ST_PREPATH="$ST_DIR/bin/$ST_N:"
}

# Where git is translated, its "not a git repository" message is only
# recognised in the C locale.
st_shared_german_locale () {
  "$st_shared_base" && ST_ENV="LC_ALL=de_DE.UTF-8 LANG=de_DE.UTF-8 LANGUAGE=de"
}

st_shared_console_names () {
  "$st_shared_base" && st_put docs/COM0.md 'clean\n' && st_put docs/LPT0.txt 'clean\n' \
    && st_put 'docs/CONIN$.md' 'clean\n' && st_put 'CONOUT$.txt' 'clean\n'
}

st_shared_project_files () {
  "$st_shared_base" && st_put .github/CODEOWNERS '* @m-doughty\n' \
    && st_put .editorconfig 'root = true\n[*]\nend_of_line = lf\n'
}

# A Finder file and a built library, both ignored by .gitignore: find
# mode must prune them as git mode ignores them.
st_shared_ignored_files () {
  "$st_shared_base" && st_put .gitignore '/bin/\n/tests/lib/\n.DS_Store\n' \
    && st_put .DS_Store '\x{00}\x{01}' && st_put docs/.DS_Store '\x{00}' \
    && st_put tests/lib/libx.a '\x{00}!<arch>' && st_put bin/tool.o '\x{00}'
}

st_shared_bad_locale () {
  "$st_shared_base" && ST_ENV="LC_ALL=xx_INVALID.UTF-8 LANG=xx_INVALID.UTF-8"
}

st_shared_decoded_name () {
  local path
  "$st_shared_base" && path=$(st_decode "$1") && st_put "$path" 'clean\n'
}

# Stand-ins for Git Bash: uname reports MINGW, cygpath maps an MSYS path
# to the same path on drive C, and git reports its top level in that
# drive-letter form, as Git for Windows does. With $1 = no, only the git
# stand-in is installed, and the gate must run without cygpath: elsewhere
# there is none, but MSYS, Git Bash and Cygwin have one beside every other
# tool, so there the gate's PATH is a directory of the tools it needs
# without cygpath (st_tool_dir), or the case is skipped, saying why.
st_shared_windows_identity () {
  local bin="$ST_DIR/bin/$ST_N"
  "$st_shared_base" && mkdir -p "$bin" || return 1
  if [ "$1" = no ]; then
    case "$(uname -s 2> /dev/null)" in
      MINGW*|MSYS*|CYGWIN*)
        if st_tool_dir "$ST_DIR/no-cygpath-bin-$ST_N" bash sh env perl find \
             mktemp rm grep basename uname tr cat sed dirname printf mkdir \
             chmod ls cut; then
          ST_PATH="$ST_DIR/no-cygpath-bin-$ST_N"
        else
          ST_SKIP_REASON=$ST_TOOL_DIR_REASON
          return 0
        fi ;;
    esac
  fi
  printf '#!/bin/sh\nif [ "$1" = rev-parse ] && [ "$2" = --show-toplevel ]; then\n  t=$("%s" rev-parse --show-toplevel) || exit $?\n  printf "C:%%s\\n" "$t"\n  exit 0\nfi\nexec "%s" "$@"\n' \
    "$ST_REAL_GIT" "$ST_REAL_GIT" > "$bin/git" || return 1
  if [ "$1" = yes ]; then
    printf '#!/bin/sh\necho MINGW64_NT-10.0-19045\n' > "$bin/uname" || return 1
    printf '#!/bin/sh\n[ "$1" = -m ] || exit 1\ncase "$2" in\n  [A-Za-z]:*) printf "%%s\\n" "$2" ;;\n  /*) printf "C:%%s\\n" "$2" ;;\n  *) exit 1 ;;\nesac\n' \
      > "$bin/cygpath" || return 1
  fi
  chmod +x "$bin"/* && ST_PREPATH="$bin:"
}

st_shared_missing_tmp () {
  "$st_shared_base" && ST_ENV="TMPDIR=/nonexistent/$ST_SECRET/tmp" \
    && ST_ABSENT=$ST_SECRET
}

st_shared_missing_alternates () {
  "$st_shared_base" \
    && ST_ENV="GIT_ALTERNATE_OBJECT_DIRECTORIES=/nonexistent/$ST_SECRET/objects" \
    && ST_ABSENT=$ST_SECRET
}

st_shared_tracked_obj () {
  "$st_shared_base" && st_put .gitignore '/obj/\n' \
    && "$st_shared_hostile" obj/generated.ads && st_track obj/generated.ads
}

st_shared_hidden () {
  "$st_shared_base" && "$st_shared_hostile" .hidden/deep/h.ads
}

st_shared_stray_git () {
  "$st_shared_base" && st_put .git/hooks/pre-commit.sample 'x\n' \
    && st_put .git/description 'x\n' && "$st_shared_hostile" .git/h.ads \
    && "$st_shared_hostile" docs/.git/h.ads
}

st_shared_dot_git_like () {
  "$st_shared_base" && "$st_shared_hostile" "$1"
}

# In staged mode only: an index that differs from the working tree.
st_shared_staged () {
  "$st_shared_base" || return 1
  if [ "$1" = hostile-index ]; then
    "$st_shared_hostile" src/h.ads && st_git add -A \
      && st_put src/h.ads 'package H with SPARK_Mode is\nend H;\n'
  else
    st_put src/h.ads 'package H with SPARK_Mode is\nend H;\n' && st_git add -A \
      && "$st_shared_hostile" src/h.ads
  fi
  ST_NO_ADD=yes
}

st_shared_empty_index () { "$st_shared_base" && ST_NO_ADD=yes; }

st_shared_unstage () {
  "$st_shared_base" && st_git add -A && st_git rm -q --cached -- "$1" \
    && ST_NO_ADD=yes
}

# The gates' own start: a missing library, from a copy in a directory
# named after a secret, and a self-test whose TMPDIR is in such a
# directory. Nothing may print the secret.
# st_tool_dir DIR TOOL...: DIR, made afresh, holding each named tool found
# on PATH (those not found are left out), usable with PATH=DIR alone, for
# the fixtures that need a PATH without some tool. First as symbolic links
# (which MSYS makes as copies); then, if a tool cannot start from there (an
# MSYS program copied away from msys-2.0.dll stops with "error while
# loading shared libraries", exit 127), as wrapper scripts that exec each
# tool by its absolute path. Fails if neither works, with the reason in
# ST_TOOL_DIR_REASON: the caller then skips its case, saying why.
st_tool_dir () {
  local dir=$1 tool t
  shift
  ST_TOOL_DIR_REASON=""
  rm -rf "$dir" 2> /dev/null
  if ! mkdir -p "$dir" 2> /dev/null; then
    ST_TOOL_DIR_REASON="cannot make a directory of tools"
    return 1
  fi
  for tool in "$@"; do
    t=$(command -v "$tool" 2> /dev/null) || continue
    case "$t" in /*) ln -s "$t" "$dir/$tool" 2> /dev/null ;; esac
  done
  if st_tool_dir_works "$dir" "$@"; then
    return 0
  fi
  for tool in "$@"; do
    t=$(command -v "$tool" 2> /dev/null) || continue
    case "$t" in /*) ;; *) continue ;; esac
    rm -f "$dir/$tool" 2> /dev/null
    printf '#!/bin/sh\nexec "%s" "$@"\n' "$t" > "$dir/$tool" 2> /dev/null \
      && chmod +x "$dir/$tool" 2> /dev/null
  done
  if st_tool_dir_works "$dir" "$@"; then
    return 0
  fi
  ST_TOOL_DIR_REASON="the tools cannot run from a directory of their own here (neither links nor wrapper scripts start)"
  return 1
}

# st_tool_dir_works DIR TOOL...: bash in DIR runs "-c true" with PATH=DIR,
# and no other tool of DIR fails to start (exit 126, or a shared library
# it cannot load) when asked for --version. id is never run.
st_tool_dir_works () {
  local dir=$1 tool status
  shift
  [ -x "$dir/bash" ] || return 1
  (cd "$ST_DIR" 2> /dev/null && PATH="$dir" "$dir/bash" -c true) \
    > /dev/null 2>&1 || return 1
  for tool in "$@"; do
    [ "$tool" = id ] && continue
    [ -e "$dir/$tool" ] || continue
    status=0
    (cd "$ST_DIR" 2> /dev/null && PATH="$dir" "$dir/$tool" --version) \
      < /dev/null > /dev/null 2> "$ST_DIR/tool-probe.err" || status=$?
    if [ "$status" -eq 126 ] \
       || grep -q "error while loading shared libraries" "$ST_DIR/tool-probe.err" 2> /dev/null; then
      return 1
    fi
  done
  return 0
}

# st_skipped NAME REASON: a case that cannot run here, said and counted.
st_skipped () {
  st_select "$1" || return 0
  echo "self-test SKIPPED: $1: $2"
  ST_SKIP=$((ST_SKIP + 1))
}

st_bootstrap_cases () {
  local d="$ST_DIR/$ST_SECRET/missing" e="$ST_DIR/$ST_SECRET/tmp-case"
  local out="$ST_DIR/bootstrap.out" status ok
  ST_ABSENT=$ST_SECRET
  if ! st_fixture "$d" || ! rm -f "$d/scripts/gate-common.sh" 2> /dev/null \
     || ! st_fixture "$e"; then
    st_failed "bootstrap: cannot build the fixtures"
    return 0
  fi
  if st_select "bootstrap: missing library"; then
    (cd "$ST_DIR" 2> /dev/null && env HOME="$ST_DIR/home" \
       bash "$d/scripts/$ST_GATE") > "$out" 2>&1
    status=$?
    ok=no
    if [ "$status" -eq 2 ] && grep -qF "ERROR: the gate library is missing" "$out" \
       && st_absent "$out"; then
      ok=yes
    fi
    if [ "$ok" = yes ]; then ST_PASS=$((ST_PASS + 1)); else
      st_failed "bootstrap: missing library (exit $status):"
      sed 's/^/    /' "$out"
    fi
  fi
  if st_select "bootstrap: self-test with a wrong TMPDIR"; then
    (cd "$e" 2> /dev/null && env HOME="$ST_DIR/home" ST_NESTED=1 \
       TMPDIR="$ST_DIR/$ST_SECRET/nowhere" bash "scripts/$ST_GATE" --self-test) \
      > "$out" 2>&1
    status=$?
    ok=no
    if [ "$status" -eq 2 ] && grep -qF "ERROR: cannot set up the self-test" "$out" \
       && st_absent "$out"; then
      ok=yes
    fi
    if [ "$ok" = yes ]; then ST_PASS=$((ST_PASS + 1)); else
      st_failed "bootstrap: self-test with a wrong TMPDIR (exit $status):"
      sed 's/^/    /' "$out"
    fi
  fi
  st_subset_case
  st_find_cases
  st_tool_dir_cases
  # A PATH without dirname: the gate must not need it, nor print the path
  # it was started from.
  st_select "bootstrap: PATH without dirname" || return 0
  local f="$ST_DIR/$ST_SECRET/no-dirname" bin="$ST_DIR/no-dirname-bin"
  if ! st_fixture "$f" \
     || ! (cd "$f" && st_put src/cbor_det.ads 'package Cbor_Det with SPARK_Mode is\nend Cbor_Det;\n' \
             && st_put README.md 'clean\n') > /dev/null 2>&1; then
    st_failed "bootstrap: cannot build the PATH fixture"
    return 0
  fi
  if ! st_tool_dir "$bin" bash sh env perl find mktemp rm grep id basename \
         uname tr cat git; then
    st_skipped "bootstrap: PATH without dirname" "$ST_TOOL_DIR_REASON"
  else
    (cd "$ST_DIR" 2> /dev/null && env HOME="$ST_DIR/home" \
       PATH="$bin" "$bin/bash" "$f/scripts/$ST_GATE") > "$out" 2>&1
    status=$?
    ok=no
    if [ "$status" -eq 0 ] && st_absent "$out"; then
      ok=yes
    fi
    if [ "$ok" = yes ]; then ST_PASS=$((ST_PASS + 1)); else
      st_failed "bootstrap: PATH without dirname (exit $status):"
      sed 's/^/    /' "$out"
    fi
  fi
}

# SELF_TEST_ONLY, in a self-test of a fixture copy: with the name of one
# case, only that case runs, the run says it was a subset (PARTIAL) and
# how many cases it ran and left out, and exits 0 because that case
# passed; with a text no case name contains, the run fails, saying so.
st_subset_case () {
  local g="$ST_DIR/$ST_SECRET/subset" out="$ST_DIR/subset.out" status ok
  local name="subset: SELF_TEST_ONLY runs only the cases named"
  local none="subset: a SELF_TEST_ONLY that names no case fails"
  st_matches "$name" || st_matches "$none" || {
    st_select "$name"
    st_select "$none"
    return 0
  }
  if ! st_fixture "$g"; then
    st_failed "subset: cannot build the fixture"
    return 0
  fi
  if st_select "$name"; then
    (cd "$ST_DIR" 2> /dev/null && env HOME="$ST_DIR/home" \
       SELF_TEST_ONLY="bootstrap: missing library" \
       bash "$g/scripts/$ST_GATE" --self-test) > "$out" 2>&1
    status=$?
    ok=no
    if [ "$status" -eq 0 ] \
       && grep -qF 'self-test: PARTIAL (only the cases whose names contain "bootstrap: missing library"): 1 run: 1 passed, 0 failed, 0 skipped;' "$out" \
       && grep -q '; [1-9][0-9]* not selected$' "$out" \
       && ! grep -q "self-test SKIPPED\|self-test FAILED" "$out" \
       && st_absent "$out"; then
      ok=yes
    fi
    if [ "$ok" = yes ]; then ST_PASS=$((ST_PASS + 1)); else
      st_failed "$name (exit $status):"
      sed 's/^/    /' "$out"
    fi
  fi
  if st_select "$none"; then
    (cd "$ST_DIR" 2> /dev/null && env HOME="$ST_DIR/home" \
       SELF_TEST_ONLY="no case is named this" \
       bash "$g/scripts/$ST_GATE" --self-test) > "$out" 2>&1
    status=$?
    ok=no
    if [ "$status" -eq 1 ] \
       && grep -qF 'self-test: FAILED: no case name contains "no case is named this"' "$out" \
       && st_absent "$out"; then
      ok=yes
    fi
    if [ "$ok" = yes ]; then ST_PASS=$((ST_PASS + 1)); else
      st_failed "$none (exit $status):"
      sed 's/^/    /' "$out"
    fi
  fi
}

# The restricted-PATH fixtures are built by st_tool_dir: links, then
# wrapper scripts, then a printed skip. Stand-in bash programs show each
# rung: one that, like an MSYS program copied away from msys-2.0.dll, can
# start only from its own directory (the wrappers must then work), and one
# that cannot start at all (st_tool_dir must give up, with a reason).
st_tool_dir_cases () {
  local src="$ST_DIR/tool-src" bad="$ST_DIR/tool-bad" d real ok
  real=$(command -v bash 2> /dev/null)
  mkdir -p "$src" "$bad" 2> /dev/null
  printf '#!/bin/sh
case "$0" in
  %s/bash) exec "%s" "$@" ;;
esac
echo "$0: error while loading shared libraries: ?: cannot open shared object file: No such file or directory" >&2
exit 127
' \
    "$src" "$real" > "$src/bash" && chmod +x "$src/bash"
  printf '#!/bin/sh
echo "$0: error while loading shared libraries: ?: cannot open shared object file: No such file or directory" >&2
exit 127
' \
    > "$bad/bash" && chmod +x "$bad/bash"
  d="$ST_DIR/tool-dir-plain"
  if st_select "tool directory: the tools run from it"; then
    ok=no
    if st_tool_dir "$d" bash cat 2> /dev/null \
       && (PATH="$d" "$d/bash" -c true) > /dev/null 2>&1; then
      ok=yes
    fi
    if [ "$ok" = yes ]; then ST_PASS=$((ST_PASS + 1)); else
      st_failed "tool directory: the tools run from it"
    fi
  fi
  d="$ST_DIR/tool-dir-wrapped"
  if st_select "tool directory: a tool that cannot start from a copy is wrapped"; then
    ok=no
    if (PATH="$src:$PATH" st_tool_dir "$d" bash cat) 2> /dev/null \
       && [ ! -L "$d/bash" ] && (PATH="$d" "$d/bash" -c true) > /dev/null 2>&1; then
      ok=yes
    fi
    if [ "$ok" = yes ]; then ST_PASS=$((ST_PASS + 1)); else
      st_failed "tool directory: a tool that cannot start from a copy is wrapped"
    fi
  fi
  d="$ST_DIR/tool-dir-broken"
  if st_select "tool directory: a tool that cannot start at all gives a skip"; then
    ok=no
    if ! (PATH="$bad:$PATH" st_tool_dir "$d" bash cat) > /dev/null 2>&1; then
      ok=yes
    fi
    if [ "$ok" = yes ]; then ST_PASS=$((ST_PASS + 1)); else
      st_failed "tool directory: a tool that cannot start at all gives a skip"
    fi
  fi
}

# Find mode must not depend on which find comes first on PATH. On Windows
# the find of System32 (a text search) can come before Git Bash's; the
# stand-in behaves like it. With such a find first, the gate still walks
# the crate; with no usable find at all, it refuses, naming the problem.
st_find_cases () {
  local f="$ST_DIR/$ST_SECRET/windows-find" wbin="$ST_DIR/windows-find-bin"
  local nbin="$ST_DIR/no-find-bin" out="$ST_DIR/find.out" status ok
  if ! st_fixture "$f" || ! mkdir -p "$wbin" \
     || ! (cd "$f" && st_put src/cbor_det.ads 'package Cbor_Det with SPARK_Mode is\nend Cbor_Det;\n' \
             && st_put README.md 'clean\n') > /dev/null 2>&1 \
     || ! printf '#!/bin/sh\necho "FIND: Parameter format not correct" >&2\nexit 2\n' \
            > "$wbin/find" || ! chmod +x "$wbin/find"; then
    st_failed "find: cannot build the fixtures"
    return 0
  fi
  if st_select "find: a Windows find first on PATH"; then
    (cd "$ST_DIR" 2> /dev/null && env HOME="$ST_DIR/home" \
       PATH="$wbin:$PATH" bash "$f/scripts/$ST_GATE") > "$out" 2>&1
    status=$?
    ok=no
    if [ "$status" -eq 0 ] && grep -qF "inventory: find mode" "$out" \
       && st_absent "$out"; then
      ok=yes
    fi
    if [ "$ok" = yes ]; then ST_PASS=$((ST_PASS + 1)); else
      st_failed "find: a Windows find first on PATH (exit $status):"
      sed 's/^/    /' "$out"
    fi
  fi
  # Every tool but find, and the Windows stand-in (a script, not a copied
  # program) as the only find.
  st_select "find: no usable find on PATH" || return 0
  if ! st_tool_dir "$nbin" bash sh env perl mktemp rm grep basename uname \
         tr cat git; then
    st_skipped "find: no usable find on PATH" "$ST_TOOL_DIR_REASON"
    return 0
  fi
  cp "$wbin/find" "$nbin/find" 2> /dev/null
  (cd "$ST_DIR" 2> /dev/null && env HOME="$ST_DIR/home" \
     PATH="$nbin" "$nbin/bash" "$f/scripts/$ST_GATE") > "$out" 2>&1
  status=$?
  ok=no
  if [ "$status" -eq 2 ] && grep -qF "ERROR: no usable find" "$out" \
     && st_absent "$out"; then
    ok=yes
  fi
  if [ "$ok" = yes ]; then ST_PASS=$((ST_PASS + 1)); else
    st_failed "find: no usable find on PATH (exit $status):"
    sed 's/^/    /' "$out"
  fi
}

# st_end: removes the fixtures, prints the counts, returns 0 only if no
# case failed.
st_end () {
  local ran=$((ST_PASS + ST_FAIL + ST_SKIP))
  chmod -R u+rwx "$ST_DIR" 2> /dev/null
  rm -rf "$ST_DIR"
  if [ -z "$ST_ONLY" ]; then
    echo "self-test: $ST_PASS passed, $ST_FAIL failed, $ST_SKIP skipped"
  else
    echo "self-test: PARTIAL (only the cases whose names contain \"$ST_ONLY\"): $ran run: $ST_PASS passed, $ST_FAIL failed, $ST_SKIP skipped; $ST_UNSELECTED not selected"
  fi
  if [ "$ST_GIT" = no ]; then
    echo "self-test: git is not installed; the git and staged cases were skipped"
  fi
  if [ -n "$ST_ONLY" ] && [ "$ran" -eq 0 ]; then
    echo "self-test: FAILED: no case name contains \"$ST_ONLY\""
    return 1
  fi
  [ "$ST_FAIL" -eq 0 ]
}
