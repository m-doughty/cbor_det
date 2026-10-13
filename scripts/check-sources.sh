#!/usr/bin/env bash
# Adapted from the scripts of the blake2b crate; to be replaced by the shared gates when that repository exists.
# Source gate: no Ada source of the crate may contain any of the ways to
# make GNATprove accept something it has not proved.
#
#   Assume, in any position               an unproved fact: pragma Assume,
#                                         and pragma Check whose name is
#                                         Assume, positional or named, in
#                                         any order
#   Assume_No_Invalid_Values              validity taken on trust
#   Annotate (..., False_Positive)        a check waved through
#   Annotate (..., Intentional)           a check waved through
#   Skip_Proof / Skip_Flow_And_Proof      a subprogram not analysed
#   SPARK_Mode => Off / (Off)             code outside SPARK, also with a
#                                         named argument
#   Import, pragma Interface, and the     a body GNATprove cannot see
#   GNAT import family: Import_Function,
#   Import_Procedure, Import_Object,
#   Import_Valued_Procedure,
#   Import_Exception, Interface_Name,
#   CPP_Constructor, CPP_Virtual,
#   CPP_Vtable
#   a library unit without SPARK_Mode     analysed in auto mode: anything
#                                         not in SPARK in it is skipped
#                                         silently
#   $ in code                             a preprocessor symbol
#
# Every Ada source outside tests/ (.ads, .adb, .ada) must name SPARK_Mode
# in its code; the test harness in tests/ is not proved and is exempt.
# A per-unit rule, rather than a configuration file with
# pragma SPARK_Mode (On), because it is checked by the gate on every unit
# in every mode, needs no change to the build that dependents see, and
# cannot be undone by editing the project file.
#
# Convention and External_Name on their own stay allowed. The words
# Assume, Import, the import family and Skip_Proof are refused wherever
# they appear in code, not just after "pragma", so named and reordered
# arguments cannot hide them; an identifier of that name is refused too.
# False_Positive and Intentional are refused inside the argument list of
# any Annotate (pragma or aspect; an Annotate whose argument list cannot
# be parsed is refused), so an ordinary identifier of that name passes.
#
# The only GNATprove annotations allowed are Hide_Info and Unhide_Info,
# which change what the provers see but never what they must prove. Every
# occurrence of the tool name GNATprove must be followed directly by one
# of them, or be the tool of a Warnings pragma; so a named or reordered
# Annotate (Tool => GNATprove, ...) or (Hide_Info, GNATprove) is refused.
#
# Warnings (GNATprove's, or unqualified ones, which GNATprove also obeys)
# may be suppressed only with a recorded Reason. The script lists the
# file of every suppression so that a reviewer sees them all.
#
# Every Ada-family file of the crate is checked (see gate-common.sh for
# the inventory and the checks every file passes first): src/, tests/,
# nested and hidden directories, any case of the extensions ads, adb,
# adc, ada and gpr, configuration pragma files and project files. At
# least one Ada source must be read, or the gate fails.
#
# Project files (.gpr) may not change which files are Ada sources: a
# package Naming, Source_Files, Source_List_File, any Excluded_Source*
# attribute, Locally_Removed_Files, and any Source_Dirs other than exactly
# ("src/", "config/") are refused, looked for in the project's code
# (comments and string literals removed, so a string that mentions them
# passes). A project file may name configuration pragmas
# (Local_Configuration_Pragmas, Global_Configuration_Pragmas, or the
# switches -gnatec and -gnatep in any string) only as a literal path to
# an .adc file that is in the inventory, so that it is scanned like any
# Ada source; a text file, a missing file, a computed value or a path out
# of the crate is refused, and so is -gnatec or -gnatep in a TOML file.
# Every chain of string literals joined with & is read as its joined
# value, and a switch is never built by concatenation: a literal that
# starts with a hyphen and a letter, or a variable assigned one, may not
# be an operand of &. The preprocessing switch -gnateD is refused in
# project and TOML files. The proof cannot be switched off from a project
# file: Externally_Built, a --mode= other than --mode=all, any --limit-
# or --no- switch, a --checks-as-errors= other than on, and a package
# Prove without --checks-as-errors=on are refused.
#
# The checks run on the source as the compiler reads it, not on its
# spelling:
#   * Ada sources are UTF-8 with no byte order mark and no zero-width or
#     format character; non-ASCII is allowed only inside comments and
#     string and character literals, never in code (so an identifier with
#     a look-alike letter is refused);
#   * CR, LF, CR LF, form feed, vertical tab, NEL, LS and PS all end a
#     line, before comments are removed;
#   * string literals, character literals and comments are removed by a
#     tokenizer, so a comment or a string that mentions a forbidden
#     pragma doesn't trip the gate, and "--" inside a string can't hide
#     the code after it. A quote after an identifier that is not a
#     reserved word, after ")" or "]", or after an attribute name is an
#     attribute tick; after a reserved word (return'"' is a character
#     literal), an operator or punctuation it starts a character literal;
#   * a % left after that is refused: the alternative string delimiter
#     is not supported, since a string written with it could hide code;
#   * the rest is lowercased (Ada is case-insensitive), and line breaks
#     and runs of spaces become one space, so a pragma split across lines
#     is caught.
#
# The gate stops accidents and a careless author; it cannot stop someone
# trying to beat a shell scanner. Find mode (no git) is a convenience
# before git init, not the shipping check: CI runs --require-git, the
# pre-commit hook --staged. Nothing in this round has been run on
# Windows (see gate-common.sh).
#
# Nothing it prints contains source text: a finding is the class and the
# file only.
#
# Usage: scripts/check-sources.sh               check the crate
#        scripts/check-sources.sh --require-git refuse to run outside
#                                               git (as CI runs it)
#        scripts/check-sources.sh --staged      check what git commit
#                                               would record (the
#                                               pre-commit hook)
#        scripts/check-sources.sh --self-test   check the gate itself,
#                                               end to end, against
#                                               known bypasses
#        SELF_TEST_ONLY=TEXT scripts/check-sources.sh --self-test
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

sources_perl () {
  cat <<'PERL'
my ($ada, @suppressions) = (0);
my $ends = qr{\r\n|[\n\r\f\x0B\x{85}\x{2028}\x{2029}]};

# A configuration pragmas file named in a project file (VALUE, relative
# to the project file at PATH) must be an .adc file the gate scans.
my $scanned_adc = sub {
  my ($path, $value) = @_;
  return 0 if $value eq "" || $value =~ m{\A/|\\|\A[A-Za-z]:};
  my @dir = split m{/}, $path;
  pop @dir;
  for my $part (split m{/}, $value) {
    next if $part eq "." || $part eq "";
    if ($part eq "..") { return 0 unless @dir; pop @dir; next; }
    push @dir, $part;
  }
  my $target = join "/", @dir;
  return ($SCANNED{$target} // "") eq "ada" && $target =~ /\.adc\z/i;
};

for my $file (@FILES) {
  my ($path, $kind, $bytes, $chars, $bom, $shown) = @$file;
  if ($kind eq "toml" && $chars =~ /-gnate[cp]/) {
    refuse("configuration pragmas switch outside a project file", $shown);
  }
  if ($kind eq "toml" && $chars =~ /-gnateD/) {
    refuse("preprocessing switch", $shown);
  }
  next unless $kind eq "ada";
  $ada++;
  refuse("byte order mark in an Ada source", $shown) if $bom;
  refuse("zero-width or format character in an Ada source", $shown)
    if $chars =~ $FORMAT;
  my $u = $chars;
  $u =~ s/$ends/\n/g;
  my @seg = ada_segments($u);
  # The code as the compiler reads it: strings become "", character
  # literals and comments a space.
  my $t = join "", map {
      $_->[0] eq "code" ? $_->[1] : $_->[0] eq "string" ? q{""} : " "
    } @seg;
  refuse("non-ASCII character in Ada code", $shown) if $t =~ /[^\x00-\x7F]/;
  $t = lc $t;
  $t =~ s/\s+/ /g;
  my $forbid = sub {
    my ($what, $re) = @_;
    refuse($what, $shown) if $t =~ $re;
  };
  $forbid->("percent string delimiter not supported", qr{%});
  # A $ in code is a preprocessor symbol; preprocessing is not supported.
  $forbid->("dollar sign in Ada code", qr{\$});
  $forbid->("Assume", qr{\bassume\b});
  $forbid->("Assume_No_Invalid_Values", qr{\bassume_no_invalid_values\b});
  $forbid->("Skip_Proof", qr{\bskip_(?:flow_and_)?proof\b});
  $forbid->("SPARK_Mode Off",
            qr{spark_mode ?(?:=> ?off\b|\( ?(?:mode ?=> ?)?off ?\))});
  $forbid->("Import", qr{\bimport\b});
  $forbid->("GNAT import pragma",
            qr{\b(?:import_function|import_procedure|import_object|import_valued_procedure|import_exception|interface_name|cpp_constructor|cpp_virtual|cpp_vtable)\b});
  $forbid->("pragma Interface", qr{pragma ?interface\b});
  # Every Annotate: its argument list, parsed with balanced brackets.
  while ($t =~ /\bannotate\b/g) {
    my $at = pos $t;
    my $rest = substr $t, $at;
    if ($rest =~ /\A ?(?:=> ?)?(\((?:[^()]++|(?1))*\))/) {
      my $args = $1;
      if ($args =~ /\b(false_positive|intentional)\b/) {
        refuse($1 eq "intentional" ? "Intentional annotation"
                                   : "False_Positive annotation", $shown);
      }
    } else {
      refuse("Annotate whose arguments cannot be parsed", $shown);
    }
  }
  # Every occurrence of the tool name GNATprove must open a Hide_Info or
  # Unhide_Info annotation, or be the tool of a Warnings pragma.
  while ($t =~ /\bgnatprove\b/g) {
    my $pre = substr $t, 0, $-[0];
    my $post = substr $t, $+[0];
    next if $post =~ /\A ?, ?(?:hide_info|unhide_info)\b/;
    next if $pre =~ /pragma warnings ?\( ?\z/ && $post =~ /\A ?, ?(?:on|off)\b/;
    refuse("GNATprove annotation other than Hide_Info / Unhide_Info", $shown);
    last;
  }
  # Every suppression pragma: pragma Warnings ([tool,] Off ...); each must
  # carry "Reason =>" before its closing semicolon.
  while ($t =~ /(pragma warnings ?\( ?(?:(?:gnatprove|gnat) ?, ?)?off\b[^;]*;)/g) {
    my $p = $1;
    if ($p =~ /reason ?=>/) {
      push @suppressions, $shown;
    } else {
      refuse("warning suppression without a Reason", $shown);
    }
  }
  # Every library unit (every Ada source outside tests/) is in SPARK: a
  # unit without SPARK_Mode would be analysed in auto mode, and anything
  # not in SPARK in it skipped silently.
  if ($path !~ m{\Atests/} && $path =~ /\.(?:ads|adb|ada)\z/i
      && $t !~ /\bspark_mode\b/) {
    refuse("Ada unit without SPARK_Mode", $shown);
  }
  # Project files: nothing may make another file an Ada source, and
  # configuration pragmas may come only from a scanned .adc file. The
  # attributes are looked for in code (comments and strings removed); a
  # string's value is looked up by its number.
  if ($path =~ /\.gpr\z/i) {
    my @strings;
    my $g = join "", map {
        $_->[0] eq "code" ? lc $_->[1]
      : $_->[0] eq "string" ? do { push @strings, $_->[1]; "\"#$#strings\"" }
      : " "
      } @seg;
    $g =~ s/\s+/ /g;
    my $remap = $g =~ /\bpackage naming\b/
      || $g =~ /\b(?:source_files|source_list_file|excluded_source\w*|locally_removed_files)\b/;
    (my $dirs = $g) =~ s{\bfor source_dirs use \( ?"#(\d+)" ?, ?"#(\d+)" ?\) ?;}
      {($strings[$1] eq "src/" && $strings[$2] eq "config/") ? " " : $&}ge;
    $remap ||= $dirs =~ /\bsource_dirs\b/;
    refuse("GPR source remapping", $shown) if $remap;
    my $config_ok = 1;
    (my $cp = $g) =~ s{\bfor (?:local|global)_configuration_pragmas use "#(\d+)" ?;}
      {$config_ok &&= $scanned_adc->($path, $strings[$1]); " "}ge;
    $config_ok = 0 if $cp =~ /\b(?:local|global)_configuration_pragmas\b/;
    # The value of every chain of string literals joined with &, as well
    # as every literal on its own.
    my @values = @strings;
    while ($g =~ /("#\d+"(?: ?& ?"#\d+")+)/g) {
      push @values, join "", map { $strings[$_] } ($1 =~ /#(\d+)/g);
    }
    for my $s (@values) {
      while ($s =~ /-gnate([cp])(=?)(\S*)/g) {
        my ($value, $start) = ($3, $-[0]);
        $config_ok = 0 if $start != 0 || $value eq "";
        $config_ok &&= $scanned_adc->($path, $value);
      }
    }
    refuse("configuration pragmas file not scanned", $shown) unless $config_ok;
    refuse("preprocessing switch", $shown) if grep { /-gnateD/ } @values;
    # A switch is never built by concatenation: a switch literal, or a
    # variable assigned one, may not be an operand of &.
    my $switch = sub { ($strings[$_[0]] // "") =~ /\A-[A-Za-z]/ };
    my $built = 0;
    while ($g =~ /"#(\d+)" ?&|& ?"#(\d+)"/g) {
      $built ||= $switch->($1 // $2);
    }
    while ($g =~ /\b([a-z][a-z0-9_.]*) ?:= ?"#(\d+)" ?;/g) {
      my ($var, $n) = ($1, $2);
      next unless $switch->($n);
      $built ||= $g =~ /(?:\b\Q$var\E ?&|& ?\Q$var\E\b)/;
    }
    refuse("switch built by concatenation", $shown) if $built;
    # The proof cannot be switched off from the project file.
    my $off = $g =~ /\bexternally_built\b/
      || grep { /\A--mode=(?!all\z)|\A--limit-|\A--no-|\A--checks-as-errors=(?!on\z)/ } @values;
    $off ||= $g =~ /\bpackage prove\b/
      && !grep { $_ eq "--checks-as-errors=on" } @values;
    refuse("proof switched off in the project file", $shown) if $off;
  }
}
refuse("no Ada source read", "the inventory") if $ada == 0;
print "Ada sources read: $ada\n";
print "warning suppressions (", scalar(@suppressions), ", each with a Reason), in:\n";
print map { "  $_\n" } @suppressions;
exit $BAD;
PERL
}

# A clean crate for the self-test.
st_sources_base () {
  st_put src/cbor_det.ads 'package Cbor_Det with SPARK_Mode, Pure is\nend Cbor_Det;\n'
}

st_sources_hostile () {
  st_put "$1" 'package H is\n   pragma Assume (True);\nend H;\n'
}

st_sources_gpr_adc () {
  st_sources_base \
    && st_put cfg/p.gpr 'project P is\n   package Compiler is\n      for Local_Configuration_Pragmas use "gnat.adc";\n   end Compiler;\nend P;\n' \
    && st_put cfg/gnat.adc 'pragma Assume_No_Invalid_Values (On);\n'
}

st_sources_gpr_naming () {
  st_sources_base \
    && st_put cfg/hostile.gpr 'project Hostile is\n   for Source_Dirs use (".");\n   package Naming is\n      for Body ("Evil") use "evil.txt";\n   end Naming;\nend Hostile;\n' \
    && st_put cfg/evil.txt 'procedure Evil is\nbegin\n   pragma Assume (False);\nend Evil;\n'
}

# A table entry: an Ada unit outside tests/ starts with pragma SPARK_Mode,
# as every library unit must, so that each case tests only its own rule.
st_sources_table_setup () {
  local prefix=""
  case "$2" in
    tests/*) ;;
    *.ads|*.adb|*.ada|*.ADS|*.ADB|*.ADA)
      case "$3" in
        '\x{EF}'*) ;;
        *) prefix='pragma SPARK_Mode;\n' ;;
      esac ;;
  esac
  "$1" && st_put "$2" "$prefix$3\\n"
}

# The reviewer's case: a spec with SPARK_Mode and a body without it.
st_sources_unit_without_spark_mode () {
  st_sources_base \
    && st_put src/cbor_det-ffi.ads 'package Cbor_Det.Ffi with SPARK_Mode is\n   procedure P;\nend Cbor_Det.Ffi;\n' \
    && st_put src/cbor_det-ffi.adb 'package body Cbor_Det.Ffi is\n   procedure P is null;\nend Cbor_Det.Ffi;\n'
}

st_sources_test_unit_without_spark_mode () {
  st_sources_base \
    && st_put tests/src/helper.adb 'with Ada.Text_IO;\nprocedure Helper is\nbegin\n   Ada.Text_IO.Put_Line ("x");\nend Helper;\n'
}

st_sources_fake_dir () {
  mkdir -p src/fake.ads
}

st_sources_tab_name () {
  st_sources_base && st_put "$(printf 'src/probe\tassume.ads')" \
    'package Probe is\nend Probe;\n' && ST_ABSENT="FORBIDDEN (Assume)"
}

# The reviewer's case: the crate's project file names a text file holding
# escape hatches as its configuration pragmas file.
st_sources_config_pragmas () {
  local use
  case "$1" in
    local) use='   package Compiler is\n      for Local_Configuration_Pragmas use "settings.txt";\n   end Compiler;\n' ;;
    switch) use='   package Compiler is\n      for Default_Switches ("Ada") use ("-gnatec=settings.txt");\n   end Compiler;\n' ;;
    adc) use='   package Compiler is\n      for Local_Configuration_Pragmas use "src/gnat.adc";\n   end Compiler;\n' ;;
    adc-switch) use='   package Compiler is\n      for Default_Switches ("Ada") use ("-gnatec=./src/gnat.adc");\n   end Compiler;\n' ;;
    adc-in-longer-string) use='   package Compiler is\n      for Default_Switches ("Ada") use ("-gnatwa -gnatec=src/gnat.adc");\n   end Compiler;\n' ;;
  esac
  st_sources_base \
    && st_put cbor_det.gpr "project Cbor_Det is\\n   for Source_Dirs use (\"src/\", \"config/\");\\n$use""end Cbor_Det;\\n" \
    && st_put settings.txt 'pragma Assume_No_Invalid_Values (On);\npragma SPARK_Mode (Off);\n' \
    && st_put src/gnat.adc 'pragma Ada_2022;\n'
}

self_test () {
  st_begin check-sources.sh || return 2
  st_shared_cases st_sources_base st_sources_hostile "FORBIDDEN (Assume) at "
  st_both "test main with pragma Assume" \
    "FORBIDDEN (Assume) at tests/src/test_main.adb" \
    st_table_setup st_sources_base tests/src/test_main.adb \
    'procedure Test_Main is\nbegin\n   pragma Assume (True);\nend Test_Main;'
  st_both "nested source" "FORBIDDEN (Assume) at src/nested/h.ads" \
    st_table_setup st_sources_base src/nested/h.ads 'pragma Assume (True);'
  st_both "hidden source" "FORBIDDEN (Assume) at src/.hidden.ads" \
    st_table_setup st_sources_base src/.hidden.ads 'pragma Assume (True);'
  st_both "uppercase extension" "FORBIDDEN (Assume) at src/h.ADS" \
    st_table_setup st_sources_base src/h.ADS 'pragma Assume (True);'
  st_both "configuration pragma file" "FORBIDDEN (Assume) at src/h.adc" \
    st_table_setup st_sources_base src/h.adc 'pragma Assume (True);'
  st_both "project file naming a hostile configuration file" \
    "FORBIDDEN (Assume_No_Invalid_Values) at cfg/gnat.adc" st_sources_gpr_adc
  st_both "no source, only a directory named like one" \
    "FORBIDDEN (no Ada source read)" st_sources_fake_dir
  st_both "tab in a file name" \
    "FORBIDDEN (Windows-invalid file name) at <file name withheld" st_sources_tab_name
  st_both "project file naming a text file for configuration pragmas" \
    "FORBIDDEN (configuration pragmas file not scanned) at cbor_det.gpr" \
    st_sources_config_pragmas local
  st_both "project file switch naming a text file for configuration pragmas" \
    "FORBIDDEN (configuration pragmas file not scanned) at cbor_det.gpr" \
    st_sources_config_pragmas switch
  st_both "project file naming a scanned configuration pragmas file" "pass" \
    st_sources_config_pragmas adc
  st_both "scanned configuration pragmas file, switch form" "pass" \
    st_sources_config_pragmas adc-switch
  st_both "switch to a scanned file inside a longer string" \
    "FORBIDDEN (configuration pragmas file not scanned) at cbor_det.gpr" \
    st_sources_config_pragmas adc-in-longer-string
  st_both "file named after a forbidden word" "pass" \
    st_table_setup st_sources_base src/probe-assume.ads 'package Probe with SPARK_Mode is\nend Probe;'
  st_both "library body without SPARK_Mode" \
    "FORBIDDEN (Ada unit without SPARK_Mode) at src/cbor_det-ffi.adb" \
    st_sources_unit_without_spark_mode
  st_both "test unit without SPARK_Mode" "pass" \
    st_sources_test_unit_without_spark_mode
  st_bootstrap_cases
  st_both "hostile project file mapping a text file" \
    "FORBIDDEN (GPR source remapping) at cfg/hostile.gpr" st_sources_gpr_naming
  # name | expectation | path | content (\n and the other escapes of st_put)
  ST_TABLE_SETUP=st_sources_table_setup
  st_table st_sources_base \
    'lower-assume|FORBIDDEN (Assume) at src/x.adb|src/x.adb|pragma assume (True);' \
    'split-assume|FORBIDDEN (Assume) at src/x.adb|src/x.adb|PRAGMA ASSUME\n   (True);' \
    'check-assume|FORBIDDEN (Assume) at src/x.adb|src/x.adb|pragma Check\n  (Assume, X > 0);' \
    'check-named-assume|FORBIDDEN (Assume) at src/x.adb|src/x.adb|pragma Check (Name => Assume, Check => False);' \
    'check-reordered-assume|FORBIDDEN (Assume) at src/x.adb|src/x.adb|pragma Check (Check => False, Name => Assume);' \
    'check-named-split-upper|FORBIDDEN (Assume) at src/x.adb|src/x.adb|PRAGMA CHECK\n  (CHECK   =>  FALSE,\n   NAME=>ASSUME);' \
    'check-named-message|FORBIDDEN (Assume) at src/x.adb|src/x.adb|pragma Check\n  (Message => "m", Check => X > 0,\n   Name => Assume);' \
    'check-positional-assume|FORBIDDEN (Assume) at src/x.adb|src/x.adb|pragma Check (Assume, False, "m");' \
    'assume-no-invalid-values|FORBIDDEN (Assume_No_Invalid_Values) at src/x.adb|src/x.adb|pragma Assume_No_Invalid_Values (On);' \
    'cr-only-line-end|FORBIDDEN (Assume) at src/x.adb|src/x.adb|--  note\rpragma Assume (X);' \
    'form-feed-line-end|FORBIDDEN (Assume) at src/x.adb|src/x.adb|--  note\fpragma Assume (X);' \
    'vertical-tab-line-end|FORBIDDEN (Assume) at src/x.adb|src/x.adb|--  note\vpragma Assume (X);' \
    'crlf-line-end|FORBIDDEN (Assume) at src/x.adb|src/x.adb|--  note\r\npragma Assume (X);' \
    'percent-string|FORBIDDEN (percent string delimiter not supported) at src/x.adb|src/x.adb|S : constant String := %--%; pragma Assume (X);' \
    'zero-width-in-assume|FORBIDDEN (zero-width or format character in an Ada source) at src/x.adb|src/x.adb|pragma Ass\u{200B}ume (X);' \
    'cyrillic-in-assume|FORBIDDEN (non-ASCII character in Ada code) at src/x.adb|src/x.adb|pragma \u{0410}ssume (X);' \
    'byte-order-mark-in-ada|FORBIDDEN (byte order mark in an Ada source) at src/x.adb|src/x.adb|\x{EF}\x{BB}\x{BF}package X is end X;' \
    'non-ascii-in-comment|pass|src/x.adb|package X is\n   --  caf\u{E9}\nend X;' \
    'non-ascii-in-string|pass|src/x.adb|package X is\n   S : constant String := "caf\u{E9}";\nend X;' \
    'non-ascii-in-character|pass|src/x.adb|package X is\n   C : constant Wide_Character := '"'"'\u{E9}'"'"';\nend X;' \
    'non-ascii-in-identifier|FORBIDDEN (non-ASCII character in Ada code) at src/x.adb|src/x.adb|package X is\n   Caf\u{E9} : Integer;\nend X;' \
    'zero-width-in-comment|FORBIDDEN (zero-width or format character in an Ada source) at src/x.adb|src/x.adb|--  a\u{200B}b' \
    'line-separator-line-end|FORBIDDEN (Assume) at src/x.adb|src/x.adb|--  note\u{2028}pragma Assume (X);' \
    'next-line-line-end|FORBIDDEN (Assume) at src/x.adb|src/x.adb|--  note\u{85}pragma Assume (X);' \
    'gpr-naming|FORBIDDEN (GPR source remapping) at cfg/hostile.gpr|cfg/hostile.gpr|project Hostile is\n   package Naming is\n      for Body ("Evil") use "evil.txt";\n   end Naming;\nend Hostile;' \
    'gpr-naming-split-upper|FORBIDDEN (GPR source remapping) at p.gpr|p.gpr|PROJECT P IS\n   PACKAGE\n     NAMING IS\n   END NAMING;\nEND P;' \
    'gpr-source-files|FORBIDDEN (GPR source remapping) at p.gpr|p.gpr|project P is\n   for Source_Files use ("a.ads");\nend P;' \
    'gpr-source-list-file|FORBIDDEN (GPR source remapping) at p.gpr|p.gpr|project P is\n   for Source_List_File use "list.txt";\nend P;' \
    'gpr-excluded-source-files|FORBIDDEN (GPR source remapping) at p.gpr|p.gpr|project P is\n   for Excluded_Source_Files use ("cbor_det.ads");\nend P;' \
    'gpr-excluded-source-list-file|FORBIDDEN (GPR source remapping) at p.gpr|p.gpr|project P is\n   for Excluded_Source_List_File use "x.txt";\nend P;' \
    'gpr-locally-removed|FORBIDDEN (GPR source remapping) at p.gpr|p.gpr|project P is\n   for Locally_Removed_Files use ("cbor_det.ads");\nend P;' \
    'gpr-other-source-dir|FORBIDDEN (GPR source remapping) at p.gpr|p.gpr|project P is\n   for Source_Dirs use ("src/", "other/");\nend P;' \
    'gpr-src-only|FORBIDDEN (GPR source remapping) at p.gpr|p.gpr|project P is\n   for Source_Dirs use ("src/");\nend P;' \
    'gpr-source-dirs-reference|FORBIDDEN (GPR source remapping) at p.gpr|p.gpr|project P is\n   for Source_Dirs use ("src/", "config/");\n   X := Project'"'"'Source_Dirs;\nend P;' \
    'tick-after-return-hides-assume|FORBIDDEN (Assume) at src/x.adb|src/x.adb|procedure Probe with SPARK_Mode is function Quote return Character is begin return\x{27}\x{22}\x{27}; end Quote; begin pragma Assume (False); pragma Assert (Quote = \x{27}\x{22}\x{27}); end Probe;' \
    'percent-character-after-return|pass|src/x.adb|function Probe return Character is begin return\x{27}%\x{27}; end Probe;' \
    'character-after-when-hides-assume|FORBIDDEN (Assume) at src/x.adb|src/x.adb|procedure P (C : Character) is begin case C is when\x{27}\x{22}\x{27} => pragma Assume (True); when others => null; end case; end P;' \
    'ticks-and-characters|pass|src/x.adb|package X is\n   N : constant := A\x{27}Length + Integer\x{27}Last;\n   C : constant Character := \x{27}a\x{27};\n   D : constant Character := Character\x{27}(\x{27}a\x{27});\n   E : constant Character := \x{27}\x{22}\x{27};\n   F : constant Character := \x{27}\x{27}\x{27};\n   L : constant := S\x{27}Image (X)\x{27}Length;\n   M : constant := X\x{27}Length\x{27}Image;\n   procedure P (Y : T\x{27}Class);\n   S : constant String := String\x{27}("ab");\nend X;' \
    'ticks-and-characters-then-assume|FORBIDDEN (Assume) at src/x.adb|src/x.adb|package X is\n   N : constant := A\x{27}Length;\n   E : constant Character := \x{27}\x{22}\x{27};\n   F : constant Character := \x{27}\x{27}\x{27};\n   D : constant Character := Character\x{27}(\x{27}\x{22}\x{27});\n   pragma Assume (N > 0);\nend X;' \
    'gpr-label-string|pass|probe.gpr|project Probe is Label := "Source_Files"; end Probe;' \
    'gpr-naming-in-strings-and-comments|pass|probe.gpr|project Probe is\n   --  package Naming, Source_List_File, Local_Configuration_Pragmas\n   A := "package Naming is, Source_Files";\nend Probe;' \
    'gpr-config-pragmas-text-file|FORBIDDEN (configuration pragmas file not scanned) at p.gpr|p.gpr|project P is\n   package Compiler is\n      for Local_Configuration_Pragmas use "settings.txt";\n   end Compiler;\nend P;' \
    'gpr-config-pragmas-missing|FORBIDDEN (configuration pragmas file not scanned) at p.gpr|p.gpr|project P is\n   package Compiler is\n      for Local_Configuration_Pragmas use "missing.adc";\n   end Compiler;\nend P;' \
    'gpr-config-pragmas-computed|FORBIDDEN (configuration pragmas file not scanned) at p.gpr|p.gpr|project P is\n   Prefix := "";\n   package Compiler is\n      for Local_Configuration_Pragmas use Prefix & "x.adc";\n   end Compiler;\nend P;' \
    'gpr-config-pragmas-global-upper|FORBIDDEN (configuration pragmas file not scanned) at p.gpr|p.gpr|PROJECT P IS\n   PACKAGE BUILDER IS\n      FOR GLOBAL_CONFIGURATION_PRAGMAS USE "SETTINGS.TXT";\n   END BUILDER;\nEND P;' \
    'gpr-config-pragmas-absolute|FORBIDDEN (configuration pragmas file not scanned) at p.gpr|p.gpr|project P is\n   package Compiler is\n      for Local_Configuration_Pragmas use "/x.adc";\n   end Compiler;\nend P;' \
    'gpr-config-pragmas-reference|FORBIDDEN (configuration pragmas file not scanned) at p.gpr|p.gpr|project P is\n   X := Compiler\x{27}Local_Configuration_Pragmas;\nend P;' \
    'gpr-gnatec-switch|FORBIDDEN (configuration pragmas file not scanned) at p.gpr|p.gpr|project P is\n   package Compiler is\n      for Default_Switches ("Ada") use ("-gnatwa", "-gnatec=settings.txt");\n   end Compiler;\nend P;' \
    'gpr-gnatec-switch-no-equals|FORBIDDEN (configuration pragmas file not scanned) at p.gpr|p.gpr|project P is\n   package Compiler is\n      for Switches ("x.adb") use ("-gnatecsettings.txt");\n   end Compiler;\nend P;' \
    'gpr-gnatep-switch|FORBIDDEN (configuration pragmas file not scanned) at p.gpr|p.gpr|project P is\n   package Compiler is\n      for Default_Switches ("Ada") use ("-gnatep=prep.txt");\n   end Compiler;\nend P;' \
    'gpr-gnatec-inside-a-string|FORBIDDEN (configuration pragmas file not scanned) at p.gpr|p.gpr|project P is\n   package Compiler is\n      for Default_Switches ("Ada") use ("-gnatwa -gnatec=gnat.adc");\n   end Compiler;\nend P;' \
    'toml-gnatec-switch|FORBIDDEN (configuration pragmas switch outside a project file) at alire.toml|alire.toml|[build-switches]\n"*".compile_checks = ["-gnatec=settings.txt"]' \
    'gpr-concatenated-gnatec|FORBIDDEN (configuration pragmas file not scanned) at p.gpr|p.gpr|project P is\n   package Compiler is\n      for Default_Switches ("Ada") use ("-gnat" & "ec=docs-pragmas.txt");\n   end Compiler;\nend P;' \
    'gpr-concatenated-in-a-variable|FORBIDDEN (configuration pragmas file not scanned) at p.gpr|p.gpr|project P is\n   Cfg := "-gnate" & "c=docs-pragmas.txt";\n   package Compiler is\n      for Default_Switches ("Ada") use (Cfg);\n   end Compiler;\nend P;' \
    'gpr-switch-variable-as-operand|FORBIDDEN (switch built by concatenation) at p.gpr|p.gpr|project P is\n   Pre := "-gnate";\n   package Compiler is\n      for Default_Switches ("Ada") use (Pre & "c=docs-pragmas.txt");\n   end Compiler;\nend P;' \
    'gpr-concatenated-other-switch|FORBIDDEN (switch built by concatenation) at p.gpr|p.gpr|project P is\n   package Compiler is\n      for Default_Switches ("Ada") use ("-gnat" & "wa");\n   end Compiler;\nend P;' \
    'gpr-benign-concatenation|pass|p.gpr|project P is\n   Opt := "O2";\n   Checks := "lang";\n   Cell := Opt & "-" & Checks;\n   for Object_Dir use "obj/" & Cell;\nend P;' \
    'gpr-gnateD|FORBIDDEN (preprocessing switch) at p.gpr|p.gpr|project P is\n   package Compiler is\n      for Default_Switches ("Ada") use ("-gnateDX=Assume");\n   end Compiler;\nend P;' \
    'toml-gnateD|FORBIDDEN (preprocessing switch) at alire.toml|alire.toml|[build-switches]\n"*".compile_checks = ["-gnateDX=Assume"]' \
    'dollar-preprocessor-symbol|FORBIDDEN (dollar sign in Ada code) at src/cbor_det-y.ads|src/cbor_det-y.ads|package Cbor_Det.Y with SPARK_Mode is pragma $X (False); end Cbor_Det.Y;' \
    'dollar-in-a-string|pass|src/x.ads|package X with SPARK_Mode is S : constant String := "$X"; end X;' \
    'prove-mode-flow|FORBIDDEN (proof switched off in the project file) at p.gpr|p.gpr|project P is\n   package Prove is\n      for Proof_Switches ("Ada") use ("--mode=flow", "--checks-as-errors=on");\n   end Prove;\nend P;' \
    'prove-without-checks-as-errors|FORBIDDEN (proof switched off in the project file) at p.gpr|p.gpr|project P is\n   package Prove is\n      for Proof_Switches ("Ada") use ("--mode=all");\n   end Prove;\nend P;' \
    'prove-checks-as-errors-off|FORBIDDEN (proof switched off in the project file) at p.gpr|p.gpr|project P is\n   package Prove is\n      for Proof_Switches ("Ada") use ("--mode=all", "--checks-as-errors=on", "--checks-as-errors=off");\n   end Prove;\nend P;' \
    'prove-limit|FORBIDDEN (proof switched off in the project file) at p.gpr|p.gpr|project P is\n   package Prove is\n      for Proof_Switches ("Ada") use ("--mode=all", "--checks-as-errors=on", "--limit-subp=x.adb:1");\n   end Prove;\nend P;' \
    'prove-no-option|FORBIDDEN (proof switched off in the project file) at p.gpr|p.gpr|project P is\n   package Prove is\n      for Proof_Switches ("Ada") use ("--mode=all", "--checks-as-errors=on", "--no-inlining");\n   end Prove;\nend P;' \
    'externally-built|FORBIDDEN (proof switched off in the project file) at p.gpr|p.gpr|project P is\n   for Externally_Built use "true";\nend P;' \
    'prove-like-the-crate|pass|p.gpr|project P is\n   package Prove is\n      for Proof_Switches ("Ada") use\n        ("--mode=all",\n         "--checks-as-errors=on",\n         "--proof-warnings=on",\n         "--warnings=error",\n         "--prover=z3,cvc5,altergo",\n         "--timeout=0",\n         "--steps=10000",\n         "--counterexamples=off",\n         "--report=fail");\n   end Prove;\nend P;' \
    'cpp-constructor|FORBIDDEN (GNAT import pragma) at src/x.adb|src/x.adb|pragma CPP_Constructor (Make, "_ZN3ObjC1Ev");' \
    'cpp-virtual|FORBIDDEN (GNAT import pragma) at src/x.adb|src/x.adb|pragma CPP_Virtual (P);' \
    'cpp-vtable|FORBIDDEN (GNAT import pragma) at src/x.adb|src/x.adb|pragma CPP_Vtable (T, V, 1);' \
    'gpr-own-dirs|pass|p.gpr|project P is\n   for Source_Dirs use\n     ("src/",   --  the sources\n      "config/");\n   --  no package Naming, no Source_Files\nend P;' \
    'split-false-positive|FORBIDDEN (False_Positive annotation) at src/x.adb|src/x.adb|pragma Annotate\n  (GNATprove,\n   False_Positive, "x", "y");' \
    'upper-intentional|FORBIDDEN (Intentional annotation) at src/x.adb|src/x.adb|PRAGMA ANNOTATE (GNATPROVE, INTENTIONAL, "x", "y");' \
    'intentional-named-reordered|FORBIDDEN (Intentional annotation) at src/x.adb|src/x.adb|pragma Annotate\n  (Entity => P,\n   Kind => Intentional, Tool => Gnatprove);' \
    'intentional-aspect|FORBIDDEN (Intentional annotation) at src/x.adb|src/x.adb|procedure P with Annotate => (GNATprove, Intentional, "x", "y");' \
    'false-positive-other-tool|FORBIDDEN (False_Positive annotation) at src/x.adb|src/x.adb|pragma Annotate (CodePeer, False_Positive, "x", "y");' \
    'annotate-unbalanced|FORBIDDEN (Annotate whose arguments cannot be parsed) at src/x.adb|src/x.adb|pragma Annotate (GNATprove, Intentional' \
    'intentional-identifier|pass|src/x.adb|package X is\n   Intentional : constant Boolean := True;\n   False_Positive : constant Boolean := False;\nend X;' \
    'aspect-skip|FORBIDDEN (Skip_Proof) at src/x.adb|src/x.adb|procedure P with Annotate => (gnatprove, skip_proof);' \
    'skip-flow-and-proof|FORBIDDEN (Skip_Proof) at src/x.adb|src/x.adb|pragma Annotate (GNATprove, Skip_Flow_And_Proof, P);' \
    'split-spark-off|FORBIDDEN (SPARK_Mode Off) at src/x.adb|src/x.adb|package P with SPARK_Mode\n   => Off is end P;' \
    'pragma-spark-off|FORBIDDEN (SPARK_Mode Off) at src/x.adb|src/x.adb|pragma spark_mode (off);' \
    'spark-mode-named-off|FORBIDDEN (SPARK_Mode Off) at src/x.adb|src/x.adb|pragma SPARK_Mode (Mode => Off);' \
    'import-aspect|FORBIDDEN (Import) at src/x.adb|src/x.adb|procedure P with Import, Convention => C;' \
    'split-import-aspect|FORBIDDEN (Import) at src/x.adb|src/x.adb|procedure P\n  with Convention => C,\n       IMPORT;' \
    'import-pragma|FORBIDDEN (Import) at src/x.adb|src/x.adb|pragma Import (C, P, "p");' \
    'import-function|FORBIDDEN (GNAT import pragma) at src/x.adb|src/x.adb|pragma Import_Function (Internal => F, External => "f");' \
    'import-procedure|FORBIDDEN (GNAT import pragma) at src/x.adb|src/x.adb|PRAGMA IMPORT_PROCEDURE\n  (P, "p");' \
    'import-object|FORBIDDEN (GNAT import pragma) at src/x.adb|src/x.adb|pragma Import_Object (V, "v");' \
    'import-valued-procedure|FORBIDDEN (GNAT import pragma) at src/x.adb|src/x.adb|pragma Import_Valued_Procedure (P, "p");' \
    'import-exception|FORBIDDEN (GNAT import pragma) at src/x.adb|src/x.adb|pragma Import_Exception (E, "e");' \
    'interface-name|FORBIDDEN (GNAT import pragma) at src/x.adb|src/x.adb|pragma Interface_Name (P, External_Name => "p");' \
    'interface-pragma|FORBIDDEN (pragma Interface) at src/x.adb|src/x.adb|pragma Interface (C, P);' \
    'convention-external-name|pass|src/x.adb|package X is\n   procedure P with Convention => C, External_Name => "p";\nend X;' \
    'other-annotation|FORBIDDEN (GNATprove annotation other than Hide_Info / Unhide_Info) at src/x.adb|src/x.adb|pragma Annotate (GNATprove, Always_Return, P);' \
    'split-other-aspect|FORBIDDEN (GNATprove annotation other than Hide_Info / Unhide_Info) at src/x.adb|src/x.adb|function F return T\n  with Annotate =>\n    (GNATprove, Inline_For_Proof);' \
    'hide-info-then-other|FORBIDDEN (GNATprove annotation other than Hide_Info / Unhide_Info) at src/x.adb|src/x.adb|pragma Annotate (GNATprove, Hide_Info, "x", F);\npragma Annotate (GNATprove, Terminating, P);' \
    'annotate-named-tool|FORBIDDEN (GNATprove annotation other than Hide_Info / Unhide_Info) at src/x.adb|src/x.adb|pragma Annotate (Tool => GNATprove, Always_Return, P);' \
    'annotate-tool-second|FORBIDDEN (GNATprove annotation other than Hide_Info / Unhide_Info) at src/x.adb|src/x.adb|pragma Annotate (Hide_Info, GNATprove, "x", F);' \
    'annotate-named-kind|FORBIDDEN (GNATprove annotation other than Hide_Info / Unhide_Info) at src/x.adb|src/x.adb|pragma Annotate\n  (GNATprove,\n   Kind => Terminating, Entity => P);' \
    'string-hides-code|FORBIDDEN (Assume) at src/x.adb|src/x.adb|S : constant String := "--"; pragma Assume (False);' \
    'char-quote-hides-code|FORBIDDEN (Assume) at src/x.adb|src/x.adb|C : constant Character := '"'"'"'"'"'; pragma Assume (X); S : String := "a";' \
    'unexplained-warning|FORBIDDEN (warning suppression without a Reason) at src/x.adb|src/x.adb|pragma Warnings (GNATprove, Off, "msg");' \
    'unexplained-plain-warning|FORBIDDEN (warning suppression without a Reason) at src/x.adb|src/x.adb|pragma Warnings\n  (Off, "msg");' \
    'hide-info|pass|src/x.adb|pragma Annotate (GNATprove, Hide_Info, "Expression_Function_Body", F);' \
    'split-hide-info|pass|src/x.adb|PRAGMA ANNOTATE\n  (GNATPROVE,\n   HIDE_INFO, "Expression_Function_Body", F);' \
    'unhide-info|pass|src/x.adb|pragma Annotate (GNATprove, Unhide_Info, "Expression_Function_Body", F);' \
    'aspect-hide-info|pass|src/x.adb|function F return T\n  with Annotate => (GNATprove, Hide_Info, "Expression_Function_Body");' \
    'hide-info-named-entity|pass|src/x.adb|pragma Annotate\n  (GNATprove, Hide_Info, "Expression_Function_Body",\n   Entity => F);' \
    'check-named-other|pass|src/x.adb|pragma Check (Name => Precondition, Check => X > 0);' \
    'comment-mentions|pass|src/x.adb|--  pragma Assume (True) would be forbidden' \
    'comment-mentions-import|pass|src/x.adb|--  with Import, Annotate (GNATprove, Intentional), 50%' \
    'string-mentions|pass|src/x.adb|S : constant String := "pragma Assume (True) at 50%";' \
    'string-mentions-import|pass|src/x.adb|S : constant String := "pragma Import (C, P);";' \
    'char-percent|pass|src/x.adb|C : constant Character := '"'"'%'"'"';' \
    'explained-warning|pass|src/x.adb|pragma Warnings (GNATprove, Off, "m",\n   Reason => "why");' \
    'explained-plain-warning|pass|src/x.adb|pragma Warnings (Off, "m", Reason => "x");' \
    'warning-on|pass|src/x.adb|pragma Warnings (GNATprove, On, "msg");' \
    'attribute-tick|pass|src/x.adb|N : constant := X'"'"'Length; pragma Assert (N > 0);' \
    'python-file|pass|tests/reference/t.py|import sys' \
    'python-file-anywhere|pass|scripts/t.py|import sys' \
    'spark-mode-on|pass|src/x.adb|package P with SPARK_Mode => On is end P;'
  st_end
}

gate_main sources sources_perl self_test "$@"
exit $?
