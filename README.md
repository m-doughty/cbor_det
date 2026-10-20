# cbor_det

Deterministic CBOR (RFC 8949, section 4.2.1) in SPARK. The crate is to
check encoded CBOR items against the core deterministic encoding
requirements of RFC 8949 section 4.2.1, within a fixed nesting limit,
and report the result as a `Status`.

**Status: proof core, value model and decoder.** Version 0.1.0 holds
the shared types of `Cbor_Det`, the proof core under `Cbor_Det.Proof`
(the specification of a deterministic item, the value an accepted item
denotes, and the lemmas about them, canonical uniqueness among them) and
the decoder, `Cbor_Det.Decoder`: `Check (Data, Result, Where)` says whether
`Data` holds exactly one deterministic item of the profile and nothing
else, and if not, which rule failed (`Result`, a `Status`) and where
(`Where`, an index of `Data`). There is no cursor and no writer yet.

```ada
with Cbor_Det;         use Cbor_Det;
with Cbor_Det.Decoder;

procedure Example (Data : Bytes) is
   Result : Status;
   Where  : Integer;
begin
   Cbor_Det.Decoder.Check (Data, Result, Where);
   --  Result = Ok exactly when Data holds one deterministic item;
   --  otherwise Where is the index of the first fault.
end Example;
```

## What is proved

GNATprove proves every check of every unit, from cold, bounded by prover
steps only, with nothing assumed: no `pragma Assume`, no justified
check, no `SPARK_Mode => Off`, no imported body. The only GNATprove
annotations are `Hide_Info` and `Unhide_Info`, which choose what the
provers see, never what they must prove. One GNATprove warning is
silenced, with its reason, in one place (see "What is trusted").

- **The specification.** `Cbor_Det.Proof.Det.Det_End (B, P, D)` is the
  end (one past the last byte) of the deterministic item that starts at
  `P`, or 0 if no item that starts there is accepted. It says nothing
  about the bytes after that item. `D` is the container depth still
  allowed: a scalar is accepted at any `D`, 0 included; every container,
  an empty one too, needs `D >= 1`, and its members are judged at
  `D - 1`. An item is accepted when its head is well formed and shortest
  (RFC 8949 section 4.2.1, rule 1; additional information 28 to 31 is
  never accepted) and it is an unsigned or negative integer of any
  64-bit argument, a byte or text string (text as bytes: UTF-8 is not
  checked) whose length fits, an array of accepted members, a map of
  accepted keys and values whose keys are strictly ascending in the
  bytewise order of their encodings (which makes them unique), or
  `false`, `true` or `null`. Tags, floats, every other simple value and
  indefinite lengths are refused. `Accept_Whole (B)` is the check of a
  whole input: `B` is not empty and `Det_End (B, B'First, Max_Depth) =
  B'Last + 1`, so 16 nested containers are accepted and 17 are not, and
  a byte after the item is refused. The proof shows that the code meets
  this specification; that the specification is RFC 8949 for this
  profile is shown by the tests below, not by the proof.
- **Heads** (`Cbor_Det.Proof.Heads`): an accepted head's bytes are the
  encoding `Encode_Head` gives for its major type and argument, and the
  bytes of that encoding, wherever they sit, are an accepted head of
  that major type and argument; so two accepted heads of the same major
  type and argument are the same bytes. A head's length is a function of
  its first byte, and a head copied byte for byte is the same head.
- **Transport and prefix-freedom** (`Cbor_Det.Proof.Transport`): an
  accepted item, or run of members, copied byte for byte anywhere is
  accepted there and ends at the corresponding place, so acceptance and
  the end depend only on the item's own bytes; and no accepted item is a
  proper prefix of another.
- **The facts the later proofs use**, each a lemma: ends are within the
  buffer and past the start; runs of members (start, step, prefix,
  monotonicity, failure propagation); the key-order rule one key at a
  time, and that it depends only on the bytes compared; and the algebra
  of equal slices. Within `Cbor_Det.Proof.Det`, in `Cbor_Det.Proof.Model`
  and `Cbor_Det.Proof.Unique`, and in the proof clients below, the
  recursive definitions are hidden from the provers and opened one step
  at a time by these lemmas; the proofs in `Cbor_Det.Proof.Transport` see
  their bodies.
- **The value an item denotes** (`Cbor_Det.Proof.Model`): `Same (B1, P1,
  B2, P2, D)` says that the accepted items at `P1` in `B1` and at `P2` in
  `B2` denote the same value. There is no value object: the value is a
  relation between two encodings. The kinds are kept apart (the major
  types must be equal), so the integer 1 is never the same as `true`, and
  a byte string never the same as a text string. Within a kind: an
  integer is its sign and magnitude (the major type and the argument); a
  byte or text string is its bytes; an array is its members in order; a
  map is the set of its key/value pairs in no order, every pair of each
  matched by a pair of the other with the same key and the same value,
  keys of any kind, containers included; `false`, `true` and `null` are
  themselves. Neither the width of a head nor the place of an item plays
  a part.
- **Canonical uniqueness** (`Cbor_Det.Proof.Unique`, P4):
  `Lemma_CU_Whole (B1, B2)`: two buffers, with any bounds, each accepted
  whole (`Accept_Whole`), whose items denote the same value (`Same` at
  `Max_Depth`), have the same length and the same bytes, byte for byte.
  So a value has at most one accepted encoding. It rests on `Lemma_CU`,
  the same for accepted items at any place in any buffers, by induction
  on the depth; for maps, on the strict order of keys (each key below
  every later key, so no two keys are the same bytes), on the key match
  as sets, which two ascending orders turn into the same keys in the same
  order, and on the values matched under those keys.
- **The converse** (`Lemma_Same_Of_Bytes`, `Lemma_Same_Of_Bytes_Whole`):
  two accepted items that are the same bytes, at any places in any
  buffers (a copy with other bounds included), denote the same value; and
  `Lemma_Same_Iff_Bytes_Whole` states both directions at once: of two
  inputs accepted whole, `Same` holds exactly when they have the same
  length and the same bytes.
- **Reflexivity** (`Lemma_Same_Refl`): `Same` holds between every
  accepted item and itself, for every kind, so it is never vacuously
  false for a kind (which would make the uniqueness above say nothing
  about it).
- **Proof clients** (`Cbor_Det.Proof.Surface`): ghost procedures that
  each consume lemma contracts as a later proof will, with the
  definitions hidden, and prove from them alone the guarantees later
  proofs rely on (for example that two accepted heads of the same major
  type and argument are the same bytes, and that an accepted map's keys
  are strictly ascending). Weakening a clause of an exported contract
  that a later proof would need makes a client fail; a few clauses follow
  from the rest of their contract, and no client can need them.
- **Proof clients of the value relation and uniqueness**
  (`Cbor_Det.Proof.Model_Surface`): for every subprogram of
  `Cbor_Det.Proof.Model` and `Cbor_Det.Proof.Unique` with a
  postcondition, a ghost procedure that calls it and asserts each
  conjunct of the postcondition on its own, with the definitions hidden;
  so a weaker postcondition no longer proves, except for the few
  conjuncts that follow from the rest of their contract.
- **The decoder** (`Cbor_Det.Decoder`): `Check` returns `Ok` exactly
  when `Accepts (Data)` holds, which is `Accept_Whole (Data)` above (P1:
  `(Result = Ok) = Accepts (Data)`); `Where` is `Data'Last + 1` on `Ok`,
  `Data'First` on an empty input (any bounds, null arrays included), and
  otherwise an index of `Data`; and `Check` always terminates. Its body
  is one pass that recurses only into nested items (at most `Max_Depth +
  1` calls active) and judges the members of a container in a loop; each
  count or length is compared with the bytes left before it is used (a
  map's count with half of them: a division, never a doubling). Which
  `Status` a rejection reports, and its exact `Where`, are tested, not
  proved.
- **Proof clients of the decoder** (`Cbor_Det.Decoder.Surface`): ghost
  procedures that each call `Check` and prove, from its contract alone,
  one clause of it on its own (`Ok` means accepted with `Where = Data'Last
  + 1`; accepted means `Ok`; a rejection means not accepted; an empty
  input is `Truncated` at `Data'First`; any other rejection is at an
  index of `Data`), so that a weaker contract would no longer prove.
- **No run-time error** in any of it, with or without checks.

## What is tested

The test runner (`tests/`, `test_main`) runs in every cell of the build
matrix. The head helpers are tested in every cell; the specification and
the lemmas are ghost code, compiled only when the library is built with
its contracts on (the `contracts` cell), and the runner says whether
they ran, and fails if they did not run where they could.

- Every head form of every major type at the argument boundaries (23/24,
  255/256, 65535/65536, 2^32-1/2^32, 2^64-1), the wider forms, the
  truncations, and additional information 28 to 31.
- RFC 8949 Appendix A, all 81 examples: the 37 in this profile accepted,
  the others refused. A refusal for each rule. Item ends with unrelated
  bytes after the item, and `Accept_Whole` on its own. 16 and 17 nested
  containers, of every kind.
- Null arrays with any bounds, buffers ending at the top of the index
  range, oversized lengths and counts (including map counts around
  2^30-1), and copies of items elsewhere.
- The lemmas executed on real bytes: each call checks its precondition
  and postcondition.
- A differential test (`scripts/differential.sh`) against an independent
  reference decoder in Python (`tests/reference/`): a corpus generated
  from a seed (every input of up to 2 bytes, structured items nested to
  the depth bound and one past it, keys in, out of and equal order,
  boundary-width heads, truncations, trailing bytes), the reference's
  head table, and every input of up to 3 bytes. Ends, head arguments
  and lengths, and whole-input verdicts are compared separately. The
  specification is a predicate written to be proved, not to be fast:
  its cost grows quickly with nested maps of more than one pair, so a
  cost model predicts each input's cost, and the few inputs too costly
  to run are counted and reported, never skipped silently.

- **The decoder**, by `scripts/decoder-tests.sh`, in a plain cell and in
  the contracts cell (where `Check`'s postcondition also runs):
  - its verdict against the reference decoder: every input of the
    reference's head table (67 705, of which 1 104 accepted, both counts
    pinned), three seeded corpora (every row in the plain cell; in the
    contracts cell every row the cost model allows, the rest counted)
    and every input of up to 3 bytes;
  - its `Status` and `Where` against an independent status oracle
    (`tests/reference/ref_status.py`, written without access to this
    crate's code from the precedence table of the decoder's contract):
    the oracle's corpus, the oracle's answers on the reference's corpora,
    and boundary inputs (arrays and maps of 65 536 members, an array of
    1 000 000, map keys that are containers nested 16 deep, maximum
    lengths and counts, map counts at and around half the bytes left);
    each input at index 1, at index 1000 and ending at the top of the
    index range, and the empty input with null bounds anywhere;
  - RFC 8949 Appendix A, all 81 examples, and a rejection vector for each
    `Status`, including the overlapping-rule examples;
  - operation counts (ghost counters, in the contracts cell): on each
    workload of N bytes the bytes consumed (each head and each string's
    payload once; a payload is consumed without being read) are N for an
    accepted input (at most N otherwise) and the bytes compared between
    map keys at most `Max_Depth` x N; the measured ratios are printed.

- **The value relation**, by `scripts/model-tests.sh` (and the CI job
  `model`), against an independent denotation oracle
  (`tests/reference/ref_denotation.py`, written without access to this
  crate's code, with values tagged so that kinds stay apart and maps are
  unordered sets of pairs): `Same` itself, executed with the library's
  contracts on, against the oracle's label on every pair of its two pair
  files: 22 000 pairs of accepted inputs from a seeded corpus (4 398 the
  same value, maps built in different orders among them) and every
  ordered pair of the 1 086 accepted inputs of up to 2 bytes (1 179 396
  pairs). Each pair is compared as written and with the second input at
  index 1000, and the uniqueness lemmas, the converse or the two-way
  lemma run on it, so that their contracts are checked on it. The oracle
  and both files are pinned by their SHA-256; the oracle's own checks
  (every input of up to 3 bytes encoded back to itself, no two distinct
  accepted inputs with the same value, a second encoder, deliberately
  faulty copies of itself caught) run first.
- **The proofs' sensitivity**: a proof mutation suite was run against
  these proofs (each postcondition clause of the value relation's and
  uniqueness lemmas weakened one at a time, the value relation made
  coarser or stricter, the key order removed from its definition and its
  lemmas); every mutant either failed its designated proof check or test,
  or was shown equivalent.\* The suite and its logs are evidence for this
  release; they are not part of the crate.

  \* Of the 107 mutants, 89 were killed by a proof check, 8 by a test
  row (each also failing its proof check) and 10 were equivalent, two of
  them shown so by argument, not by the tool. GNATprove 16 reports every
  assertion it cannot prove as "provers reached step limit" and does not
  tell a false assertion from one that is only hard, so the 89 proof
  kills rest on that report. The suite ran with a limit of 10 000
  steps; each of the 89 kills was rerun with a limit of 100 000 and
  stayed unproved at the same assertion, with no counterexample, so it
  is also unproved at the crate's limit of 40 000; and the unmutated
  proofs and the mutants that remove a derivable clause prove. That is
  evidence the checks are sensitive, not a proof that the mutated
  assertions are unprovable.

## What is trusted

Nothing beyond the GNAT run-time and the toolchain (GNAT, gprbuild,
GNATprove and its provers) at the pinned versions below.

One GNATprove warning is silenced: in `Same`, the branch for tags
(`when 6 => False`) is proved unreachable, since `Det_End` accepts no
tag, and GNATprove's "unreachable branch" warning on it is turned off
for that definition only, with the reason in the source. Nothing is
assumed by it.

## What is not claimed

- No cursor and no writer exist yet: the decoder checks an input but
  does not read values out of it.
- No round trip is proved, and no existence: canonical uniqueness says
  that a value has at most one accepted encoding, not that every value
  has one, nor that a writer produces it (there is no writer yet).
- Not "RFC 8949 conformant": the specification covers this profile of
  section 4.2.1 only, and its agreement with the RFC is tested, not
  proved.
- UTF-8 validity of text strings is not checked.
- Inputs longer than 2^31-2 bytes are outside the index range.
- No timing, stack or performance figure is claimed or proved. The speed
  target for this crate (less than 100% slower than a comparable C or
  Rust implementation) is not claimed: no comparison has been made. The
  figures under "Measured" are information for one machine per platform.

## Concurrency

`Check` reads only its arguments. In a production build it is pure and
any number of tasks may call it at once. In the contracts build (the
test cell with assertions and ghost code on) it also updates the ghost
operation counters, `Cbor_Det.Decoder.Counters`, which are shared
mutable state: that build is for tests, and calls from several tasks
would race on the counters.

## Measured (information, not claims)

`scripts/decoder-measure.sh`, in a production cell (`-O3`, run-time
checks off, no contracts), on one machine per platform. Throughput is
the median of 11 samples; stack is what `Check` used beyond its caller,
found with a stack pad (to 64 bytes). The long-string figure is high
because `Check` reads a string's head and skips its bytes.

| Workload | macOS arm64 | Linux aarch64 | Linux x86_64 (emulated) |
|---|---|---|---|
| small message, a map of 6 pairs (23 bytes) | 468 MB/s | 470 MB/s | 265 MB/s |
| 16 nested containers (28 bytes) | 332 MB/s | 365 MB/s | 151 MB/s |
| a map of 65 536 pairs (261 869 bytes) | 615 MB/s | 601 MB/s | 316 MB/s |
| a 1 MB byte string (head only; bytes skipped) | 237 TB/s | 230 TB/s | 105 TB/s |
| stack, 16 nested containers | 2 624 bytes | 2 352 bytes | 2 288 bytes |
| stack, arrays of 65 536 and 1 000 000 members | 464 bytes | 432 bytes | 368 bytes |
| stack, a map of 65 536 pairs | 464 bytes | 432 bytes | 408 bytes |

The Linux figures come from containers on the macOS machine (Linux
x86_64 under emulation, so far slower than native). In these
measurements the stack did not grow with width: arrays of 65 536 and
1 000 000 members took the same stack on each platform (464, 432 and
368 bytes), and a map of 65 536 pairs about the same (464, 432 and 408
bytes). The Windows x86_64 figures come from the information step of the
CI `decoder` job and are not recorded here yet.


## Platforms and toolchain

The CI workflow builds and proves on:

- Linux x86_64 (glibc)
- Linux aarch64 (glibc)
- macOS arm64
- Windows x86_64

with a pinned toolchain: Alire 2.1.1, GNAT 16.1.0, gprbuild 26.0.1 and
GNATprove 16.1.0.

## Building

With [Alire](https://alire.ada.dev) 2.1.1:

```sh
alr -n build
```

The build matrix (`-O0`/`-O2`/`-O3` with checks off and on, plus one
cell with contracts enabled), and the test of its driver:

```sh
bash scripts/test-matrix.sh
bash scripts/matrix.sh
```

## Proving

GNATprove is a dependency of the nested `tests/` crate only, so the
library's own manifest stays free of it. Provers are bounded by steps,
not time.

```sh
bash scripts/test-prove.sh      # the script fails on each way a proof run can fail
bash scripts/prove.sh --jobs 2
```

runs the proof from cold, per unit and then per subprogram, with an
explicit number of parallel proof jobs, and prints for each command the
checks proved and not proved and the most steps any check took. It
fails if a check is not proved; if gnatprove fails or is killed by a
signal; if a command leaves no summary, or one without a well-formed
total; if the summary does not show the unit or subprogram as analysed,
or counts checks the output does not report; or if the summary shows a
justified check or a `pragma Assume`. `--guard SECONDS` stops a command
that runs longer; a tripped guard is an error to rerun, never a failed
proof. The guard is a safeguard, not a result: its value for CI is not
measured yet, so none is set.

Each result line ends with the command's wall-clock time in whole
seconds (`NAME: proved P, not proved U, max steps S, exit E, T s`).

`--shard K/N` (1 <= K <= N <= 999) runs one of N shards of those
commands, split by measured time. Each command costs its seconds in
`scripts/prove-costs.txt` (a command not listed costs the median of the
listed ones); taken largest first, each goes to the shard with the
least cost so far, and a shard runs its commands in the order above
(the files of `src/` in C collation order, so the same on every
platform), each exactly as in a whole run. The table is used only to
balance the shards: a missing, stale or wrong entry can make one shard
slower than the others, but never changes which commands run or what
they prove; names in it that are not commands are ignored, and with no
table the split is round robin. A malformed table fails the sharded run
(exit 2) before anything runs. Before any proof a sharded run checks
that the N shards together hold every command exactly once and that its
own holds at least one, and prints `shard K/N: M of T commands`; if
not, it exits 2 having proved nothing. A run, sharded or not, that started fewer commands than
it listed exits 2 and never reports all proved. `--list` prints the
names of the commands (of the shard, with `--shard`) and runs nothing.
CI runs the proof in three shards on each platform; the proof is all
proved only if all three pass. The script cannot see which shards CI
runs: the workflow's matrix must list each of the three once.

To measure the costs again, run the shards (or the whole proof) on a
few machines, keep their output, and make a new table from it:

```sh
bash scripts/prove.sh --jobs 2 --shard 1/3 > shard-1.log
# ... the other shards, on each machine ...
bash scripts/prove-costs.sh *.log > scripts/prove-costs.txt
```

`scripts/prove-costs.sh` takes the mean time of each command over every
result line in the files (CI logs too, whatever precedes the name),
rounded to whole seconds and at least 1. A stale table only worsens the
balance.

The whole project in one command:

```sh
cd tests
alr -n build
alr -n exec -- gnatprove -P ../cbor_det.gpr -j2
```

## Testing

```sh
bash scripts/matrix.sh          # every cell, the test runner in each
bash scripts/differential.sh    # the differential test (Python 3.10+)
```

The differential fails if the cost model and the reference disagree on
any row's end (the row is reported, never deferred); rows too costly to
run are deferred and counted.

On Windows, in Git Bash, `bash scripts/windows-check.sh` runs every check
above and exits 0 only if all ran and passed: 1 if any failed, 2 if one
could not run (alr or Python 3.10 or later missing). `--only STEP,...`
or `--skip STEP,...` runs some of the steps (the names are in the
script's header and in its summary); a run that leaves any step out
exits 3 (PARTIAL), never 0, even if every step it ran passed, and an
unknown step name or option exits 4 with nothing run.
`bash scripts/test-windows-check.sh` tests those exit statuses.

`CBOR_DET_SEEDS` chooses the corpus seeds (default 1).

```sh
bash scripts/test-runner.sh       # the runner fails on a missing, empty or short input, without printing its path (Python 3.10+)
bash scripts/decoder-tests.sh     # the decoder against both references (Python 3.10+)
bash scripts/decoder-measure.sh   # throughput and stack, as information
bash scripts/model-tests.sh       # the value relation Same against the denotation oracle (Python 3.10+)
```

`decoder-tests.sh` runs the corpus seeds 1 to 3 by default
(`CBOR_DET_SEEDS`); in the contracts cell it runs the corpus rows whose
predicted cost is at most `CBOR_DET_DECODER_COST_LIMIT` (default
1 000 000 calls) and counts the rest.

When a build fails, `matrix.sh`, `differential.sh`, `decoder-tests.sh`
and `decoder-measure.sh` print at most the first 40 lines of its log
that have a known form: a compiler message on one of the crate's own
files (`unit.adb:12:4: ...`), or one of gprbuild's and alr's fixed lines
for a failed compilation; a line holding a slash or a backslash is never
printed. The whole log stays in `tests/obj`. The limit: a message can
quote a value the caller gave a project setting (an invalid
`CBOR_DET_LIBRARY_TYPE` or `LIBRARY_TYPE` is printed back as `value
"..." is illegal for typed string "library_type"`, or on Windows with an
`error:` prefix and a second line naming `Library_Kind`), so no private value
belongs in one. A message that itself holds a slash (one about the
operator "/") is not shown either; it is in the log.

## Gates

```sh
bash scripts/check-sources.sh --self-test     # the gate catches known bypasses
bash scripts/check-sources.sh --require-git   # no proof escape hatches
bash scripts/test-version.sh                  # the version gate refuses each fault
bash scripts/check-version.sh                 # versions agree
bash scripts/check-leakage.sh --self-test     # the gate catches each class
bash scripts/check-leakage.sh --require-git   # no local paths or private references
```

CI runs the two gates with `--require-git`, which refuses to run unless
the crate is a git work tree. Without it, outside git, a gate falls back
to scanning the directory with `find`: a convenience before `git init`,
not the shipping check.

To run the source and leakage gates on the staged content before every
commit, install the pre-commit hook once per clone:

```sh
git config core.hooksPath .githooks
```

The hook (`.githooks/pre-commit`) runs `scripts/check-sources.sh --staged`
and `scripts/check-leakage.sh --staged` on what the commit would record,
and refuses the commit if either fails or if the gate scripts in the
working tree differ from the staged ones.

The gates stop accidents and a careless author; they cannot stop someone
trying to beat a shell scanner. Escaped or encoded forms (JSON `\u`
escapes, percent-encoding, base64, HTML entities, compressed data) are
not decoded and are not a supported way to write anything the gates
look for. Three stated limits of the leakage gate: an emoji built with a
zero-width joiner is refused like any other format character; in
Markdown code spans and fenced blocks a single bare word in double
square brackets (the boolean `true`, say) is refused as a wikilink,
while other code there (nested lists, quoted strings, shell tests)
passes; and in shell and Python files, where double square brackets are
code, only a wikilink without white space inside is caught. Shell and
Python files are read as prose throughout, so a ticket-like token (a T
or D and digits) is refused even in their code.

Symbolic links are refused from the git index (mode 120000), so the rule
does not depend on whether a checkout supports symbolic links; Windows
junctions are detected by comparing each directory's real path with its
path. Under Git Bash, MSYS or Cygwin both sides of every path comparison
go through `cygpath -m -l` first (long names, so that a short name such
as `RUNNER~1` in a temporary directory matches the long name git
reports). Git mode and that `cygpath` comparison are verified by the CI
gates job on the Windows runner (`--require-git`), not by a local run.
On Windows the self-test compares a fixture's paths with the real `git`,
`uname` and `cygpath`; elsewhere it uses stand-ins for them.

A local Windows check needs no git: in Git Bash, in a plain copy of the
crate (no `.git`), `bash scripts/windows-check.sh` runs the gates in find
mode and everything else, and writes its summary and logs to
`tests/obj/windows`. Find mode needs a POSIX `find`. Windows has its own
`find` (a text search, in System32); the gates look past it to the first
`find` on the PATH that behaves as a POSIX one, and refuse, saying so, if
there is none. If they do refuse, put Git's tools first and run it again:

```sh
export PATH=/usr/bin:$PATH
bash scripts/windows-check.sh
```

The summary records which `find` comes first on the PATH and whether the
copy is a git work tree. Find mode leaves out anything named `.git`, as
git never records it, so a stray `.git` in the copy is not scanned.

What a Windows run is expected to print: each self-test ends with
`self-test: N passed, 0 failed, K skipped`, and every skipped case is
named on its own line, `self-test SKIPPED: CASE (MODE): REASON`. Where
Git Bash cannot make symbolic links, expect skips for the link cases in
find mode ("symbolic links are not available here, and find mode has no
index"), for the cases that need a real link in the working tree ("this
case needs a real symbolic link in the working tree"), for the
unreadable-file case if `chmod` cannot make a file unreadable, for the
fifo case if `mkfifo` is missing, and for the cases that run the gates
with a PATH of their own (a tool left out) if the tools can run from
such a directory neither as links nor as wrapper scripts (MSYS programs
need msys-2.0.dll beside them, so the self-test uses wrappers there);
the link cases still run in git
and staged mode, through 120000 index entries. The cases whose file
names Windows cannot hold (device names, a trailing dot or space, a
colon, a question mark, a tab) are decided by trying: where `git` will
not record such a name from the working tree (Git for Windows refuses
them), git and staged mode put the entry in the index alone and say so
in a `self-test NOTE` line, and if even that fails, the case is skipped
with the reason; find mode, which has no index, is skipped where the
name cannot be written. Any `self-test FAILED`
line is a finding, and the first one is preceded by the system, the git
version and the git settings that differ between hosts; a failed pre-commit hook case is followed by a
diagnosis (what `git rev-parse --show-toplevel` gave, the PATH and the
`git` the hook saw, and a `bash -x` trace of the hook), with paths and
names scrubbed. The two gates should end with `sources: clean` and
`leakage: clean`.

The hook case without `cmp` runs with a PATH of only the tools the hook
needs. Git puts its own directory (its exec-path) first on a hook's
PATH. If the `git` there cannot start under that PATH (an MSYS `git`
needs `msys-2.0.dll`, from a directory that PATH leaves out), the case
sets `GIT_EXEC_PATH` to the tools' directory and says so in a
`self-test NOTE` line; if git still cannot work inside a hook, the case
is skipped, with the reason.

To run only some self-test cases, set `SELF_TEST_ONLY` to a part of
their names, as the FAILED and SKIPPED lines show them. The run ends
`self-test: PARTIAL (...)` with the number of cases run and not
selected; it exits 0 only if every case it ran passed, and fails if no
case name contains the text. A partial run is never the check itself.

```sh
SELF_TEST_ONLY="hook: a missing cmp" bash scripts/check-leakage.sh --self-test
```

## License

BSD-3-Clause: see [LICENSE](LICENSE).
