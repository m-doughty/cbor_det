# Changelog

## 0.1.0 - 2026-10-11

- The value model and canonical uniqueness, `Cbor_Det.Proof.Model` and
  `Cbor_Det.Proof.Unique`: specification and lemmas only.
  - Defined: `Same`, the value two accepted items denote: kinds kept
    apart (so 1 is never `true`, and a byte string never a text string),
    integers by sign and magnitude, strings by their bytes, arrays by
    their members in order, maps as unordered sets of key/value pairs
    with keys of any kind, `false`, `true` and `null` as themselves;
    head widths and positions play no part.
  - Proved: canonical uniqueness (P4), `Lemma_CU_Whole`: two inputs, each
    accepted whole, that denote the same value have the same length and
    the same bytes, so a value has at most one accepted encoding; its
    converse, `Lemma_Same_Of_Bytes_Whole` (the same bytes, at any bounds,
    denote the same value), and both at once,
    `Lemma_Same_Iff_Bytes_Whole`; `Same` reflexive for every kind
    (`Lemma_Same_Refl`). No round trip and no existence are claimed.
  - Proof clients, `Cbor_Det.Proof.Model_Surface`: each conjunct of each
    postcondition of the two units asserted on its own from the contract
    alone.
  - Tested: `Same`, executed with contracts on, against an independent
    denotation oracle (`tests/reference/ref_denotation.py`) on 22 000
    seeded pairs and all 1 179 396 ordered pairs of the accepted inputs
    of up to 2 bytes, each also with one input rebased, with the
    uniqueness lemmas executed on each pair (`scripts/model-tests.sh`,
    CI job `model`); the oracle and its pair files are pinned by SHA-256.
  - One GNATprove warning ("unreachable branch", on the proved-dead
    branch for tags in `Same`) is silenced there, with its reason.
- The decoder, `Cbor_Det.Decoder`: `Check (Data, Result, Where)`.
  - Proved: `Result = Ok` exactly when `Accepts (Data)`, that is
    `Accept_Whole (Data)`; `Where` is `Data'Last + 1` on `Ok`,
    `Data'First` on an empty input, and an index of `Data` on any other
    rejection; no run-time error; `Check` always terminates.
  - Tested, not proved: the `Status` and `Where` of a rejection, against
    an independent status oracle (`tests/reference/ref_status.py`); the
    verdict against the reference decoder (its head table, seeded corpora
    and every input of up to 3 bytes); RFC 8949 Appendix A; boundary
    inputs; operation counts (`scripts/decoder-tests.sh`).
  - Measured, as information: throughput and stack
    (`scripts/decoder-measure.sh`). The speed target is not claimed.
  - Proof clients, `Cbor_Det.Decoder.Surface`: each clause of `Check`'s
    contract proved on its own from the contract alone.
- `scripts/prove.sh` reports the largest step count of every prover on
  every line and of the summary, and runs the subprograms declared only
  in a body too.
- `scripts/prove.sh --shard K/N` (N at most 999) runs one of N shards
  of the proof commands, after checking that the N shards cover every
  command exactly once; a run that starts fewer commands than it listed
  fails; `--list` prints the commands. The files are taken in C collation
  order on every platform. CI runs the proof in three shards per
  platform. The shards are split by measured time: each command's
  seconds from `scripts/prove-costs.txt`, a table used only to balance
  the shards (coverage never depends on it), made from run logs by
  `scripts/prove-costs.sh`. Each result line ends with the command's
  time in whole seconds.
- The proof step limit is 40 000 (was 10 000), per prover and per
  check.
- The crate layout, the build matrix, the proof configuration (bounded by
  prover steps, not time) and the CI gates. `Cbor_Det` declares the
  shared types.
- The proof core, `Cbor_Det.Proof` and its children `Heads`, `Det` and
  `Transport`: specification and lemmas only, nothing a consumer calls
  to check an input yet.
  - Proved: an accepted head is the shortest encoding of its major type
    and argument, and the bytes of that encoding are an accepted head
    (uniqueness, both ways); a head's length is a function of its first
    byte.
  - Defined: `Det_End`, the end of the deterministic item that starts at
    a position, or 0, for the whole profile (integers, byte and text
    strings, arrays, maps with keys in bytewise order, `false`, `true`,
    `null`, at most `Max_Depth` = 16 containers nested), and
    `Accept_Whole`, the check of a whole input.
  - Proved: whether an item is accepted, and where it ends, depends only
    on its own bytes (transport), and no accepted item is a proper
    prefix of another; with the facts about runs of members, key order
    and equal slices that those proofs use.
- `Cbor_Det.Proof.Surface`: ghost proof clients that consume the exported
  lemma contracts, so that a weakened contract fails the proof.
- Tests: head vectors at every argument boundary; RFC 8949 Appendix A;
  a refusal per rule; depth 16 and 17; null arrays, buffers at the top of
  the index range, oversized lengths and counts; the lemmas executed on
  real bytes; a differential test against an independent reference
  decoder over generated inputs, its head table and every input of up to
  3 bytes (`scripts/differential.sh`).
- `scripts/prove.sh`: the proof per unit and per subprogram, from cold,
  with the steps each subprogram took.
- The source and leakage gates read Python files (`.py`). The version
  gate expects the release heading with an ASCII hyphen
  (`## x.y.z - YYYY-MM-DD`), so that every file of the crate is ASCII;
  `scripts/test-version.sh` tests it.
- The gate self-tests run a subset with `SELF_TEST_ONLY` (reported as
  PARTIAL), and a failed pre-commit hook case prints a scrubbed
  diagnosis. On a host whose git will not record a file name Windows
  cannot hold, those cases use the index alone (or are skipped, saying
  why); on Windows the path comparison is tested with the real tools.
- Under Git Bash, MSYS or Cygwin the gates compare paths in their long
  form (`cygpath -m -l`).
- `scripts/windows-check.sh` gathers every check on Windows and exits
  non-zero if a step failed or could not run, or if `--only` or `--skip`
  left a step out; `scripts/test-windows-check.sh` tests that.
