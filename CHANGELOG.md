# Changelog

## 0.1.0 - 2026-10-11

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
