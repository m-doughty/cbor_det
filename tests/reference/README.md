# The reference decoder

`ref_cbor_det.py` is an independent decoder for this crate's profile of
RFC 8949: deterministic encoding (section 4.2.1), integers of both signs
with 64-bit arguments, byte strings, text strings as bytes (UTF-8 is not
checked), arrays, maps with keys of any kind in bytewise order, `false`,
`true` and `null`, and at most 16 containers nested in one another. It
was written without access to this crate's code, and shares none with
it. It uses Python's standard library only (Python 3.10 or later).

It is kept as received with one change: the display labels of three
RFC 8949 Appendix A examples (lines 202 to 204: the one-character text
strings U+00FC, U+6C34 and U+10151) are written with Python `\u` and
`\U` escapes instead of the characters themselves, so that the file is
ASCII. The escapes denote the same strings, so the module's values are
unchanged: the escaped file writes byte for byte the same corpora (seeds
1 and 2), head table and self-test output as the original. Nothing else
differs.

    as received:  aa52b799511abb2676c1e02d7b47d1f48131fa949e6786ae0214e3b2bd88d696
    as kept here: 287a37add851d40c2dd980f7ce17d6dadae7ba1d657927658816eaea9ba597fe

`scripts/differential.sh` refuses to run unless the file is the one kept
here. Any tooling around it lives in other files.

## What it provides

- `item_end (buf, start, depth_left)`: the end of the item at `start`,
  or -1; bytes after the item are not its concern.
- `whole (buf)`: the buffer holds exactly one item, nested at most 16
  deep.
- `head (buf, start)`: the major type, argument and length of a shortest
  head of major type 0 to 5, or nothing.
- `corpus --seed N --out FILE`: a corpus generated from a seed: every
  input of up to 2 bytes, the RFC 8949 Appendix A examples in the
  profile, the mandatory witnesses, boundary-width heads, random items
  nested up to 16 deep and one deeper, keys in, out of and equal order,
  truncations, trailing bytes, non-shortest forms, tags, floats and
  indefinite lengths. One line per input: the bytes, `item_end` at 0, and
  `whole`.
- `heads --out FILE`: a table of heads, one per line.
- `selftest`: its own checks.

## The files beside it

- `cost_model.py` predicts how long the library's ghost predicate takes
  on each corpus row, so that rows too costly to run are counted and
  deferred, never skipped silently, and checks the prediction against
  the times measured.
- `exhaustive.py` writes the reference's verdict on every input of 0 to
  3 bytes, for the runner to compare.

Run everything with `scripts/differential.sh`. Generated files go to
`tests/obj/differential`, which is not part of the repository.
