# The reference decoder

`ref_cbor_det.py` is an independent decoder for this crate's profile of
RFC 8949: deterministic encoding (section 4.2.1), integers of both signs
with 64-bit arguments, byte strings, text strings as bytes (UTF-8 is not
checked), arrays, maps with keys of any kind in bytewise order, `false`,
`true` and `null`, and at most 16 containers nested in one another. It
was written without access to this crate's code, and shares none with
it. It uses Python's standard library only (Python 3.10 or later).

It is kept as received with two changes:

- the display labels of three RFC 8949 Appendix A examples (the
  one-character text strings U+00FC, U+6C34 and U+10151) are written
  with Python `\u` and `\U` escapes instead of the characters
  themselves, so that the file is ASCII. The escapes denote the same
  strings, so the module's values are unchanged;
- its command line parser, on an error, prints a fixed message (the
  arguments are not valid) instead of argparse's, which quotes the
  argument given.

The kept file writes byte for byte the same corpora (seeds 1 and 2),
head table and self-test output as the original. Nothing else differs.

    as received:  aa52b799511abb2676c1e02d7b47d1f48131fa949e6786ae0214e3b2bd88d696
    as kept here: 36f1d76b9cf4a96a10104ecbb5e108624a7d1d0f34b4eb3f365f2daf893edd89

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

## The status oracle

`ref_status.py` is a second, independent program: for any buffer it
reports the first fault in decode order, as a status and a 0-based
position, or `Ok`. It was written blind, from RFC 8949 and the decoder's
precedence table only, by a second author without access to this
crate's code, and shares none with it. It holds two implementations (a
recursive one, the oracle, and one with an explicit stack) that its
self-test checks against each other. Standard library only (Python 3.10
or later).

It is kept as received with three changes:

- where its comments and four self-test labels named one of its author's
  decisions by a short code, a letter and a digit, the code is replaced
  by the neutral words "owed-member decision" (or "owed" in a label);
- `classify`, on a line whose first field is not hex bytes, prints the
  line's number and a fixed message instead of the field;
- its command line parser, on an error, prints a fixed message (the
  arguments are not valid) instead of argparse's, which quotes the
  argument given.

The program's values are unchanged: the kept file writes byte for byte
the same corpora (seeds 1, 2 and 3), classifies the same rows the same
way and passes the same self-test as the original.

    as received:  5e313c5a10ec1e3f6903bfffa314f36b555055d5bc02e7dbc0dc6b38f44675f9
    as kept here: 6dc6f3064139acdc6fbf3f139a94bf59062fb68f3b71edccff9acf1231fdcb9f

- `classify --in FILE --out FILE`: the status and position for the
  bytes in the first field of each line.
- `corpus --seed N --out FILE`: a corpus with every buffer of up to 2
  bytes, nesting around the depth bound, every head form at argument
  boundaries, counts, keys, faults, owed members and random items, each
  with its status and position.
- `selftest`: its own checks.

`scripts/decoder-tests.sh` refuses to run unless both files are the ones
kept here.

## The files beside it

- `cost_model.py` predicts how long the library's ghost predicate takes
  on each corpus row, so that rows too costly to run are counted and
  deferred, never skipped silently, and checks the prediction against
  the times measured.
- `exhaustive.py` writes the reference's verdict on every input of 0 to
  3 bytes, for the runner to compare.
- `boundary.py` writes the boundary inputs for the decoder (wide arrays
  and maps, nested container keys, maximum lengths and counts, map counts
  around half the bytes left); what each should give is the status
  oracle's to say.

Run them with `scripts/differential.sh` (the ghost predicate) and
`scripts/decoder-tests.sh` (the decoder). Generated files go to
`tests/obj/differential`, which is not part of the repository.
