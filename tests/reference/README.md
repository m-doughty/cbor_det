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

## The denotation oracle

`ref_denotation.py` is a third independent program: it says what value
an accepted input denotes, in the sense of the crate's value relation
`Same` (`Cbor_Det.Proof.Model`). It was written blind, from the profile
and the definition of the value only, without access to this crate's
code or to the other references, and shares no code with them. Standard
library only (Python 3.10 or later).

Its values are tagged, so that kinds stay apart: an integer is its sign
and magnitude (a major type 1 argument n is the magnitude n + 1), a byte
string and a text string are their bytes under different tags (text is
not checked to be UTF-8), an array is its members in order, a map is the
set of its key/value pairs in no order, with keys of any kind, a
container included, and `false`, `true` and `null` are tags of their
own. Two inputs denote the same value when their tagged values are
equal. It rejects what the crate's profile rejects, at most 16
containers nested in one another.

It is kept as received: no change.

    sha256: 9067be6cf0bfc67b126942409b184609dcfb7f03ccc3aaa1825026dd61f9d4ff

- `selftest`: its own checks, among them ten deliberately faulty
  copies of its decoder, each of which its batteries catch.
- `check`: every input of 0 to 3 bytes (16 843 009, walked by prefix):
  269 799 accepted (0, 55, 1 031 and 268 713 by length), each encoded
  back to its own bytes, and no two distinct accepted inputs with the
  same value; then 100 985 values generated from a seeded corpus,
  checked against a second encoder of its own.
- `pairs FILE`: writes two pair files, FILE and FILE.small, one line
  per pair, `HEXA HEXB S` when the two denote the same value and
  `HEXA HEXB D` when they do not, after a header of lines that start
  with `#`. FILE holds 22 000 pairs from the seeded corpus (4 398 S,
  17 602 D), among them maps built in different orders; FILE.small
  holds every ordered pair of the 1 086 accepted inputs of up to 2 bytes
  (1 179 396 pairs: 1 086 S, 1 178 310 D). The seeds are fixed in the
  program (corpus 1362215088, pairs 1362229966), so the files are the
  same on every run:

      pairs.txt        c46e87b889e0e3805ce21ff1df118ed4b94be5543cdbd785432460450635fb43
      pairs.txt.small  bcc969eab765fec25ea35583a647207022cc9f87803b18a95c1c5f2cc982a2b6

`scripts/model-tests.sh` refuses to run unless the program and both
files it writes are the recorded ones; it writes them to
`tests/obj/model`, which is not part of the repository, and compares
`Same` with every label.

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

Run them with `scripts/differential.sh` (the ghost predicate),
`scripts/decoder-tests.sh` (the decoder) and `scripts/model-tests.sh`
(the value relation). Generated files go to
`tests/obj/differential`, which is not part of the repository.
