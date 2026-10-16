#!/usr/bin/env python3
"""Independent status oracle for the "cbor_det" deterministic-CBOR profile.

Written from RFC 8949 and the oracle brief only.  For any byte buffer it
reports the FIRST FAULT IN DECODE ORDER as (status, where), or
("Ok", len(buf)).

Rule numbers in comments ("rule 1" .. "rule 8") are the per-head rule order
of the brief:

  1. Truncated           head bytes (1 + 0/1/2/4/8) run past the end
  2. Reserved_Info       additional information 28, 29, 30 (any major)
  3. Indefinite_Length   additional information 31 (any major, incl. ff)
  4. Unsupported_Type    major 6 (tag)
  5. Unsupported_Simple  major 7 other than f4/f5/f6
  6. Non_Shortest        majors 0..5, argument wider than needed
  7. Truncated           string length / array count / 2 x map count
                         exceeds the bytes remaining after the head
  8. Too_Deep            container head nested more than 16 deep

after which a COMPLETE map key that is <= the previous key (bytewise on its
encoding) is Unsorted_Key / Duplicate_Key at the key's first byte, and bytes
after the single top-level item are Trailing_Bytes.

RFC 8949 references: section 3 (initial byte, major types, additional
information 24..27 = 1/2/4/8 argument bytes, 28..30 reserved, 31 indefinite),
3.1 (major types), 3.2 (indefinite lengths), 3.3 (simple values / floats),
3.4 (tags), 4.2.1 (core deterministic encoding: shortest arguments, definite
lengths, map keys sorted bytewise lexicographically on their encodings).

Policy decided here where the brief is silent (the owed-member decision):
a container that is still owed a member when the buffer is exhausted
(e.g. 82 81 00) is reported as Truncated at THAT CONTAINER'S head, because
the missing member has no head byte to point at and `where` must be < len.

Usage:
  python3 ref_status.py classify --in FILE --out FILE
  python3 ref_status.py selftest
  python3 ref_status.py corpus --seed N --out FILE
"""

from __future__ import annotations

import argparse
import random
import sys
from typing import Callable


class _Parser(argparse.ArgumentParser):
    """A parser whose errors never print the arguments given."""

    def error(self, message: str) -> None:
        self.exit(2, "ref_status.py: the arguments are not valid "
                     "(see --help)\n")

STATUSES = (
    "Ok",
    "Truncated",
    "Reserved_Info",
    "Indefinite_Length",
    "Unsupported_Type",
    "Unsupported_Simple",
    "Non_Shortest",
    "Too_Deep",
    "Unsorted_Key",
    "Duplicate_Key",
    "Trailing_Bytes",
)

MAX_DEPTH = 16  # a top-level container is depth 1; depth 17 is rejected

# RFC 8949 section 3: additional information 24..27 means the argument
# follows in 1, 2, 4 or 8 bytes.  Every other value has no argument bytes.
ARG_WIDTH = {24: 1, 25: 2, 26: 4, 27: 8}

# RFC 8949 section 4.2.1 (first rule): smallest argument value that NEEDS
# each width.  An argument below the bound for its width is non-shortest.
SHORTEST_MIN = {1: 24, 2: 256, 4: 65536, 8: 1 << 32}

ACCEPTED_SIMPLE = (0xF4, 0xF5, 0xF6)  # false, true, null (RFC 8949 3.3)


class _Fault(Exception):
    def __init__(self, status: str, where: int) -> None:
        super().__init__(status, where)
        self.status = status
        self.where = where


# ---------------------------------------------------------------------------
# Primary oracle: recursive descent in decode order (preorder).
# ---------------------------------------------------------------------------


def _item(buf: bytes, pos: int, depth: int) -> int:
    """Decode one item whose head starts at buf[pos] (pos < len(buf)).

    `depth` is the depth this item has IF it is a container (a top-level
    container is depth 1).  Returns the index just past the item, or raises
    _Fault with the first fault in decode order.
    """
    n = len(buf)
    ib = buf[pos]
    major = ib >> 5
    ai = ib & 0x1F
    width = ARG_WIDTH.get(ai, 0)

    # rule 1: the head's own bytes must be present (RFC 8949 section 3).
    if pos + 1 + width > n:
        raise _Fault("Truncated", pos)
    # rule 2: additional information 28..30 is reserved (RFC 8949 3).
    if ai in (28, 29, 30):
        raise _Fault("Reserved_Info", pos)
    # rule 3: additional information 31 is indefinite length / break
    # (RFC 8949 3.2); 4.2.1 forbids indefinite lengths.
    if ai == 31:
        raise _Fault("Indefinite_Length", pos)
    # rule 4: tags (RFC 8949 3.4) are outside the profile.
    if major == 6:
        raise _Fault("Unsupported_Type", pos)
    # rule 5: only false/true/null of major 7 (RFC 8949 3.3).  This covers
    # simple 0..19 (e0..f3), undefined f7, f8 xx for every xx, f9/fa/fb.
    if major == 7:
        if ib in ACCEPTED_SIMPLE:
            return pos + 1
        raise _Fault("Unsupported_Simple", pos)

    # Majors 0..5 from here on.
    after = pos + 1 + width
    arg = ai if width == 0 else int.from_bytes(buf[pos + 1 : after], "big")

    # rule 6: shortest argument (RFC 8949 4.2.1, first rule).
    if width and arg < SHORTEST_MIN[width]:
        raise _Fault("Non_Shortest", pos)

    if major in (0, 1):  # unsigned / negative integer (RFC 8949 3.1)
        return after

    remaining = n - after  # bytes left after the head, never negative here

    # rule 7: Python integers are unbounded, so 2 * count cannot overflow.
    if major in (2, 3):  # byte / text string (text not UTF-8 checked)
        if arg > remaining:
            raise _Fault("Truncated", pos)
        return after + arg
    if major == 4:
        if arg > remaining:
            raise _Fault("Truncated", pos)
    else:  # major 5
        if 2 * arg > remaining:
            raise _Fault("Truncated", pos)

    # rule 8: container nesting limit.
    if depth > MAX_DEPTH:
        raise _Fault("Too_Deep", pos)

    p = after
    if major == 4:  # definite array: members in order
        for _ in range(arg):
            if p >= n:  # owed-member decision: owed member, no head byte
                raise _Fault("Truncated", pos)
            p = _item(buf, p, depth + 1)
        return p

    # major 5: definite map.  Each key is judged for order as soon as it is
    # complete, before its value is read (RFC 8949 4.2.1 key ordering).
    prev_key: bytes | None = None
    for _ in range(arg):
        if p >= n:  # owed-member decision
            raise _Fault("Truncated", pos)
        key_start = p
        p = _item(buf, p, depth + 1)
        key = buf[key_start:p]
        if prev_key is not None:
            # bytes comparison is bytewise lexicographic, shorter first on a
            # common prefix -- exactly the 4.2.1 ordering.
            if key < prev_key:
                raise _Fault("Unsorted_Key", key_start)
            if key == prev_key:
                raise _Fault("Duplicate_Key", key_start)
        prev_key = key
        if p >= n:  # owed-member decision: value owed
            raise _Fault("Truncated", pos)
        p = _item(buf, p, depth + 1)
    return p


def status(buf: bytes) -> tuple[str, int]:
    """First fault in decode order as (status, where), or ("Ok", len)."""
    buf = bytes(buf)
    n = len(buf)
    if n == 0:
        return ("Truncated", 0)  # brief: empty buffer is (Truncated, 0)
    try:
        end = _item(buf, 0, 1)
    except _Fault as f:
        return (f.status, f.where)
    if end < n:
        return ("Trailing_Bytes", end)
    return ("Ok", n)


# ---------------------------------------------------------------------------
# Second, structurally different implementation (explicit stack, table
# driven).  Used only by selftest to cross-check the primary oracle.
# ---------------------------------------------------------------------------


def _byte_class(ib: int) -> str:
    major, ai = ib >> 5, ib & 31
    if ai >= 28:
        return "reserved" if ai < 31 else "indef"
    if major == 6:
        return "tag"
    if major == 7:
        return "ok7" if ib in (0xF4, 0xF5, 0xF6) else "simple"
    return ("uint", "nint", "bstr", "tstr", "arr", "map")[major]


_CLASS = [_byte_class(b) for b in range(256)]
_WIDTH = [(0, 1, 2, 4, 8)[max(0, (b & 31) - 23)] if 24 <= (b & 31) <= 27
          else 0 for b in range(256)]


def status_stack(buf: bytes) -> tuple[str, int]:
    n = len(buf)
    if n == 0:
        return ("Truncated", 0)
    # frame: [head_pos, items_left, is_map, prev_key, key_start]
    stack: list[list] = []
    pos = 0
    while True:
        if pos >= n:
            return ("Truncated", stack[-1][0])
        top = stack[-1] if stack else None
        if top is not None and top[2] and top[1] % 2 == 0:
            top[4] = pos  # this item is a key
        ib = buf[pos]
        w = _WIDTH[ib]
        cls = _CLASS[ib]
        if n - pos < 1 + w:
            return ("Truncated", pos)
        if cls == "reserved":
            return ("Reserved_Info", pos)
        if cls == "indef":
            return ("Indefinite_Length", pos)
        if cls == "tag":
            return ("Unsupported_Type", pos)
        if cls == "simple":
            return ("Unsupported_Simple", pos)
        end_head = pos + 1 + w
        if cls == "ok7":
            pos = end_head
        else:
            arg = ib & 31
            if w:
                arg = 0
                for b in buf[pos + 1 : end_head]:
                    arg = arg * 256 + b
                if arg < (24 if w == 1 else 1 << (4 * w)):
                    return ("Non_Shortest", pos)
            left = n - end_head
            if cls in ("uint", "nint"):
                pos = end_head
            elif cls in ("bstr", "tstr"):
                if arg > left:
                    return ("Truncated", pos)
                pos = end_head + arg
            else:
                members = arg * (2 if cls == "map" else 1)
                if members > left:
                    return ("Truncated", pos)
                if len(stack) + 1 > MAX_DEPTH:
                    return ("Too_Deep", pos)
                if members:
                    stack.append([pos, members, cls == "map", None, -1])
                    pos = end_head
                    continue
                pos = end_head
        # an item just completed at `pos`; close frames
        while stack:
            f = stack[-1]
            if f[2] and f[1] % 2 == 0:
                key = buf[f[4]:pos]
                if f[3] is not None:
                    if key == f[3]:
                        return ("Duplicate_Key", f[4])
                    if key < f[3]:
                        return ("Unsorted_Key", f[4])
                f[3] = key
            f[1] -= 1
            if f[1]:
                break
            stack.pop()
        if not stack:
            return ("Trailing_Bytes", pos) if pos < n else ("Ok", n)


# ---------------------------------------------------------------------------
# Independent canonical encoder (for generating accepted items).
# ---------------------------------------------------------------------------


def enc_head(major: int, arg: int, width: int | None = None) -> bytes:
    """Encode a head.  width None = shortest (RFC 8949 4.2.1); otherwise
    0 (inline, arg < 24) or 1/2/4/8 forced argument bytes."""
    if width is None:
        if arg < 24:
            width = 0
        elif arg < 256:
            width = 1
        elif arg < 65536:
            width = 2
        elif arg < (1 << 32):
            width = 4
        else:
            width = 8
    if width == 0:
        assert arg < 24
        return bytes([(major << 5) | arg])
    ai = {1: 24, 2: 25, 4: 26, 8: 27}[width]
    return bytes([(major << 5) | ai]) + arg.to_bytes(width, "big")


def enc_map(pairs: list[tuple[bytes, bytes]]) -> bytes:
    """Canonical map from already-encoded (key, value) pairs; keys sorted
    bytewise on their encodings and deduplicated."""
    uniq: dict[bytes, bytes] = {}
    for k, v in pairs:
        uniq.setdefault(k, v)
    items = sorted(uniq.items())
    return enc_head(5, len(items)) + b"".join(k + v for k, v in items)


INT_EDGES = [0, 1, 10, 23, 24, 25, 255, 256, 257, 65535, 65536, 65537,
             (1 << 32) - 1, 1 << 32, (1 << 63) - 1, 1 << 63, (1 << 64) - 1]


def gen_item(rng: random.Random, depth: int, max_depth: int,
             budget: list[int] | None = None) -> bytes:
    """Random accepted item; containers may appear while depth <= max.

    `budget` caps the total number of nodes (default 40) so that deep
    random trees stay small."""
    if budget is None:
        budget = [40]
    budget[0] -= 1
    choices = ["uint", "nint", "bstr", "tstr", "simple"]
    if depth <= max_depth and budget[0] > 0:
        choices += ["arr", "map", "arr", "map"]
    kind = rng.choice(choices)
    if kind in ("uint", "nint"):
        if rng.random() < 0.5:
            v = rng.choice(INT_EDGES)
        else:
            v = rng.getrandbits(rng.choice([4, 8, 16, 32, 64]))
        return enc_head(0 if kind == "uint" else 1, v)
    if kind in ("bstr", "tstr"):
        ln = rng.choice([0, 1, 2, 5, 23, 24, 30])
        return enc_head(2 if kind == "bstr" else 3, ln) + rng.randbytes(ln)
    if kind == "simple":
        return bytes([rng.choice(ACCEPTED_SIMPLE)])
    count = min(rng.choice([0, 1, 1, 2, 3, 4]), max(budget[0], 0))
    if kind == "arr":
        return enc_head(4, count) + b"".join(
            gen_item(rng, depth + 1, max_depth, budget) for _ in range(count))
    pairs = [(gen_item(rng, depth + 1, max_depth, budget),
              gen_item(rng, depth + 1, max_depth, budget))
             for _ in range(count)]
    return enc_map(pairs)


# ---------------------------------------------------------------------------
# Selftest
# ---------------------------------------------------------------------------


def h(s: str) -> bytes:
    return bytes.fromhex(s.replace(" ", ""))


A16 = "81" * 16
A15 = "81" * 15

# (hex, expected status, expected where, note) -- every expectation derived
# by hand from the brief's rules, not computed by status().
WORKED_EXAMPLES = [
    ("d8", "Truncated", 0, "rule 1: tag head needs 1 more byte"),
    ("f8", "Truncated", 0, "rule 1 before rule 5"),
    ("19 00", "Truncated", 0, "rule 1: needs 2 argument bytes"),
    ("dc", "Reserved_Info", 0, "rule 2 (ai 28 has no width)"),
    ("df", "Indefinite_Length", 0, "rule 3"),
    ("ff", "Indefinite_Length", 0, "rule 3: break"),
    ("d8 01", "Unsupported_Type", 0, "rule 4"),
    ("f8 14", "Unsupported_Simple", 0, "rule 5"),
    ("59 00 01", "Non_Shortest", 0, "rule 6 before rule 7"),
    (A16 + "98 00", "Non_Shortest", 16, "rule 6 before rules 7/8"),
    (A16 + "81", "Truncated", 16,
     "brief asked: rule 7 (count 1 > 0 left) precedes rule 8"),
    (A16 + "80", "Too_Deep", 16, "rule 8: depth 17"),
    ("82 f8 14 1f", "Unsupported_Simple", 1, "first member"),
    ("82 01", "Truncated", 0, "rule 7: count 2 > 1"),
    ("81 42 00", "Truncated", 1, "member rule 7"),
    ("a2 01 00 01 18", "Duplicate_Key", 3, "key judged before value"),
    ("a2 02 01 01 18 05", "Unsorted_Key", 3, "key judged before value"),
    ("a2 01 00 81 c0 00", "Unsupported_Type", 4, "fault inside a key"),
    ("00 c0", "Trailing_Bytes", 1, ""),
    ("01 ff", "Trailing_Bytes", 1, ""),
]

MANDATORY = [
    ("61 ff", "Ok", 2, "text not UTF-8 validated"),
    ("a2 01 00 f5 00", "Ok", 5, "1 and true are different keys"),
    ("a2 18 18 00 20 00", "Ok", 6, "18 18 < 20 bytewise"),
    ("a2 20 00 18 18 00", "Unsorted_Key", 3, ""),
    ("a1 00 00", "Ok", 3, ""),
    ("a1 00 00 00", "Trailing_Bytes", 3, ""),
    ("5b ff ff ff ff ff ff ff ff", "Truncated", 0, "rule 7, len 2^64-1"),
    ("1b ff ff ff ff ff ff ff ff", "Ok", 9, "max unsigned"),
    ("3b ff ff ff ff ff ff ff ff", "Ok", 9, "-2^64"),
    ("18 01", "Non_Shortest", 0, ""),
    ("", "Truncated", 0, "empty buffer"),
]

DERIVED = [
    # integers and shortest form (rule 6, RFC 8949 4.2.1)
    ("00", "Ok", 1, ""),
    ("17", "Ok", 1, "23 inline"),
    ("18 17", "Non_Shortest", 0, "23 in one byte"),
    ("18 18", "Ok", 2, "24 needs one byte"),
    ("19 00 ff", "Non_Shortest", 0, "255 in two bytes"),
    ("19 01 00", "Ok", 3, "256"),
    ("1a 00 00 ff ff", "Non_Shortest", 0, "65535 in four"),
    ("1a 00 01 00 00", "Ok", 5, "65536"),
    ("1b 00 00 00 00 ff ff ff ff", "Non_Shortest", 0, "2^32-1 in eight"),
    ("1b 00 00 00 01 00 00 00 00", "Ok", 9, "2^32"),
    ("1a 00 01 00", "Truncated", 0, "rule 1"),
    ("1b 00", "Truncated", 0, "rule 1"),
    ("38 00", "Non_Shortest", 0, "-1 non-shortest"),
    ("20", "Ok", 1, "-1"),
    # strings
    ("40", "Ok", 1, ""),
    ("41", "Truncated", 0, "rule 7"),
    ("43 01 02", "Truncated", 0, "rule 7: 3 > 2"),
    ("60", "Ok", 1, ""),
    ("62 ff fe", "Ok", 3, "invalid UTF-8 accepted"),
    ("78 17", "Non_Shortest", 0, "rule 6 before rule 7"),
    ("78 18", "Truncated", 0, "rule 7: 24 > 0"),
    ("5a ff ff ff ff", "Truncated", 0, "rule 7"),
    ("5b 00 00 00 01 00 00 00 00", "Truncated", 0, "len 2^32"),
    ("5b 00 00 00 00 ff ff ff ff", "Non_Shortest", 0, "rule 6 first"),
    ("7b ff ff ff ff ff ff ff ff", "Truncated", 0, ""),
    # reserved / indefinite / tags / simple (rules 2-5)
    ("9f", "Indefinite_Length", 0, ""),
    ("bf", "Indefinite_Length", 0, ""),
    ("5f", "Indefinite_Length", 0, ""),
    ("7f", "Indefinite_Length", 0, ""),
    ("1f", "Indefinite_Length", 0, "ai 31 on major 0"),
    ("3f", "Indefinite_Length", 0, ""),
    ("1c", "Reserved_Info", 0, ""),
    ("3d", "Reserved_Info", 0, ""),
    ("5e", "Reserved_Info", 0, ""),
    ("fc", "Reserved_Info", 0, "rule 2 before rule 5"),
    ("fe", "Reserved_Info", 0, ""),
    ("f7", "Unsupported_Simple", 0, "undefined"),
    ("e0", "Unsupported_Simple", 0, "simple 0"),
    ("f3", "Unsupported_Simple", 0, "simple 19"),
    ("f8 00", "Unsupported_Simple", 0, ""),
    ("f8 ff", "Unsupported_Simple", 0, ""),
    ("f9 00", "Truncated", 0, "rule 1 before rule 5"),
    ("f9 00 00", "Unsupported_Simple", 0, "half float"),
    ("fa 00 00 00", "Truncated", 0, ""),
    ("fb 00 00 00 00 00 00 00 00", "Unsupported_Simple", 0, ""),
    ("f4", "Ok", 1, ""),
    ("f5", "Ok", 1, ""),
    ("f6", "Ok", 1, ""),
    ("c0", "Unsupported_Type", 0, ""),
    ("c0 00", "Unsupported_Type", 0, ""),
    ("d9", "Truncated", 0, "rule 1 before rule 4"),
    ("db 00 00 00 00 00 00 00 00", "Unsupported_Type", 0,
     "rule 6 is majors 0-5 only"),
    # arrays, counts, owed members (owed-member decision)
    ("80", "Ok", 1, ""),
    ("a0", "Ok", 1, ""),
    ("82 01 02", "Ok", 3, ""),
    ("83 01 02", "Truncated", 0, "rule 7"),
    ("82 00", "Truncated", 0, "rule 7"),
    ("81 f5", "Ok", 2, ""),
    ("82 81 00", "Truncated", 0, "owed: outer still owed a member"),
    ("82 82 00 00", "Truncated", 0, "owed"),
    ("a1 81 00", "Truncated", 0, "owed: map value owed"),
    ("a2 00 81 81 00", "Truncated", 0, "owed: second key owed"),
    ("81 19 00", "Truncated", 1, "member rule 1"),
    ("81 81 81", "Truncated", 2, "innermost rule 7"),
    ("82 00 82 00", "Truncated", 2, "inner rule 7"),
    ("bb 80 00 00 00 00 00 00 00", "Truncated", 0, "2*count = 2^64"),
    ("bb 80 00 00 00 00 00 00 01 00 00", "Truncated", 0,
     "2*count wraps to 2 in u64"),
    ("9b ff ff ff ff ff ff ff ff", "Truncated", 0, ""),
    ("bb 7f ff ff ff ff ff ff ff", "Truncated", 0, ""),
    # maps and key order
    ("a1 00", "Truncated", 0, "2*1 > 1"),
    ("a2 00 00 01", "Truncated", 0, "4 > 3"),
    ("a1 00 9f", "Indefinite_Length", 2, "fault in value"),
    ("a1 00 41", "Truncated", 2, "value rule 7"),
    ("a2 00 00 00 00", "Duplicate_Key", 3, ""),
    ("a2 01 00 00 00", "Unsorted_Key", 3, ""),
    ("a2 00 1c 00 00", "Reserved_Info", 2, "earlier value before dup key"),
    ("a2 00 00 00 41", "Duplicate_Key", 3, "dup key before truncated value"),
    ("a2 80 00 80 00", "Duplicate_Key", 3, "container keys"),
    ("a2 81 00 00 80 00", "Unsorted_Key", 4, "80 < 81 00"),
    ("a2 80 00 81 00 00", "Ok", 6, ""),
    ("a2 a0 00 80 00", "Unsorted_Key", 3, "80 < a0"),
    ("a2 41 00 00 42 00 00 00", "Ok", 8, "41 00 < 42 00 00"),
    ("a2 61 61 00 41 61 00", "Unsorted_Key", 4, "bstr < tstr"),
    ("a2 f4 00 f5 00", "Ok", 5, ""),
    ("a2 f5 00 f4 00", "Unsorted_Key", 3, ""),
    ("a2 f6 00 f6 00", "Duplicate_Key", 3, ""),
    ("a2 17 00 18 18 00", "Ok", 6, ""),
    ("a2 18 18 00 17 00", "Unsorted_Key", 4, ""),
    ("a2 00 00 20 00", "Ok", 5, ""),
    ("a2 20 00 00 00", "Unsorted_Key", 3, ""),
    ("a1 a0 a0", "Ok", 3, ""),
    ("a2 a0 00 a0 00", "Duplicate_Key", 3, ""),
    # two faults: first in decode order wins
    ("82 18 01 c0", "Non_Shortest", 1, ""),
    ("a1 18 01 c0", "Non_Shortest", 1, "fault in key"),
    ("82 f8 18 f5", "Unsupported_Simple", 1, ""),
    ("c0 00 00", "Unsupported_Type", 0, "rejected, then trailing"),
    ("18 01 00", "Non_Shortest", 0, "rejected, then trailing"),
    ("84 c0 00 00", "Truncated", 0, "outer rule 7 before inner tag"),
    ("98 01 00", "Non_Shortest", 0, "container head non-shortest"),
    ("82 81 18 01 c0", "Non_Shortest", 2, "deeper earlier fault wins"),
    ("a2 c0 00 00 00", "Unsupported_Type", 1, "fault in first key"),
    ("fd", "Reserved_Info", 0, ""),
    ("80 00", "Trailing_Bytes", 1, ""),
    ("a0 a0", "Trailing_Bytes", 1, ""),
    # depth (rule 8)
    (A15 + "80", "Ok", 16, "depth 16"),
    (A15 + "a0", "Ok", 16, ""),
    (A16 + "a0", "Too_Deep", 16, ""),
    (A16 + "00", "Ok", 17, "scalar at any depth"),
    ("a1" + A15 + "80" + "00", "Too_Deep", 16, "too-deep container key"),
    ("a1 00" * 16 + "00", "Ok", 33, "16 nested maps"),
    ("a1 00" * 17 + "00", "Too_Deep", 32, "17th map"),
]


def _check_table(rows, label: str, failures: list[str]) -> int:
    for hx, st, wh, _note in rows:
        got = status(h(hx))
        if got != (st, wh):
            failures.append(f"{label}: {hx!r}: expected {(st, wh)}, got {got}")
    return len(rows)


def selftest() -> int:
    failures: list[str] = []
    checks = 0
    checks += _check_table(WORKED_EXAMPLES, "worked", failures)
    checks += _check_table(MANDATORY, "mandatory", failures)
    checks += _check_table(DERIVED, "derived", failures)

    # Property: the two implementations agree on every buffer of 0..2
    # bytes, and every rejection of a non-empty buffer has where < len.
    for buf in _all_short():
        a = status(buf)
        checks += 1
        if a != status_stack(buf):
            failures.append(f"impls differ on {buf.hex()}: {a} vs "
                            f"{status_stack(buf)}")
        checks += 1
        if not _where_ok(buf, a):
            failures.append(f"where out of range: {buf.hex()} {a}")

    # Properties over random accepted items from the independent encoder.
    rng = random.Random(20261014)
    for i in range(1500):
        item = gen_item(rng, 1, rng.choice([2, 4, 16]))
        checks += 1
        if status(item) != ("Ok", len(item)):
            failures.append(f"encoder item rejected: {item.hex()} "
                            f"{status(item)}")
            continue
        # every proper non-empty prefix is Truncated with where < len
        for cut in range(1, len(item)):
            pre = item[:cut]
            got = status(pre)
            checks += 1
            if got[0] != "Truncated" or not 0 <= got[1] < cut:
                failures.append(f"prefix {pre.hex()} gave {got}")
            checks += 1
            if got != status_stack(pre):
                failures.append(f"impls differ on prefix {pre.hex()}")
        # one extra byte is Trailing_Bytes at len(item)
        extra = item + bytes([rng.randrange(256)])
        checks += 1
        if status(extra) != ("Trailing_Bytes", len(item)):
            failures.append(f"trailing {extra.hex()} gave {status(extra)}")
        # random single-byte mutation: implementations agree, where in range
        if item:
            j = rng.randrange(len(item))
            mut = item[:j] + bytes([rng.randrange(256)]) + item[j + 1 :]
            checks += 2
            a = status(mut)
            if a != status_stack(mut):
                failures.append(f"impls differ on {mut.hex()}")
            if not _where_ok(mut, a):
                failures.append(f"where out of range: {mut.hex()} {a}")

    # Implementations agree on the whole seed-1 corpus.
    for _cat, buf in _corpus_cases(1):
        checks += 1
        if status(buf) != status_stack(buf):
            failures.append(f"impls differ on corpus {buf.hex()}")
        checks += 1
        if not _where_ok(buf, status(buf)):
            failures.append(f"where out of range: corpus {buf.hex()}")

    for line in failures[:50]:
        print("FAIL", line)
    print(f"{checks} checks")
    if failures:
        print(f"{len(failures)} FAILED")
        return 1
    print("ok")
    return 0


def _where_ok(buf: bytes, res: tuple[str, int]) -> bool:
    st, wh = res
    if st == "Ok":
        return wh == len(buf)
    if not buf:
        return (st, wh) == ("Truncated", 0)
    return 0 <= wh < len(buf)


# ---------------------------------------------------------------------------
# Corpus
# ---------------------------------------------------------------------------


def _all_short():
    yield b""
    for a in range(256):
        yield bytes([a])
    for a in range(256):
        for b in range(256):
            yield bytes([a, b])


def _prefixes(buf: bytes):
    for cut in range(len(buf) + 1):
        yield buf[:cut]


BOUNDARY_ARGS = [0, 1, 23, 24, 255, 256, 65535, 65536, (1 << 32) - 1,
                 1 << 32, (1 << 63) - 1, 1 << 63, (1 << 64) - 1]

# Faulty fragments: each is a complete (or truncation-at-end) bad item.
FAULTS = ["18 01", "19 00 17", "c0 00", "d8 01 00", "1c", "5d", "9f", "ff",
          "f7", "f8 20", "f9 00 00", "e0", "38 17", "78 05 61 61 61 61 61",
          "81 1d", "a1 00 fc"]

KEYS = ["00", "01", "17", "18 18", "18 ff", "19 01 00", "1b ff ff ff ff ff ff"
        " ff ff", "20", "37", "38 18", "3b ff ff ff ff ff ff ff ff", "40",
        "41 00", "41 01", "42 00 00", "42 00 01", "60", "61 61", "61 62",
        "62 61 61", "80", "81 00", "81 01", "82 00 00", "a0", "a1 00 00",
        "a1 00 01", "a1 01 00", "f4", "f5", "f6"]


def _corpus_cases(seed: int):
    """Yield (category, buffer) in a deterministic order."""
    rng = random.Random(seed)

    # 1. every buffer of 0..2 bytes
    for buf in _all_short():
        yield "short", buf

    # 2. nesting depth 14..18, several shapes, all prefixes, + trailing,
    #    + an innermost fault
    for d in range(14, 19):
        shapes = [
            h("81" * (d - 1) + "80"),
            h("81" * (d - 1) + "a0"),
            h("81" * d + "00"),
            h("a1 00" * d + "00"),
            h("a1 00" * (d - 1) + "a0"),
            h("a1" * d + "a0" + "00" * d),  # map keys nested d deep
            h("81 a1 00" * (d // 2) + ("81" if d % 2 else "") + "00"),
            h("82 00" * d + "00"),
        ]
        # the key-nesting shape above is a1 (a1 (... a0 00) ...) 00: the
        # innermost key a0 at depth d+1; keep it as is (it is what we test).
        for s in shapes:
            for p in _prefixes(s):
                yield "depth", p
            yield "depth", s + b"\x00"
            for fb in ("c0 00", "18 01", "9f"):
                yield "depth", h("81" * (d - 1)) + h(fb)
                yield "depth", h("a1 00" * (d - 1)) + h(fb)

    # 3. every head form at argument boundaries, every major, every width
    #    that can hold the value, truncated at every position
    for major in range(8):
        for v in BOUNDARY_ARGS:
            for w in (0, 1, 2, 4, 8):
                if w == 0 and v >= 24:
                    continue
                if w and v >= (1 << (8 * w)):
                    continue
                head = enc_head(major, v, w)
                if major in (0, 1, 6, 7):
                    body = h("00") if major in (6,) else b""
                    full = head + body
                elif v <= 300:
                    if major in (2, 3):
                        full = head + rng.randbytes(v)
                    elif major == 4:
                        full = head + b"\x00" * v
                    else:  # sorted int keys are bytewise ascending
                        full = head + b"".join(enc_head(0, k) + b"\x00"
                                               for k in range(v))
                else:
                    full = head + b"\x00" * rng.choice([0, 1, 3])
                for p in _prefixes(full):
                    yield "heads", p
                yield "heads", full + b"\x00"

    # 4. counts against bytes left: exactly, one below, one above; near 2^64
    for major in (2, 3, 4, 5):
        for left in range(0, 6):
            for c in range(0, 8):
                tail = b"\x00" * left
                yield "counts", enc_head(major, c) + tail
        for c in [(1 << 64) - 1, (1 << 64) - 2, 1 << 63, (1 << 63) + 1,
                  (1 << 63) - 1, (1 << 62), 1 << 32, (1 << 32) - 1,
                  (1 << 32) + 1]:
            for left in (0, 1, 2, 3):
                yield "counts", enc_head(major, c, 8 if c >= 1 << 32
                                         else None) + b"\x00" * left
    for c in (24, 255, 256):
        for delta in (-1, 0, 1):
            yield "counts", enc_head(4, c) + b"\x00" * (c + delta)
            yield "counts", enc_head(5, c) + b"".join(
                enc_head(0, k) + b"\x00" for k in range(c))[: 2 * c + delta]

    # 5. key orders: every ordered pair of keys, triples, container keys,
    #    keys sharing prefixes
    keys = [h(k) for k in KEYS]
    for k1 in keys:
        for k2 in keys:
            yield "keys", b"\xa2" + k1 + b"\x00" + k2 + b"\x00"
            yield "keys", b"\xa2" + k1 + b"\x00" + k2  # value owed
    for _ in range(600):
        n_pairs = rng.randrange(2, 5)
        ks = [rng.choice(keys) for _ in range(n_pairs)]
        if rng.random() < 0.4:
            ks = sorted(set(ks))
            n_pairs = len(ks)
        yield "keys", enc_head(5, n_pairs) + b"".join(k + b"\xf6" for k in ks)

    # 6. faults inside keys and values, at several positions
    for f in FAULTS:
        fb = h(f)
        yield "faults", b"\xa1" + fb + b"\x00"
        yield "faults", b"\xa1\x00" + fb
        yield "faults", b"\xa2\x00\x00" + fb + b"\x00"
        yield "faults", b"\xa2\x00" + fb + b"\x01\x00"
        yield "faults", b"\xa1\x81" + fb + b"\x00"
        yield "faults", b"\xa1\x00\x81" + fb
        yield "faults", b"\x83\x00" + fb + b"\x00"
        yield "faults", b"\x81\x81" + fb
        yield "faults", fb

    # 7. two faults in one item: every ordered pair of fault fragments,
    #    plus key-order faults against value faults
    for f1 in FAULTS:
        for f2 in FAULTS:
            yield "two", b"\x82" + h(f1) + h(f2)
            yield "two", b"\xa1" + h(f1) + h(f2)
        yield "two", b"\xa2\x01" + h(f1) + b"\x00\x00"  # value then key
        yield "two", b"\xa2\x01\x00\x00" + h(f1)  # key then value
        yield "two", b"\xa2\x01\x00\x01" + h(f1)
        yield "two", h("81" * 16 + "80") + h(f1)
        yield "two", h("82" + "81" * 15 + "80") + h(f1)

    # 8. trailing bytes after accepted and rejected items
    for base in ("00", "f4", "80", "a0", "a1 00 00", "61 ff", "1b ff ff ff "
                 "ff ff ff ff ff", "c0 00", "18 01", "ff", "82 00",
                 "a2 01 00 00 00"):
        for t in ("00", "ff", "00 00", "c0", "18"):
            yield "trailing", h(base) + h(t)

    # 9. owed members (owed-member decision)
    for d in range(1, 6):
        yield "owed", h("82" * d + "00" * (d + 1))[:-1]  # drop last byte
        yield "owed", h("82" + "81" * d + "00")
        yield "owed", h("a1" + "81" * d + "00")
        yield "owed", h("a2 00" + "81" * d + "00")

    # 10. random accepted items from the independent encoder, and mutations
    for _ in range(4000):
        item = gen_item(rng, 1, rng.choice([1, 2, 3, 15, 16, 17]))
        yield "random", item
        op = rng.randrange(6)
        if op == 0 and len(item) > 1:
            yield "random", item[: rng.randrange(1, len(item))]
        elif op == 1:
            j = rng.randrange(len(item))
            yield "random", item[:j] + bytes([rng.randrange(256)]) + \
                item[j + 1 :]
        elif op == 2:
            j = rng.randrange(len(item) + 1)
            yield "random", item[:j] + bytes([rng.randrange(256)]) + item[j:]
        elif op == 3 and len(item) > 1:
            j = rng.randrange(len(item))
            yield "random", item[:j] + item[j + 1 :]
        elif op == 4:
            yield "random", item + bytes([rng.randrange(256)])
        else:
            yield "random", b"\x81" * rng.randrange(14, 18) + item


def write_corpus(seed: int, out: str) -> None:
    seen: dict[bytes, str] = {}  # insertion-ordered, deterministic
    for cat, buf in _corpus_cases(seed):
        if buf not in seen:
            seen[buf] = cat
    cats: dict[str, int] = {}
    stats: dict[str, int] = {}
    with open(out, "w", newline="\n") as fh:
        for buf, cat in seen.items():
            st, wh = status(buf)
            fh.write(f"{buf.hex()}\t{st}\t{wh}\n")
            cats[cat] = cats.get(cat, 0) + 1
            stats[st] = stats.get(st, 0) + 1
    print(f"seed {seed}", file=sys.stderr)
    print(f"total {len(seen)}", file=sys.stderr)
    for c in cats:
        print(f"category {c} {cats[c]}", file=sys.stderr)
    for s in STATUSES:
        print(f"status {s} {stats.get(s, 0)}", file=sys.stderr)


def classify(inp: str, out: str) -> int:
    with open(inp, "r", newline="") as fi, open(out, "w", newline="\n") as fo:
        for lineno, line in enumerate(fi, 1):
            field = line.rstrip("\r\n").split("\t", 1)[0].strip().lower()
            if len(field) % 2 or any(c not in "0123456789abcdef"
                                     for c in field):
                print(f"line {lineno}: the first field is not hex bytes",
                      file=sys.stderr)
                return 2
            st, wh = status(bytes.fromhex(field))
            fo.write(f"{field}\t{st}\t{wh}\n")
    return 0


def main(argv: list[str]) -> int:
    ap = _Parser(description=__doc__.splitlines()[0])
    sub = ap.add_subparsers(dest="cmd", required=True)
    c = sub.add_parser("classify")
    c.add_argument("--in", dest="inp", required=True)
    c.add_argument("--out", required=True)
    sub.add_parser("selftest")
    g = sub.add_parser("corpus")
    g.add_argument("--seed", type=int, required=True)
    g.add_argument("--out", required=True)
    a = ap.parse_args(argv)
    if a.cmd == "classify":
        return classify(a.inp, a.out)
    if a.cmd == "selftest":
        return selftest()
    write_corpus(a.seed, a.out)
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
