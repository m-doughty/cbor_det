#!/usr/bin/env python3
"""Boundary inputs for the decoder: the shapes its arithmetic is tested on.

Writes one input per line, in hexadecimal, and nothing else: what each
input should give is the status oracle's (ref_status.py classify) and the
reference decoder's (ref_cbor_det.py) to say, never this file's. The
inputs:

  * wide arrays and maps: 65 536 members or pairs, and an array of
    1 000 000 members (each accepted, and each with its last byte cut);
  * nested container keys: maps whose keys are arrays and maps nested
    16 deep in all (and one deeper);
  * maximum and near-maximum lengths and counts: heads of byte strings,
    text strings, arrays and maps with arguments 2**64 - 1, 2**63,
    2**32, 2**31, 2**31 - 1, in every width that holds them;
  * map counts around the division threshold: for bytes-left R from 0 to
    40, a map head with count R // 2 - 1, R // 2 and R // 2 + 1, followed
    by R bytes of members (so a count of exactly half the bytes left, and
    one more than fits);
  * empty containers at the end of the buffer.

Usage: boundary.py --out FILE [--no-huge]
  --no-huge leaves out the 1 000 000-member array.
Standard library only; Python 3.10 or later.
"""

from __future__ import annotations

import argparse


class _Parser(argparse.ArgumentParser):
    """A parser whose errors never print the arguments given."""

    def error(self, message: str) -> None:
        self.exit(2, "boundary.py: the arguments are not valid "
                     "(see --help)\n")


def head(major: int, arg: int, width: int | None = None) -> bytes:
    """A head of the major type and argument, shortest unless width (in
    argument bytes: 0, 1, 2, 4 or 8) is given."""
    if width is None:
        width = (0 if arg < 24 else 1 if arg < 2**8 else 2 if arg < 2**16
                 else 4 if arg < 2**32 else 8)
    if width == 0:
        return bytes([major << 5 | arg])
    info = {1: 24, 2: 25, 4: 26, 8: 27}[width]
    return bytes([major << 5 | info]) + arg.to_bytes(width, "big")


def uint(v: int) -> bytes:
    return head(0, v)


def inputs(huge: bool):
    # Wide arrays and maps.
    for n in (65_536,) + ((1_000_000,) if huge else ()):
        arr = head(4, n) + b"\x00" * n
        yield arr
        yield arr[:-1]
    keys = b"".join(uint(k) + b"\xf6" for k in range(65_536))
    wide_map = head(5, 65_536) + keys
    yield wide_map
    yield wide_map[:-1]

    # Nested container keys: a map of three keys, each an array (or a map)
    # nested so that the whole item is 16 deep (and one deeper).
    for depth in (16, 17):
        inner = depth - 1                      # containers in each key
        arr_keys = [b"\x81" * (inner - 1) + head(4, 1) + uint(k)
                    for k in range(3)]
        yield head(5, 3) + b"".join(k + b"\x00" for k in arr_keys)
        map_keys = [b"\xa1" * (inner - 1) + b"\xa1" + uint(k) + b"\x00"
                    + b"\x00" * (inner - 1) for k in range(3)]
        yield head(5, 3) + b"".join(k + b"\x00" for k in map_keys)
    # Keys that are arrays, out of order and equal.
    yield head(5, 2) + b"\x81\x01\x00" + b"\x81\x00\x00"
    yield head(5, 2) + b"\x81\x00\x00" + b"\x81\x00\x00"

    # Maximum and near-maximum lengths and counts.
    for major in (2, 3, 4, 5):
        for arg in (2**64 - 1, 2**63, 2**32, 2**31, 2**31 - 1, 2**30,
                    2**30 - 1):
            for width in (4, 8):
                if arg < 2**(8 * width):
                    yield head(major, arg, width)
                    yield head(major, arg, width) + b"\x00" * 8

    # Map counts around the division threshold.
    for r in range(0, 41):
        for count in (r // 2 - 1, r // 2, r // 2 + 1):
            if count < 0:
                continue
            members = b"".join(uint(k) + b"\x00" for k in range(r // 2))
            members += b"\x00" * (r - len(members))
            yield head(5, count) + members
    # A map whose count is exactly half the bytes left.
    yield head(5, 20) + b"".join(uint(k) + b"\xf5" for k in range(20))

    # Empty containers and strings at the end of the buffer.
    for tail in (b"\x80", b"\xa0", b"\x40", b"\x60"):
        yield b"\x82\x00" + tail
        yield b"\x81" * 15 + tail


def main() -> None:
    p = _Parser(description=__doc__,
                formatter_class=argparse.RawDescriptionHelpFormatter)
    p.add_argument("--out", required=True)
    p.add_argument("--no-huge", action="store_true")
    a = p.parse_args()
    seen = set()
    count = 0
    with open(a.out, "w", encoding="ascii", newline="\n") as out:
        for buf in inputs(not a.no_huge):
            if buf in seen:
                continue
            seen.add(buf)
            out.write(buf.hex() + "\n")
            count += 1
    print(f"boundary: inputs={count}")


if __name__ == "__main__":
    main()
