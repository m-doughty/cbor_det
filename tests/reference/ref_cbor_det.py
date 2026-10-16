#!/usr/bin/env python3
"""Independent cbor_det reference decoder; Python 3.10+, standard library only.

RFC 8949 sections 3.1 and 4.2.1 define the heads and deterministic ordering.
This profile deliberately treats text as uninterpreted bytes, prohibits tags and
all simple/float values except false/true/null, and bounds container depth.
No Python decoded-key equality is used: map keys are compared as encoded bytes.
"""

from __future__ import annotations

import argparse
from dataclasses import dataclass
import random
import sys
from typing import Iterator


class _Parser(argparse.ArgumentParser):
    """A parser whose errors never print the arguments given."""

    def error(self, message: str) -> None:
        self.exit(2, "ref_cbor_det.py: the arguments are not valid "
                     "(see --help)\n")


MAX_ARGUMENT = (1 << 64) - 1
ARGUMENT_BOUNDARIES = (0, 1, 23, 24, 255, 256, 65535, 65536,
                       (1 << 32) - 1, 1 << 32, MAX_ARGUMENT)


def head(buf: bytes, start: int):
    """Return a canonical major-0..5 head, independently of its payload."""
    if not isinstance(start, int) or start < 0 or start >= len(buf):
        return None
    initial = buf[start]
    major, additional = initial >> 5, initial & 31
    # RFC 8949 3.1: 28..30 reserved; 31 indefinite; this profile excludes both.
    if major > 5 or additional > 27:
        return None
    if additional < 24:
        return major, additional, 1
    width = (1, 2, 4, 8)[additional - 24]
    # Subtract before comparing so the corresponding bounded-integer design
    # does not overflow by calculating start + width + 1.
    if width > len(buf) - start - 1:
        return None
    argument = int.from_bytes(buf[start + 1:start + 1 + width], "big")
    # RFC 8949 4.2.1 first rule: shortest argument representation.
    minimum = (24, 256, 65536, 1 << 32)[additional - 24]
    if argument < minimum:
        return None
    return major, argument, width + 1


@dataclass
class _Frame:
    """A pending container; maps count pairs, arrays count elements."""
    major: int
    remaining: int
    child_depth: int
    key_start: int = 0
    previous_key: bytes | None = None
    expecting_key: bool = True


def item_end(buf: bytes, start: int, depth_left: int = 16) -> int:
    """Return the first accepted item's end; suffix bytes are unconstrained.

    An explicit stack avoids relying on Python's recursion limit, including
    when callers supply a container budget greater than the profile default.
    """
    if (not isinstance(start, int) or not isinstance(depth_left, int)
            or start < 0 or start >= len(buf) or depth_left < 0):
        return -1
    position = start
    budget = depth_left
    stack: list[_Frame] = []
    while True:
        if position >= len(buf):
            return -1
        initial = buf[position]
        major = initial >> 5
        if major == 7:
            # RFC 8949 3.3: only these direct simple-value encodings allowed.
            if initial not in (0xF4, 0xF5, 0xF6):
                return -1
            position += 1
        else:
            decoded_head = head(buf, position)
            if decoded_head is None:  # Includes every major-6 tag.
                return -1
            major, argument, head_length = decoded_head
            position += head_length
            available = len(buf) - position
            if major in (2, 3):
                # RFC 8949 3.1 lengths; compare before advancing. Text bytes
                # intentionally bypass RFC 8949's usual UTF-8 validity check.
                if argument > available:
                    return -1
                position += argument
            elif major in (4, 5):
                if budget < 1:
                    return -1
                # Every item takes >=1 byte. Maps need >=2 bytes per pair.
                # Division avoids overflow from either 2*argument or sums.
                capacity = available if major == 4 else available // 2
                if argument > capacity:
                    return -1
                if argument:
                    stack.append(_Frame(major, argument, budget - 1,
                                        key_start=position))
                    budget -= 1
                    continue
            # Major 0/1 consume just the head, including all uint64 arguments.

        # One complete child is now available. Propagate completed containers
        # upward, or schedule the next child with its parent's original budget.
        while stack:
            parent = stack[-1]
            if parent.major == 5 and parent.expecting_key:
                key = buf[parent.key_start:position]
                # RFC 8949 4.2.1: unsigned-byte lexicographic order, strictly
                # ascending. This is NOT RFC 7049's length-first ordering.
                if parent.previous_key is not None and key <= parent.previous_key:
                    return -1
                parent.previous_key = key
                parent.expecting_key = False
                budget = parent.child_depth
                break
            parent.remaining -= 1
            if parent.remaining:
                if parent.major == 5:
                    parent.expecting_key = True
                    parent.key_start = position
                budget = parent.child_depth
                break
            stack.pop()
        else:
            return position


def whole(buf: bytes) -> bool:
    """Exactly one nonempty accepted item with the profile's depth limit."""
    return bool(buf) and item_end(buf, 0, 16) == len(buf)


# Encoding helpers are solely for generating inputs, never for decoding them.
def _argument_head(major: int, argument: int) -> bytes:
    if not 0 <= major <= 5 or not 0 <= argument <= MAX_ARGUMENT:
        raise ValueError("invalid generator head")
    if argument < 24:
        return bytes([(major << 5) | argument])
    for width, additional in ((1, 24), (2, 25), (4, 26), (8, 27)):
        if argument < 1 << (8 * width):
            return bytes([(major << 5) | additional]) + argument.to_bytes(width, "big")
    raise AssertionError("uint64 width exhausted")


def _string(major: int, data: bytes) -> bytes:
    return _argument_head(major, len(data)) + data


def _array(items: list[bytes]) -> bytes:
    return _argument_head(4, len(items)) + b"".join(items)


def _map(pairs: list[tuple[bytes, bytes]], *, sort: bool = True) -> bytes:
    if sort:
        pairs = sorted(pairs, key=lambda pair: pair[0])
    return _argument_head(5, len(pairs)) + b"".join(k + v for k, v in pairs)


def _nest_array(depth: int) -> bytes:
    return b"\x81" * depth + b"\x00"


def _nest_map(depth: int) -> bytes:
    return b"\xa1\x00" * depth + b"\x00"


# RFC 8949 Appendix A in-profile examples, transcribed from RFC knowledge.
# The expected bytes and acceptance below are literals, not encoder products.
RFC_EXAMPLES: tuple[tuple[str, str, bool], ...] = (
    ("0", "00", True),
    ("1", "01", True),
    ("10", "0a", True),
    ("23", "17", True),
    ("24", "1818", True),
    ("25", "1819", True),
    ("100", "1864", True),
    ("1000", "1903e8", True),
    ("1000000", "1a000f4240", True),
    ("1000000000000", "1b000000e8d4a51000", True),
    ("18446744073709551615", "1bffffffffffffffff", True),
    ("-18446744073709551616", "3bffffffffffffffff", True),
    ("-1", "20", True),
    ("-10", "29", True),
    ("-100", "3863", True),
    ("-1000", "3903e7", True),
    ("false", "f4", True),
    ("true", "f5", True),
    ("null", "f6", True),
    ("h''", "40", True),
    ("h'01020304'", "4401020304", True),
    ('""', "60", True),
    ('"a"', "6161", True),
    ('"IETF"', "6449455446", True),
    ("quote and backslash", "62225c", True),
    ('"\u00fc"', "62c3bc", True),
    ('"\u6c34"', "63e6b0b4", True),
    ('"\U00010151"', "64f0908591", True),
    ("[]", "80", True),
    ("[1,2,3]", "83010203", True),
    ("[1,[2,3],[4,5]]", "8301820203820405", True),
    ("[1..25]", "98190102030405060708090a0b0c0d0e0f101112131415161718181819", True),
    ("{}", "a0", True),
    ("{1:2,3:4}", "a201020304", True),
    ('{"a":1,"b":[2,3]}', "a26161016162820203", True),
    ('["a",{"b":"c"}]', "826161a161626163", True),
    ('{"a":"A","b":"B","c":"C","d":"D","e":"E"}',
     "a56161614161626142616361436164614461656145", True),
)


# Each mandatory ordinary-depth witness has a literal expected end and whole.
WITNESSES: tuple[tuple[str, int, bool], ...] = (
    ("61ff", 2, True),
    ("a20100f500", 5, True),
    ("a21818002000", 6, True),
    ("a22000181800", -1, False),
    ("a28000a000", 5, True),  # Empty array key, empty map key.
    ("a2a0008000", -1, False),
    ("a241000042000000", 8, True),
    ("a242000000410000", -1, False),
    ("a261610062616100", 8, True),
    ("a262616100616100", -1, False),
    ("a2810000810100", 7, True),  # Common complete-encoding initial byte.
    ("a2810100810000", -1, False),
    ("a2a1000000a1000100", 9, True),  # Keys share a two-byte prefix.
    ("a2a1000100a1000000", -1, False),
    ("a10000", 3, True),
    ("a1000000", 3, False),
    ("81" * 16 + "00", 17, True),
    ("81" * 17 + "00", -1, False),
    ("a100" * 16 + "00", 33, True),
    ("a100" * 17 + "00", -1, False),
    ("f814", -1, False),
    ("1801", -1, False),
    ("1bffffffffffffffff", 9, True),
    ("3bffffffffffffffff", 9, True),
    ("5bffffffffffffffff", -1, False),
)


def _random_scalar(rng: random.Random) -> bytes:
    choice = rng.randrange(7)
    if choice < 2:
        argument = (rng.choice(ARGUMENT_BOUNDARIES) if rng.randrange(2)
                    else rng.getrandbits(64))
        return _argument_head(choice, argument)
    if choice < 4:
        length = rng.choice((0, 1, 2, 3, 8, 23, 24))
        return _string(choice, bytes(rng.randrange(256) for _ in range(length)))
    return bytes([(0xF4, 0xF5, 0xF6)[choice - 4]])


def _random_item(rng: random.Random, depth_left: int) -> bytes:
    if depth_left == 0 or rng.randrange(10) < 6:
        return _random_scalar(rng)
    count = rng.randrange(4)
    if rng.randrange(2):
        return _array([_random_item(rng, depth_left - 1) for _ in range(count)])
    # Uniqueness is equality of encodings, never Python CBOR-value equality.
    pairs: dict[bytes, bytes] = {}
    for _ in range(count):
        key = _random_item(rng, depth_left - 1)
        pairs[key] = _random_item(rng, depth_left - 1)
    return _map(list(pairs.items()))


def _depth_chains(seed: int) -> list[bytes]:
    """Random mixed containers with a forced path of exactly 16 levels."""
    rng = random.Random(seed ^ 0xCB0D16)
    chains = []
    for _ in range(24):
        encoded = _random_scalar(rng)
        for _ in range(16):
            choice = rng.randrange(3)
            if choice == 0:
                members = [_random_scalar(rng) for _ in range(rng.randrange(3))]
                members.insert(rng.randrange(len(members) + 1), encoded)
                encoded = _array(members)
            elif choice == 1:
                encoded = _map([(_random_scalar(rng), encoded)])
            else:
                encoded = _map([(encoded, _random_scalar(rng))])
        chains.append(encoded)
    return chains


def _accepted_items(seed: int) -> list[bytes]:
    rng = random.Random(seed)
    items = [bytes.fromhex(encoded) for _, encoded, expected in RFC_EXAMPLES if expected]
    items += [bytes.fromhex(encoded) for encoded, _, expected in WITNESSES if expected]
    for major in (0, 1):
        items.extend(_argument_head(major, argument) for argument in ARGUMENT_BOUNDARIES)
    for size in (0, 1, 2, 23, 24, 25, 255, 256):
        payload = bytes(i % 256 for i in range(size))
        items.extend((_string(2, payload), _string(3, payload)))
    for size in (0, 1, 2, 23, 24, 25):
        items.append(_array([b"\x00"] * size))
        items.append(_map([(_argument_head(0, i), b"\xf6") for i in range(size)]))
    items.extend(_string(3, x) for x in (b"\xff", b"\xc0\x80", b"\xed\xa0\x80", b"\xf4\x90\x80\x80"))
    keys = [b"\x00", b"\x01", b"\x18\x18", b"\x20", b"\x41\x00",
            b"\x42\x00\x00", b"\x61\x61", b"\x62\x61\x61", b"\x80",
            b"\x81\x00", b"\xa0", b"\xa1\x00\x00", b"\xf4", b"\xf5", b"\xf6"]
    items.append(_map([(key, _random_scalar(rng)) for key in keys]))
    items.append(_map([(b"\x41a", b"\x00"), (b"\x61a", b"\x00")]))
    # Nonempty arrays, map values, and map keys each exercise depth 16.
    for depth in range(1, 17):
        items.extend((_nest_array(depth), _nest_map(depth),
                      b"\xa1" * depth + b"\x00" * (depth + 1)))
    items.extend(_depth_chains(seed))
    for _ in range(1200):
        items.append(_random_item(rng, rng.randint(1, 16)))
    return items


def _widen(encoded: bytes) -> bytes | None:
    parsed = head(encoded, 0)
    if parsed is None:
        return None
    major, argument, length = parsed
    next_width = {1: 1, 2: 2, 3: 4, 5: 8}.get(length)
    if next_width is None:
        return None
    additional = {1: 24, 2: 25, 4: 26, 8: 27}[next_width]
    return bytes([(major << 5) | additional]) + argument.to_bytes(next_width, "big") + encoded[length:]


def _short_buffers() -> Iterator[bytes]:
    yield b""
    for value in range(256):
        yield bytes([value])
    for value in range(65536):
        yield value.to_bytes(2, "big")


def corpus_cases(seed: int) -> Iterator[bytes]:
    """Stable order; intentional duplicates preserve each mutation as a case."""
    yield from _short_buffers()
    accepted = _accepted_items(seed)
    for encoded in accepted:
        yield encoded
        if len(encoded) <= 96:
            for cut in range(len(encoded)):
                yield encoded[:cut]
        # Each suffix is outside the item and is deliberately not interpreted.
        for suffix in (b"\x00", b"\xff", b"\x18\xff\xf8\x14"):
            yield encoded + suffix
        widened = _widen(encoded)
        if widened is not None:
            yield widened
        yield b"\xc0" + encoded  # RFC 8949 3.4 tag, excluded by profile.
    yield from (bytes.fromhex(encoded) for encoded, _, _ in WITNESSES)
    for chain in _depth_chains(seed):
        yield b"\x81" + chain  # One deeper than each forced random depth-16 path.
    yield _nest_array(17)
    yield _nest_map(17)
    yield b"\xa1" * 17 + b"\x00" * 18  # Overdeep map-key nesting.
    # Swapped and duplicate keys of every accepted key kind, including
    # composite encodings; later values never excuse ordering violations.
    keys = [b"\x00", b"\x18\x18", b"\x20", b"\x41\x00", b"\x42\x00\x00",
            b"\x61a", b"\x62aa", b"\x80", b"\x81\x00", b"\xa0",
            b"\xa1\x00\x00", b"\xf4", b"\xf5", b"\xf6"]
    for key in keys:
        yield _map([(key, b"\x00"), (key, b"\xf6")], sort=False)
    for left, right in zip(keys, keys[1:]):
        yield _map([(left, b"\x00"), (right, b"\x00")])
        yield _map([(right, b"\x00"), (left, b"\x00")], sort=False)
    for value in range(256):
        yield bytes([0xF8, value])
    for encoded in ("f90000", "f93c00", "f97c00", "f97e00", "fa3f800000",
                    "fb3ff0000000000000", "9f00ff", "bf0000ff", "5f4100ff", "7f6161ff"):
        yield bytes.fromhex(encoded)
    for major in range(8):
        for additional in (28, 29, 30, 31):
            yield bytes([(major << 5) | additional]) + b"\x00\xff"
    for major in (2, 3, 4, 5):
        for count in (1, 2, 3, 23, 24, 255, 256, 65535, 65536,
                      (1 << 32) - 1, 1 << 32, MAX_ARGUMENT):
            # Canonical head but an unsatisfiable length/count; maps must use
            # count <= remaining//2, avoiding the overflow in count*2.
            yield _argument_head(major, count)
            yield _argument_head(major, count) + b"\x00" * min(count - 1, 3)
    yield b"\xa2\x00\x00\x01"  # 2 pairs cannot fit in 3 bytes.
    yield b"\x82\x00"            # 2 elements cannot fit in 1 byte.


def head_cases() -> Iterator[bytes]:
    yield from _short_buffers()
    for major in range(8):
        for additional, width in ((24, 1), (25, 2), (26, 4), (27, 8)):
            candidates = set(ARGUMENT_BOUNDARIES)
            candidates.update((0, (1 << (8 * width)) - 1))
            for argument in sorted(candidates):
                if argument >= 1 << (8 * width):
                    continue
                encoded = bytes([(major << 5) | additional]) + argument.to_bytes(width, "big")
                yield encoded
                yield encoded + b"\x00\xff"
                for cut in range(1, len(encoded)):
                    yield encoded[:cut]
    for major in range(8):
        for additional in range(32):
            yield bytes([(major << 5) | additional]) + b"\xff" * 9


def selftest() -> int:
    checks = 0

    def check(actual, expected, label: str) -> None:
        nonlocal checks
        checks += 1
        if actual != expected:
            raise AssertionError(f"{label}: expected {expected!r}, got {actual!r}")

    for encoded, end, expected in WITNESSES:
        data = bytes.fromhex(encoded)
        check(item_end(data, 0), end, f"witness end {encoded}")
        check(whole(data), expected, f"witness whole {encoded}")
    for label, encoded, expected in RFC_EXAMPLES:
        data = bytes.fromhex(encoded)
        check(whole(data), expected, f"RFC Appendix A {label}")
        check(item_end(data, 0), len(data), f"RFC Appendix A end {label}")
    check(item_end(b"\x80", 0, 0), -1, "empty array consumes depth")
    check(item_end(b"\xa0", 0, 0), -1, "empty map consumes depth")
    for encoded in (b"\x00", b"\x20", b"\x40", b"\x60", b"\xf4", b"\xf5", b"\xf6"):
        check(item_end(encoded, 0, 0), 1, "scalar at zero depth")
        check(item_end(encoded, 0, -1), -1, "negative budget")
    for start in (-2, -1, 1, 2, MAX_ARGUMENT):
        check(item_end(b"\x00", start), -1, "invalid item start")
        check(head(b"\x00", start), None, "invalid head start")
    check(item_end(b"", 0), -1, "empty item")
    check(whole(b""), False, "empty whole")
    check(head(b"", 0), None, "empty head")
    check(item_end(b"\xff\xa1\x00\x00\xff", 1), 4, "nonzero start")
    check(head(b"\xff\x18\x18", 1), (0, 24, 2), "nonzero head start")
    for major in range(6):
        for argument in ARGUMENT_BOUNDARIES:
            encoded = _argument_head(major, argument)
            check(head(encoded, 0), (major, argument, len(encoded)), "head boundary")
            for cut in range(len(encoded)):
                check(head(encoded[:cut], 0), None, "head truncation")
            widened = _widen(encoded)
            if widened is not None:
                check(head(widened, 0), None, "widened head")
    for initial in range(256):
        major, additional = initial >> 5, initial & 31
        expected = (major, additional, 1) if major <= 5 and additional < 24 else None
        check(head(bytes([initial]), 0), expected, "every single-byte head")
    for value in range(256):
        check(item_end(bytes([0xF8, value]), 0), -1, "all two-byte simple values")
    for depth in range(17):
        for builder in (_nest_array, _nest_map):
            data = builder(depth)
            check(item_end(data, 0, depth), len(data), "exact budget")
            if depth:
                check(item_end(data, 0, depth - 1), -1, "budget exhausted")
    # Empty final containers count as depth, and sibling containers reuse the
    # same parent budget rather than consuming a shared global depth counter.
    check(whole(b"\x81" * 15 + b"\x80"), True, "empty array at depth16")
    check(whole(b"\x81" * 16 + b"\x80"), False, "empty array at depth17")
    check(whole(b"\xa1\x00" * 15 + b"\xa0"), True, "empty map at depth16")
    check(whole(b"\xa1\x00" * 16 + b"\xa0"), False, "empty map at depth17")
    check(item_end(b"\x82\x80\x80", 0, 2), 3, "sibling budgets")
    check(item_end(_nest_array(1100), 0, 1100), 1101, "explicit stack")
    for chain in _depth_chains(1):
        check(item_end(chain, 0, 16), len(chain), "random exact depth16")
        check(item_end(chain, 0, 15), -1, "random path needs all 16 levels")
        check(whole(b"\x81" + chain), False, "random one-deeper mutation")
    for encoded in ("f90000", "f93c00", "f97c00", "f97e00", "fa3f800000",
                    "fb3ff0000000000000", "9f00ff", "bf0000ff", "5f4100ff", "7f6161ff"):
        check(item_end(bytes.fromhex(encoded), 0), -1, "float or indefinite")
    for major in range(8):
        for additional in (28, 29, 30, 31):
            check(item_end(bytes([(major << 5) | additional]) + b"\x00\xff", 0),
                  -1, "reserved or indefinite additional information")
    for major in (2, 3, 4, 5):
        for count in (1, 2, 3, 23, 24, 255, 256, 65535, 65536,
                      (1 << 32) - 1, 1 << 32, MAX_ARGUMENT):
            encoded = _argument_head(major, count)
            check(item_end(encoded, 0), -1, "unsatisfied count")
            check(item_end(encoded + b"\x00" * min(count - 1, 3), 0),
                  -1, "count exceeds remaining bytes")
    check(item_end(bytes.fromhex("a2000001"), 0), -1, "odd-byte pair capacity")
    check(item_end(bytes.fromhex("8200"), 0), -1, "array element capacity")
    test_keys = [bytes.fromhex(x) for x in
                 ("00", "1818", "20", "4100", "420000", "6161", "626161",
                  "80", "8100", "8101", "a0", "a10000", "a10001", "f4", "f5", "f6")]
    for key in test_keys:
        check(whole(_map([(key, b"\x00"), (key, b"\xf6")], sort=False)),
              False, "duplicate encoded key")
    for left, right in zip(test_keys, test_keys[1:]):
        check(whole(_map([(left, b"\x00"), (right, b"\x00")], sort=False)),
              True, "ascending encoded keys")
        check(whole(_map([(right, b"\x00"), (left, b"\x00")], sort=False)),
              False, "swapped encoded keys")
    for data in _accepted_items(1):
        check(whole(data), True, "generated accepted item")
        check(item_end(b"\xff" + data + b"\xff", 1), len(data) + 1, "offset and suffix")
        for cut in range(len(data)) if len(data) <= 96 else ():
            check(whole(data[:cut]), False, "proper accepted-item truncation")
        widened = _widen(data)
        if widened is not None:
            check(whole(widened), False, "generated nonshortest mutation")
    # Exhaustive short-input checks use a separate closed-form expectation.
    # A complete <=2-byte item can only be a direct scalar, a one-extra-byte
    # integer, a 0/1-byte string, or a 0/1-element array (maps must be empty).
    scalar_initials = set(range(0x18)) | set(range(0x20, 0x38)) | {0x40, 0x60, 0x80, 0xA0, 0xF4, 0xF5, 0xF6}
    for data in _short_buffers():
        expected_end = -1
        if data:
            first = data[0]
            if first in scalar_initials:
                expected_end = 1
            elif len(data) == 2:
                if first in (0x18, 0x38) and data[1] >= 24:
                    expected_end = 2
                elif first in (0x41, 0x61):
                    expected_end = 2
                elif first == 0x81 and data[1] in scalar_initials:
                    expected_end = 2
        check(item_end(data, 0), expected_end, "exhaustive short end")
        check(whole(data), bool(data) and expected_end == len(data), "exhaustive short whole")
    print(f"{checks} checks ok")
    print(f"RFC Appendix A examples: {len(RFC_EXAMPLES)}")
    return checks


def main() -> None:
    parser = _Parser(description=__doc__)
    commands = parser.add_subparsers(dest="command", required=True)
    corpus = commands.add_parser("corpus")
    corpus.add_argument("--seed", required=True, type=int)
    corpus.add_argument("--out", required=True)
    heads = commands.add_parser("heads")
    heads.add_argument("--out", required=True)
    commands.add_parser("selftest")
    args = parser.parse_args()
    if args.command == "selftest":
        selftest()
        return
    count = 0
    with open(args.out, "w", encoding="ascii", newline="\n") as output:
        cases = corpus_cases(args.seed) if args.command == "corpus" else head_cases()
        for data in cases:
            if args.command == "corpus":
                output.write(f"{data.hex()}\t{item_end(data, 0, 16)}\t{int(whole(data))}\n")
            else:
                decoded = head(data, 0)
                suffix = "NONE" if decoded is None else "\t".join(map(str, decoded))
                output.write(f"{data.hex()}\t{suffix}\n")
            count += 1
    if args.command == "corpus":
        print(f"seed={args.seed} corpus_cases={count}", file=sys.stderr)
    else:
        print(f"head_cases={count}", file=sys.stderr)


if __name__ == "__main__":
    main()
