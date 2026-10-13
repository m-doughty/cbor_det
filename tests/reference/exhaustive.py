#!/usr/bin/env python3
"""The reference decoder's verdict on every input of 0 to 3 bytes.

Writes one byte per input, inputs in order of length and then of value
(big endian): the reference's end of the item at the first byte plus one
(0 when it refuses the item) in the low 7 bits, and its whole-input
verdict in the top bit. 16 843 009 bytes in all. The test runner
(test_main exhaustive FILE) enumerates the same inputs in the same order
and compares.

The reference (ref_cbor_det.py, beside this file) is loaded by its path
and used through its item_end and whole functions only; nothing here
decides a verdict.

Usage: exhaustive.py --out FILE
Standard library only; Python 3.10 or later.
"""

from __future__ import annotations

import argparse
import importlib.util
import os
import sys


def load_reference():
    path = os.path.join(os.path.dirname(os.path.abspath(__file__)),
                        "ref_cbor_det.py")
    spec = importlib.util.spec_from_file_location("ref_cbor_det", path)
    module = importlib.util.module_from_spec(spec)
    sys.modules["ref_cbor_det"] = module
    spec.loader.exec_module(module)
    return module


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__,
                                     formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--out", required=True)
    args = parser.parse_args()
    ref = load_reference()
    count = accepted = 0
    with open(args.out, "wb") as out:
        for length in range(4):
            verdicts = bytearray()
            for value in range(256 ** length):
                data = value.to_bytes(length, "big")
                end = ref.item_end(data, 0, 16)
                whole = ref.whole(data)
                if end < -1 or end > 3:
                    raise SystemExit("exhaustive: end out of range")
                verdicts.append((end + 1) | (0x80 if whole else 0))
                count += 1
                accepted += whole
            out.write(verdicts)
    print(f"exhaustive: inputs={count} accepted_whole={accepted}")


if __name__ == "__main__":
    main()
