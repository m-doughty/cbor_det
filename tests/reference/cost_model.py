#!/usr/bin/env python3
"""The cost of running the ghost predicate Det_End on one input.

The differential test (scripts/differential.sh) runs the library's ghost
predicate, compiled with assertions on, over the corpus of the reference
decoder. Det_End is a specification written to be proved, not to be fast:
its expression functions are evaluated as written, with nothing
remembered, so a map evaluates its members twice and then once more per
key for the order rule. The cost of one input is therefore quadratic in
the width of a map and exponential in the nesting of maps of more than one
pair. A few corpus rows would take hours or days.

This module predicts that cost without running it. It follows the
evaluation order of Det_End, Members_End, Keys_Ascending and Lex_Less
call for call (the same branches, the same short circuits, every actual
parameter evaluated) and counts the calls. Each call is memoised here, so
the prediction takes milliseconds while the count is that of the
unmemoised evaluation. The count is a model of time: validate checks it
against measured times.

It is tooling, not an oracle. It also computes the verdict the count
belongs to; a row on which that end differs from the reference's is
classified "unmodelled" (the count would not be the count of what runs),
reported with its row number, bytes and both ends, and fails the
classification (non-zero exit status). The test runner fails any
unmodelled row too. The deferred class (rows too costly to run) is
separate, and only counted.

Usage:
  cost_model.py classify --in CORPUS --out CLASSIFIED --limit N
      CORPUS is the reference's corpus (hex, end, whole per line). Every
      row is written to CLASSIFIED with two more columns, its class and
      its predicted count: "run" when the count is at most N, "deferred"
      when it is larger, "unmodelled" as above (which fails the
      classification). The counts per class are printed; no row is
      dropped. The model runs on the main thread with the platform's stack
      and recursion limit, a few frames per level of nesting (about 55 at
      the depth limit, whatever the width of a container); a row it cannot
      finish (out of stack) fails the classification, naming the row, and
      no CLASSIFIED is written.
  cost_model.py selftest
      The classifier on small corpora: agreeing rows pass, a disagreeing
      row fails naming the row and both ends, a costly row is deferred.
      The stack: the deepest and widest rows are classified when no thread
      stack size is accepted and within a bounded number of frames, and a
      stack too small for a row fails naming the row, leaving no
      CLASSIFIED. The validator on small timings: proportional times pass;
      identical rows, a negative correlation, constant counts or times,
      and a single row of 0.1 s or more each fail. A failed check prints
      the exit status and the last 20 lines of output of the run it made.
  cost_model.py validate --timings FILE
      FILE holds "count<TAB>seconds" per row, as measured by the test
      runner. Prints the fit of seconds against the count (least squares
      through the origin), the correlation of their logarithms, and the
      largest and smallest ratio of seconds to count over the rows that
      took 0.1 s or more. Fails if the correlation is undefined, not
      finite or below 0.8; if fewer than two rows took 0.1 s or more
      (insufficient evidence); or if those ratios differ by more than a
      factor of 10.

Standard library only; Python 3.10 or later.
"""

from __future__ import annotations

import argparse
import math
import os
import sys

MAX_DEPTH = 16
NATURAL_LAST = 2**31 - 1

# What validate requires of the measured times: their logarithms correlate
# with those of the predicted counts at least this well, and over the rows
# long enough to time (0.1 s or more) the seconds per call vary by at most
# this factor.
MIN_TIMED = 0.1
MIN_CORRELATION = 0.8
MAX_SPREAD = 10.0


def model(buf: bytes, depth: int = MAX_DEPTH) -> tuple[int | None, int]:
    """(end, count): Det_End's end (0-based, None when rejected) at 0."""
    n = len(buf)

    def head_len(ib: int) -> int:
        info = ib & 31
        if info <= 23:
            return 1
        return {24: 2, 25: 3, 26: 5, 27: 9}.get(info, 0)

    def arg(p: int) -> int:
        info = buf[p] & 31
        if info <= 23:
            return info
        width = head_len(buf[p]) - 1
        return int.from_bytes(buf[p + 1:p + 1 + width], "big")

    def head_ok(p: int) -> bool:
        length = head_len(buf[p])
        if length < 1 or n - p < length:
            return False
        info = buf[p] & 31
        minimum = {24: 24, 25: 1 << 8, 26: 1 << 16, 27: 1 << 32}
        return info <= 23 or arg(p) >= minimum[info]

    def arg_fits(p: int, room: int) -> bool:
        return arg(p) <= NATURAL_LAST and arg(p) <= room

    # The three functions are memoised by hand (each result is the count of
    # the unmemoised call). Det_End recurses only into an item nested one
    # level deeper (D one less), and Members_End and Keys_Ascending, whose
    # definitions recurse on the member count and the pair count, are
    # computed here by loops from the largest count already known; so the
    # Python stack holds a few frames per level of nesting (17 levels at
    # most), whatever the width of a container.
    det_ends: dict[tuple[int, int], tuple[int | None, int]] = {}
    members: dict[tuple[int, int, int], tuple[int | None, int]] = {}
    ascending: dict[tuple[int, int, int], tuple[bool, int]] = {}

    def det_end(p: int, d: int) -> tuple[int | None, int]:
        known = det_ends.get((p, d))
        if known is None:
            known = det_ends[(p, d)] = det_end_once(p, d)
        return known

    def det_end_once(p: int, d: int) -> tuple[int | None, int]:
        count = 1
        if not head_ok(p):
            return None, count
        length = head_len(buf[p])
        room = n - p - length
        major = buf[p] >> 5
        if major in (0, 1):
            return p + length, count
        if major in (2, 3):
            return (p + length + arg(p) if arg_fits(p, room) else None), count
        if major == 4:
            if d == 0 or not arg_fits(p, room):
                return None, count
            end, c = members_end(p + length, arg(p), d - 1)
            return end, count + c
        if major == 5:
            if d == 0 or not arg_fits(p, room // 2):
                return None, count
            q, pairs = p + length, arg(p)
            end, c = members_end(q, 2 * pairs, d - 1)
            count += c
            if end is None:
                return None, count
            ok, c = keys_ascending(q, pairs, d - 1)
            count += c
            if not ok:
                return None, count
            end, c = members_end(q, 2 * pairs, d - 1)
            return end, count + c
        if major == 6:
            return None, count
        return (p + 1 if (buf[p] & 31) in (20, 21, 22) else None), count

    def members_end(q: int, k: int, d: int) -> tuple[int | None, int]:
        # Members_End (Q, K, D) is Members_End (Q, K - 1, D) and then one
        # more item; Members_End (Q, 0, D) is Q.
        first = k
        while first > 0 and (q, first - 1, d) not in members:
            first -= 1
        for j in range(first, k + 1):
            if (q, j, d) in members:
                continue
            if j == 0:
                members[(q, j, d)] = (q, 1)
                continue
            start, count = members[(q, j - 1, d)]
            count += 1
            if start is None or start >= n:
                members[(q, j, d)] = (None, count)
                continue
            end, c = det_end(start, d)
            members[(q, j, d)] = (end, count + c)
        return members[(q, k, d)]

    def keys_ascending(q: int, pairs: int, d: int) -> tuple[bool, int]:
        # Keys_Ascending (Q, P, D) is Keys_Ascending (Q, P - 1, D) and then
        # the order of the last two keys; fewer than two pairs are in order.
        first = pairs
        while first > 0 and (q, first - 1, d) not in ascending:
            first -= 1
        for j in range(first, pairs + 1):
            if (q, j, d) in ascending:
                continue
            if j < 2:
                ascending[(q, j, d)] = (True, 1)
                continue
            ok, c = ascending[(q, j - 1, d)]
            count = 1 + c
            if not ok:
                ascending[(q, j, d)] = (False, count)
                continue
            bounds = []
            for k in (2 * j - 4, 2 * j - 3, 2 * j - 2, 2 * j - 1):
                end, c = members_end(q, k, d)
                count += c
                bounds.append(end)
            less, c = lex_less(*bounds)
            ascending[(q, j, d)] = (less, count + c)
        return ascending[(q, pairs, d)]

    def lex_less(p1, e1, p2, e2) -> tuple[bool, int]:
        def slice_ok(p, e):
            return p is not None and e is not None and 0 <= p <= e <= n
        count = 1
        if not slice_ok(p1, e1) or not slice_ok(p2, e2):
            return False, count
        while True:
            if p1 == e1:
                return p2 < e2, count
            if p2 == e2:
                return False, count
            if buf[p1] != buf[p2]:
                return buf[p1] < buf[p2], count
            p1, p2, count = p1 + 1, p2 + 1, count + 1

    if n == 0:
        return None, 0
    return det_end(0, depth)


def classify(source: str, target: str, limit: int) -> int:
    """Classify every row; return the number of rows on which the model's
    end differs from the reference's, each reported on standard error.
    CLASSIFIED is written whole or not at all: if a row cannot be
    classified (a malformed row, or the model running out of stack) the
    run fails naming the row and no CLASSIFIED is left behind."""
    counts = {"run": 0, "deferred": 0, "unmodelled": 0}
    largest_run = 0
    partial = target + ".partial"
    try:
        with open(source, encoding="ascii") as rows, \
                open(partial, "w", encoding="ascii", newline="\n") as out:
            for number, line in enumerate(rows, start=1):
                fields = line.rstrip("\r\n").split("\t")
                if len(fields) != 3:
                    raise SystemExit(f"cost_model: malformed corpus row {number}")
                data = bytes.fromhex(fields[0])
                shown = fields[0]
                if len(shown) > 64:
                    shown = shown[:64] + "..."
                try:
                    end, count = model(data)
                except RecursionError:
                    raise SystemExit(
                        f"cost_model: FAILED: row {number} (bytes "
                        f"{shown or 'none'}): the model ran out of stack "
                        f"(recursion limit {sys.getrecursionlimit()}, on the "
                        "main thread's stack as the platform sets it); no "
                        "class is written for this row or any other") from None
                model_end = end if end is not None else -1
                reference_end = int(fields[1])
                if model_end != reference_end:
                    cls = "unmodelled"
                    print(f"cost_model: row {number} (bytes {shown or 'none'}): "
                          f"the model's end {model_end} differs from the "
                          f"reference's end {reference_end}", file=sys.stderr)
                elif count <= limit:
                    cls = "run"
                    largest_run = max(largest_run, count)
                else:
                    cls = "deferred"
                counts[cls] += 1
                out.write("\t".join(fields + [cls, str(count)]) + "\n")
        os.replace(partial, target)
    finally:
        if os.path.exists(partial):
            os.remove(partial)
    total = sum(counts.values())
    print(f"cost classes (limit {limit} calls): rows={total} "
          f"run={counts['run']} deferred={counts['deferred']} "
          f"unmodelled={counts['unmodelled']} largest_run={largest_run}")
    return counts["unmodelled"]


def validate(path: str) -> None:
    """Fail unless the measured times follow the predicted counts: the
    correlation of their logarithms is defined, finite and at least
    MIN_CORRELATION, and at least two rows took MIN_TIMED seconds or more
    and their seconds per call differ by at most MAX_SPREAD. Too few such
    rows is reported as insufficient evidence, and fails too."""
    pairs = []
    with open(path, encoding="ascii") as rows:
        for line in rows:
            count, seconds = line.split()
            pairs.append((int(count), float(seconds)))
    if len(pairs) < 2:
        raise SystemExit("cost_model: too few timings to validate")
    slope = (sum(c * s for c, s in pairs) / sum(c * c for c, _ in pairs))
    xs = [math.log(c) for c, s in pairs if c > 0 and s > 0]
    ys = [math.log(s) for c, s in pairs if c > 0 and s > 0]
    corr = float("nan")
    if len(xs) >= 2:
        mx, my = sum(xs) / len(xs), sum(ys) / len(ys)
        sxy = sum((x - mx) * (y - my) for x, y in zip(xs, ys))
        sxx = sum((x - mx) ** 2 for x in xs)
        syy = sum((y - my) ** 2 for y in ys)
        if sxx > 0 and syy > 0:
            corr = sxy / math.sqrt(sxx * syy)
    print(f"timings={len(pairs)} seconds_per_call={slope:.3e} "
          f"log_log_correlation={corr:.4f}")
    if not math.isfinite(corr):
        raise SystemExit("model: NOT VALID: the correlation of times with "
                         "predicted counts is undefined (counts or times do "
                         "not vary)")
    if corr < MIN_CORRELATION:
        raise SystemExit(f"model: NOT VALID: correlation {corr:.4f} is below "
                         f"{MIN_CORRELATION}")
    timed = [(c, s) for c, s in pairs if s >= MIN_TIMED and c > 0]
    ratios = [s / c for c, s in timed]
    if len(ratios) < 2:
        raise SystemExit(f"model: insufficient evidence: {len(ratios)} row(s) "
                         f"of {MIN_TIMED} s or more, at least 2 needed to "
                         "bound the rate; not validated")
    spread = max(ratios) / min(ratios)
    print(f"rows timed at 0.1 s or more: {len(timed)}, seconds per call "
          f"from {min(ratios):.3e} to {max(ratios):.3e} (spread {spread:.1f})")
    if spread > MAX_SPREAD:
        raise SystemExit("model: NOT VALID: the measured times do not follow "
                         "the predicted counts; the cost classes are not valid")
    print("model: valid (correlation at least "
          f"{MIN_CORRELATION}, spread at most {MAX_SPREAD})")


# The selftest runs some classifications through this harness, in a child
# process: it loads this file by its path and constrains the stack the way
# a platform might before running the command. REFUSE_ABOVE (bytes) makes
# threading.stack_size refuse any larger size with the ValueError Windows'
# Python raises for 512 MB (-1: no refusal). ROOM (frames) caps the
# recursion available to the model at that many frames above its caller
# (0: unchanged). Nothing outside the selftest uses it. It holds no double
# quote, so that it passes through a Windows command line unchanged.
HARNESS = """
import importlib.util, sys, threading
script, refuse_above, room = sys.argv[1], int(sys.argv[2]), int(sys.argv[3])
platform_stack_size = threading.stack_size
def stack_size(size=0):
    if refuse_above >= 0 and size > refuse_above:
        raise ValueError(f'size not valid: {size} bytes')
    return platform_stack_size(size)
threading.stack_size = stack_size
spec = importlib.util.spec_from_file_location('cost_model', script)
module = importlib.util.module_from_spec(spec)
spec.loader.exec_module(module)
if room > 0:
    unconstrained = module.model
    def model(*args):
        depth, frame = 0, sys._getframe()
        while frame is not None:
            depth, frame = depth + 1, frame.f_back
        sys.setrecursionlimit(depth + room)
        return unconstrained(*args)
    module.model = model
sys.argv = [script] + sys.argv[4:]
module.main()
"""

# The recursion the model needs, as the selftest checks it: the deepest
# rows within ROOM_ENOUGH frames (they need about 55, a few per level of
# nesting), and a row of 16 nested arrays fails within ROOM_TOO_SMALL
# frames, which a one-byte row (about 5) fits in.
ROOM_ENOUGH = 120
ROOM_TOO_SMALL = 12


def stack_rows() -> list[str]:
    """Rows as deep and as wide as an item can be, as corpus rows (each
    with the reference's end and whole-input verdict): 16 nested arrays;
    16 nested maps of two pairs, nested in a key and in a value; 17
    nested arrays and maps (refused at the depth limit); an array of 2000
    members and a map of 500 pairs."""
    def maps(level, in_key):
        if level == 0:
            return b"\x01"
        inner = maps(level - 1, in_key)
        if in_key:
            return b"\xa2\x00\x00" + inner + b"\x00"
        return b"\xa2\x00" + inner + b"\x01\x00"

    def key(v):
        if v < 24:
            return bytes([v])
        if v < 256:
            return bytes([0x18, v])
        return b"\x19" + v.to_bytes(2, "big")

    accepted = [b"\x81" * 16 + b"\x00", maps(16, True), maps(16, False),
                b"\x99\x07\xd0" + b"\x00" * 2000,
                b"\xb9\x01\xf4"
                + b"".join(key(v) + b"\x00" for v in range(500))]
    refused = [b"\x81" * 17 + b"\x00", maps(17, True), maps(17, False)]
    return ([f"{r.hex()}\t{len(r)}\t1" for r in accepted]
            + [f"{r.hex()}\t-1\t0" for r in refused])


def selftest() -> None:
    """The classifier and the validator on small inputs, each run as a
    separate process, as the differential runs them: rows the model agrees
    on are classified and the run passes; a row on which the model's end
    and the reference's differ fails the run, naming the row and both ends;
    a costly row is deferred, not failed; the deepest and widest rows are
    classified with no thread stack size accepted and within ROOM_ENOUGH
    frames, and a stack too small for a row fails the run, naming the row
    and the limit, with no classified file left; the validator passes
    times that follow the counts and fails an undefined or low
    correlation, constant times, and too few rows of 0.1 s or more. A
    failed check prints the child's exit status and the last lines of its
    output."""
    import subprocess
    import tempfile
    script = os.path.abspath(__file__)
    checks = 0

    def classify_run(rows, limit, refuse_above=None, room=0):
        with tempfile.TemporaryDirectory() as d:
            source = os.path.join(d, "corpus.tsv")
            target = os.path.join(d, "classified.tsv")
            with open(source, "w", encoding="ascii", newline="\n") as f:
                f.write("".join(r + "\n" for r in rows))
            command = ["classify", "--in", source, "--out", target,
                       "--limit", str(limit)]
            if refuse_above is None and room == 0:
                child = [sys.executable, "-B", "-I", script] + command
            else:
                child = ([sys.executable, "-B", "-I", "-c", HARNESS, script,
                          str(-1 if refuse_above is None else refuse_above),
                          str(room)] + command)
            p = subprocess.run(child, capture_output=True, text=True)
            out = ""
            if os.path.exists(target):
                with open(target, encoding="ascii") as f:
                    out = f.read()
            leftovers = sorted(set(os.listdir(d)) - {"corpus.tsv"})
            return p.returncode, p.stdout + p.stderr, out, leftovers

    def expect(cond, what, code, text):
        nonlocal checks
        checks += 1
        if not cond:
            home = os.path.expanduser("~")
            if home not in ("", "~", os.sep):
                text = text.replace(home, "~")
            lines = text.splitlines()[-20:]
            print(f"cost_model selftest: the failed check's child exited "
                  f"{code}; the last {len(lines)} lines of its output:",
                  file=sys.stderr)
            for line in lines:
                print(f"    {line}", file=sys.stderr)
            raise SystemExit(f"cost_model selftest FAILED: {what}")

    good = ["00\t1\t1", "8100\t2\t1", "\t-1\t0", "a1\t-1\t0", "0000\t1\t0"]
    code, text, out, _ = classify_run(good, 10**9)
    expect(code == 0, "agreeing rows: exit 0", code, text)
    expect(out.count("\trun\t") == 5, "agreeing rows: all run", code, text)
    code, text, out, _ = classify_run(good + ["00\t-1\t0"], 10**9)
    expect(code != 0, "a disagreeing row fails the classification", code, text)
    expect("row 6" in text and "00" in text, "the failure names the row",
           code, text)
    expect("model's end 1" in text and "reference's end -1" in text,
           "the failure names both ends", code, text)
    code, text, out, _ = classify_run(["8100\t2\t1"], 1)
    expect(code == 0 and "\tdeferred\t" in out,
           "a costly row is deferred, not failed", code, text)

    # The stack. The model needs no thread of its own and no stack larger
    # than the platform's: it classifies the deepest and widest rows when
    # threading.stack_size refuses 512 MB (as Windows' Python does) and
    # when it refuses every size, and within ROOM_ENOUGH frames.
    deep = stack_rows()
    for refuse_above, what in ((256 * 1024 * 1024, "above 256 MB"),
                               (0, "of any size")):
        code, text, out, _ = classify_run(deep, 10**9, refuse_above)
        expect(code == 0 and len(out.splitlines()) == len(deep)
               and "unmodelled" not in out,
               f"the deepest and widest rows classify with thread stacks "
               f"{what} refused", code, text)
    code, text, out, _ = classify_run(deep, 10**9, None, ROOM_ENOUGH)
    expect(code == 0 and len(out.splitlines()) == len(deep),
           f"the deepest and widest rows classify within {ROOM_ENOUGH} "
           "frames", code, text)
    # A stack too small for a row fails loudly: non-zero, naming the row
    # and the limit, and no classified file (whole or partial) is left.
    code, text, out, leftovers = classify_run(["00\t1\t1"] + deep, 10**9, None,
                                              ROOM_TOO_SMALL)
    expect(code != 0 and "row 2 " in text and "ran out of stack" in text
           and "recursion limit" in text,
           "a stack too small for a row fails, naming the row and the limit",
           code, text)
    expect(leftovers == [],
           f"a failed classification leaves no file (left: {leftovers})",
           code, text)

    def validate_run(rows):
        with tempfile.TemporaryDirectory() as d:
            path = os.path.join(d, "timings.txt")
            with open(path, "w", encoding="ascii", newline="\n") as f:
                f.write("".join(r + "\n" for r in rows))
            p = subprocess.run([sys.executable, "-B", "-I", script, "validate",
                                "--timings", path],
                               capture_output=True, text=True)
            return p.returncode, p.stdout + p.stderr

    # validate: a finite correlation above the threshold and a bounded
    # rate over at least two rows of 0.1 s or more, or the run fails.
    code, text = validate_run(["1000000\t0.2", "2000000\t0.4", "10\t0.00001"])
    expect(code == 0 and "model: valid" in text, "proportional times validate",
           code, text)
    code, text = validate_run(["100\t0.2", "100\t0.2"])
    expect(code != 0 and "model: valid" not in text,
           "identical rows (no correlation defined) fail", code, text)
    code, text = validate_run(["1\t0.09", "10\t0.01"])
    expect(code != 0 and "model: valid" not in text,
           "a negative correlation fails even with no row of 0.1 s",
           code, text)
    code, text = validate_run(["100\t0.2", "100\t0.3"])
    expect(code != 0 and "model: valid" not in text,
           "equal counts (correlation NaN) fail", code, text)
    code, text = validate_run(["100\t0.2", "200\t0.2", "400\t0.2"])
    expect(code != 0 and "model: valid" not in text,
           "constant times (correlation NaN) fail", code, text)
    code, text = validate_run(["1000000\t0.2", "10\t0.00001", "100\t0.0001"])
    expect(code != 0 and "insufficient" in text and "model: valid" not in text,
           "one row of 0.1 s or more is insufficient evidence, and fails",
           code, text)
    print(f"cost_model selftest: {checks} checks passed")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__,
                                     formatter_class=argparse.RawDescriptionHelpFormatter)
    commands = parser.add_subparsers(dest="command", required=True)
    c = commands.add_parser("classify")
    c.add_argument("--in", dest="source", required=True)
    c.add_argument("--out", dest="target", required=True)
    c.add_argument("--limit", type=int, required=True)
    v = commands.add_parser("validate")
    v.add_argument("--timings", required=True)
    commands.add_parser("selftest")
    args = parser.parse_args()
    if args.command == "classify":
        if classify(args.source, args.target, args.limit):
            raise SystemExit("cost_model: FAILED: the model and the reference "
                             "disagree on an end (rows above); the model's "
                             "counts are not valid for those rows")
    elif args.command == "selftest":
        selftest()
    else:
        validate(args.timings)


if __name__ == "__main__":
    main()
