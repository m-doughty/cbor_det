#!/usr/bin/env python3
"""Q1 denotation oracle. Standard library only; run with python3 -I.

An Incomplete rejection supplies a lower bound on the total length required by
any extension. Every other rejection is permanent under extension, except the
trailing-data rejection, which is itself also permanent under extension.
"""
import hashlib
import random
import sys
import time
import types
from pathlib import Path

MAX = (1 << 64) - 1
CORPUS_SEED = 0x5131C0B0
PAIRS_SEED = 0x5131FACE
_FAULT = None


class Rejection(ValueError):
    """The input is outside Q1."""


class Incomplete(Rejection):
    """Any valid extension needs at least minimum total bytes."""
    def __init__(self, minimum):
        self.minimum = minimum
        super().__init__("truncated item; needs at least %d bytes" % minimum)


def _decode(data):
    if type(data) is not bytes:
        raise TypeError("decode requires bytes")
    size = len(data)
    fault = _FAULT

    def item(pos, depth):
        if pos == size:
            raise Incomplete(pos + 1)
        initial = data[pos]
        pos += 1
        major, ai = initial >> 5, initial & 31
        if major == 7:
            if ai == 20:
                return ('false',), pos
            if ai == 21:
                return (('int', '+', 1) if fault == 'true_is_int'
                        else ('true',)), pos
            if ai == 22:
                return ('null',), pos
            raise Rejection('forbidden major-7 encoding')
        if major == 6 and fault != 'tag':
            raise Rejection('tags forbidden')
        if ai >= 28:
            if ai == 31 and fault == 'indefinite' and major in (2, 3, 4, 5):
                if pos < size and data[pos] == 255:
                    pos += 1
                return {2: ('bytes', b''), 3: ('text', b''),
                        4: ('array', ()), 5: ('map', frozenset())}[major], pos
            raise Rejection('reserved or indefinite argument')
        if ai < 24:
            arg = ai
        else:
            width = 1 << (ai - 24)
            if size - pos < width:
                raise Incomplete(pos + width)
            arg = int.from_bytes(data[pos:pos + width], 'big')
            pos += width
            minimum = (24, 256, 65536, 4294967296)[ai - 24]
            if arg < minimum and fault != 'nonshortest':
                raise Rejection('non-shortest argument')
        if major == 6:
            return item(pos, depth)
        if major == 0:
            return ('int', '+', arg), pos
        if major == 1:
            return ('int', '-', arg + 1), pos
        if major in (2, 3):
            if arg > size - pos:
                raise Incomplete(pos + arg)
            tag = 'bytes' if major == 2 or fault == 'text_is_bytes' else 'text'
            return (tag, data[pos:pos + arg]), pos + arg
        if depth >= 16 and fault != 'depth':
            raise Rejection('more than 16 nested containers')
        slots = arg if major == 4 else 2 * arg
        if slots > size - pos:
            raise Incomplete(pos + slots)
        if major == 4:
            values = []
            for _ in range(arg):
                value, pos = item(pos, depth + 1)
                values.append(value)
            return ('array', tuple(values)), pos
        pairs = []
        previous = None
        for _ in range(arg):
            start = pos
            key, pos = item(pos, depth + 1)
            key_bytes = data[start:pos]
            order = key_bytes
            if fault == 'value_order':
                order = ((0, key[2] if key[1] == '+' else -key[2])
                         if key[0] == 'int' else (1, repr(key)))
            if previous is not None:
                invalid = order < previous if fault == 'equal_keys' else order <= previous
                if invalid:
                    raise Rejection('map keys not strictly ascending')
            previous = order
            value, pos = item(pos, depth + 1)
            pairs.append((key, value))
        contents = tuple(pairs) if fault == 'ordered_map' else frozenset(pairs)
        return ('map', contents), pos

    value, end = item(0, 0)
    if end != size and fault != 'trailing':
        raise Rejection('trailing bytes')
    return value


def decode(data: bytes):
    """Return the tagged denotation, or raise Rejection (including Incomplete)."""
    return _decode(data)


def _head(major, arg):
    if arg < 24:
        return bytes([(major << 5) | arg])
    for ai, width in ((24, 1), (25, 2), (26, 4), (27, 8)):
        if arg < (1 << (8 * width)):
            return bytes([(major << 5) | ai]) + arg.to_bytes(width, 'big')
    raise ValueError('argument exceeds uint64')


def encode(value):
    """Encode a strictly validated VALUE; reject duplicate semantic map keys."""
    def visit(v, depth):
        if type(v) is not tuple or not v or type(v[0]) is not str:
            raise ValueError('value must be a tagged tuple')
        tag = v[0]
        if tag in ('false', 'true', 'null'):
            if len(v) != 1:
                raise ValueError('invalid singleton')
            return bytes([{'false': 244, 'true': 245, 'null': 246}[tag]])
        if tag == 'int':
            if len(v) != 3 or type(v[1]) is not str or type(v[2]) is not int:
                raise ValueError('invalid integer')
            sign, magnitude = v[1:]
            if sign == '+' and 0 <= magnitude <= MAX:
                return _head(0, magnitude)
            if sign == '-' and 1 <= magnitude <= MAX + 1:
                return _head(1, magnitude - 1)
            raise ValueError('integer sign or magnitude out of range')
        if len(v) != 2:
            raise ValueError('invalid value arity')
        if tag in ('bytes', 'text'):
            if type(v[1]) is not bytes:
                raise ValueError('string content must be bytes')
            return _head(2 if tag == 'bytes' else 3, len(v[1])) + v[1]
        if tag not in ('array', 'map'):
            raise ValueError('unknown value tag')
        if depth >= 16:
            raise ValueError('more than 16 nested containers')
        if tag == 'array':
            if type(v[1]) is not tuple:
                raise ValueError('array members must be a tuple')
            return _head(4, len(v[1])) + b''.join(visit(x, depth + 1) for x in v[1])
        if type(v[1]) is not frozenset:
            raise ValueError('map pairs must be a frozenset')
        encoded = []
        seen = set()
        for pair in v[1]:
            if type(pair) is not tuple or len(pair) != 2:
                raise ValueError('invalid map pair')
            key, val = pair
            key_bytes = visit(key, depth + 1)
            if key_bytes in seen:
                raise ValueError('duplicate map key')
            seen.add(key_bytes)
            encoded.append((key_bytes, visit(val, depth + 1)))
        encoded.sort(key=lambda pair: pair[0])
        return _head(5, len(encoded)) + b''.join(k + v for k, v in encoded)
    return visit(value, 0)


def same(v1, v2):
    """Structural tagged-value equality; map frozensets ignore pair order."""
    return v1 == v2


def _reference_encode(v):
    """Independent VALUE encoder: arithmetic head construction, no _head/encode."""
    def head(m, n):
        digits = []
        q = n
        while q:
            digits.insert(0, q % 256)
            q //= 256
        if n <= 23:
            return bytes([32 * m + n])
        width = next(w for w in (1, 2, 4, 8) if len(digits) <= w)
        info = {1: 24, 2: 25, 4: 26, 8: 27}[width]
        return bytes([32 * m + info] + [0] * (width - len(digits)) + digits)
    tag = v[0]
    if tag in ('false', 'true', 'null'):
        return {'false': b'\xf4', 'true': b'\xf5', 'null': b'\xf6'}[tag]
    if tag == 'int':
        return head(0 if v[1] == '+' else 1, v[2] if v[1] == '+' else v[2] - 1)
    if tag in ('bytes', 'text'):
        return head(2 if tag == 'bytes' else 3, len(v[1])) + v[1]
    if tag == 'array':
        result = head(4, len(v[1]))
        for member in v[1]:
            result += _reference_encode(member)
        return result
    pairs = [(_reference_encode(k), _reference_encode(val)) for k, val in v[1]]
    # Deliberately use insertion selection rather than encode's list sort.
    result = head(5, len(pairs))
    while pairs:
        pair = min(pairs, key=lambda p: p[0])
        pairs.remove(pair)
        result += pair[0] + pair[1]
    return result


def _int(n):
    return ('int', '+' if n >= 0 else '-', abs(n))


def _map(pairs):
    return ('map', frozenset(pairs))


def _nest(v, n, maps=False):
    for i in range(n):
        v = _map([(_int(0), v)]) if maps and i % 2 else ('array', (v,))
    return v


def _must_differ():
    i = _int
    m = _map
    a = lambda *xs: ('array', xs)
    cases = [
        ('1/true', i(1), ('true',)), ('0/false', i(0), ('false',)),
        ('0/null', i(0), ('null',)), ('true/null', ('true',), ('null',)),
        ('text/bytes', ('text', b'a'), ('bytes', b'a')),
        ('empty text/bytes', ('bytes', b''), ('text', b'')),
        ('array order', a(i(1), i(2)), a(i(2), i(1))),
        ('empty containers', a(), m([])),
        ('map value', m([(i(1), i(1))]), m([(i(1), i(2))])),
        ('map key', m([(i(1), i(0))]), m([(i(2), i(0))])),
        ('map pair', m([(i(0), i(0)), (i(1), i(1))]), m([(i(0), i(0)), (i(2), i(2))])),
        ('map count', m([(i(0), i(0))]), m([(i(0), i(0)), (i(1), i(1))])),
        ('prefix keys', m([(('bytes', b'\x01'), i(1))]), m([(('bytes', b'\x01\x00'), i(1))])),
        ('positive/negative', i(1), i(-1)), ('24/map key', i(24), m([(i(24), i(0))])),
        ('array length', a(i(1)), a(i(1), i(1))),
        ('depth16 inner', _nest(i(1), 16, True), _nest(i(2), 16, True)),
    ]
    return [(name, encode(x), encode(y)) for name, x, y in cases]


def _reject_cases():
    samples = {
        'nonshortest8': '1800', 'nonshortest16': '190000',
        'nonshortest32': '1a00000000', 'nonshortest64': '1b0000000000000000',
        'nonshortest string0': '5800', 'nonshortest string23': '5817' + '00' * 23,
        '1817': '1817', 'indef array': '9fff', 'indef map': 'bfff',
        'indef bytes': '5f', 'indef text': '7f', 'tag': 'c000',
        'float16': 'f90000', 'float32': 'fa00000000', 'float64': 'fb0000000000000000',
        'undefined': 'f7', 'simple': 'f800', 'break': 'ff',
        'equal keys': 'a201010102', 'descending keys': 'a202010102',
        'encoded order reversed': 'a22001181801', 'trailing': '0000',
        'empty': '', 'missing int arg': '18', 'missing string': '4200',
        'missing array': '8200', 'missing map value': 'a100',
        'depth17': '81' * 17 + '00',
    }
    for major in range(8):
        for ai in (28, 29, 30, 31):
            samples['major%d info%d' % (major, ai)] = '%02x' % (major * 32 + ai)
    for major in range(2, 8):
        samples['huge major%d' % major] = '%02x' % (major * 32 + 27) + 'ff' * 8 + '00'
    for major in (0, 1):
        samples['maximum integer with trailing data major%d' % major] = (
            '%02x' % (major * 32 + 27) + 'ff' * 8 + '00')
    samples['depth17 in map key'] = 'a1' + '81' * 16 + '00' + '00'
    for major in range(6):
        for ai, zeros in ((24, 1), (25, 2), (26, 4), (27, 8)):
            samples['nonshortest major%d info%d' % (major, ai)] = '%02x' % (major * 32 + ai) + '00' * zeros
    for byte in range(224, 256):
        if byte not in (244, 245, 246):
            samples['major7 %02x' % byte] = '%02x' % byte
    return [(name, bytes.fromhex(s)) for name, s in samples.items()]


def _accept_cases():
    values = [(_int(MAX)), ('int', '-', MAX + 1), ('text', b'\xff\xc0\x80'),
              _nest(_int(0), 16), _nest(_int(0), 16, True),
              _map([(_int(24), _int(1)), (_int(-1), _int(1))]),
              _map([(('array', (_int(0),)), _int(1)), (_map([]), _int(2))])]
    return [('reference value %d' % n, _reference_encode(v), v) for n, v in enumerate(values)] + [
        ('1818 valid', bytes.fromhex('1818'), _int(24)),
        ('encoded key ordering', bytes.fromhex('a21818012001'), _map([(_int(24), _int(1)), (_int(-1), _int(1))])),
    ]


def _battery(decoder=decode):
    """Return first failed battery/case, or None; used unchanged by selftest."""
    for name, raw in _reject_cases():
        try:
            decoder(raw)
        except Rejection:
            pass
        else:
            return 'must-reject: ' + name
    for name, left, right in _must_differ():
        try:
            if same(decoder(left), decoder(right)):
                return 'must-differ: ' + name
        except (Rejection, ValueError, TypeError):
            return 'must-differ acceptance: ' + name
    for name, raw, expected in _accept_cases():
        try:
            actual = decoder(raw)
            if not same(actual, expected) or encode(actual) != raw:
                return 'check value/roundtrip: ' + name
        except (Rejection, ValueError, TypeError):
            return 'check acceptance: ' + name
    return None


def _small_inputs(limit, verify=False):
    """Exhaust every prefix; count its pruned subtree, not just valid leaves.

    Incomplete.minimum is a lower bound because each missing argument byte,
    payload byte, or container slot needs a byte; ignoring pending ancestors
    only weakens that bound. Permanent failures cannot be repaired by append.
    Accepted prefixes have exclusively invalid nonempty extensions (trailing).
    """
    seen = {}
    accepted = []
    counts = [0] * (limit + 1)
    covered = 0
    attempted = 0
    pruned = 0
    stack = [b'']
    while stack:
        raw = stack.pop()
        attempted += 1
        descendants = sum(256 ** n for n in range(1, limit - len(raw) + 1))
        covered += 1
        expand = False
        try:
            value = decode(raw)
        except Incomplete as exc:
            expand = len(raw) < limit and exc.minimum <= limit
        except Rejection:
            pass
        else:
            accepted.append(raw)
            counts[len(raw)] += 1
            if verify:
                assert encode(value) == raw, ('roundtrip', raw.hex())
                old = seen.setdefault(value, raw)
                assert old == raw, ('collision', old.hex(), raw.hex())
        if expand:
            stack.extend(raw + bytes([byte]) for byte in range(255, -1, -1))
        else:
            covered += descendants
            pruned += descendants
    assert covered == sum(256 ** n for n in range(limit + 1))
    assert counts == [0, 55, 1031, 268713][:limit + 1], counts
    return accepted, counts, covered, attempted, pruned


def _random_value(rng, remaining=3):
    kind = rng.randrange(9 if remaining else 7)
    if kind <= 1:
        choices = [0, 1, 23, 24, 255, 256, 65535, 65536, (1 << 32) - 1,
                   1 << 32, MAX, rng.getrandbits(64)]
        n = rng.choice(choices)
        return ('int', '+' if kind == 0 else '-', n if kind == 0 else n + 1)
    if kind <= 3:
        n = rng.randrange(33)
        return ('bytes' if kind == 2 else 'text', bytes(rng.randrange(256) for _ in range(n)))
    if kind <= 6:
        return [('false',), ('true',), ('null',)][kind - 4]
    if kind == 7:
        return ('array', tuple(_random_value(rng, remaining - 1) for _ in range(rng.randrange(4))))
    pairs = {}
    for _ in range(rng.randrange(4)):
        pairs[_random_value(rng, remaining - 1)] = _random_value(rng, remaining - 1)
    return _map(pairs.items())


def _structured_values():
    rng = random.Random(CORPUS_SEED)
    boundaries = (0, 23, 24, 255, 256, 65535, 65536, (1 << 32) - 1, 1 << 32, MAX)
    for n in boundaries:
        yield _int(n)
        yield _int(-n)
        yield ('int', '-', n + 1)
    yield ('array', ())
    yield _map([])
    for n in range(301):
        content = bytes((i * 73 + n) % 256 for i in range(n))
        yield ('bytes', content)
        yield ('text', content)
        yield _map([(_int(i), ('text', bytes([i % 256]))) for i in range(n)])
    for depth in range(1, 17):
        yield _nest(_int(depth), depth)
        yield _nest(('text', b'\xff'), depth, True)
        # Containers occurring in key position, with total depth exactly depth.
        key = _nest(_int(0), depth - 1, True)
        yield _map([(key, ('null',))])
    prefix = b'prefix' * 40
    yield _map([(('bytes', prefix + bytes([i])), _int(i)) for i in range(100)])
    yield _map([(('text', b'a'), ('true',)), (('bytes', b'a'), ('false',))])
    for n in range(100000):
        value = ('array', (_int(n), _random_value(rng)))
        yield _nest(value, n % 4, True)


def _validate_encoder():
    bad = [None, True, 1, (), ('unknown',), ('true', 1), ('int', '+', True),
           ('int', '-', 0), ('int', '+', -1), ('int', '+', MAX + 1),
           ('int', '-', MAX + 2), ('int', '?', 1), ('bytes', 'x'),
           ('text', bytearray(b'x')), ('array', []), ('map', ()),
           _map([(_int(0), _int(1)), (_int(0), _int(2))]),
           _nest(_int(0), 17)]
    for value in bad:
        try:
            encode(value)
        except (ValueError, TypeError):
            pass
        else:
            raise AssertionError(('encoder accepted invalid value', value))
    return len(bad)


def command_check():
    start = time.perf_counter()
    print('seeds: corpus=%d pairs=%d' % (CORPUS_SEED, PAIRS_SEED), flush=True)
    failed = _battery()
    assert failed is None, failed
    print('batteries: rejected=%d must_differ=%d accepted=%d encoder_invalid=%d' % (
        len(_reject_cases()), len(_must_differ()), len(_accept_cases()), _validate_encoder()), flush=True)
    accepted, counts, covered, attempted, pruned = _small_inputs(3, True)
    print('exhaustive: universe=%d accepted=%d by_length=%s decoder_calls=%d pruned=%d' % (
        covered, len(accepted), counts, attempted, pruned), flush=True)
    print('coverage: prefix traversal; permanent failures and trailing extensions pruned; '
          'incomplete prefixes pruned only when minimum completion length exceeds 3', flush=True)
    del accepted
    seen = {}
    count = 0
    for value in _structured_values():
        raw = _reference_encode(value)
        actual = decode(raw)
        assert same(actual, value), ('reference disagreement', raw.hex())
        assert encode(actual) == raw, ('roundtrip', raw.hex())
        previous = seen.setdefault(actual, raw)
        assert previous == raw, ('collision', previous.hex(), raw.hex())
        count += 1
    assert count >= 100000
    assert len(seen) >= 100000
    print('structured: accepted=%d distinct_inputs=%d independent_value_checks=%d' % (count, len(seen), count), flush=True)
    print('check PASS elapsed_seconds=%.3f' % (time.perf_counter() - start), flush=True)


def command_selftest():
    start = time.perf_counter()
    assert _battery() is None
    print('baseline batteries: PASS')
    faults = ('nonshortest', 'tag', 'equal_keys', 'trailing', 'value_order',
              'depth', 'text_is_bytes', 'true_is_int', 'ordered_map', 'indefinite')
    for fault in faults:
        namespace = dict(globals())
        namespace['_FAULT'] = fault
        mutant = types.FunctionType(_decode.__code__, namespace, 'mutant_' + fault)
        caught = _battery(mutant)
        assert caught is not None, 'surviving mutant: ' + fault
        print('mutant %-14s caught by %s' % (fault, caught))
    # Equality is Python equality on tagged tuples; maps are unordered sets.
    pairs = [(_int(0), ('false',)), (_int(1), ('true',))]
    assert same(_map(pairs), _map(reversed(pairs)))
    assert encode(_map(pairs)) == encode(_map(reversed(pairs)))
    assert not same(_int(1), ('true',))
    assert not same(('text', b'a'), ('bytes', b'a'))
    print('selftest PASS mutants=10 elapsed_seconds=%.3f' % (time.perf_counter() - start))


def _pair_values(n, rng):
    tag = n % 10
    base = ('array', (_int(n), _random_value(rng, 2)))
    if tag == 0:
        return base, base
    if tag == 1:
        entries = [(_int(n), base), (('text', b'order'), ('null',))]
        return _map(entries), _map(reversed(entries))
    if tag == 2:
        return base, ('array', (_int(n + 1), base[1][1]))
    if tag == 3:
        data = n.to_bytes(4, 'big')
        return ('bytes', data), ('text', data)
    if tag == 4:
        return ('array', (_int(n), ('true',))), ('array', (_int(n), _int(1)))
    if tag == 5:
        return ('array', (_int(n), _int(n + 1))), ('array', (_int(n + 1), _int(n)))
    entries = [(_int(n), _int(0)), (_int(n + 1), _int(1))]
    if tag == 6:
        return _map(entries), _map(entries[:1])
    if tag == 7:
        return _map(entries), _map([(_int(n + 2), _int(0)), entries[1]])
    if tag == 8:
        return _map(entries), _map([(entries[0][0], _int(2)), entries[1]])
    return _nest(_int(n), 16, True), _nest(_int(n + 1), 16, True)


def _file_hash(path):
    digest = hashlib.sha256()
    with path.open('rb') as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b''):
            digest.update(chunk)
    return digest.hexdigest()


def command_pairs(outfile):
    start = time.perf_counter()
    rng = random.Random(PAIRS_SEED)
    print('seeds: corpus=%d pairs=%d' % (CORPUS_SEED, PAIRS_SEED), flush=True)
    lines = set()
    for _, a, b in _must_differ():
        assert not same(decode(a), decode(b))
        lines.add(a.hex() + ' ' + b.hex() + ' D\n')
    n = 0
    while len(lines) < 22000:
        a, b = _pair_values(n, rng)
        # Pair generation uses the independent encoder, then verifies both APIs.
        ea, eb = _reference_encode(a), _reference_encode(b)
        da, db = decode(ea), decode(eb)
        assert same(da, a) and same(db, b)
        assert encode(da) == ea and encode(db) == eb
        relation = 'S' if same(da, db) else 'D'
        assert (ea == eb) == (relation == 'S')
        lines.add(ea.hex() + ' ' + eb.hex() + ' ' + relation + '\n')
        n += 1
    path = Path(outfile)
    header = ('# Q1 deterministic denotation pairs; data lines sorted lexicographically.\n'
              '# S: equal denotations; D: different denotations; both inputs accepted.\n'
              '# Distinct accepted encodings cannot share a value. S includes maps\n'
              '# constructed from different pair orders, which encode identically.\n'
              '# corpus_seed=%d pairs_seed=%d\n' % (CORPUS_SEED, PAIRS_SEED))
    with path.open('w', encoding='ascii', newline='\n') as stream:
        stream.write(header)
        stream.writelines(sorted(lines))
    s_count = sum(line.endswith(' S\n') for line in lines)
    print('pairs main: lines=%d S=%d D=%d sha256=%s' % (
        len(lines), s_count, len(lines) - s_count, _file_hash(path)), flush=True)
    small, counts, _, _, _ = _small_inputs(2, True)
    small.sort()
    assert len(small) == 1086
    hexes = [raw.hex() for raw in small]
    small_path = Path(str(path) + '.small')
    small_count = 0
    with small_path.open('w', encoding='ascii', newline='\n') as stream:
        stream.write(header)
        stream.write('# Every ordered pair of accepted inputs of length 0..2.\n')
        for a in hexes:
            for b in hexes:
                stream.write(a + ' ' + b + (' S\n' if a == b else ' D\n'))
                small_count += 1
    assert small_count == 1179396
    print('pairs small: inputs=%d lines=%d S=%d D=%d sha256=%s' % (
        len(small), small_count, len(small), small_count - len(small), _file_hash(small_path)), flush=True)
    print('pairs PASS elapsed_seconds=%.3f' % (time.perf_counter() - start), flush=True)


def main(argv):
    if argv == ['check']:
        command_check()
    elif argv == ['selftest']:
        command_selftest()
    elif len(argv) == 2 and argv[0] == 'pairs':
        command_pairs(argv[1])
    else:
        raise SystemExit('usage: oracle.py {selftest|check|pairs OUTFILE}')


if __name__ == '__main__':
    main(sys.argv[1:])
