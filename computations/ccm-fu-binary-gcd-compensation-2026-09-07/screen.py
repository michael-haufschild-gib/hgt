"""Frozen binary gcd compensation diagnostic. Execute only on RunPod."""
import csv
import hashlib
import json
import math
import multiprocessing as multiprocessing
from pathlib import Path
import time


def inspect_cutoff(item):
    cutoff, records = item
    components = {int(r['r']): float(r['G_r']) for r in records}
    assert set(components) == set(range(1, cutoff+1))
    totals = {float(r['total_off_diagonal']) for r in records}
    assert len(totals) == 1
    total = totals.pop()
    tolerance = 1e-12*max(1.0, abs(total))
    packets = [dict(r=r, left=components[r], right=components.get(2*r, 0.0),
                    packet=math.fsum([components[r], components.get(2*r, 0.0)]))
               for r in range(1, cutoff+1, 2)]
    reconstruction_error = abs(math.fsum(p['packet'] for p in packets)-total)
    assert reconstruction_error <= tolerance
    failures = [p for p in packets if p['packet'] > tolerance]
    return dict(M=cutoff, total=total, tolerance=tolerance, packets=packets,
                failures=failures, reconstruction_error=reconstruction_error)


def independent_audit(cutoff):
    import mpmath as m
    m.mp.dps = 80
    defect = [m.mpf(0)] + [
        m.fsum(m.log(j) for j in range(1, n+1))
        - sum(n//d for d in range(1, n+1)) + 2*m.euler*n
        for n in range(1, cutoff)]

    def mobius(n):
        sign, p = 1, 2
        while p*p <= n:
            if n % p == 0:
                n //= p
                sign = -sign
                if n % p == 0:
                    return 0
            p += 1
        return -sign if n > 1 else sign

    channels = {d: mobius(d)*m.fsum(
        (m.sqrt(k+1)-m.sqrt(k))*defect[k//d] for k in range(d, cutoff))
                for d in range(1, cutoff+1)}
    components = {r: 2*m.fsum(channels[d]*channels[e]
                  for d in range(1, cutoff+1) for e in range(d+1, cutoff+1)
                  if math.gcd(d, e) == r)
                  for r in range(1, cutoff+1)}
    packets = {r: components[r]+components.get(2*r, m.mpf(0))
               for r in range(1, cutoff+1, 2)}
    source = m.fsum(channels.values())
    diagonal = m.fsum(c*c for c in channels.values())
    total = source**2-diagonal
    assert abs(m.fsum(packets.values())-total) < m.mpf('1e-65')
    assert abs(m.fsum(components.values())-total) < m.mpf('1e-65')
    return dict(M=cutoff, channels={str(d): m.nstr(c, 65) for d, c in channels.items()},
                components={str(r): m.nstr(c, 65) for r, c in components.items()},
                packets={str(r): m.nstr(c, 65) for r, c in packets.items()},
                source=m.nstr(source, 65), diagonal=m.nstr(diagonal, 65),
                total=m.nstr(total, 65))


def main():
    started = time.monotonic()
    source_path = Path('components.csv')
    grouped = {}
    with source_path.open() as handle:
        for row in csv.DictReader(handle):
            grouped.setdefault(int(row['M']), []).append(row)
    assert set(grouped) == set(range(1, 101))
    with multiprocessing.Pool(8) as pool:
        cutoffs = pool.map(inspect_cutoff, sorted(grouped.items()))
    failures = [dict(M=s['M'], **p) for s in cutoffs for p in s['failures']]
    audit = independent_audit(failures[0]['M']) if failures else None
    if audit:
        import mpmath as m
        tol = cutoffs[audit['M']-1]['tolerance']
        for failure in (f for f in failures if f['M'] == audit['M']):
            assert m.mpf(audit['packets'][str(failure['r'])]) > tol
    result = dict(input_sha256=hashlib.sha256(source_path.read_bytes()).hexdigest(),
                  script_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
                  workers=8, cutoff_count=len(cutoffs),
                  packet_count=sum(len(s['packets']) for s in cutoffs),
                  failure_count=len(failures), failures=failures,
                  first_failure_audit=audit, cutoffs=cutoffs,
                  wall_seconds=time.monotonic()-started)
    Path('summary.json').write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps({k: v for k, v in result.items()
                      if k not in ('cutoffs', 'failures', 'first_failure_audit')}, indent=2))
    print('first_failures:', json.dumps(failures[:5]))
    if audit:
        print('first_cutoff_audit:', json.dumps(audit, indent=2))


if __name__ == '__main__':
    main()
