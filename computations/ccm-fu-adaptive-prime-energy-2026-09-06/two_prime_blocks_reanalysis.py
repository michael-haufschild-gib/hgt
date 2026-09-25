"""Frozen two-prime cofactor-block diagnostic; saved energies only."""
import csv
import hashlib
import itertools
import json
import math
from collections import defaultdict
from pathlib import Path

BASE = Path(__file__).resolve().parent
source = BASE / 'subset-states.csv'
tables = defaultdict(dict)
with source.open() as handle:
    for row in csv.DictReader(handle):
        tables[int(row['M'])][int(row['mask'])] = float(row['energy'])
first_failure = None
failures = []
blocks = pairs = 0
max_reconstruction_error = 0.0
ratio_pairs = 0
ratio_failures = []
max_ratio = None
for cutoff, energies in sorted(tables.items()):
    primes = [p for p in range(2, cutoff)
              if all(p % d for d in range(2, math.isqrt(p) + 1))]
    if len(primes) < 2:
        continue
    late_i = next(i for i, p in reversed(list(enumerate(primes))) if 2*p > cutoff)
    bit = 1 << late_i
    cp = -(math.sqrt(cutoff)-math.sqrt(primes[late_i]))*(2*0.5772156649015328606065120900824-1)
    signed = []
    for mask in range(len(energies)):
        if mask & bit:
            signed.append((energies[mask]-energies[mask ^ bit])/(2*cp)+cp)
        else:
            signed.append((energies[mask | bit]-energies[mask])/(2*cp))
    for i in range(len(primes)):
        for mask in range(len(signed)):
            if mask >> i & 1:
                signed[mask] -= signed[mask ^ (1 << i)]
    unsigned = {}
    for mask, value in enumerate(signed):
        d = math.prod(p for i, p in enumerate(primes) if mask >> i & 1)
        if d < cutoff:
            unsigned[d] = (-1 if bin(mask).count('1') % 2 else 1)*value
    tolerance = 1e-12*max(1, energies[0])
    for p in primes:
        for d, value in sorted(unsigned.items()):
            if d % p == 0 or p*d >= cutoff:
                continue
            child = unsigned[p*d]
            ratio_pairs += 1
            witness = dict(M=cutoff, p=p, d=d, parent=value, child=child)
            if child > 2*value+tolerance:
                ratio_failures.append(witness)
            if value > tolerance and (max_ratio is None or child/value > max_ratio['ratio']):
                max_ratio = dict(witness, ratio=child/value)
    for i, j in itertools.combinations(range(len(primes)), 2):
        p, q = primes[i], primes[j]
        pair_final = []
        pair_initial = []
        for d in sorted(unsigned):
            if d % p == 0 or d % q == 0:
                continue
            a, b, c, e = [unsigned.get(n, 0.0) for n in (d, p*d, q*d, p*q*d)]
            initial = math.fsum(x*x for x in (a, b, c, e))
            final = (a-b-c+e)**2
            pair_initial.append(initial)
            pair_final.append(final)
            blocks += 1
            if final > initial+tolerance:
                witness = dict(M=cutoff, p=p, q=q, d=d, coefficients=[a,b,c,e],
                               initial=initial, final=final, excess=final-initial)
                failures.append(witness)
                if first_failure is None:
                    first_failure = witness
        pairs += 1
        error = max(abs(math.fsum(pair_initial)-energies[0]),
                    abs(math.fsum(pair_final)-energies[(1 << i) | (1 << j)]))
        max_reconstruction_error = max(max_reconstruction_error, error)
        assert error <= tolerance
summary = dict(question='Every original two-prime cofactor block contracts at every stored cutoff through32?',
               input_sha256=hashlib.sha256(source.read_bytes()).hexdigest(),
               tolerance='1e-12*max(1,original_energy)', pairs=pairs, blocks=blocks,
               failing_blocks=len(failures), first_failure=first_failure,
               max_reconstruction_error=max_reconstruction_error, failures=failures,
               ratio_pairs=ratio_pairs, ratio_failures=ratio_failures, max_ratio=max_ratio)
(BASE / 'two-prime-blocks-reanalysis.json').write_text(json.dumps(summary, indent=2)+'\n')
print(json.dumps({k:v for k,v in summary.items() if k != 'failures'}, indent=2))
