"""Frozen geometric-defect reserve diagnostic from stored energies only."""
import csv
import hashlib
import json
import math
from collections import defaultdict
from pathlib import Path

BASE = Path(__file__).resolve().parent
source = BASE / 'subset-states.csv'
rows = defaultdict(dict)
with source.open() as handle:
    for row in csv.DictReader(handle):
        rows[int(row['M'])][int(row['mask'])] = float(row['energy'])
D1 = 2 * 0.5772156649015328606065120900824 - 1
max_head_error = max_energy_error = max_anchor_error = max_outside_coefficient = 0.0
weak_first_failure = tight_first_failure = None
weak_failures = tight_failures = states = 0
results = []
for cutoff, energy in sorted(rows.items()):
    primes = [p for p in range(2, cutoff) if all(p % d for d in range(2, math.isqrt(p) + 1))]
    late = [i for i, p in enumerate(primes) if 2 * p > cutoff]
    count = len(energy)
    tol = 1e-12 * max(1, energy[0])
    heads = {}
    for mask, value in energy.items():
        anchors = []
        for i in late:
            bit = 1 << i
            cp = -(math.sqrt(cutoff) - math.sqrt(primes[i])) * D1
            if mask & bit:
                anchors.append((value - energy[mask ^ bit]) / (2 * cp) + cp)
            else:
                anchors.append((energy[mask | bit] - value) / (2 * cp))
        if anchors:
            heads[mask] = anchors[-1]
            max_anchor_error = max(max_anchor_error, max(anchors) - min(anchors))
        else:
            assert count == 1
            heads[mask] = math.sqrt(value)
    coefficients = [heads[mask] for mask in range(count)]
    for i in range(len(primes)):
        bit = 1 << i
        for mask in range(count):
            if mask & bit:
                coefficients[mask] -= coefficients[mask ^ bit]
    support = []
    for label, value in enumerate(coefficients):
        integer = math.prod(p for i, p in enumerate(primes) if label >> i & 1)
        if integer < cutoff:
            support.append((label, value))
        else:
            max_outside_coefficient = max(max_outside_coefficient, abs(value))
    certificate = {}
    local_states = []
    for mask in range(count):
        fibres = defaultdict(list)
        for label, value in support:
            fibres[label & ~mask].append(value)
        grouped = {label: math.fsum(values) for label, values in fibres.items()}
        good = math.fsum(max((-1 if bin(label).count('1') % 2 else 1) * value, 0) ** 2
                         for label, value in grouped.items())
        defect = math.fsum(max(-(-1 if bin(label).count('1') % 2 else 1) * value, 0) ** 2
                           for label, value in grouped.items())
        e_error = abs(good + defect - energy[mask])
        h_error = abs(grouped.get(0, 0) - heads[mask])
        max_energy_error = max(max_energy_error, e_error)
        max_head_error = max(max_head_error, h_error)
        assert e_error <= tol and h_error <= tol
        upper = energy[mask] + 2 * math.sqrt(good * defect)
        certificate[mask] = upper <= energy[0] + tol
        state = {'M': cutoff, 'mask': mask, 'P': [p for i, p in enumerate(primes) if mask >> i & 1],
                 'energy': energy[mask], 'initial_energy': energy[0], 'good': good, 'defect': defect,
                 'geometric_upper': upper}
        states += 1
        if not certificate[mask]:
            tight_failures += 1
            if tight_first_failure is None:
                tight_first_failure = state
        if bin(mask).count('1') == 1:
            weak = energy[mask] + 2 * math.sqrt(energy[0] * defect)
            if weak > energy[0] + tol:
                weak_failures += 1
                if weak_first_failure is None:
                    weak_first_failure = dict(state, weaker_upper=weak)
        local_states.append(state)
    paths = {0: []}
    for mask in range(1, count):
        for i, prime in enumerate(primes):
            bit = 1 << i
            if mask & bit and mask ^ bit in paths and certificate[mask ^ bit]:
                paths[mask] = paths[mask ^ bit] + [prime]
                break
    results.append({'M': cutoff, 'complete_certificate_path': paths.get(count - 1),
                    'certified_states': sum(certificate.values()), 'states': local_states})
summary = {'question': 'Complete paths under Q+2sqrt(GD)<=Q_initial; also every first-prime weaker reserve.',
           'method': 'Stored-energy heads, finite subset inversion, exact squarefree-support regrouping.',
           'tolerance': '1e-12*max(1,initial_energy)',
           'input_sha256': hashlib.sha256(source.read_bytes()).hexdigest(),
           'states': states, 'tight_failing_states': tight_failures, 'first_tight_failure': tight_first_failure,
           'weak_failing_singletons': weak_failures, 'first_weak_failure': weak_first_failure,
           'first_path_failure': next((r['M'] for r in results if r['complete_certificate_path'] is None), None),
           'max_reconstructed_energy_error': max_energy_error, 'max_reconstructed_head_error': max_head_error,
           'max_late_anchor_spread': max_anchor_error, 'max_outside_source_coefficient': max_outside_coefficient,
           'results': results}
(BASE / 'defect-reserve-reanalysis.json').write_text(json.dumps(summary, indent=2) + '\n')
print(json.dumps({k: v for k, v in summary.items() if k != 'results'}, indent=2))
