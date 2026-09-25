"""Frozen complete-prime coarea-envelope diagnostic. Execute only on RunPod."""
import hashlib
import json
import math
import multiprocessing as mp
from pathlib import Path
import signal
import time

import numpy as np
from source_screen import source


def quantities(F, A):
    active = A > 0
    J = float(np.sum(F[active]**2 / A[active]))
    largest = float(np.max(A))
    return J, largest, J*largest, float(np.dot(F, F))


def cutoff(M):
    primes, factors, coeff = source(M)
    F = np.zeros(M)
    for d, value in coeff:
        F[d] = value
    A = np.abs(F)
    original_sum = math.fsum(v for _, v in coeff)
    original_mass = math.fsum(abs(v) for _, v in coeff)
    J, largest, B, Q = quantities(F, A)
    initial = dict(J=J, largest=largest, envelope=B, raw_energy=Q)
    initial_B = B
    remaining = {p: np.arange(p, M, p) for p in primes}
    path = []
    P = []
    first_trap = None
    while remaining:
        candidates = []
        for q, all_children in remaining.items():
            child = all_children[A[all_children] > 0]
            base = child // q
            a, b = A[base], A[child]
            x, y = F[base], F[child]
            assert np.all(a > 0)
            assert np.all(base % q != 0)
            loss = float(np.sum((b*x-a*y)**2/(a*b*(a+b))))
            new_largest = max(largest, float(np.max(a+b, initial=0)))
            next_B = new_largest*(J-loss)
            candidates.append((next_B, q, loss, new_largest))
        candidates.sort()
        next_B, q, loss, new_largest = candidates[0]
        gain = next_B-B
        strict_trap = gain > 1e-10*max(1, initial_B)
        if strict_trap and first_trap is None:
            first_trap = dict(step=len(P), P=P.copy(), before=dict(J=J,largest=largest,
                envelope=B,raw_energy=Q), candidates=[dict(prime=p,envelope=z,
                gain=z-B,loss=l,largest=m) for z,p,l,m in candidates])
        record = dict(step=len(P),prime=q,envelope_before=B,raw_energy_before=Q,
            conditional_J_before=J,largest_mass_before=largest,gain=gain,
            variance_loss=loss,strict_trap=strict_trap,
            next_choice_margin=(candidates[1][0]-next_B) if len(candidates)>1 else None)
        child = remaining[q][A[remaining[q]] > 0]
        base = child//q
        F[base] += F[child]
        A[base] += A[child]
        F[child] = 0
        A[child] = 0
        J, largest, B, Q = quantities(F,A)
        assert abs(B-next_B) <= 1e-9*max(1,initial_B)
        assert abs(largest-new_largest) <= 1e-10*max(1,largest)
        record.update(envelope_after=B, raw_energy_after=Q,
                      conditional_J_after=J,largest_mass_after=largest)
        path.append(record)
        P.append(q)
        del remaining[q]
    assert abs(F[1]-original_sum) <= 1e-10*max(1,original_mass)
    assert abs(A[1]-original_mass) <= 1e-10*max(1,original_mass)
    assert np.count_nonzero(A)==1
    assert abs(B-original_sum**2) <= 1e-9*max(1,initial_B)
    return dict(M=M,initial=initial,signed_sum=original_sum,absolute_mass=original_mass,
        steps=len(path),first_trap=first_trap,path=path,
        peak_ratio=max([initial_B]+[s['envelope_after'] for s in path])/initial_B,
        positive_steps=sum(s['strict_trap'] for s in path),terminal=B)


def deadline(*_):
    raise TimeoutError('Frozen90seconddeadline')


def init():
    signal.signal(signal.SIGALRM,signal.SIG_DFL)
    signal.signal(signal.SIGTERM,signal.SIG_DFL)


if __name__ == '__main__':
    signal.signal(signal.SIGALRM,deadline)
    signal.signal(signal.SIGTERM,deadline)
    signal.alarm(90)
    started=time.monotonic()
    with mp.Pool(4,initializer=init) as pool:
        results=pool.map(cutoff,[512,1024,2048,8192])
    output=dict(question='Every next-prime minimum of the complete coarea mass envelope is nonincreasing',
        workers=4,seconds=time.monotonic()-started,
        script_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        source_sha256=hashlib.sha256(Path('source_screen.py').read_bytes()).hexdigest(),results=results)
    Path('summary.json').write_text(json.dumps(output,indent=2))
    print(json.dumps({k:v for k,v in output.items() if k!='results'}))
    print(json.dumps([dict(M=r['M'],steps=r['steps'],peak_ratio=r['peak_ratio'],
        positive_steps=r['positive_steps'],first_trap_step=None if r['first_trap'] is None
        else r['first_trap']['step']) for r in results]))
