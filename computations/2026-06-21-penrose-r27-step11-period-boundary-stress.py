#!/usr/bin/env python3
import math
import random

import mpmath as mp
import numpy as np

mp.mp.dps = 35


def first_primes(limit):
    primes = []
    n = 2
    while len(primes) < limit:
        ok = True
        for p in primes:
            if p * p > n:
                break
            if n % p == 0:
                ok = False
                break
        if ok:
            primes.append(n)
        n += 1
    return primes


PRIMES = first_primes(120)


def zeta_logder(s):
    h = mp.mpf("1.0e-5")
    z0 = mp.zeta(s)
    dz = (mp.zeta(s + h) - mp.zeta(s - h)) / (2 * h)
    return complex(dz / z0)


def finite_logder(s, pcount=80, phases=None):
    total = 0j
    for idx, p in enumerate(PRIMES[:pcount]):
        logp = math.log(p)
        phase = 1.0 if phases is None else phases[idx]
        x = phase * complex(mp.e ** (-s * logp))
        total += -logp * x / (1.0 - x)
    return total


def gamma_part(s):
    return complex(0.5 * mp.digamma(s / 2.0) - 0.5 * mp.log(mp.pi))


def xi_logder(s):
    return gamma_part(s) + zeta_logder(s)


def fake_quartet_logder(s, gamma, beta=0.65, strength=0.35):
    rho = [
        mp.mpc(beta, gamma),
        mp.mpc(beta, -gamma),
        mp.mpc(1.0 - beta, gamma),
        mp.mpc(1.0 - beta, -gamma),
    ]
    return complex(strength * sum(1.0 / (s - r) for r in rho))


def lane_pair_matrix(left, right):
    left = np.asarray(left, dtype=complex)
    right = np.asarray(right, dtype=complex)
    m00 = float(np.mean(np.abs(left) ** 2))
    m11 = float(np.mean(np.abs(right) ** 2))
    m01 = float(np.mean(np.real(left * np.conjugate(right))))
    mat = np.array([[m00, m01], [m01, m11]], dtype=float)
    tr = float(np.trace(mat))
    if tr > 1e-12:
        mat = mat / tr
    return mat


def sample_matrix(field, z0, delta=0.14):
    ts = np.linspace(z0 - 0.28, z0 + 0.28, 42)
    rng = random.Random(3000 + int(z0 * 1000))
    phases = [complex(math.cos(rng.random() * 2 * math.pi), math.sin(rng.random() * 2 * math.pi)) for _ in PRIMES]
    lanes = []
    for sigma in [0.5 - delta, 0.5 + delta]:
        vals = []
        for t in ts:
            s = mp.mpc(sigma, t)
            if field == "xi":
                v = xi_logder(s)
            elif field == "bare":
                v = zeta_logder(s)
            elif field == "finite_gamma":
                v = gamma_part(s) + finite_logder(s, pcount=90)
            elif field == "random_gamma":
                v = gamma_part(s) + finite_logder(s, pcount=90, phases=phases)
            elif field == "xi_offline":
                v = xi_logder(s) + fake_quartet_logder(s, z0, beta=0.65, strength=0.35)
            elif field == "xi_offline_strong":
                v = xi_logder(s) + fake_quartet_logder(s, z0, beta=0.70, strength=0.55)
            else:
                raise ValueError(field)
            vals.append(v)
        lanes.append(vals)
    return lane_pair_matrix(lanes[0], lanes[1])


def summarize(field):
    zeros = [float(mp.im(mp.zetazero(n))) for n in [20, 21, 22, 60, 61, 62, 120, 121]]
    mats = [sample_matrix(field, z0) for z0 in zeros]
    avg = sum(mats) / len(mats)
    avg_eigs = np.linalg.eigvalsh(avg)
    sample_eigs = [np.linalg.eigvalsh(m) for m in mats]
    annealed_boundary = float(avg_eigs[0])
    quenched_boundary = float(np.mean([e[0] for e in sample_eigs]))
    worst_boundary = float(np.min([e[0] for e in sample_eigs]))
    gap = annealed_boundary - quenched_boundary
    return field, annealed_boundary, quenched_boundary, worst_boundary, gap


if __name__ == "__main__":
    print("STEP 11 method 15: strengthen the D_infty period-domain annealed/quenched test")
    print("Boundary score is the normalized minimum eigenvalue of the two-lane period-proxy carrier; smaller means closer to a boundary/hyperbolic direction.")
    for field in ["xi", "bare", "finite_gamma", "random_gamma", "xi_offline", "xi_offline_strong"]:
        field, annealed, quenched, worst, gap = summarize(field)
        print(
            f"field={field} annealed_boundary={annealed:.6f} "
            f"quenched_boundary={quenched:.6f} worst_boundary={worst:.6f} "
            f"annealed_minus_quenched={gap:.6f}"
        )
