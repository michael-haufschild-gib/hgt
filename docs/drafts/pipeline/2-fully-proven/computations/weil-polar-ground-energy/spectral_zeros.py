#!/usr/bin/env python3
"""
Fourier zeros of the ground states of the restricted Weil form (full form and pole-vanishing
subspace) versus the imaginary parts of the zeta zeros.

For the ground state f = sum_j c_j P~_j on [-a, a], the Fourier transform in the variable
t = 2 pi xi (so that F(1/2 + i t) = fhat(-t/2pi) in the explicit-formula normalization) is

    fhat(t) = sum_j c_j sqrt((2j+1)/(2a)) * 2a * (-i)^j * j_j(a t)      (spherical Bessel j_j).

For an even ground state only even j occur and fhat is real; for an odd one, purely imaginary.
We list the real zeros t_k of fhat on [0, T] and compare with gamma_k (zeta zeros).
"""
import sys, json, math
from mpmath import mp, mpf, mpmathify, matrix, eigsy, besselj, sqrt, pi, findroot, mpc
from weil_polar_mp import WeilMP
from multiprocessing import Pool

ZETA_ZEROS = [14.134725141734693, 21.022039638771555, 25.010857580145688, 30.424876125859513,
              32.935061587739189, 37.586178158825671, 40.918719012147495, 43.327073280914999,
              48.005150881167159, 49.773832477672302, 52.970321477714460, 56.446247697063394,
              59.347044002602353, 60.831778524609809, 65.112544048081606, 67.079810529494173,
              69.546401711173979, 72.067157674481907, 75.704690699083933, 77.144840068874805]


def spherical_j(n, z):
    if z == 0:
        return mpf(1) if n == 0 else mpf(0)
    return sqrt(pi / (2 * z)) * besselj(n + mpf(1) / 2, z)


def fhat(coeffs, a, t):
    N = len(coeffs)
    val = mpc(0)
    for j in range(N):
        c = coeffs[j]
        if c == 0:
            continue
        val += c * sqrt(mpf(2 * j + 1) / (2 * a)) * 2 * a * (mpc(0, -1) ** j) * spherical_j(j, a * t)
    return val


def real_zeros(func, T, step):
    zs = []
    t = mpf(step)
    prev = func(t)
    while t < T:
        t2 = t + step
        cur = func(t2)
        if prev * cur < 0:
            try:
                z = findroot(func, (t, t2), solver='bisect', tol=1e-20)
                zs.append(float(z))
            except Exception:
                zs.append(float((t + t2) / 2))
        prev, t = cur, t2
    return zs


def lowest_vector(M):
    E, V = eigsy(M)
    k = min(range(len(E)), key=lambda i: E[i])
    return E[k], [V[i, k] for i in range(len(E))]


def run(args):
    a, N, dps, T = args
    mp.dps = dps
    W = WeilMP(a, N)
    A = W.arch_matrix()
    P, cp, cm = W.constrained_projector()
    Pole = matrix(N, N)
    for j in range(N):
        for k in range(N):
            Pole[j, k] = cp[j] * cm[k] + cm[j] * cp[k]
    Q = A + Pole - W.prime_matrix()
    out = {"a": float(a), "N": N, "dps": dps}
    # full form ground state
    e_full, v_full = lowest_vector(Q)
    # constrained ground state (projected form; shift the constraint directions away)
    Mc = P * Q * P + mpf(1000) * (mp.eye(N) - P)
    e_con, v_con = lowest_vector(Mc)
    v_con = [sum(P[i, j] * v_con[j] for j in range(N)) for i in range(N)]   # project into V0
    for label, e, v in (("full", e_full, v_full), ("polar", e_con, v_con)):
        even_mass = sum(v[j] ** 2 for j in range(0, N, 2))
        odd_mass = sum(v[j] ** 2 for j in range(1, N, 2))
        parity = "even" if even_mass > odd_mass else "odd"
        if parity == "even":
            func = lambda t: fhat(v, W.a, t).real
        else:
            func = lambda t: fhat(v, W.a, t).imag
        zs = real_zeros(func, mpf(T), mpf('0.05'))
        out[label] = {"energy": mp.nstr(e, 15), "parity": parity,
                      "even_mass": float(even_mass), "odd_mass": float(odd_mass),
                      "fourier_zeros": zs[:20],
                      "diff_to_zeta": [round(z - g, 4) for z, g in zip(zs, ZETA_ZEROS)]}
    print(json.dumps(out), flush=True)
    return out


if __name__ == "__main__":
    jobs = [(a, N, dps, T) for (a, N, dps, T) in (
        ("0.35", 48, 40, 80), ("0.5", 48, 40, 80), ("0.7", 48, 60, 80), ("0.9", 56, 60, 80),
        ("1.1", 56, 80, 80), ("1.3", 64, 80, 80), ("1.5", 64, 100, 80), ("1.8", 72, 120, 80),
        ("2.1", 80, 140, 80))]
    with Pool(len(jobs)) as pool:
        res = pool.map(run, jobs)
    json.dump(res, open("spectral_zeros.json", "w"), indent=1)
