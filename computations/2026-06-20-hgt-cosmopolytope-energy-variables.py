import argparse
import math

import mpmath as mp
import numpy as np


def zeta(s):
    return mp.fp.zeta(s)


def dlog_zeta(s, h):
    return (zeta(s + h) - zeta(s - h)) / (2.0 * h * (zeta(s) + 1e-30))


def dlog_gamma_factor(s, h=None):
    return -0.5 * math.log(math.pi) + 0.5 * mp.fp.digamma(s / 2.0)


def dlog_lambda(s, h):
    return dlog_gamma_factor(s) + dlog_zeta(s, h)


def von_mangoldt(n):
    p = 2
    m = n
    prime = None
    exp = 0
    while p * p <= m:
        while m % p == 0:
            prime = p
            exp += 1
            m //= p
        p += 1
    if m > 1:
        if prime is not None:
            return 0.0
        prime = m
        exp = 1
    if prime is None:
        return 0.0
    return math.log(prime)


def dlog_dirichlet_trunc(s, nmax):
    out = 0.0 + 0.0j
    for n in range(2, nmax + 1):
        lam = von_mangoldt(n)
        if lam:
            out += lam * np.exp(-s * math.log(n))
    return out


def dlog_finite_euler(s, h=None, primes=(2, 3, 5, 7, 11, 13, 17, 19, 23, 29)):
    out = 0.0 + 0.0j
    for p in primes:
        q = mp.fp.power(p, -s)
        out += math.log(p) * q / (1.0 - q)
    return out


DLOGS = {
    "zeta": dlog_zeta,
    "lambda": dlog_lambda,
    "gamma-factor": dlog_gamma_factor,
    "finite-euler": dlog_finite_euler,
}


def node_demo():
    rng = np.random.default_rng(20260620)
    energies = rng.uniform(0.2, 4.0, size=(2000, 3))
    e1, e2, y = energies[:, 0], energies[:, 1], energies[:, 2]
    canonical = 1.0 / (e1 * e2 * (e1 + e2 + y))
    times = rng.uniform(-20.0, 20.0, size=2000)
    coord = np.exp(1j * (e1 + e2 + y) * times) * canonical
    print("NODE: cosmological polytope energy-variable positivity")
    print("Constraint: positivity belongs to positive energy variables; coordinate/time samples oscillate.")
    print(f"energy_form_positive_frac={np.mean(canonical > 0):.4f} min={canonical.min():.6g} max={canonical.max():.6g}")
    print(f"time_coordinate_real_positive_frac={np.mean(coord.real > 0):.4f} imag_abs_mean={np.mean(np.abs(coord.imag)):.6g}")


def fit_energy_coeffs(func, sigma, t_min, t_max, samples, nmax, h):
    ts = np.linspace(t_min, t_max, samples, endpoint=False)
    ns = np.arange(2, nmax + 1)
    basis = np.exp(-1j * np.outer(ts, np.log(ns)))
    ys = []
    keep_ts = []
    for t in ts:
        try:
            val = complex(func(complex(float(sigma), float(t)), h))
        except Exception:
            continue
        if np.isfinite(val.real) and np.isfinite(val.imag):
            ys.append(val)
            keep_ts.append(t)
    ys = np.asarray(ys, dtype=complex)
    if len(ys) != len(ts):
        basis = np.exp(-1j * np.outer(np.asarray(keep_ts), np.log(ns)))
    coeff, *_ = np.linalg.lstsq(basis, ys, rcond=None)
    pred = basis @ coeff
    residual = float(np.linalg.norm(pred - ys) / max(np.linalg.norm(ys), 1e-12))
    real_pos = float(np.mean(coeff.real > 0))
    imag_small = float(np.mean(np.abs(coeff.imag) <= 0.25 * (np.abs(coeff.real) + 1e-12)))
    positive_energy_score = float(np.mean((coeff.real > 0) & (np.abs(coeff.imag) <= 0.25 * (np.abs(coeff.real) + 1e-12))))
    return residual, real_pos, imag_small, positive_energy_score


def main():
    parser = argparse.ArgumentParser(description="NODE+HT energy-variable positivity reverse test.")
    parser.add_argument("--sigmas", type=float, nargs="*", default=[1.3, 0.7, 0.3])
    parser.add_argument("--t-min", type=float, default=14.0)
    parser.add_argument("--t-max", type=float, default=184.0)
    parser.add_argument("--samples", type=int, default=180)
    parser.add_argument("--nmax", type=int, default=70)
    parser.add_argument("--functions", default="zeta,lambda,gamma-factor,finite-euler")
    parser.add_argument("--h", type=float, default=1e-4)
    args = parser.parse_args()

    node_demo()
    print("\nSTEP8/9 HT transfer")
    print("Minimal edit: energy variables -> Dirichlet frequencies log n for continuum dlog fields.")
    print("Method #3 reverse: fit coordinate samples back to energy coefficients; test positivity/realness.")
    print("function       sigma   residual   real_pos   imag_small  pos_energy_score")
    for name in [x.strip() for x in args.functions.split(",") if x.strip()]:
        func = DLOGS[name]
        for sigma in args.sigmas:
            residual, real_pos, imag_small, score = fit_energy_coeffs(
                func, sigma, args.t_min, args.t_max, args.samples, args.nmax, args.h
            )
            print(f"{name:13s} {sigma:5.2f}   {residual:8.4f}   {real_pos:8.4f}   {imag_small:9.4f}       {score:8.4f}")


if __name__ == "__main__":
    main()
