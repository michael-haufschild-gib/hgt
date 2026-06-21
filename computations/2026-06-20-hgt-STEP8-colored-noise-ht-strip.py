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


def dlog_finite_euler(s, h=None, primes=(2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47)):
    out = 0.0 + 0.0j
    for p in primes:
        q = mp.fp.power(p, -s)
        out += math.log(p) * q / (1.0 - q)
    return out


DLOGS = {
    "lambda": dlog_lambda,
    "zeta": dlog_zeta,
    "gamma-factor": dlog_gamma_factor,
    "finite-euler": dlog_finite_euler,
}


def colored_noise(rng, samples, tau, sigma):
    if tau <= 0:
        return rng.normal(0.0, sigma, size=samples)
    rho = math.exp(-1.0 / tau)
    eps = rng.normal(0.0, sigma * math.sqrt(1.0 - rho * rho), size=samples)
    out = np.empty(samples, dtype=float)
    out[0] = rng.normal(0.0, sigma)
    for i in range(1, samples):
        out[i] = rho * out[i - 1] + eps[i]
    return out


def eval_dlog(func, sigma, t, h):
    try:
        val = complex(func(complex(float(sigma), float(t)), h))
    except Exception:
        return None
    if not (np.isfinite(val.real) and np.isfinite(val.imag)):
        return None
    return val


def run_tau(func, tau, seed, args):
    rng = np.random.default_rng(seed)
    offsets = colored_noise(rng, args.samples, tau, args.sigma_noise)
    ts = np.linspace(args.t_min, args.t_max, args.samples, endpoint=False)
    rough = []
    mirror = []
    for u, t in zip(offsets, ts):
        u = float(np.clip(u, -args.clip, args.clip))
        vp = eval_dlog(func, 0.5 + abs(u), t, args.h)
        vm = eval_dlog(func, 0.5 - abs(u), t, args.h)
        if vp is None or vm is None:
            continue
        rough.append(math.log1p(abs(vp)) + math.log1p(abs(vm)))
        mirror.append(abs(abs(vp) - abs(vm)) / (abs(vp) + abs(vm) + 1e-30))
    if len(rough) < 0.85 * args.samples:
        return np.nan, np.nan
    return float(np.mean(rough)), float(np.mean(mirror))


def main():
    parser = argparse.ArgumentParser(description="STEP8 HT colored-noise horizontal-drift transfer.")
    parser.add_argument("--functions", default="lambda,zeta,gamma-factor,finite-euler")
    parser.add_argument("--taus", type=float, nargs="*", default=[0, 1, 2, 4, 8, 16, 32, 64])
    parser.add_argument("--t-min", type=float, default=14.0)
    parser.add_argument("--t-max", type=float, default=184.0)
    parser.add_argument("--samples", type=int, default=180)
    parser.add_argument("--seeds", type=int, default=9)
    parser.add_argument("--sigma-noise", type=float, default=0.11)
    parser.add_argument("--clip", type=float, default=0.42)
    parser.add_argument("--h", type=float, default=1e-4)
    args = parser.parse_args()

    print("STEP8 HT colored-noise strip transfer")
    print("NODE kept: low-frequency noise may escape shallow basins but induce slow drift.")
    print("HT change: colored horizontal drift around Re(s)=1/2; measure roughness and mirror imbalance of dlog fields.")
    print("function       tau   roughness   mirror_imbalance")
    for name in [x.strip() for x in args.functions.split(",") if x.strip()]:
        func = DLOGS[name]
        for tau in args.taus:
            vals = [run_tau(func, tau, 5000 + seed, args) for seed in range(args.seeds)]
            rough = float(np.nanmean([v[0] for v in vals]))
            mirror = float(np.nanmean([v[1] for v in vals]))
            print(f"{name:13s} {tau:5.1f}   {rough:9.5f}       {mirror:9.5f}")


if __name__ == "__main__":
    main()
