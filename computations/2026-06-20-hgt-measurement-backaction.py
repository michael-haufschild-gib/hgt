import argparse
import math

import mpmath as mp
import numpy as np


def node_consuming_readout(measure_rate, consuming=True, dt=0.01, steps=3000):
    x = 1.0
    y = 0.0
    m = 0.0
    k_compute = 0.55
    for _ in range(steps):
        if consuming:
            read = measure_rate * x
            x += -read * dt
            y += k_compute * x * dt
            m += read * dt
        else:
            y += k_compute * x * dt
            m += measure_rate * x * dt
    return x, y, m


def zeta(s):
    return mp.fp.zeta(s)


def gamma_factor(s):
    return mp.fp.power(math.pi, -0.5 * s) * mp.fp.gamma(0.5 * s)


def lambda_func(s):
    return gamma_factor(s) * zeta(s)


def finite_euler_func(s, primes=(2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47)):
    out = 1.0 + 0.0j
    for p in primes:
        out *= 1.0 / (1.0 - mp.fp.power(p, -s))
    return out


FUNCS = {
    "lambda": lambda_func,
    "zeta": zeta,
    "gamma-factor": gamma_factor,
    "finite-euler": finite_euler_func,
}


def log_gamma_factor(s):
    return -0.5 * s * math.log(math.pi) + mp.loggamma(0.5 * s)


def log_finite_euler(s, primes=(2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47)):
    out = 0.0 + 0.0j
    for p in primes:
        out += -mp.fp.log(1.0 - mp.fp.power(p, -s))
    return out


def log_func(name, s):
    if name == "gamma-factor":
        return log_gamma_factor(s)
    if name == "lambda":
        return log_gamma_factor(s) + mp.fp.log(zeta(s))
    if name == "zeta":
        return mp.fp.log(zeta(s))
    if name == "finite-euler":
        return log_finite_euler(s)
    raise KeyError(name)


def dlog_fd(name, s, h):
    return (log_func(name, s + h) - log_func(name, s - h)) / (2.0 * h)


def ht_sensitivity(name, sigma, t_min, t_max, samples, h, href):
    vals = []
    ts = np.linspace(t_min, t_max, samples)
    for t in ts:
        s = complex(float(sigma), float(t))
        try:
            a = complex(dlog_fd(name, s, h))
            b = complex(dlog_fd(name, s, href))
        except Exception:
            continue
        if np.isfinite(a.real) and np.isfinite(a.imag) and np.isfinite(b.real) and np.isfinite(b.imag):
            vals.append(abs(math.log1p(abs(a)) - math.log1p(abs(b))))
    if not vals:
        return np.nan, np.nan, 0
    vals = np.asarray(vals)
    return float(np.median(vals)), float(np.quantile(vals, 0.95)), int(len(vals))


def main():
    parser = argparse.ArgumentParser(description="NODE+HT measurement backaction / finite-difference strength.")
    parser.add_argument("--sigmas", type=float, nargs="*", default=[0.3, 0.5, 0.7])
    parser.add_argument("--h-values", type=float, nargs="*", default=[1e-1, 3e-2, 1e-2, 3e-3, 1e-3])
    parser.add_argument("--href", type=float, default=1e-4)
    parser.add_argument("--t-min", type=float, default=14.0)
    parser.add_argument("--t-max", type=float, default=184.0)
    parser.add_argument("--samples", type=int, default=120)
    parser.add_argument("--functions", default="lambda,zeta,gamma-factor,finite-euler")
    args = parser.parse_args()

    print("NODE: measurement can perturb chemical computation")
    print("Subclaims: consuming readout changes the state; stronger readout changes the computation; nonconsuming readout is a control.")
    print("measure_rate  consuming_final_X  consuming_Y  nonconsuming_final_X  nonconsuming_Y")
    for rate in [0.0, 0.02, 0.05, 0.10, 0.20, 0.40]:
        cx, cy, _ = node_consuming_readout(rate, True)
        nx, ny, _ = node_consuming_readout(rate, False)
        print(f"{rate:11.3f}      {cx:10.5f}  {cy:11.5f}          {nx:10.5f}  {ny:13.5f}")

    print("\nSTEP8/9 HT transfer")
    print("Minimal edit: chemical readout strength -> finite-difference measurement strength h on d/ds log f(s).")
    print("Method #1 split: compare h-sensitivity by function and strip location against href.")
    print("function       sigma       h      median_delta   q95_delta   samples")
    for name in [x.strip() for x in args.functions.split(",") if x.strip()]:
        for sigma in args.sigmas:
            for h in args.h_values:
                med, q95, n = ht_sensitivity(name, sigma, args.t_min, args.t_max, args.samples, h, args.href)
                print(f"{name:13s} {sigma:5.2f}  {h:8.4g}   {med:12.6g} {q95:11.6g} {n:9d}")


if __name__ == "__main__":
    main()
