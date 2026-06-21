import argparse
import itertools
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


def sign_stats(rows, eps=1e-10):
    signs = []
    for comb in itertools.combinations(range(len(rows)), 4):
        det = float(np.linalg.det(rows[list(comb), :]))
        if abs(det) <= eps:
            signs.append(0)
        elif det > 0:
            signs.append(1)
        else:
            signs.append(-1)
    signs = np.asarray(signs, dtype=int)
    nonzero = signs[signs != 0]
    if len(nonzero) == 0:
        return 0.0, 0.0, 1.0, 0, 0, len(signs)
    pos = float(np.mean(nonzero > 0))
    neg = float(np.mean(nonzero < 0))
    coherent = max(pos, neg)
    return coherent, pos, neg, int(np.sum(nonzero > 0)), int(np.sum(nonzero < 0)), int(np.sum(signs == 0))


def moment_curve(n):
    ts = np.linspace(-1.0, 1.0, n)
    return np.column_stack([np.ones(n), ts, ts * ts, ts * ts * ts])


def order_rows(rows, order_name, vals=None):
    n = len(rows)
    if order_name == "natural":
        order = np.arange(n)
    elif order_name == "cyclic-shift":
        order = np.r_[n // 3 : n, : n // 3]
    elif order_name == "adjacent-swap":
        order = np.arange(n)
        order[n // 2 - 1], order[n // 2] = order[n // 2], order[n // 2 - 1]
    elif order_name == "reverse":
        order = np.arange(n - 1, -1, -1)
    elif order_name == "random":
        rng = np.random.default_rng(20260620)
        order = rng.permutation(n)
    elif order_name == "phase" and vals is not None:
        order = np.argsort(np.unwrap(np.angle(vals)))
    elif order_name == "magnitude" and vals is not None:
        order = np.argsort(np.abs(vals))
    else:
        raise ValueError(order_name)
    return rows[order], order


def ht_rows(name, sigma, t_min, t_max, n, h):
    func = DLOGS[name]
    ts = np.linspace(t_min, t_max, n)
    vals = []
    for t in ts:
        try:
            val = complex(func(complex(float(sigma), float(t)), h))
        except Exception:
            val = np.nan + 1j * np.nan
        vals.append(val)
    vals = np.asarray(vals, dtype=complex)
    mask = np.isfinite(vals.real) & np.isfinite(vals.imag)
    vals = vals[mask]
    ts = ts[mask]
    logabs = np.log1p(np.abs(vals))
    rows = np.column_stack(
        [
            np.ones(len(vals)),
            (ts - ts.mean()) / max(ts.ptp(), 1e-12),
            np.real(vals) / (np.std(np.real(vals)) + 1e-12),
            np.imag(vals) / (np.std(np.imag(vals)) + 1e-12),
        ]
    )
    rows[:, 2] += 0.05 * (logabs - logabs.mean()) / (np.std(logabs) + 1e-12)
    return rows, vals


def print_stats(label, rows, vals=None):
    for order_name in ["natural", "cyclic-shift", "adjacent-swap", "reverse", "random", "phase", "magnitude"]:
        if vals is None and order_name in {"phase", "magnitude"}:
            continue
        ordered, _ = order_rows(rows, order_name, vals)
        coherent, pos, neg, npos, nneg, nzero = sign_stats(ordered)
        print(f"{label:18s} {order_name:14s} coherent={coherent:.4f} pos={pos:.4f} neg={neg:.4f} counts=+{npos}/-{nneg}/0{nzero}")


def main():
    parser = argparse.ArgumentParser(description="NODE+HT cyclic-order positivity / reverse-order test.")
    parser.add_argument("--n", type=int, default=16)
    parser.add_argument("--sigma", type=float, default=0.3)
    parser.add_argument("--t-min", type=float, default=14.0)
    parser.add_argument("--t-max", type=float, default=184.0)
    parser.add_argument("--functions", default="lambda,zeta,gamma-factor,finite-euler")
    parser.add_argument("--h", type=float, default=1e-4)
    args = parser.parse_args()

    print("NODE: positive geometry cyclic order")
    print("Constraint: same external data can be sign-coherent in the correct order and defective after non-cyclic permutations.")
    print_stats("moment-curve", moment_curve(args.n))

    print("\nSTEP8/9 HT transfer")
    print("Minimal edit: external data rows -> continuum points from d/ds log f(sigma+it).")
    print("Method #3 reverse: can sign-coherence recover a preferred order from HT data?")
    for name in [x.strip() for x in args.functions.split(",") if x.strip()]:
        rows, vals = ht_rows(name, args.sigma, args.t_min, args.t_max, args.n, args.h)
        print_stats(name, rows, vals)


if __name__ == "__main__":
    main()
