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


def sign_coherence(rows, eps=1e-10):
    pos = neg = zero = 0
    for comb in itertools.combinations(range(len(rows)), 4):
        det = float(np.linalg.det(rows[list(comb), :]))
        if abs(det) <= eps:
            zero += 1
        elif det > 0:
            pos += 1
        else:
            neg += 1
    nz = pos + neg
    if nz == 0:
        return 0.0, pos, neg, zero
    return max(pos, neg) / nz, pos, neg, zero


def make_rows(name, sigmas, t_min, t_max, n, h):
    func = DLOGS[name]
    rows = []
    labels = []
    for sigma in sigmas:
        for j, t in enumerate(np.linspace(t_min, t_max, n)):
            try:
                val = complex(func(complex(float(sigma), float(t)), h))
            except Exception:
                continue
            if not (np.isfinite(val.real) and np.isfinite(val.imag)):
                continue
            labels.append((sigma, j, t, val))
    vals = np.asarray([x[3] for x in labels], dtype=complex)
    ts = np.asarray([x[2] for x in labels], dtype=float)
    lane = np.asarray([2.0 * (x[0] - 0.5) for x in labels], dtype=float)
    rows = np.column_stack(
        [
            np.ones(len(labels)),
            lane,
            (ts - ts.mean()) / max(ts.ptp(), 1e-12),
            np.angle(vals),
        ]
    )
    return rows, labels


def order_indices(labels, order_name):
    if order_name == "two-lane-forward":
        return sorted(range(len(labels)), key=lambda i: (labels[i][0], labels[i][1]))
    if order_name == "fe-folded":
        return sorted(
            range(len(labels)),
            key=lambda i: (labels[i][0], labels[i][1] if labels[i][0] < 0.5 else -labels[i][1]),
        )
    if order_name == "interleaved-pairs":
        return sorted(range(len(labels)), key=lambda i: (labels[i][1], labels[i][0]))
    if order_name == "phase":
        return sorted(range(len(labels)), key=lambda i: np.angle(labels[i][3]))
    if order_name == "random":
        rng = np.random.default_rng(20260620)
        return list(rng.permutation(len(labels)))
    raise ValueError(order_name)


def main():
    parser = argparse.ArgumentParser(description="STEP11 FE-folded cyclic-order attack.")
    parser.add_argument("--sigmas", type=float, nargs="*", default=[0.3, 0.7])
    parser.add_argument("--t-min", type=float, default=14.0)
    parser.add_argument("--t-max", type=float, default=184.0)
    parser.add_argument("--n", type=int, default=10)
    parser.add_argument("--functions", default="lambda,zeta,gamma-factor,finite-euler")
    parser.add_argument("--h", type=float, default=1e-4)
    args = parser.parse_args()

    print("STEP11 positive-geometry metaphor: FE-folded cyclic boundary order")
    print("Method #2 attack-as-false: if FE folding is real, fe-folded order should improve sign coherence for Lambda.")
    print("function       order              coherence  counts")
    for name in [x.strip() for x in args.functions.split(",") if x.strip()]:
        rows, labels = make_rows(name, args.sigmas, args.t_min, args.t_max, args.n, args.h)
        for order in ["two-lane-forward", "fe-folded", "interleaved-pairs", "phase", "random"]:
            idx = order_indices(labels, order)
            coh, pos, neg, zero = sign_coherence(rows[idx])
            print(f"{name:13s} {order:18s} {coh:9.4f}  +{pos}/-{neg}/0{zero}")


if __name__ == "__main__":
    main()
