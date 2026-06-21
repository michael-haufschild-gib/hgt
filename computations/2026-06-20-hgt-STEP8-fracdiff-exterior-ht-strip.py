#!/usr/bin/env python3
"""THE-MACHINE Step 8/9 HT transfer.

NODE: fractional diffusion discretizations can accidentally approximate a
different bounded-domain operator by omitting exterior interactions.

Minimal HT edit: keep the nonlocal regional-vs-exterior operator test, replace
the thermal profile by a continuum differential strip profile

    g_f(t) = log(1 + |d/ds log f(sigma + i t)|).

Step-9 method #7 (strip to essentials): no heat equation solve here; only the
operator-definition mismatch is measured.
"""

import argparse
import math

import mpmath as mp
import numpy as np


PRIMES_20 = (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71)


def zeta(s):
    return mp.fp.zeta(s)


def dlog_zeta(s, h=1e-4):
    z0 = zeta(s)
    return (zeta(s + h) - zeta(s - h)) / (2.0 * h * (z0 + 1e-300))


def dlog_gamma_factor(s, h=None):
    return -0.5 * math.log(math.pi) + 0.5 * mp.fp.digamma(s / 2.0)


def dlog_lambda(s, h=1e-4):
    return dlog_gamma_factor(s) + dlog_zeta(s, h)


def dlog_finite_euler(s, h=None, primes=PRIMES_20):
    out = 0.0 + 0.0j
    for p in primes:
        q = mp.fp.power(p, -s)
        out -= math.log(p) * q / (1.0 - q)
    return out


def dlog_sine(s, h=None):
    return math.pi / mp.fp.tan(math.pi * s)


DLOGS = {
    "lambda": dlog_lambda,
    "zeta": dlog_zeta,
    "gamma-factor": dlog_gamma_factor,
    "finite-euler": dlog_finite_euler,
    "sine": dlog_sine,
}


def profile(name, sigma, ts, h):
    f = DLOGS[name]
    vals = np.empty(len(ts), dtype=float)
    for k, t in enumerate(ts):
        val = complex(f(complex(float(sigma), float(t)), h))
        vals[k] = math.log1p(abs(val)) if np.isfinite(val.real) and np.isfinite(val.imag) else np.nan
    finite = np.isfinite(vals)
    if not finite.all():
        med = float(np.nanmedian(vals))
        vals[~finite] = med
    return vals


def frac_operator_values(g, ts, inside_mask, frac):
    """Return regional, actual-exterior, and zero-exterior operators on inside points."""
    inside_idx = np.flatnonzero(inside_mask)
    outside_idx = np.flatnonzero(~inside_mask)
    h = float(np.median(np.diff(ts)))
    power = 1.0 + 2.0 * frac
    reg = np.zeros(len(inside_idx), dtype=float)
    actual = np.zeros(len(inside_idx), dtype=float)
    zero = np.zeros(len(inside_idx), dtype=float)
    for out_i, i in enumerate(inside_idx):
        dx_inside = np.abs(ts[i] - ts[inside_idx])
        good = dx_inside > 0
        weights_inside = h / np.maximum(dx_inside[good], 1e-300) ** power
        reg[out_i] = np.sum((g[i] - g[inside_idx][good]) * weights_inside)
        dx_out = np.abs(ts[i] - ts[outside_idx])
        weights_out = h / np.maximum(dx_out, 1e-300) ** power
        exterior_actual = np.sum((g[i] - g[outside_idx]) * weights_out)
        exterior_zero = np.sum(g[i] * weights_out)
        actual[out_i] = reg[out_i] + exterior_actual
        zero[out_i] = reg[out_i] + exterior_zero
    return reg, actual, zero


def summarize(reg, actual, zero):
    eps = 1e-30
    exterior = actual - reg
    zero_extra = zero - reg
    return {
        "actual_over_regional": float(np.linalg.norm(actual) / (np.linalg.norm(reg) + eps)),
        "exterior_share": float(np.linalg.norm(exterior) / (np.linalg.norm(actual) + eps)),
        "zero_error": float(np.linalg.norm(zero - actual) / (np.linalg.norm(actual) + eps)),
        "zero_actual_cos": float(
            np.dot(zero_extra, exterior) / ((np.linalg.norm(zero_extra) + eps) * (np.linalg.norm(exterior) + eps))
        ),
        "mean_exterior": float(np.mean(exterior)),
        "max_abs_exterior": float(np.max(np.abs(exterior))),
    }


def run_case(name, sigma, t_min, t_max, samples, buffer, frac, hdiff):
    dt = (t_max - t_min) / (samples - 1)
    total = samples + 2 * buffer
    ts = t_min - buffer * dt + np.arange(total) * dt
    inside_mask = np.zeros(total, dtype=bool)
    inside_mask[buffer : buffer + samples] = True
    g = profile(name, sigma, ts, hdiff)
    reg, actual, zero = frac_operator_values(g, ts, inside_mask, frac)
    row = summarize(reg, actual, zero)
    row.update({"name": name, "sigma": sigma, "window": f"[{t_min:g},{t_max:g}]", "frac": frac})
    return row


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--functions", default="lambda,zeta,gamma-factor,finite-euler,sine")
    parser.add_argument("--sigmas", default="0.3,0.5,0.7")
    parser.add_argument("--windows", default="14:84,100:170,500:570")
    parser.add_argument("--samples", type=int, default=100)
    parser.add_argument("--buffer", type=int, default=30)
    parser.add_argument("--frac", type=float, default=0.65)
    parser.add_argument("--hdiff", type=float, default=1e-4)
    args = parser.parse_args()

    names = [x.strip() for x in args.functions.split(",") if x.strip()]
    sigmas = [float(x) for x in args.sigmas.split(",")]
    windows = []
    for item in args.windows.split(","):
        a, b = item.split(":")
        windows.append((float(a), float(b)))

    print("STEP8/9 fractional exterior HT strip probe")
    print("method=7 strip-to-essentials; field=log(1+|dlog f|)")
    print("name sigma window actual/reg exterior_share zero_error zero_cos mean_ext max_abs_ext")
    for t_min, t_max in windows:
        for sigma in sigmas:
            for name in names:
                row = run_case(name, sigma, t_min, t_max, args.samples, args.buffer, args.frac, args.hdiff)
                print(
                    f"{row['name']:12s} {row['sigma']:.1f} {row['window']:9s}"
                    f" {row['actual_over_regional']:.6g} {row['exterior_share']:.6g}"
                    f" {row['zero_error']:.6g} {row['zero_actual_cos']:.6g}"
                    f" {row['mean_exterior']:.6g} {row['max_abs_exterior']:.6g}"
                )


if __name__ == "__main__":
    main()
