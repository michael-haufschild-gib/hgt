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


def dlog_finite_euler(s, h=None, primes=(2, 3, 5, 7, 11, 13, 17, 19, 23, 29)):
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


def field(dlog_func, sigmas, ts, h):
    out = np.empty((len(sigmas), len(ts)), dtype=float)
    for i, sigma in enumerate(sigmas):
        for j, t in enumerate(ts):
            val = complex(dlog_func(complex(float(sigma), float(t)), h))
            out[i, j] = math.log1p(abs(val)) if np.isfinite(val.real) and np.isfinite(val.imag) else np.nan
    return out


def summarize(arr, sigmas, boundary_width):
    center_idx = int(np.argmin(np.abs(sigmas - 0.5)))
    boundary = np.r_[0:boundary_width, len(sigmas) - boundary_width : len(sigmas)]
    center = arr[center_idx : center_idx + 1, :]
    band = arr[boundary, :]
    thresh = np.nanquantile(arr, 0.75)
    return {
        "center_peak": float(np.nanquantile(center, 0.95)),
        "boundary_peak": float(np.nanquantile(band, 0.95)),
        "center_hot_frac": float(np.nanmean(center > thresh)),
        "boundary_hot_frac": float(np.nanmean(band > thresh)),
        "boundary_over_center": float(np.nanquantile(band, 0.95) / max(np.nanquantile(center, 0.95), 1e-12)),
    }


def main():
    parser = argparse.ArgumentParser(description="HT strip boundary heat-loss analogue.")
    parser.add_argument("--functions", default="lambda,zeta,gamma-factor,finite-euler")
    parser.add_argument("--sigma-min", type=float, default=0.1)
    parser.add_argument("--sigma-max", type=float, default=0.9)
    parser.add_argument("--sigma-count", type=int, default=25)
    parser.add_argument("--boundary-width", type=int, default=3)
    parser.add_argument("--t-min", type=float, default=14.0)
    parser.add_argument("--t-max", type=float, default=570.0)
    parser.add_argument("--samples", type=int, default=420)
    parser.add_argument("--h", type=float, default=1e-4)
    args = parser.parse_args()

    sigmas = np.linspace(args.sigma_min, args.sigma_max, args.sigma_count)
    ts = np.linspace(args.t_min, args.t_max, args.samples)
    print("STEP8 HT strip boundary analogue")
    print("NODE constraint kept: compare centerline peak vs boundary-band peak and hot fraction")
    print("HT change: thermal field -> log(1+|d/ds log f(s)|) on a complex strip")
    print("function      center_peak  boundary_peak  boundary/center  center_hot  boundary_hot")
    for name in [x.strip() for x in args.functions.split(",") if x.strip()]:
        arr = field(DLOGS[name], sigmas, ts, args.h)
        row = summarize(arr, sigmas, args.boundary_width)
        print(
            f"{name:12s}  {row['center_peak']:11.4f}  {row['boundary_peak']:13.4f}"
            f"  {row['boundary_over_center']:15.4f}  {row['center_hot_frac']:10.4f}"
            f"  {row['boundary_hot_frac']:12.4f}"
        )


if __name__ == "__main__":
    main()
