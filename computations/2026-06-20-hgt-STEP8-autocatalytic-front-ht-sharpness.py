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


def kpp_selected_speed(lam):
    lam = max(float(lam), 1e-6)
    return lam + 1.0 / lam if lam < 1.0 else 2.0


def sharpness_profile(dlog_func, sigma, t_min, t_max, n, h):
    ts = np.linspace(t_min, t_max, n)
    sharp = []
    speeds = []
    for t in ts:
        val = dlog_func(complex(float(sigma), float(t)), h)
        lam = abs(float(np.real(val)))
        if not np.isfinite(lam):
            continue
        sharp.append(lam)
        speeds.append(kpp_selected_speed(lam))
    return np.array(sharp), np.array(speeds)


def summarize(name, sigma, sharp, speeds):
    return {
        "function": name,
        "sigma": sigma,
        "median_lambda": float(np.median(sharp)),
        "p10_lambda": float(np.quantile(sharp, 0.10)),
        "frac_shallow": float(np.mean(sharp < 1.0)),
        "median_speed": float(np.median(speeds)),
        "p90_speed": float(np.quantile(speeds, 0.90)),
    }


def main():
    parser = argparse.ArgumentParser(description="HT continuum KPP leading-edge sharpness transfer.")
    parser.add_argument("--functions", default="lambda,zeta,gamma-factor,finite-euler")
    parser.add_argument("--sigmas", type=float, nargs="*", default=[0.3, 0.5, 0.7])
    parser.add_argument("--t-min", type=float, default=14.0)
    parser.add_argument("--t-max", type=float, default=570.0)
    parser.add_argument("--samples", type=int, default=1200)
    parser.add_argument("--h", type=float, default=1e-4)
    args = parser.parse_args()

    print("STEP8 HT KPP sharpness transfer")
    print("NODE constraint kept: leading-edge steepness selects transient/asymptotic front speed")
    print("HT change: KPP tail lambda -> continuum sigma-sharpness |Re(d/ds log f)|")
    print(f"trace t=[{args.t_min},{args.t_max}], samples={args.samples}")
    print("function      sigma  med_lambda  p10_lambda  frac_lambda<1  med_speed  p90_speed")

    for name in [x.strip() for x in args.functions.split(",") if x.strip()]:
        for sigma in args.sigmas:
            sharp, speeds = sharpness_profile(DLOGS[name], sigma, args.t_min, args.t_max, args.samples, args.h)
            row = summarize(name, sigma, sharp, speeds)
            print(
                f"{name:12s} {sigma:5.2f}  {row['median_lambda']:10.4f}"
                f"  {row['p10_lambda']:10.4f}  {row['frac_shallow']:13.3f}"
                f"  {row['median_speed']:9.4f}  {row['p90_speed']:9.4f}"
            )


if __name__ == "__main__":
    main()
