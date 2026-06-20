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


def dlog_finite_euler(s, h=None, primes=(2, 3, 5, 7, 11, 13, 17, 19, 23, 29)):
    out = 0.0 + 0.0j
    for p in primes:
        q = mp.fp.power(p, -s)
        out += math.log(p) * q / (1.0 - q)
    return out


def component_fields(sigmas, ts, h, prime_kind):
    gamma = np.empty((len(sigmas), len(ts)), dtype=complex)
    prime = np.empty_like(gamma)
    prime_func = dlog_zeta if prime_kind == "zeta" else dlog_finite_euler
    for i, sigma in enumerate(sigmas):
        for j, t in enumerate(ts):
            s = complex(float(sigma), float(t))
            gamma[i, j] = complex(dlog_gamma_factor(s, h))
            prime[i, j] = complex(prime_func(s, h))
    mask = np.isfinite(gamma.real) & np.isfinite(gamma.imag) & np.isfinite(prime.real) & np.isfinite(prime.imag)
    gamma = np.where(mask, gamma, np.nan + 1j * np.nan)
    prime = np.where(mask, prime, np.nan + 1j * np.nan)
    return gamma, prime


def classify_ratio(field, sigmas, boundary_width):
    heat = np.log1p(np.abs(field))
    center_idx = int(np.argmin(np.abs(sigmas - 0.5)))
    boundary = np.r_[0:boundary_width, len(sigmas) - boundary_width : len(sigmas)]
    center_peak = np.nanquantile(heat[center_idx : center_idx + 1, :], 0.95)
    boundary_peak = np.nanquantile(heat[boundary, :], 0.95)
    ratio = float(boundary_peak / max(center_peak, 1e-12))
    if ratio < 0.85:
        cls = "boundary-cooled"
    elif ratio > 1.15:
        cls = "boundary-hot"
    else:
        cls = "neutral"
    return ratio, cls


def main():
    parser = argparse.ArgumentParser(description="Step 11 boundary-case classifier for completion strength.")
    parser.add_argument("--prime-kind", choices=["zeta", "finite"], default="zeta")
    parser.add_argument("--betas", type=float, nargs="*", default=[0, 0.25, 0.5, 0.75, 1, 1.5, 2])
    parser.add_argument("--sigma-min", type=float, default=0.1)
    parser.add_argument("--sigma-max", type=float, default=0.9)
    parser.add_argument("--sigma-count", type=int, default=31)
    parser.add_argument("--boundary-width", type=int, default=3)
    parser.add_argument("--t-min", type=float, default=14.0)
    parser.add_argument("--t-max", type=float, default=570.0)
    parser.add_argument("--samples", type=int, default=360)
    parser.add_argument("--h", type=float, default=1e-4)
    args = parser.parse_args()

    sigmas = np.linspace(args.sigma_min, args.sigma_max, args.sigma_count)
    ts = np.linspace(args.t_min, args.t_max, args.samples)
    gamma, prime = component_fields(sigmas, ts, args.h, args.prime_kind)
    print("STEP11 boundary-case classification for beta-completion family")
    print(f"prime_kind={args.prime_kind}; field = beta*Gamma_dlog + prime_dlog")
    print("beta   boundary/center  class")
    for beta in args.betas:
        ratio, cls = classify_ratio(beta * gamma + prime, sigmas, args.boundary_width)
        print(f"{beta:5.2f}      {ratio:9.4f}  {cls}")


if __name__ == "__main__":
    main()
