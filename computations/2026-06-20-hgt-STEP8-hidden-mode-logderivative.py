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


def phase_gate(delta_phi, sharpness=3.0, floor=0.05):
    return floor + (1.0 - floor) * np.exp(sharpness * np.cos(delta_phi) - sharpness)


def trace_values(func, sigma, ts, h):
    vals = np.array([complex(func(complex(float(sigma), float(t)), h)) for t in ts])
    return vals


def phase_reach(vals, coupling=0.985, threshold=0.12):
    phases = np.unwrap(np.angle(vals))
    deltas = np.diff(phases, prepend=phases[0])
    gates = phase_gate(deltas)
    amp = np.zeros(len(vals), dtype=float)
    activation = np.full(len(vals), np.inf)
    amp[0] = 1.0
    activation[0] = 0.0
    for i in range(1, len(vals)):
        amp[i] = amp[i - 1] * coupling * gates[i]
        if amp[i] > threshold:
            activation[i] = activation[i - 1] + 1.0 / max(amp[i], 1e-12)
        else:
            break
    return int(np.isfinite(activation).sum())


def circular_distance(a, b):
    pa = np.angle(a)
    pb = np.angle(b)
    return float(np.mean(np.abs(np.angle(np.exp(1j * (pa - pb))))))


def analyze(sigma, ts, h):
    gamma = trace_values(dlog_gamma_factor, sigma, ts, h)
    zeta_part = trace_values(dlog_zeta, sigma, ts, h)
    finite = trace_values(dlog_finite_euler, sigma, ts, h)
    mask = (
        np.isfinite(gamma.real)
        & np.isfinite(gamma.imag)
        & np.isfinite(zeta_part.real)
        & np.isfinite(zeta_part.imag)
        & np.isfinite(finite.real)
        & np.isfinite(finite.imag)
    )
    gamma = gamma[mask]
    zeta_part = zeta_part[mask]
    finite = finite[mask]
    completed = gamma + zeta_part
    finite_completed = gamma + finite

    gamma_amp = np.median(np.abs(gamma))
    zeta_amp = np.median(np.abs(zeta_part))
    finite_amp = np.median(np.abs(finite))
    return {
        "gamma_amp": float(gamma_amp),
        "zeta_amp": float(zeta_amp),
        "finite_amp": float(finite_amp),
        "zeta_amp_frac": float(zeta_amp / max(gamma_amp + zeta_amp, 1e-12)),
        "finite_amp_frac": float(finite_amp / max(gamma_amp + finite_amp, 1e-12)),
        "reach_gamma": phase_reach(gamma),
        "reach_zeta": phase_reach(zeta_part),
        "reach_finite": phase_reach(finite),
        "reach_lambda": phase_reach(completed),
        "reach_gamma_plus_finite": phase_reach(finite_completed),
        "phase_dist_lambda_gamma": circular_distance(completed, gamma),
        "phase_dist_lambda_zeta": circular_distance(completed, zeta_part),
        "phase_dist_lambda_finite": circular_distance(completed, finite),
    }


def main():
    parser = argparse.ArgumentParser(description="HT hidden-mode log-derivative decomposition probe.")
    parser.add_argument("--sigmas", type=float, nargs="*", default=[0.3, 0.5, 0.7])
    parser.add_argument("--t-min", type=float, default=14.0)
    parser.add_argument("--t-max", type=float, default=570.0)
    parser.add_argument("--samples", type=int, default=900)
    parser.add_argument("--h", type=float, default=1e-4)
    args = parser.parse_args()

    ts = np.linspace(args.t_min, args.t_max, args.samples)
    print("STEP8 HT hidden-mode probe")
    print("NODE constraint kept: a visually small leading component can select the front behavior")
    print("HT change: components are gamma log-derivative and zeta/prime log-derivative in dlog Lambda")
    print("sigma  amp_gamma  amp_zeta  zeta_frac  reach_G  reach_Z  reach_L  reach_G+finite  dist(L,G)  dist(L,Z)")
    for sigma in args.sigmas:
        row = analyze(sigma, ts, args.h)
        print(
            f"{sigma:5.2f}  {row['gamma_amp']:9.4f}  {row['zeta_amp']:8.4f}"
            f"  {row['zeta_amp_frac']:9.4f}  {row['reach_gamma']:7d}"
            f"  {row['reach_zeta']:7d}  {row['reach_lambda']:7d}"
            f"  {row['reach_gamma_plus_finite']:14d}"
            f"  {row['phase_dist_lambda_gamma']:9.4f}  {row['phase_dist_lambda_zeta']:9.4f}"
        )


if __name__ == "__main__":
    main()
