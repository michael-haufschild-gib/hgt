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


def lockin_for_mode(func, mode, noise, t0, t1, samples, amp, h, seed):
    rng = np.random.default_rng(seed)
    phase = np.linspace(0.0, 2.0 * math.pi, samples, endpoint=False)
    ts = np.linspace(t0, t1, samples, endpoint=False)
    drive = np.cos(mode * phase)
    jitter = rng.normal(0.0, noise, size=samples)
    ys = np.empty(samples, dtype=float)
    for i, (t, x, eta) in enumerate(zip(ts, drive, jitter)):
        sigma = 0.5 + amp * x + eta
        try:
            val = complex(func(complex(float(sigma), float(t)), h))
        except Exception:
            ys[i] = np.nan
            continue
        if np.isfinite(val.real) and np.isfinite(val.imag):
            ys[i] = math.log1p(abs(val))
        else:
            ys[i] = np.nan
    mask = np.isfinite(ys)
    if mask.mean() < 0.9:
        return np.nan
    y = ys[mask]
    x = drive[mask]
    y = y - np.mean(y)
    denom = float(np.std(y) * np.std(x))
    if denom <= 1e-14:
        return 0.0
    return float(abs(np.mean(y * x)) / denom)


def scan_function(name, args):
    func = DLOGS[name]
    rows = []
    for mode in args.modes:
        responses = []
        for noise in args.noises:
            vals = [
                lockin_for_mode(
                    func,
                    mode,
                    noise,
                    args.t_min,
                    args.t_max,
                    args.samples,
                    args.amp,
                    args.h,
                    seed + 97 * mode,
                )
                for seed in range(args.seeds)
            ]
            responses.append(float(np.nanmean(vals)))
        best_i = int(np.nanargmax(responses))
        zero = responses[0]
        peak = responses[best_i]
        if best_i == 0:
            action = "suppressed-by-jitter"
        elif peak > max(1.0e-12, 1.10 * zero):
            action = "noise-amplifies-mode"
        else:
            action = "flat/shift-only"
        rows.append((mode, args.noises[best_i], peak, action, responses))
    return rows


def main():
    parser = argparse.ArgumentParser(
        description="STEP8/9 HT transfer of mode-specific stochastic-resonance optima."
    )
    parser.add_argument("--functions", default="lambda,zeta,gamma-factor,finite-euler")
    parser.add_argument("--modes", type=int, nargs="*", default=[1, 2, 3, 5])
    parser.add_argument(
        "--noises",
        type=float,
        nargs="*",
        default=[0.0, 0.002, 0.004, 0.007, 0.011, 0.017, 0.026, 0.039, 0.058, 0.086],
    )
    parser.add_argument("--t-min", type=float, default=14.0)
    parser.add_argument("--t-max", type=float, default=184.0)
    parser.add_argument("--samples", type=int, default=224)
    parser.add_argument("--seeds", type=int, default=7)
    parser.add_argument("--amp", type=float, default=0.045)
    parser.add_argument("--h", type=float, default=1e-4)
    args = parser.parse_args()

    print("STEP8 HT mode/noise transfer")
    print("NODE kept: multiple optimal noise levels for different spatial modes.")
    print("Minimal HT change: bistable field response -> lock-in of log(1+|d/ds log f(s)|)")
    print("on s=1/2 + amp*cos(mode*phase) + Gaussian horizontal jitter + it.")
    print("function       mode  best_jitter  peak_lockin  action                 all_lockins")
    for name in [x.strip() for x in args.functions.split(",") if x.strip()]:
        for mode, best_noise, peak, action, responses in scan_function(name, args):
            packed = ",".join(f"{x:.4f}" for x in responses)
            print(f"{name:13s} {mode:4d}    {best_noise:9.4f}    {peak:10.4f}  {action:20s}  {packed}")


if __name__ == "__main__":
    main()
