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


def phase_gate(delta_phi, sharpness=3.0, floor=0.05):
    return floor + (1.0 - floor) * np.exp(sharpness * np.cos(delta_phi) - sharpness)


def trace_values(func, sigma, ts, h):
    return np.array([complex(func(complex(float(sigma), float(t)), h)) for t in ts])


def common_components(sigma, ts, h):
    gamma = trace_values(dlog_gamma_factor, sigma, ts, h)
    zeta_part = trace_values(dlog_zeta, sigma, ts, h)
    mask = (
        np.isfinite(gamma.real)
        & np.isfinite(gamma.imag)
        & np.isfinite(zeta_part.real)
        & np.isfinite(zeta_part.imag)
    )
    return gamma[mask], zeta_part[mask]


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


def surrogate_reaches(gamma, zeta_part, reps, seed):
    rng = np.random.default_rng(seed)
    amp = np.abs(zeta_part)
    phase = np.angle(zeta_part)
    out = {"real": [phase_reach(gamma + zeta_part)]}
    out["amplitude_only"] = [phase_reach(gamma + amp)]
    out["constant_phase"] = [phase_reach(gamma + amp * np.exp(1j * np.median(phase)))]
    shuffled = []
    random_phase = []
    for _ in range(reps):
        shuffled.append(phase_reach(gamma + amp * np.exp(1j * rng.permutation(phase))))
        random_phase.append(phase_reach(gamma + amp * np.exp(1j * rng.uniform(-np.pi, np.pi, len(amp)))))
    out["phase_shuffled"] = shuffled
    out["random_phase"] = random_phase
    return out


def summarize(values):
    arr = np.array(values, dtype=float)
    return float(arr.mean()), float(np.quantile(arr, 0.1)), float(np.quantile(arr, 0.9))


def main():
    parser = argparse.ArgumentParser(description="Step 11 phase-surrogate test for hidden prime mode.")
    parser.add_argument("--sigmas", type=float, nargs="*", default=[0.7, 0.8, 0.9, 1.1])
    parser.add_argument("--t-min", type=float, default=14.0)
    parser.add_argument("--t-max", type=float, default=570.0)
    parser.add_argument("--samples", type=int, default=900)
    parser.add_argument("--h", type=float, default=1e-4)
    parser.add_argument("--reps", type=int, default=40)
    parser.add_argument("--seed", type=int, default=2246186626)
    args = parser.parse_args()

    ts = np.linspace(args.t_min, args.t_max, args.samples)
    print("STEP11 hidden-mode metaphor: phase surrogate dependency chain")
    print("dependency tested: hidden selection needs ordered prime phase, not only hidden-component amplitude")
    print("sigma  mode             mean_reach  q10  q90")
    for sigma in args.sigmas:
        gamma, zeta_part = common_components(sigma, ts, args.h)
        reaches = surrogate_reaches(gamma, zeta_part, args.reps, args.seed + int(1000 * sigma))
        for mode in ("real", "amplitude_only", "constant_phase", "phase_shuffled", "random_phase"):
            mean, q10, q90 = summarize(reaches[mode])
            print(f"{sigma:5.2f}  {mode:15s}  {mean:10.2f}  {q10:4.1f}  {q90:4.1f}")


if __name__ == "__main__":
    main()
