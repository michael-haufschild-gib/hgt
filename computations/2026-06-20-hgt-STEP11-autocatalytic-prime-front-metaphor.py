import argparse
import math

import numpy as np
from scipy.special import digamma


def primes_up_to(n):
    sieve = np.ones(n + 1, dtype=bool)
    sieve[:2] = False
    for p in range(2, int(n**0.5) + 1):
        if sieve[p]:
            sieve[p * p : n + 1 : p] = False
    return np.nonzero(sieve)[0].astype(float)


def phase_gate(delta_phi, sharpness=3.0, floor=0.05):
    return floor + (1.0 - floor) * np.exp(sharpness * np.cos(delta_phi) - sharpness)


def gamma_dlog(sigma, ts):
    s = sigma + 1j * ts
    return -0.5 * math.log(math.pi) + 0.5 * digamma(s / 2.0)


def prime_front_dlog(sigma, ts, logs, cutoff, cutoff_sharpness):
    s = sigma + 1j * ts[:, None]
    ratio = logs / math.log(cutoff)
    weights = np.exp(-(ratio ** cutoff_sharpness))
    q = np.exp(-s * logs[None, :])
    terms = weights[None, :] * logs[None, :] * q / (1.0 - q)
    return terms.sum(axis=1)


def phase_gated_reach(dlog_values, coupling=0.985, threshold=0.12):
    phases = np.unwrap(np.angle(dlog_values))
    deltas = np.diff(phases, prepend=phases[0])
    gates = phase_gate(deltas)
    amp = np.zeros(len(phases), dtype=float)
    activation = np.full(len(phases), np.inf)
    amp[0] = 1.0
    activation[0] = 0.0
    for i in range(1, len(phases)):
        amp[i] = amp[i - 1] * coupling * gates[i]
        if amp[i] > threshold:
            activation[i] = activation[i - 1] + 1.0 / max(amp[i], 1e-12)
        else:
            break
    participated = np.isfinite(activation)
    reach = int(participated.sum())
    return {
        "reach": reach,
        "phase_span": float(phases[-1] - phases[0]),
        "mean_gate": float(gates.mean()),
        "median_real_sharpness": float(np.median(np.abs(np.real(dlog_values)))),
    }


def run(args):
    primes = primes_up_to(args.pmax)
    logs = np.log(primes)
    ts = np.linspace(args.t_min, args.t_max, args.samples)
    print("STEP11 wild metaphor: prime-cutoff sharpness as an autocatalytic constraint front")
    print("metaphor: a constraint with a sharper leading edge may propagate differently before asymptotic behavior")
    print(f"pmax={args.pmax}, t=[{args.t_min},{args.t_max}], samples={args.samples}")
    print("cutoff  sharp  sigma  reach  phase_span  mean_gate  med_|Re dlog|")
    for cutoff in args.cutoffs:
        for sharp in args.sharpnesses:
            for sigma in args.sigmas:
                dlog = gamma_dlog(sigma, ts) + prime_front_dlog(sigma, ts, logs, cutoff, sharp)
                row = phase_gated_reach(dlog, coupling=args.coupling, threshold=args.threshold)
                print(
                    f"{cutoff:6.0f}  {sharp:5.1f}  {sigma:5.2f}"
                    f"  {row['reach']:5d}  {row['phase_span']:10.4f}"
                    f"  {row['mean_gate']:9.4f}  {row['median_real_sharpness']:13.4f}"
                )


def main():
    parser = argparse.ArgumentParser(description="Step 11 prime-front metaphor experiment.")
    parser.add_argument("--pmax", type=int, default=12000)
    parser.add_argument("--cutoffs", type=float, nargs="*", default=[80, 300, 1200, 5000])
    parser.add_argument("--sharpnesses", type=float, nargs="*", default=[1, 2, 4, 8, 16])
    parser.add_argument("--sigmas", type=float, nargs="*", default=[0.3, 0.5, 0.7])
    parser.add_argument("--t-min", type=float, default=14.0)
    parser.add_argument("--t-max", type=float, default=570.0)
    parser.add_argument("--samples", type=int, default=420)
    parser.add_argument("--coupling", type=float, default=0.985)
    parser.add_argument("--threshold", type=float, default=0.12)
    args = parser.parse_args()
    run(args)


if __name__ == "__main__":
    main()
