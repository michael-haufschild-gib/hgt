import argparse
import math

import mpmath as mp
import numpy as np


def zeta(s):
    return mp.fp.zeta(s)


def gamma_factor(s):
    return mp.fp.power(mp.pi, -s / 2) * mp.fp.gamma(s / 2)


def completed_zeta(s):
    return gamma_factor(s) * zeta(s)


def finite_euler(s, primes=(2, 3, 5, 7, 11, 13, 17, 19, 23, 29)):
    out = 1.0 + 0j
    for p in primes:
        out *= 1.0 / (1.0 - mp.fp.power(p, -s))
    return out


def sine_control(s):
    return mp.fp.sin(s)


FUNCTIONS = {
    "lambda": completed_zeta,
    "zeta": zeta,
    "gamma-factor": gamma_factor,
    "finite-euler": finite_euler,
    "sine": sine_control,
}


def dlog_zeta(s, h):
    fp = zeta(s + h)
    fm = zeta(s - h)
    f0 = zeta(s)
    return (fp - fm) / (2.0 * h * (f0 + 1e-30))


def dlog_gamma_factor(s, h=None):
    return -0.5 * math.log(math.pi) + 0.5 * mp.fp.digamma(s / 2.0)


def dlog_completed_zeta(s, h):
    return dlog_gamma_factor(s) + dlog_zeta(s, h)


def dlog_finite_euler(s, h=None, primes=(2, 3, 5, 7, 11, 13, 17, 19, 23, 29)):
    out = 0.0 + 0.0j
    for p in primes:
        lp = math.log(p)
        q = mp.fp.power(p, -s)
        out += lp * q / (1.0 - q)
    return out


def dlog_sine(s, h=None):
    return mp.fp.cos(s) / (mp.fp.sin(s) + 1e-30)


DLOGS = {
    "lambda": dlog_completed_zeta,
    "zeta": dlog_zeta,
    "gamma-factor": dlog_gamma_factor,
    "finite-euler": dlog_finite_euler,
    "sine": dlog_sine,
}


def phase_gate(delta_phi, sharpness=3.0, floor=0.05):
    return floor + (1.0 - floor) * math.exp(sharpness * math.cos(delta_phi) - sharpness)


def dlog_phase(dlog_func, s, h):
    deriv_log = dlog_func(s, h)
    return math.atan2(deriv_log.imag, deriv_log.real)


def unwrap(phases):
    return np.unwrap(np.array(phases, dtype=float))


def simulate_trace(dlog_func, sigma, t_min, t_max, n, h, coupling, threshold):
    ts = np.linspace(t_min, t_max, n)
    phases = unwrap([dlog_phase(dlog_func, complex(float(sigma), float(t)), h) for t in ts])
    deltas = np.diff(phases, prepend=phases[0])
    gates = np.array([phase_gate(float(delta)) for delta in deltas])
    amp = np.zeros(n, dtype=float)
    activation = np.full(n, np.inf)
    amp[0] = 1.0
    activation[0] = 0.0
    for i in range(1, n):
        amp[i] = amp[i - 1] * coupling * gates[i]
        if amp[i] > threshold:
            activation[i] = activation[i - 1] + 1.0 / max(amp[i], 1e-12)
        else:
            break

    participated = np.isfinite(activation)
    reach = int(participated.sum())
    speed = reach / activation[reach - 1] if reach > 1 else 0.0
    coherence = abs(np.mean(np.exp(1j * np.diff(phases)))) if len(phases) > 1 else 0.0
    return {
        "reach": reach,
        "speed": float(speed),
        "mean_gate": float(gates.mean()),
        "participating_gate": float(gates[participated].mean()) if reach else 0.0,
        "phase_coherence": float(coherence),
        "final_amp": float(amp[reach - 1]) if reach else 0.0,
        "phase_span": float(phases[-1] - phases[0]),
    }


def main():
    parser = argparse.ArgumentParser(description="HT continuum transfer of phase-gated wound-wave participation.")
    parser.add_argument("--functions", default="lambda,zeta,gamma-factor,finite-euler,sine")
    parser.add_argument("--sigmas", type=float, nargs="*", default=[0.3, 0.5, 0.7])
    parser.add_argument("--t-min", type=float, default=14.0)
    parser.add_argument("--t-max", type=float, default=84.0)
    parser.add_argument("--samples", type=int, default=360)
    parser.add_argument("--h", type=float, default=1e-4)
    parser.add_argument("--coupling", type=float, default=0.985)
    parser.add_argument("--threshold", type=float, default=0.12)
    args = parser.parse_args()

    names = [name.strip() for name in args.functions.split(",") if name.strip()]
    print("STEP8 HT continuum phase-gated wave participation")
    print("NODE constraint kept: recursive wave participation filtered by internal phase gates")
    print("HT change: cell-cycle phase -> local continuum phase of d/ds log f(s)")
    print(f"trace t=[{args.t_min},{args.t_max}], samples={args.samples}, coupling={args.coupling}, threshold={args.threshold}")
    print("function      sigma  reach  speed    mean_gate  part_gate  phase_coh  phase_span  final_amp")

    for name in names:
        dlog_func = DLOGS[name]
        for sigma in args.sigmas:
            row = simulate_trace(dlog_func, sigma, args.t_min, args.t_max, args.samples, args.h, args.coupling, args.threshold)
            print(
                f"{name:12s} {sigma:5.2f}  {row['reach']:5d}  {row['speed']:7.4f}"
                f"  {row['mean_gate']:9.4f}  {row['participating_gate']:9.4f}"
                f"  {row['phase_coherence']:9.4f}  {row['phase_span']:10.4f}"
                f"  {row['final_amp']:9.4f}"
            )


if __name__ == "__main__":
    main()
