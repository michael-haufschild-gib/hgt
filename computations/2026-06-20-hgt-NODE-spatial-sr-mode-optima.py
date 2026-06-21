import argparse
import math

import numpy as np


def simulate_mode(mu, drive_omega, drive_amp, noise, dt, steps, burn, seed):
    rng = np.random.default_rng(seed)
    a = -math.sqrt(max(mu, 0.0))
    lock_s = 0.0
    lock_c = 0.0
    count = 0
    sqrt_dt = math.sqrt(dt)
    for n in range(steps):
        t = n * dt
        force = drive_amp * math.sin(drive_omega * t)
        drift = mu * a - a * a * a + force
        a += drift * dt + math.sqrt(2.0 * noise) * sqrt_dt * rng.normal()
        if n >= burn:
            lock_s += a * math.sin(drive_omega * t)
            lock_c += a * math.cos(drive_omega * t)
            count += 1
    return 2.0 * math.hypot(lock_s / count, lock_c / count)


def main():
    parser = argparse.ArgumentParser(
        description="NODE test: mode-specific stochastic-resonance optima in an extended bistable field."
    )
    parser.add_argument("--modes", type=int, nargs="*", default=[1, 2, 3])
    parser.add_argument("--base-mu", type=float, default=1.0)
    parser.add_argument("--laplacian", type=float, default=0.06)
    parser.add_argument("--drive-omega", type=float, default=0.045)
    parser.add_argument("--drive-amp", type=float, default=0.055)
    parser.add_argument("--dt", type=float, default=0.15)
    parser.add_argument("--steps", type=int, default=14000)
    parser.add_argument("--burn", type=int, default=3500)
    parser.add_argument("--seeds", type=int, default=12)
    parser.add_argument(
        "--noises",
        type=float,
        nargs="*",
        default=[0.004, 0.007, 0.011, 0.017, 0.026, 0.039, 0.058, 0.086, 0.128, 0.19],
    )
    args = parser.parse_args()

    print("NODE: stochastic resonance in spatially extended systems")
    print("Constraint: each Fourier mode sees a different Laplacian-shifted barrier.")
    print("Reduced mode equation: da=(mu_k a-a^3+A sin(omega t))dt+sqrt(2D)dW")
    print("mode  mu_k    barrier~mu^2/4  best_D    peak_lockin  all_lockins")
    for mode in args.modes:
        mu = args.base_mu - args.laplacian * mode * mode
        if mu <= 0:
            continue
        responses = []
        for noise in args.noises:
            vals = [
                simulate_mode(mu, args.drive_omega, args.drive_amp, noise, args.dt, args.steps, args.burn, seed + 101 * mode)
                for seed in range(args.seeds)
            ]
            responses.append(float(np.mean(vals)))
        best_i = int(np.argmax(responses))
        packed = ",".join(f"{x:.4f}" for x in responses)
        print(
            f"{mode:4d}  {mu:5.3f}      {0.25 * mu * mu:9.4f}"
            f"  {args.noises[best_i]:7.4f}    {responses[best_i]:10.4f}  {packed}"
        )


if __name__ == "__main__":
    main()
