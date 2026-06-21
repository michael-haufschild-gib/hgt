import argparse
import math

import numpy as np


def grad_u(x):
    return x * (x * x - 1.0) - 0.06


def colored_noise(rng, steps, tau, sigma):
    if tau <= 0:
        return rng.normal(0.0, sigma, size=steps)
    rho = math.exp(-1.0 / tau)
    eps = rng.normal(0.0, sigma * math.sqrt(1.0 - rho * rho), size=steps)
    out = np.empty(steps, dtype=float)
    out[0] = rng.normal(0.0, sigma)
    for i in range(1, steps):
        out[i] = rho * out[i - 1] + eps[i]
    return out


def run_one(tau, seed, args):
    rng = np.random.default_rng(seed)
    noise = colored_noise(rng, args.steps, tau, args.noise)
    x = -1.0
    escaped_at = None
    tail = []
    for n in range(args.steps):
        x += -args.lr * grad_u(x) + noise[n]
        x = float(np.clip(x, -2.0, 2.0))
        if escaped_at is None and x > 0.35:
            escaped_at = n
        if n > args.steps // 2:
            tail.append(x)
    tail = np.asarray(tail)
    return escaped_at is not None, float(np.mean(tail)), float(np.std(tail))


def main():
    parser = argparse.ArgumentParser(description="NODE: low-frequency colored noise escape/drift tradeoff.")
    parser.add_argument("--taus", type=float, nargs="*", default=[0, 1, 2, 4, 8, 16, 32, 64])
    parser.add_argument("--steps", type=int, default=900)
    parser.add_argument("--runs", type=int, default=240)
    parser.add_argument("--lr", type=float, default=0.035)
    parser.add_argument("--noise", type=float, default=0.032)
    args = parser.parse_args()

    print("NODE: colored noise can escape shallow basins but drift around optima")
    print("Minimal counterexample: tilted double well, same marginal noise variance, varied correlation time tau.")
    print("tau     escape_frac   mean_tail_x   drift_std")
    for tau in args.taus:
        rows = [run_one(tau, 100000 + i, args) for i in range(args.runs)]
        escape = float(np.mean([r[0] for r in rows]))
        mean_tail = float(np.mean([r[1] for r in rows]))
        drift = float(np.mean([r[2] for r in rows]))
        print(f"{tau:5.1f}      {escape:8.4f}     {mean_tail:9.4f}   {drift:9.4f}")


if __name__ == "__main__":
    main()
