#!/usr/bin/env python3
"""STEP 11 for urban autocorrelation -> APEX-A: fake-proof attack.

Fake proof:
  Degree-2 prime-log monomial support autocorrelation is high; therefore the
  monomials are arithmetically dependent or Schanuel-relevant.

Gap test:
  Replace prime logs by generic sorted random logs and by geometric controls.
  If Moran's I persists, it is a shared-support/order artifact, not arithmetic.
"""

from __future__ import annotations

import runpy

import numpy as np


BASE = runpy.run_path("computations/2026-06-21-conway-urban-autocorr-apexa.py")

first_primes = BASE["first_primes"]
moran_i = BASE["moran_i"]


def monomial_graph_values(logs: np.ndarray):
    nodes = []
    values = []
    n = len(logs)
    for i in range(n):
        for j in range(i, n):
            nodes.append((i, j))
            values.append(float(logs[i] * logs[j]))
    adjacency = []
    for a, (i, j) in enumerate(nodes):
        support = {i, j}
        neigh = []
        for b, (k, l) in enumerate(nodes):
            if a != b and support & {k, l}:
                neigh.append(b)
        adjacency.append(neigh)
    return np.array(values), adjacency


def control_stats(logs: np.ndarray, rng: np.random.Generator):
    values, adjacency = monomial_graph_values(logs)
    obs = moran_i(values, adjacency)
    shuf = np.array([moran_i(rng.permutation(values), adjacency) for _ in range(200)])
    return obs, float(np.mean(shuf)), float(np.std(shuf))


def main() -> None:
    rng = np.random.default_rng(2606215709)
    print("STEP 11 APEX-A autocorrelation fake-proof control")
    print("method=19 write the fake proof")
    print("control n moran_I shuffled_mean shuffled_sd z_score")
    for n in [12, 24, 32]:
        prime_logs = np.log(np.array(first_primes(n), dtype=float))
        controls = {
            "prime_logs": prime_logs,
            "sorted_uniform": np.sort(rng.uniform(0.5, 4.0, size=n)),
            "sorted_lognormal": np.sort(rng.lognormal(mean=0.6, sigma=0.45, size=n)),
            "geometric": np.geomspace(float(prime_logs[0]), float(prime_logs[-1]), n),
            "unsorted_uniform": rng.uniform(0.5, 4.0, size=n),
        }
        for name, logs in controls.items():
            obs, mu, sd = control_stats(logs, rng)
            z = (obs - mu) / (sd + 1e-300)
            print(f"{name:16s} {n:02d} {obs:+.5f} {mu:+.5f} {sd:.5f} {z:+.2f}")
    print(
        "\nInterpretation: if sorted random/geometric logs reproduce prime-log support autocorrelation, "
        "the invariant is a support/order artifact. It can audit finite experiment dependence, but "
        "it cannot be promoted toward APEX-A arithmetic dependence."
    )


if __name__ == "__main__":
    main()
