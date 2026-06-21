#!/usr/bin/env python3
import math
from bisect import bisect_right

import numpy as np


def simulate_lineage(rng, birth=0.92, death=1.0, mutate=0.0008, tmax=80.0):
    t = 0.0
    n = 1
    times = [0.0]
    sizes = [1]
    while n > 0 and t < tmax:
        rate = n * (birth + death + mutate)
        t += rng.exponential(1.0 / rate)
        r = rng.random() * (birth + death + mutate)
        if r < birth:
            n += 1
        elif r < birth + death:
            n -= 1
        else:
            times.append(t)
            sizes.append(n)
            return "success", t, times, sizes
        times.append(t)
        sizes.append(n)
    if n <= 0:
        return "failed", t, times, sizes
    return "censored", tmax, times, sizes


def observed_at_grid(times, sizes, end_t, dt, threshold):
    k = 1
    sample_t = dt
    while sample_t <= end_t:
        idx = bisect_right(times, sample_t) - 1
        if idx >= 0 and sizes[idx] >= threshold:
            return True
        k += 1
        sample_t = k * dt
    return False


def main():
    rng = np.random.default_rng(20260621)
    lineages = [simulate_lineage(rng) for _ in range(50000)]
    statuses = np.array([x[0] for x in lineages])
    true_success = np.mean(statuses == "success")
    true_failed = np.mean(statuses == "failed")
    print("NODE: stochastic tunneling sampling misses transient failed intermediates")
    print(f"lineages={len(lineages)} true_success_frac={true_success:.6f} true_failed_frac={true_failed:.6f}")
    print("birth=0.92 death=1.0 mutate_to_success=0.0008 subcritical_intermediate")
    print()
    print("dt threshold observed_frac failed_seen_frac failed_missed_frac success_seen_frac success_enrichment")
    for dt in [0.25, 0.5, 1.0, 2.0, 5.0, 10.0]:
        for threshold in [1, 3, 8]:
            seen = np.array(
                [
                    observed_at_grid(times, sizes, end_t, dt, threshold)
                    for status, end_t, times, sizes in lineages
                ]
            )
            failed = statuses == "failed"
            success = statuses == "success"
            failed_seen = np.mean(seen[failed])
            success_seen = np.mean(seen[success])
            observed_success = np.mean(success[seen]) if np.any(seen) else 0.0
            enrichment = observed_success / true_success if true_success > 0 else math.nan
            print(
                f"{dt:4.2f} {threshold:9d} {np.mean(seen):13.6f} "
                f"{failed_seen:16.6f} {1.0 - failed_seen:18.6f} "
                f"{success_seen:17.6f} {enrichment:18.6f}"
            )


if __name__ == "__main__":
    main()
