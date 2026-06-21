#!/usr/bin/env python3
import math


def miss_probability(p, n):
    return math.exp(n * math.log1p(-p))


def main():
    print("NODE test: Gibbs rare states and recurrence scale")
    print("rare state probability p = exp(-beta DeltaE) / (1 + exp(-beta DeltaE))")
    print()
    budgets = [10**3, 10**5, 10**7]
    for gap in [2, 5, 10, 15, 20]:
        p = math.exp(-gap) / (1 + math.exp(-gap))
        mean_return = 1 / p
        print(f"beta_DeltaE={gap:2d}  p={p:.3e}  mean_return≈{mean_return:.3e}")
        for n in budgets:
            print(f"  samples={n:8d}  miss_probability≈{miss_probability(p, n):.3e}")
    print()
    print("finite sampling certificate")
    for p in [1e-2, 1e-4, 1e-6, 1e-8]:
        n95 = math.log(0.05) / math.log1p(-p)
        print(f"p_min={p:.0e}  samples_for_95_percent_hit≈{math.ceil(n95)}")


if __name__ == "__main__":
    main()
