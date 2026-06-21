#!/usr/bin/env python3
"""Fast hard-edge density check without enumerating thousands of zeros.

The slow version computed

    [mp.zetazero(n) for n in range(1, N)]

and then binned `y = 1/gamma_n^2`.  That is the wrong query for bin counts:
mpmath already exposes `nzeros(T)`, the number of nontrivial zeros with
`0 < Im(rho) <= T`.  For a y-bin `[a,b]`, the corresponding gamma interval is
`[1/sqrt(b), 1/sqrt(a)]`, so the count is just a difference of two `N(T)`
queries.
"""

import argparse
import math
import time

import mpmath as mp


DEFAULT_BINS = (
    (1e-6, 4e-6),
    (4e-6, 1.6e-5),
    (1.6e-5, 6.4e-5),
    (6.4e-5, 2.56e-4),
    (2.56e-4, 1.024e-3),
)


def predicted_count(a: float, b: float) -> float:
    """Closed form for int_a^b |log y|/(8*pi) * y^(-3/2) dy, y < 1."""
    ua = 1.0 / math.sqrt(a)
    ub = 1.0 / math.sqrt(b)
    primitive = lambda u: u * math.log(u) - u
    return (primitive(ua) - primitive(ub)) / (2.0 * math.pi)


def count_y_bin(a: float, b: float) -> int:
    lo = 1.0 / math.sqrt(b)
    hi = 1.0 / math.sqrt(a)
    return int(mp.nzeros(hi) - mp.nzeros(lo))


def parse_bins(raw: str):
    if not raw:
        return DEFAULT_BINS
    bins = []
    for item in raw.split(","):
        a_raw, b_raw = item.split(":")
        a = float(a_raw)
        b = float(b_raw)
        if not (0.0 < a < b < 1.0):
            raise ValueError(f"bad y-bin {item!r}; expected 0 < a < b < 1")
        bins.append((a, b))
    return tuple(bins)


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--bins", default="", help="comma list of a:b y-bins")
    parser.add_argument("--dps", type=int, default=30)
    parser.add_argument("--max-seconds", type=float, default=120.0)
    args = parser.parse_args()

    mp.mp.dps = args.dps
    started = time.monotonic()
    bins = parse_bins(args.bins)

    print("# hard-edge density via chunked interval zero-count queries")
    print("# count([a,b]) = N(1/sqrt(a)) - N(1/sqrt(b)); no zetazero loop")
    print("y-bin                 empirical   predicted   elapsed_s")
    for a, b in bins:
        if time.monotonic() - started > args.max_seconds:
            raise TimeoutError(f"runtime exceeded {args.max_seconds}s")
        before = time.monotonic()
        empirical = count_y_bin(a, b)
        elapsed = time.monotonic() - before
        print(
            f"[{a:.2e},{b:.2e}]  {empirical:9d}  "
            f"{predicted_count(a, b):10.1f}  {elapsed:9.4f}"
        )
    print(f"total_elapsed_s={time.monotonic() - started:.4f}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
