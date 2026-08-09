# A single Báez-Duarte generator is quantitatively useless

Status: formalized (Lean, unconditional)
Date: 2026-08-09

## Why this, rather than more closed forms

`quarter-gram-entry.md` showed the residue-class method reaches exactly `m ∈ {1,2,4}`, so the table of closed
forms cannot be extended without Gauss's general digamma theorem. But the asymptotic question needs no closed
form at all, and it has a sharp answer.

## What is proved

`RHTower/SingleGeneratorUseless.lean`:

* **`bdGram_self_lower` — `bdGram (1/m) (1/m) ≥ (m − 1)/(2m²)`.**  The Gram series has nonnegative terms, so it
  dominates its first `m − 1` terms; there `(n mod m) = n`, the summand is `n/(m²(n+1)) ≥ 1/(2m²)`, and there are
  `m − 1` of them (`sum_le_hasSum` on the series of `hasSum_bdGram_discrete`).
* **`bdDist_single_ge` — `d² ≥ 1 − 2(log m)²/(m − 1)`** for the one-generator family `{1/m}`, `m ≥ 2`.  The
  pairing is exactly `(log m)/m`, so the optimal gain `pairing²/gram` is at most
  `((log m)/m)²·2m²/(m−1) = 2(log m)²/(m−1)`, and the exact single-generator value
  `d² = 1 − pairing²/gram` comes from `bdDist_sq_eq_of_realNormalEquations` at the `1×1` normal solution.

## What it says

The single-generator gain is `O((log m)²/m)`, so it **tends to `0`**: no modulus, however large, pushes the
distance appreciably below `1` on its own. The `m = 2` and `m = 4` bounds of the earlier cards are therefore not
arbitrary small cases — the small moduli are where essentially all of the single-generator gain lives, and the
optimum over `m` is attained early.

The consequence for the route is the useful part: **any path to `d_N → 0` must be collective.** It cannot come
from a clever choice of one modulus, or of a few large ones; it needs the joint effect of many, which is exactly
the estimate recorded as open in `baez-duarte-layer-map.md`. This closes off a whole class of attempts at the
cost of one lower bound on a series with nonnegative terms.
