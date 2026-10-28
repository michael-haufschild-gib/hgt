# The positive index of the torsion form grows like N^{1/φ²}

- **ID:** ait-torsion-index-exponent-is-inverse-golden-square
- **Stage:** 0-backlog
- **Type:** CONJECTURE
- **Source:** AIT Pillar XIX (index `≥ M/log M`, `M ≍ N^{1/5}`); RP22, RP23 (golden ratio and the
  fixed-point law).
- **Statement:** The positive index of the renormalized torsion form `−P_N − diag(log n − d(n))`
  on `[1, N]` is `N^{1/φ² + o(1)}`, `1/φ² = 0.38197…`.

## Heuristic

The fixed-point identity at `κ = −1/φ` (`α = 1`): `diag(log n) + P_N = −R/φ + φ D_κ` with rows
`R ≈ (log N)|x|²`, so negative directions of `diag(log n) + P_N` are the states of the twisted walk
`D_κ` with energy `< log N/φ²`. The twisted walk is a product over primes up to the horizon, with
modes labelled by `m` and energies `≈ log m`; their number below `log N/φ²` is `≈ N^{1/φ²}`.

## Evidence

Positive index 6, 9, 14, 18, 23 at `N = 100…4000`, slope `≈ 0.38` in `log N`.

## Log
- 2026-10-28 — created in 0-backlog.
