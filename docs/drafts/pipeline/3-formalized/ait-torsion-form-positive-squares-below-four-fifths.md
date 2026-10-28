# The positive squares of the torsion form live below N^{4/5}

- **ID:** ait-torsion-form-positive-squares-below-four-fifths
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** AIT §9 topic 5 ("Open: the exact exponent and an upper bound"); Pillar XIX.
- **Statement:** `R_N ≤ diag(2A(⌊N/n⌋) + d(n) − ½ log n)` for the renormalized torsion form on
  `[1, N]`; hence every `R_N`-positive subspace has dimension `≤ N^{4/5 + ε}` for large `N`.

## Proof

Ground-state identity `P_N + D_N = Σ (A + log n) x²`; on each pole relation
`(a − b)² ≤ (3/2)a² + 3b²` (`= ½(a + 2b)² ≥ 0` difference), so
`D_N ≤ (3/2) Σ log n x² + 3 Σ A x²` and `P_N ≥ −½ Σ log n x² − 2 Σ A x²`. With `c = log n − d`:
`R_N = −P_N − Σ c x² ≤ Σ (2A + d − ½ log n) x²`. A positive definite subspace injects into the
coordinates where the diagonal is positive. There `½ log n < 2(log N − log n + C) + d(n)` and
`d(n) ≤ 2 log K + 2 log 4 + 2 log n/K` (small primes by Mertens, large primes by `Σ_{p|n} log p ≤ log n`)
give `n < N^{4/5 + ε}`. The split `θ = ½` in `(a − b)² ≤ (1 + θ)a² + (1 + 1/θ)b²` is optimal for this
method: `(1 − θ + 1/θ)u ≥ 1/θ` first holds at `u = 4/5`.

## Significance

First upper bound on the positive index: `N^{1/5 − o(1)} ≤ ind₊(R_N) ≤ N^{4/5 + o(1)}`. The positive
squares are localized on the atoms below `N^{4/5}`. Conjectured exponent `1/φ²`
(`0-backlog/ait-torsion-index-exponent-is-inverse-golden-square.md`).

## Status

Lean: `formal/GaloisForLFunctions/ArithmeticIntersectionTheory/ThePositiveSquaresOfTheTorsionFormLiveBelowFourFifths.lean`
(`poleDefect_le_diag`, `renormalizedTorsionForm_le_diag`, `torsionPositiveAtoms`,
`finrank_le_of_renormalizedTorsionForm_pos`, `tameDifferent_le_split`, `eventually_finrank_le_rpow`).
Axioms `propext, Classical.choice, Quot.sound`; wired in the AIT umbrella.
