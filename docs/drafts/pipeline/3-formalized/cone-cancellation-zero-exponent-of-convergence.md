# Exact spline cone cancellation with zero exponent of convergence

- **Stage:** 3-formalized
- **Type:** Unconditional existence theorem
- **Parent:** SC2; polynomial upper density cannot supply the missing generic rigidity.

For distinct primes `p,q` and `0<d<D`, there is one countable injective
family `z_i` with `d≤Re z_i<D`, `Im z_i≥1`, and real parts cofinal at `D`,
such that every `ε>0` satisfies

```text
Σ_i (1+Im z_i)^(-ε) < ∞.
```

Its coefficients are exactly `F(z_i)=(sinh(z_i)/z_i)^8`, all nonzero, with
unit multiplicities and `Σ|F(z_i)|≤2`. Every real exponential moment
converges absolutely; every positive moment on
`{m log p+n log q : m,n∈ℕ, m+n>0}` vanishes.

The same witness has distinct sign/conjugation quartets. Their positive
inverse-power absolute-ordinate sums also converge for every exponent;
quartet coupling on the natural two-prime cone is bounded by twenty.
Core unit-height windows embed into `Fin 3`, and quartet windows into
`Fin 12`. Positive width is unattained.

Thus zero exponent of convergence, exact spline weights, unit
multiplicities, symmetry, and bounded local counts coexist with cone
cancellation. The construction is not the actual zeta divisor and does
not settle SC2. An additional arithmetic property is required.

## Proof

Retain the geometric block-size bound `n_k≤U R^k` from the explicit sparse
schedule. Matched heights satisfy
`H_k^8=n_k exp(4^(s+k))`, so `log H_k≥4^(s+k)/8`.
Every node in block `k` lies above `H_k`; its total inverse-power mass is
at most `U R^k exp(−ε4^(s+k)/8)`. This is summable for every `ε>0`.
Compatible prefixes preserve these heights in the exact cancelling
nullseries. Finite quartet copies preserve ordinate magnitudes and
inverse-power summability.

## Lean

Directory: `ArithmeticCouplingTheory/ConeMoments`.

- `SparseSplineSchedule.lean`: `exists_two_prime_sparse_spline_tail_schedule_with_geometric_sizes`
  retains the same schedule and its geometric sizes; the old interface is preserved.
- `SparseSplineInverseDensity`: logarithmic height bound and inverse-power summability.
- `ZeroExponentSplineNullseries.lean`: `exists_two_prime_zero_exponent_prescribed_spline_nullseries`:
  one witness satisfies all core conclusions.
- `ZeroExponentSplineQuartets.lean`: `exists_two_prime_zero_exponent_prescribed_spline_cone_model`:
  exact quartet model with every density and coupling conclusion simultaneously.

Every module passes its direct Lean check; transitive axiom audits contain
only `propext`, `Classical.choice`, and `Quot.sound`. Umbrella imports are wired.
Corpus search found the predecessor sparse model but no zero-exponent
conclusion. External priority is unchecked.
