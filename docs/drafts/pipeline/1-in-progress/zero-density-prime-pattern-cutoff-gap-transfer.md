# Finite-cutoff upper bounds at zero Euler density

- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Obstacles:** Γ12; route-obstacles B24.
- **Statement:** For every prime set `P` and cutoff `Q`,
  `primeSetGreatestGap P ≤ finiteFlipGreatestGap (primeSetCutoff P Q)`.

## Consequence

The existing strict finite-flip comparison would extend the atomic Hodge
index or its two-adic probe to every nontrivial prime-set flip, without a
density or harmonic cancellation assumption.

## Argument under investigation

1. For fixed `d`, `S(N/d) = S(N) + O_d(1)` by bounded sign coefficients.
2. Fixed Ramanujan correlations are `S(N)` times the finite Euler conductor
   coefficient, with bounded error.
3. A positive gap forces `S(N)² ≥ c log N` along a cofinal subsequence
   (`frequently_harmonicSum_sq_ge_of_hasHyperplaneGap`).
4. On that subsequence, bounded correlation errors vanish relative to
   `S(N)`. Fixed conductor quasimodes then transfer a finite-cutoff witness
   with exact hyperplane correction.

## Open proof obligations

Exact relative correlation formula; finite-packet energy convergence;
hyperplane correction with error controlled along the forced subsequence.
No theorem counted before paper proof and Lean audit.
