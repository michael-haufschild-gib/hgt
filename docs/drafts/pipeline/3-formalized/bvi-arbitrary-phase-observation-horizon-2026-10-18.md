# Arbitrary-phase observation horizon

- **ID:** bvi-arbitrary-phase-observation-horizon
- **Stage:** 3-formalized
- **Type:** THEOREM (resolves the backlog conjecture negatively, with the exact mechanism)
- **Original question:** does vanishing on `2N − 3` consecutive values (or any linear number)
  force a level-`N` row to vanish at every phase? Answer: no linear horizon exists.

## Statements (Lean, `formal/GaloisForLFunctions/BezoutValuationIncidence/`)

- `SuperlinearObservabilityHorizonAtArbitraryPhase.lean`:
  `exists_zero_response_window` — for every `m` and `N ≥ (m+2)(2^{m+1})!(1+2^{m+1})` there are a
  phase `A` and a nonzero row whose response vanishes on `Ico A (A + mN)`;
  `not_exists_linear_observability_horizon`.
- `SuperlinearDiscrepancyObservabilityHorizon.lean`:
  `exists_discrepancy_zero_window` — for `N ≥ (m+4)(2^{m+3})!(1+3·2^{m+1})` a row of positive
  variance has vanishing prefix discrepancy on `Icc A (A + mN)`;
  `not_exists_linear_discrepancy_observability_horizon`.

## Paper proof

Alternating grid: `M` divisible by every integer below `2^m`, `b_j = M2^j`, `d_S = D − Σ_{j∈S} b_j`,
`ι_S = Σ_{j∈S} j b_j`, row `Σ_{S⊆[0,m)} (−1)^{|S|} δ_{d_S}`. For `(m+1)M2^m < D`, inside the window
`[A, A + m(D − M2^m))` the hits of `d_S` are exactly `A + ι_S + J d_S = A + JD + Σ_{j∈S}(j−J)b_j`,
`J < m`. In block `J` the `J`-weight vanishes, so `S ↦ S Δ {J}` preserves the hit and flips the
sign: each block cancels. A common phase exists by CRT: `gcd(d_S, d_{S'}) | M(σ_S − σ_{S'})` with
`0 < |σ_S − σ_{S'}| < 2^m`; every such prime divides `M`, hence `D`, contradicting `gcd(D,M) = 1`.
For the discrepancy, three grids with bases `D − iM2^m` (all `3·2^m` moduli pairwise coprime, `M`
absorbing integers below `2^{m+2}`) give three zero-response rows on a common window; a nonzero
combination annihilates `H` and the discrepancy at the phase; the grid tops carry the coefficients,
so the variance is positive.

## Audit

Both modules pass plain `lake --old env lean` with no diagnostics; all main theorems use only
`propext`, `Classical.choice`, `Quot.sound`; both are wired into `BezoutValuationIncidence.lean`.

## Open survivor

The exact growth of the universal horizon between `N·ω(1)` and `Φ(N) ≍ N²`. The grid needs `N`
factorial in `2^m` to beat `mN`, so it gives only `N log log N`-type growth.
