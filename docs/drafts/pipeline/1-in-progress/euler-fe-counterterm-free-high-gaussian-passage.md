# Counterterm-free Gaussian passage at high ordinates

- **Stage:** 1-in-progress
- **Type:** CANDIDATE
- **Source:** Euler–FE transport: joint prime-current admission in the actual finite-layer world.

## Target

Under `¬AAL`, seek `1/2<σ<1` with an actual zero strictly right of `σ` such that,
uniformly for `σ≤Re s≤1` as `t=Im s→+∞`,

`G_s(1/t)−e^(−1/t)(A(s)−ξ′/ξ(s)) → 0`.

No Gamma counterterm remains in this observable. Also determine whether the
continuum term vanishes uniformly, giving the same law for the literal full
von Mangoldt sum `ΣΛ(n)n^(−s)e^(−n²/t)`.

## Mechanism to verify

The finite-exception estimate contributes
`O((t⁻¹+t^(−(σ−θ)/2))(1+log t))`, which vanishes for `θ<σ`.
Above twice every exceptional ordinate, translated squared resolvents are
`O(t⁻²)`. At `y=1/t`, the power of damping in each exceptional Gamma mode is
at most `t`, so the entire finite correction is `O(t⁻¹)`.

For the continuum `E(1/t,1−s)`, one Mellin recursion gives a first term
`O(t⁻¹)`. The next Mellin integral has norm `O(t^(3/2))` and coefficient
`O(t⁻²)`, hence contributes `O(t^(−1/2))`.

This would provide raw-prime passage on a genuine interior high strip while
retaining the full infinite Euler data. It would not create a new zero or
settle same-depth replication, `LinAt C`, or AAL.

Formalization: `EulerFETransportTheory/ThePrimeCurrentPassesAtInverseHeight.lean`.
Lean verification is pending.
