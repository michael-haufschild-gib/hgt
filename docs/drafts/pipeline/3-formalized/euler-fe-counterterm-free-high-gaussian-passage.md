# Counterterm-free Gaussian passage at high ordinates

- **Stage:** 3-formalized
- **Type:** THEOREM
- **Source:** Euler–FE transport: joint prime-current admission in the actual finite-layer world.

## Theorems

Under `¬AAL`, there is `1/2<σ<1` with an actual zero strictly right of `σ` such that,
uniformly for `σ≤Re s≤1` as `t=Im s→+∞`,

`ΣΛ(n)n^(−s)e^(−n²/t)+ζ′/ζ(s) → 0`.

The sum retains every von Mangoldt coefficient. No divisor, continuum,
scalar or polar counterterm remains. The intermediate normalized law is
`G_s(1/t)−e^(−1/t)(A(s)−ξ′/ξ(s))→0`.

## Proof

The finite-exception estimate contributes
`O((t⁻¹+t^(−(σ−θ)/2))(1+log t))`, which vanishes for `θ<σ`.
Above twice every exceptional ordinate, translated squared resolvents are
`O(t⁻²)`. At `y=1/t`, the power of damping in each exceptional Gamma mode is
at most `t`, so the entire finite correction is `O(t⁻¹)`.

For the continuum `E(1/t,1−s)`, one Mellin recursion gives a first term
`O(t⁻¹)`. The next Mellin integral has norm `O(t^(3/2))` and coefficient
`O(t⁻²)`, hence contributes `O(t^(−1/2))`.

Finally, `A−ξ′/ξ=−ζ′/ζ−(s−1)⁻¹`. The finite layer gives a fixed
positive distance from every zero above a fixed height, so
`|ζ′/ζ(s)|=O(log t)`. Since `|1−e^(−1/t)|≤1/t`, removing the scalar and
polar terms costs only `O((1+log t)/t)`.

This provides raw-prime passage on an interior high strip while
retaining the full infinite Euler data. It does not create a new zero or
settle same-depth replication, `LinAt C`, or AAL.

Formalization: `EulerFETransportTheory/ThePrimeCurrentPassesAtInverseHeight.lean`.

## Lean declarations and audit

- `norm_gaussianContinuum_inverseHeight_le`: uniform continuum bound.
- `not_asymptoticAbscissaLaw_has_countertermFree_highGaussianPassage`: prime-minus-continuum passage.
- `not_asymptoticAbscissaLaw_has_rawPrime_highGaussianPassage`: literal infinite prime-sum passage.
- `norm_normalizedGaussianFinitePart_add_logDeriv_le`: scalar and polar correction bound.
- `not_asymptoticAbscissaLaw_has_rawEuler_highGaussianPassage`: convergence to `−ζ′/ζ`.

Direct `lake --old env lean` checking passes. All five transitive axiom audits
contain only `propext`, `Classical.choice`, and `Quot.sound`.
