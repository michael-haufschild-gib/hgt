# One Gaussian scale across an escaping height window

- **Stage:** 3-formalized
- **Type:** THEOREM
- **Source:** Euler–FE transport: matching analytic continuation to the full arithmetic mean.

## Theorem

Under `¬AAL`, there is `1/2<σ<1` below an actual exceptional abscissa such that

`sup_{σ≤Re s≤1, T≤Im s≤2T}|ΣΛ(n)n^(−s)e^(−n²/T)+ζ′/ζ(s)| → 0`.

The same damping `1/T` is used at every point of the window. Every von
Mangoldt coefficient is retained. Setting `T=Im s` recovers the inverse-height
passage theorem.

## Proof

The finite exceptional layer supplied by `¬AAL` has complementary abscissa
`θ<σ`. Its finite-part error is
`O((T⁻¹+T^(−(σ−θ)/2))(1+log(2T)))`.
Above twice the exceptional ordinates, the unit-damping Gamma modes are
`O(T⁻²)`. Damping `1/T` amplifies them by at most `T`, so their finite sum
is `O(T⁻¹)`.

One Mellin recursion bounds the continuum, whenever `Im s≥T≥1`, by
`T⁻¹+Γ(3/2)T^(−1/2)`. The scalar normalization and polar term cost
`O((1+log(2T))/T)` on the separated high strip. Each error vanishes uniformly.

This supplies the damping regime needed by the infinite rough mean theorem.
Transferring that mean through the small-prime split remains a separate
obligation; no new zero or replication law follows from passage alone.

## Formalization

`EulerFETransportTheory/ThePrimeCurrentPassesAcrossDyadicWindows.lean`:

- `norm_gaussianContinuum_horizon_le`.
- `not_asymptoticAbscissaLaw_has_countertermFree_dyadicGaussianPassage`.
- `not_asymptoticAbscissaLaw_has_rawPrime_dyadicGaussianPassage`.
- `norm_normalizedGaussianFinitePart_horizon_add_logDeriv_le`.
- `not_asymptoticAbscissaLaw_has_rawEuler_dyadicGaussianPassage`.

Direct `lake --old env lean` checking and all five transitive axiom audits
pass with only `propext`, `Classical.choice`, and `Quot.sound`.
`ThePrimeCurrentPassesAtInverseHeight.lean` recovers the corresponding
inverse-height statements by specialization to the lower window endpoint.
Its direct check and five transitive axiom audits pass with the same axioms.
