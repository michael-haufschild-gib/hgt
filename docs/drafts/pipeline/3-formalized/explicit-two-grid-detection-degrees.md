# Explicit degrees for two heat grids

- **ID:** explicit-two-grid-detection-degrees
- **Stage:** 3-formalized
- **Type:** THEOREM
- **Source:** review-0511, A18.

## Statement

An explicit polynomial and degree detect each off-line ξ-zero on one of the
prime-log grids `log 2`, `log 3`, including arbitrary starting offsets and the
arithmetic source's pole constraint.

## Bound

Write `λᵢ=exp(−h zᵢ²)` and choose a nonreal target `α=λᵢ₀`, `r=|α|`.
The existing reciprocal-square mass and heat-term bounds give
`Σ|λᵢ|≤M=6/h`. Let `F` contain the distinct sampled nodes with modulus at
least `r/2`. Then `#F≤ceil(2M/r)`.

For the ideal generator `a`, use `c=sqrt(−1/α)` and the existing real orbit
separator with target value `c/a(α)`. Let `E` be its explicit coefficient norm
bound on the radius-`r` disc, multiplied by the coefficient norm bound of `a`.
Set `n=ceil(log(1+2E²M)/log 4)+1`.

The phase-corrected radial factor gives tail norm at most `E²M·4⁻ⁿ<1/2`.
Every retained copy of the target or its conjugate contributes `−1`; all
other outer nodes vanish. Thus the trace-Hankel value is below `−1/2`, with
separator degree at most `2#F+1+n`.

For the source grid take `a=X^K(X−exp(h/4))`; the test degree is at most
`2ceil(2M/r)+2+n`. The finite spectral set and its separation products remain
in `E`; this is not yet a bound in height and depth alone.

## Proof and dependencies

1. `TraceHankelConverse.lean` supplies the real orbit separator, exact target
   values and coefficient norm bound. Retaining its radial factor gives the
   pointwise bound `E(|λ|/r)^n`, hence `E²M·4⁻ⁿ` for the omitted trace.
   The exponent above makes this less than `1/2` by exponentiating the ceiling
   inequality. The outer trace is at most `−1`.
2. Each separator factor is quadratic, the phase correction affine, and the
   radial factor has degree `n`. Thus the separator degree is at most
   `2#F+1+n`. Each outer atom has mass at least `r/2`, so `#F≤ceil(2M/r)`.
3. The zeroth source moment is less than `1`, while the sector estimate gives
   `(167/168)Σ|zᵢ|⁻²≤moment₀`. Therefore `Σ|zᵢ|⁻²<2`. The existing sector
   heat bound is `|exp(−h zᵢ²)|≤(3/h)|zᵢ|⁻²`, proving `M=6/h`.
4. `XiGaussianHeatTwoPrimeSourceSampling.lean` identifies the arithmetic
   source square form with this trace after multiplication by
   `X^K(X−exp(h/4))`. Its ideal generator is nonzero at each nonreal sampled
   node. The source test vanishes at the pole and adds one degree.
5. The existing prime-log phase-clock injectivity proves that a nonreal
   squared ξ-frequency is nonreal on at least one of the two sampled grids.
   Every off-line ξ-zero has such a frequency, since its ordinate is nonzero.

## Lean status

Both source modules passed direct `lake --old env lean` checks:

- `SquareRootThreshold/EffectiveHorizons/TraceHankelDegrees.lean`:
  `traceHankelIdealDetector_negative`,
  `natDegree_traceHankelIdealDetector_le`, `card_le_ceil_of_half_norm_mass`.
- `SquareRootThreshold/EffectiveHorizons/HeatGridDegrees.lean`:
  `tsum_norm_xiGaussianHeatTerm_le_six_div`,
  `natDegree_xiHeatGridExplicitDetector_le`,
  `xiPrimeArchHeatGrid_explicitDetector_negative`,
  `two_prime_heatGrids_explicitDetector_negative`,
  `two_three_heatGrids_explicitDetector_negative_of_offLine`.

All eight transitive axiom audits contain only `propext`, `Classical.choice`
and `Quot.sound`. Both modules are imported by the owning umbrella.
The degree depends on finite spectral separation products, not height and depth alone.
