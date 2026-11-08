# Sharp decay of one averaged Narain source

- **ID:** W11-NS
- **Stage:** 0-backlog
- **Type:** CANDIDATE
- **Source:** [Actual target average](../3-formalized/ads3-narain-target-average.md)

## Conjecture

Fix any positive target heights `Y,Z` and let `A_YZ` be their actual scalar
heat average. For `1/2≤σ₀≤1`, the following are equivalent:

1. `ξ(s)≠0` whenever `Re s>σ₀`.
2. For every `ε>0`,
   `yA_YZ(y)+(3/π)log y−B_YZ = O(y^(1−σ₀/2−ε))` as `y→0+`.

Here `B_YZ` is the derivative at `u=1/2` of
`narainMeanMainPoleNumerator Y Z`. At `σ₀=1`, this gives an unconditional
coarse rate. At `σ₀=1/2`, it is a fixed-source RH criterion, not a proof of
the RH-strength rate.

## Unconditional boundary candidate

The stronger endpoint
`yA_YZ(y)+(3/π)log y−B_YZ = o(y^(1/2))`
is developed in [the boundary-rate card](../1-in-progress/ads3-narain-average-boundary-rate.md).
It remains a candidate until the actual-source contour proof is formalized.

## Proof obligations

Necessity is formalized in
[the fixed-average pole obstruction](../3-formalized/ads3-narain-average-pole-decay-boundary.md):
if an arithmetic zero has real part `β>σ₀`, choose
`ε=(β−σ₀)/4`.

For sufficiency, use the filled mean numerator directly. On each fixed
vertical strip, positive-height powers have bounded norm, and
`T_Y(u)=O((1+|Im u|)^N exp(−π|Im u|/2))` follows from the corpus's sharp
xi bound. The product supplies twice that decay. The existing
`exists_exp_mul_norm_inv_xi_le` absorbs one exponential factor into
`1/ξ(1+2u)`, leaving polynomial growth of `1/ζ(1+2u)` and one decaying
exponential. The elementary denominators are bounded away from zero at
large imaginary height. This yields vertical integrability and vanishing
horizontal edges. Remove the apparent central singularity at `u=0`,
then shift past the sole double pole at `s=1`, whose weighted residue is
`y⁻¹[−(3/π)log y+B_YZ]`.

Corpus inputs include `mellinInv_mellin_eq`,
`HTGeometry.FinitePoleVerticalContourShift`,
`WeilHigherDenominator.laurentCoeff_mellin_doublePole`, sharp xi strip bounds in
`BlackHoleRingdown/ThePolynomialGrowthOfTheEisensteinFunction.lean`, and
the public `zeroFree_iff_zeta_lower_bound` in
`CountingHolography/ThermalizationFasterThanTheSquareRootIsAZeroFreeStrip.lean`.
For `σ₀=1`, use `RHTower.norm_inv_riemannZeta_le_of_le_re`:
`‖ζ(s)⁻¹‖≤1+1/(a−1)` on `Re s≥a>1`. The reciprocal-zeta inputs'
kernel audits remain open. The [central removal and exact weighted residue](../3-formalized/ads3-narain-average-principal-part.md)
are formalized for this specific mean. Contour bounds remain to be proved;
none are extra premises of the claimed equivalence.

## Gates

- [ ] 0 → 1: complete source and pole-obstruction modules; audit contour inputs.
- [ ] 1 → 2: dependency-closed paper proof of both directions.
- [ ] 2 → 3: Lean formalization and transitive axiom audit.
