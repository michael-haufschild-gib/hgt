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

The proposed equivalence also classifies the optimal exponent: if
`Θ=sup{Re ρ: ξ(ρ)=0}`, then every positive target pair should have
`sup{α: R_YZ(y)=O(y^α)}=1−Θ/2`. Thus target averaging preserves the
entire zero-abscissa invariant, not only the RH threshold. This corollary
still depends on the unproved sufficiency direction.

An [unconditional corollary](../3-formalized/ads3-narain-average-pole-decay-boundary.md) needs no sufficiency theorem: Hardy's
critical-line zero and the proved fixed-average pole obstruction exclude
every `O(y^α)` remainder with `α>3/4`, for any logarithmic and constant
subtraction. `RHTower.XiSeamSupremum.exists_xi_zero_on_line` supplies the
actual zero. The Narain specialization is formalized as
`narainScalarHeatAverage_no_better_than_three_quarters`.
The [endpoint amplitude candidate](ads3-narain-pole-endpoint-amplitude.md)
strengthens this to failure of little-o at the exact pole exponent and
a lower amplitude carrying the pole multiplicity. It also predicts that
an exact `O(y^(3/4))` bound would force simplicity as well as RH; the
epsilon-loss criterion above makes no simplicity claim.

## Formalized unconditional boundary

The stronger endpoint
`yA_YZ(y)+(3/π)log y−B_YZ = o(y^(1/2))`
is [formalized](../3-formalized/ads3-narain-average-boundary-rate.md), including
actual-source Mellin inversion, boundary integrability and vanishing horizontal edges.

## Formalized conditional strip bounds

`NarainMeanZeroFreeStrip` proves analyticity of the actual mean wherever
`σ₀<1+2 Re u`, away from the main pole, under the explicit assumption
that `ξ` has no zero on `Re s>σ₀`. For `0≤σ₀<1` and
`σ₀<1+2a<1`, it proves
`|M_YZ(u)|≤C(1+|Im u|)^N exp(−π|Im u|/2)` uniformly on
`a≤Re u≤0`, `|Im u|≥1`. The reciprocal-zeta polynomial lower bound
combines with the proved filled-numerator envelope. The module and both
endpoint axiom audits passed, with only the standard three axioms.
This is an implication with its zero-free premise explicit; it does not
establish that premise or the proposed sharp source rate.

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
then use the proved source identity on `Re s=1/2`. Moving that boundary
to any `a` with `σ₀/2<a<1/2` crosses no pole: the main pole at `s=1`
has already been subtracted. Absolute integrability on `Re s=a` and
Riemann–Lebesgue would give the stronger fixed-line conclusion
`R_YZ(y)=o(y^(1−a))`. This contour argument belongs inside the
zero-free-to-rate implication; it supplies no unconditional zero-free
half-plane.

Corpus inputs include `mellinInv_mellin_eq`,
`HTGeometry.FinitePoleVerticalContourShift`,
`WeilHigherDenominator.laurentCoeff_mellin_doublePole`, sharp xi strip bounds in
`BlackHoleRingdown/ThePolynomialGrowthOfTheEisensteinFunction.lean`, and
the public `zeroFree_iff_zeta_lower_bound` in
`CountingHolography/ThermalizationFasterThanTheSquareRootIsAZeroFreeStrip.lean`.
For `σ₀=1`, the already proved `o(y^(1/2))` boundary estimate implies
every required epsilon-loss bound directly; no further contour is needed. The reciprocal-zeta inputs'
transitive axiom audits contain only the standard three axioms. The [central removal and exact weighted residue](../3-formalized/ads3-narain-average-principal-part.md)
are formalized for this specific mean. The contour at `Re s=1/2` is proved;
transport to every zero-free interior line remains open. None of these
bounds is an extra premise of the claimed equivalence.

## Gates

- [x] Conditional analyticity and uniform decay on every closed interior strip.
- [ ] 0 → 1: transport the actual boundary identity to every interior line.
- [ ] 1 → 2: dependency-closed paper proof of both directions.
- [ ] 2 → 3: Lean formalization and transitive axiom audit.
