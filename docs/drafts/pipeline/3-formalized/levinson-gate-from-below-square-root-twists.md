# Levinson's gate from the two-main-term twisted moment

- **ID:** A111
- **Stage:** 3-formalized
- **Type:** THEOREM

## Result

One mollifier of length `floor(U^(13/50))` supplies the literal dyadic
Levinson law at `R=13/10`, `c=18/5`. Consequently, eventually

`((1−log(18/5)/(13/10))/4) · xiPosZeroCount(U) ≤ xiOddFiberCount(U)`.

The coefficient is strictly positive. The proof uses the below-square-root
two-main-term twisted moment and fixes coefficients before every gate
abscissa and every dyadic block.

## Proved analytic reduction

`exists_linearDetector_main_remainder_bound` in
`MultiscaleMollifiedZetaField/TheDetectorMomentErrorsAreSmall.lean` proves
that the actual tapered detector integral equals `detectorThreeMomentMain`
up to `C T^(7/8)`, uniformly for `q∈[T,2T]`,
`1/T≤d≤min(r,1/40)`, `1<N≤T^θ`, `0≤λ≤1`, and `λ log N≤1`.
One common taper has width `T^a`, `0<a<1`.

For `F=ζΨ`, `G=λζΨ′`, `H=F−G`, and `q_J(d)=∫W|J(1/2−d+it)|²`,
the exact identity is

`∫W|(ζ+λζ′)Ψ|² = q_H − (λ/2)(q_F′−q_G′+q_H′) + (λ²/4)q_F″`
`+ λ∫W′ Im(F conj G) + (λ²/4)∫W″|F|²`.

The moment jets differentiate displacement with all coefficients frozen.
Their errors have arbitrary power saving. Thin-strip Weyl bounds and
edge-supported taper derivatives give the stated `T^(7/8)` remainder.
The exact identity, derivative transfer, and remainder passed Lean checks.
See `3-formalized/linear-detector-three-moment-remainder.md`.

## Proved arithmetic reduction

The shifted gcd form has an exact Euler correction and harmonic Möbius
model. Absolute triple-fibre weights have a common summable majorant;
the correction has limiting unit mass. Every normalized correction jet
has a Cauchy majorant, and positive-order jets vanish along every bounded moving-centre sequence.
See `3-formalized/shifted-selberg-euler-factorization.md`.

For `P∈C²`, `P(0)=0`, the normalized power-shifted Möbius transform tends
to `P′(u)−vP(u)`, uniformly on `δ≤u≤1` and compact `v` intervals.
It is uniformly bounded on the full cutoff interval. This compact uniform
statement passed Lean in `TheShiftedMobiusProfilesConvergeUniformly`.
See `3-formalized/smoothed-mobius-tests-and-power-shifts.md`.

## Arithmetic jets and gate assembly

The full corrected polynomial-profile limit and both actual
frozen-coefficient directional derivatives are formalized. They apply
to arbitrary real-height cutoffs tending to infinity and convergent
normalized shifts. The original direct and reflected gcd sums have
exact directions `(−2,2)` and `(2,0)` respectively.
See `3-formalized/shifted-selberg-euler-correction.md`.

The scaled zeta-pole value and its first two literal derivatives are
formalized for arbitrary diverging scales. Every normalized chi-conductor
error jet vanishes. The actual chi jets converge uniformly across moving
blocks whose endpoint conductor ratios converge. Differentiation under
the taper and its integrated jet limits are formalized; only bounded
relative support length is required. Exact first and second product
formulas for the actual normalized main term are formalized. The exact
three-profile scalar equals the Levinson constant at `θ=13/50, R=13/10`.
The actual first three main jets and their three-profile detector combination
have these scalar limits in `TheFrozenMainJetsHaveTheirScalarLimits`,
for arbitrary diverging cutoffs and convergent normalized displacement
and endpoint conductor ratios.

Actual interval energy is dominated by its taper. Along every admissible
large-block family it is bounded by `C a`; above `δ U/log U` it is bounded
by `(18/5)(v−a)+εa`. These estimates are formalized in
`TheMatchedDetectorHasItsBlockBounds`.
`TheMatchedDetectorBoundsAreUniform` supplies a common constant and
threshold for all admissible blocks and all gate displacements.

The fixed-coefficient transfer is formalized in
`TheFixedDetectorKeepsTheMatchedBlockBounds`. The capstone
`TheTwistedMomentGivesAPositiveCriticalProportion` proves
`shortLevinson_dyadicDetectorMeanSquareLaw`,
`shortLevinson_reciprocalLogMeanSquareGate`, and
`eventually_critical_odd_fiber_proportion_from_short_twisted_moment`.
All new modules passed direct Lean checks and are wired into
`MultiscaleMollifiedZetaField.lean`.

## Low-height split and scalar choice

The dyadic receiver uses one mollifier for every block down to height 20.
Take length exponent `θ=13/50` and split exponent `α=53/100`:
`θ/α=26/53<1/2`, while `θ+(11/8)α=791/800<1`.
A thin-strip Weyl bound for the detector then makes the initial segment
`O(U^(791/800))`; larger blocks admit the proved short twisted moment.
The detector Weyl bound and the resulting bound `C B² N A^(11/8)` for
coefficients satisfying `|b_n|≤B n^(σ−1/2)` are formalized in
`TheLinearDetectorKeepsTheWeylBound` and `TheLowDetectorBlocksHaveASublinearHead`.

For `R=13/10`, exact integration of the linear scalar proves
`c(13/50)<18/5<exp(13/10)`, giving a strictly positive gate margin.
`TheShortLevinsonMollifierHasAPositiveScalarMargin` formalizes these bounds
using rational estimates for `exp(13/20)`.
`TheThreeProfileScalarIsTheLevinsonConstant` proves the exact identification
by integrating the polynomial arithmetic jets.

The receiver fixes coefficients before choosing its nearby abscissa.
`TheShortMollifierKeepsItsLogarithmicScale` proves the integer cutoff's
logarithmic limit and all coefficient admissibility conditions, including
the weighted fourth-moment mass bound.
Using coefficients at `d_U=R/log U` instead of the gate displacement `d`
changes the normalized exponent by at most `R/(U−1)`.
`TheFixedLinearMollifierChangesLittleAcrossTheGate` proves the full
gate-strip exponent bound `R/(U−1)` and discrepancy envelope
`D exp D · n⁻ᵈ`. The Young energy estimate is formalized in
`TheDetectorEnergyIsStableUnderCoefficientChanges`; both negligible-error
estimates are formalized in `TheShortMollifierMakesTheHeadAndGateErrorNegligible`.

The block argument uses the Weyl head below `U^(53/100)`, a uniform linear
energy bound up to `δ U/log U`, and the sharp scalar above that threshold.
Choosing `δ` after the linear bound absorbs the middle range into the
gate's additive slack. The squared coefficient perturbation has exponent
`13/50+11/8−2=−73/200`, so the same fixed coefficients serve every block.
