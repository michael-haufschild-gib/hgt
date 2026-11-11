# Levinson's gate from the two-main-term twisted moment

- **ID:** A111
- **Stage:** 1-in-progress
- **Type:** CONJECTURE

## Target

Produce an unconditional positive critical-zero proportion through the
Levinson detector using mollifier length `T^θ`, `θ<1/2`.

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

## Arithmetic jets and remaining gate assembly

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

The dyadic law, fixed-coefficient transfer and count insertion have complete
Lean proof drafts, pending dependency checks. The capstone is
`TheTwistedMomentGivesAPositiveCriticalProportion`: its target fraction is
`(1−log(18/5)/(13/10))/4`. No detector gate from these inputs is yet claimed.

## Low-height split and scalar choice

The dyadic receiver uses one mollifier for every block down to height 20.
Take length exponent `θ=13/50` and split exponent `α=53/100`:
`θ/α=26/53<1/2`, while `θ+(11/8)α=791/800<1`.
A thin-strip Weyl bound for the detector then makes the initial segment
`O(U^(791/800))`; larger blocks admit the proved short twisted moment.
The detector Weyl bound and the resulting bound `C B² N A^(11/8)` for
coefficients satisfying `|b_n|≤B n^(σ−1/2)` have Lean proof drafts.
Their checks and the block assembly remain required.

For `R=13/10`, exact integration of the linear scalar proves
`c(13/50)<18/5<exp(13/10)`, giving a strictly positive gate margin.
`TheShortLevinsonMollifierHasAPositiveScalarMargin` formalizes these bounds
using rational estimates for `exp(13/20)`.
`TheThreeProfileScalarIsTheLevinsonConstant` proves the exact identification
by integrating the polynomial arithmetic jets.

The receiver fixes coefficients before choosing its nearby abscissa.
Using coefficients at `d_U=R/log U` instead of `d=R/log T₂` changes each
coefficient by relative size `O((d−d_U)log N)=O(1/(U log U))`.
Proof drafts now bound the full gate-strip exponent change by `R/(U−1)`,
the coefficient discrepancy by `D exp D · n⁻ᵈ`, and the resulting energy
via Young's inequality and the Weyl bound. These checks and their dyadic
assembly remain required.

The block argument uses the Weyl head below `U^(53/100)`, a uniform linear
energy bound up to `δ U/log U`, and the sharp scalar above that threshold.
Choosing `δ` after the linear bound absorbs the middle range into the
gate's additive slack. The squared coefficient perturbation has exponent
`13/50+11/8−2=−73/200`, so the same fixed coefficients serve every block.
