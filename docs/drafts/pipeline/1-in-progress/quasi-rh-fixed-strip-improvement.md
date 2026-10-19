# Improving the fixed quasi-RH strip

- **ID:** quasi-rh-fixed-strip-improvement
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Source:** [Report, Section 8](../../../report/quasi-rh.md#8-opportunities-and-todos)
- **Statement:** Obtain an unconditional fixed bound `Re(ρ) ≤ b < 7/8` for every nontrivial ζ zero, then establish the corresponding Dirichlet-family result.

## Goal

Discharge the actual arithmetic estimates in report Section 8. A conditional zero-width implication, rephrased RH criterion, logarithmic saving, or finite-height result is not completion. The assumed mathematical baseline does not authorize adding a Lean axiom for it.

## Gates

- [x] Exact arithmetic objects and zero-width targets identified in the corpus.
- [ ] Dependency-closed paper proof of an improved arithmetic estimate.
- [ ] Unconditional Lean theorem for that estimate and its zero-strip consequence.
- [ ] Character-twisted source and common improved exponent across the requested Dirichlet family.
- [ ] Requirement-by-requirement audit of report Section 8.

## Targets

| Priority | Exact target | Current status |
|---|---|---|
| Suzuki | `P₂(N) = E_N²/C_N = O(N^r)` for an explicit `r < 1/2`; alternatively bounded `P₃` | `[OPEN CORE]` |
| Prime lag / Abel | One-sided prime-lag exponent `< 3/8`, or the precise sampled-Abel counterpart | `[OPEN CORE]` |
| Wold | Uniform upper bound on literal directed covariance for every `0 < t < 1/6` | `[OPEN CORE]` |
| Möbius | `WeightedMertensMoment a` at some `a > 1/8` without RH | `[OPEN CORE]` |
| Dirichlet | Twisted source identification and the improved estimate for every character | `[OPEN CORE]` |

## Literal Suzuki normalization

Use the existing objects
`A_N = unitRieszCoherentPrimeOutgoingCharge N`,
`G_N = suzukiNaturalApertureCompletedLowerHardyAmplitude N`,
`C_N = suzukiNaturalApertureTransitionCoreCauchyEnergy N`,
`E_N = suzukiTransitionCoreAlignedGammaCompletedEnergy N`.

`SuzukiCanonicalSignedCompensationSaturation` proves `A_N/√N → 1/3`, `G_N/√N → 0`, and `E_N/C_N → 0`. `SuzukiTransitionCoreAlignedGammaCompletion` proves `C_N ≤ K N`, eventual `A_N² ≥ N/104976`, and `G_N² ≤ E_N ≤ K'G_N²` eventually. All are unconditional source statements.

### Dependency-closed elementary consequence

For sufficiently large N, both A_N and C_N are nonzero. Definitions give

`E_N = C_N (G_N/A_N)²`,
`P₂(N) = C_N (G_N/A_N)⁴`,
`P₂(N)/C_N = (G_N/A_N)⁴`.

Since `G_N/A_N → 0`, the last expression tends to zero. Nonnegativity and `C_N ≤ K N` imply

`0 ≤ P₂(N)/N ≤ K (G_N/A_N)⁴ → 0`.

Thus `P₂(N) = o(N)`. This is a **BRIDGE from existing PNT control**, not a fixed-power improvement, not a novelty claim, and not completion of the target. Exact quantitative decay of `G_N/A_N` remains the issue.

Formal status: `SuzukiQuadraticContactUnconditionalDecay.lean` proves all-N normalization identities and both ratio limits, including totalized zero cases. Its foreground leaf check and five theorem axiom audits passed; only `propext`, `Classical.choice`, and `Quot.sound` occur. The leaf is wired into `RHTower`.

### Competing proof directions

1. Strengthen the completed scalar cancellation directly. `SuzukiTransitionCoreAbelSourceMultiGateWeld` identifies G_N with an explicit signed Selberg square-root Abel action plus polar-lattice and archimedean corrections. Seek a bound of order `N^a`, `a < 3/8`, for that literal action.
2. Use Ward cancellation geometry only after establishing a quantitative comparison with the aligned scalar. `SuzukiCompletedWardCancellativeBand` restricts negative Cauchy-Gram cross terms to comparable lags, but does not itself estimate the scalar or its full covariance.
3. Examine the Wold signed covariance at a radius above 1/8 for an independent arithmetic saving. Compactness or diagonal summability alone does not bound the growing flat probes.

## Upstream detector exponent obstruction

**Verdict: BRIDGE / exact obstruction for the displayed exponent estimates.** This does not rule out a stronger estimate for the actual arithmetic source. External novelty is uncertified.

The cached source is at `tmp/hgt-openai-math/quasirh-source`, relative to the repository root. Its `Detector/LowGramScale.lean` gives the low Gram exponent `g(x,y)=(5x+y)/12` at scales `X=Z^x`, `Y=Z^y`, ignoring arbitrarily small positive losses. `PrincipalSignalComparison.lean:411` identifies the normalized principal exponent as `s+c`, with `c=x/3−5/6+L/6` when total slot length is L. The published values are `x=17/48`, `y=23/48`, `L=1/6`.

### Fixed total scales

At `x+y=5/6` and `L=1/6`, direct subtraction gives

`g(x,y)−c = (x+y)/12 + 5/6 − L/6 = 7/8`.

Thus redistributing X and Y cannot improve the boundary through these estimates: the signal and error shifts cancel exactly. The `3/16` floor is supplied by the low Gram estimate, not by the slack central high-row budget.

### Increasing slot length exposes a sharp reflected-budget face

Consider the natural retuning `p=x+y=1−L`. The nominal low boundary would be `11/12−L/4`, suggesting improvement when `L>1/6`. However, the current reflected estimate uses a parent exponent `p−2d` and selected length `ell0≤L−d`.

The zero-error reflected exponent is

`R = O/2 + max(H,v+l) − S − B + z − min(v,z,(v+z)/3) − l − 2e/3 − max(0,T−v−3l−e)/2`,

where `T=2H+2A+2z−1−ell0−N−3B`. The linear budget includes `H≤p−2d−O`, `2A≤O`, `0≤N≤A`, `z≤ell0≤L−d`, nonnegative remaining costs, and `v+3l+e≤T`. These are the zero-error inequalities in `Detector/LowReflectedLength.lean`; the published cap is `L=1/6`.

For any `0<h≤5/6`, set

`L=1/6+h`, `p=5/6−h`, `d=1/6−h/5`,
`H=1/2−3h/5`, `z=ell0=6h/5`,
`O=A=N=S=B=v=l=e=0`.

Every stated nonnegativity and length inequality holds, `H=p−2d`, and `T=0`. The hybrid saving and retained-kernel saving both vanish. Therefore

`R=H+z = (p−2d)+6h/5`.

This is a counterexample to extending the same abstract reflected budget beyond total slot length `1/6`. Even improving its intermediate quarter-kernel inequality cannot eliminate this witness, because its retained length is exactly zero. It is not a constructed arithmetic configuration or a lower bound on actual arithmetic energy.

### Positive survivor: exact cost of this retuning

To cover this face with a uniform reflected-energy allowance, one must pay at least

`loss(L)=max(0,(6L−1)/5)`.

Taking the square root contributes half that loss to the low source bound. The resulting necessary exponent budget is

`B(L)=11/12−L/4 + max(0,(6L−1)/5)/2`.

Its exact piecewise decomposition is

- `B(L)=7/8+(1/6−L)/4` when `L≤1/6`;
- `B(L)=7/8+7(L−1/6)/20` when `L≥1/6`.

Hence `B(L)≥7/8`, with equality exactly at `L=1/6`. This is a dependency-closed algebraic proof of an exponent-budget minimum, not a zero-free theorem.

**Replacement target [OPEN CORE]:** improve the actual low Gram bound or the actual reflected source estimate on the zero-retained-length face. At the published scales, replacing Gram power `1/6` by `1/6−u` would lower the nominal boundary by `u/16`; all high/transport estimates must still be checked at that boundary. The constant optimization route alone has not supplied this new arithmetic estimate.

Formal status: the exact witness, scale invariant, boundary decomposition, sharp minimum, and Gram-power sensitivity are proved in `QuasiRHDetectorScaleBudget.lean`, with a warning-free foreground leaf check and six standard-axiom audits. This narrow retuning route is closed in [its failed-route card](../5-failed/quasi-rh-detector-scale-retuning.md). The overall task remains in progress.

### Weighted exceptional contribution: exact next arithmetic target

`Detector/GramClassification.lean` defines exceptional frequencies by divisibility of ideal valuations by six outside the fixed modulus. `LowGramExceptional.lean` counts them with exponent `1/6`. `GramSourceDivisors.lean:24` identifies the actual coefficient as the ideal Möbius value on the divisor pool. `GramTruncation.lean:17` preserves that coefficient in `sourceCanonicalSum`, and its splitting theorem isolates the exceptional contribution exactly.

`GramIdealMass.lean:85` then permits arbitrary coefficients of norm at most one and applies `normalized_double_sum_bound`; this loses the actual Möbius signs. The concrete open estimate is for `sourceCanonicalSum` with `exceptionalFrequencies` and `sourceMobiusWeight`, before that norm bound. It is not an estimate for an arbitrary bounded coefficient array. A source-specific cancellation estimate or controlled secondary-term subtraction must preserve the principal residue and all family quantifiers.

## Research constraints

Use local corpus searches; no external searches under the user's standing instruction. Consequently no external novelty certification is claimed. No numerical experiments. New capstones must not take the desired estimate, RH, or an improved strip as a premise. Finish paper proofs before formalizing. Use sequential foreground leaf checks with `lake --old env lean`; no full or umbrella builds. Preserve other agents' files.

Knowledge ledger: [logs/quasi-rh-fixed-strip.md](../../../../logs/quasi-rh-fixed-strip.md).
