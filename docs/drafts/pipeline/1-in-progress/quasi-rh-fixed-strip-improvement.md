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
| Dirichlet | Improved reflected binary-correlation estimate for every character; twisted source and receiver already exist | `[OPEN CORE]` |

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

## Developed routes to 5/6 and 3/4

Implementation target: unconditional Lean proofs for the arithmetic estimates and both strip consequences. Neither target strip is proved. Full mathematical statements are in report Sections 8.1–8.5; external web research is excluded.

### Baseline-dependent quotient-tail reduction — paper proof

Let \(F(q)=\texttt{primeFreeDivisorDefect}\ q\), \(T(N)=\texttt{mobiusDivisorSquareRootAbelMoment}\ N\), and \(K_N(q)=\texttt{mobiusClippedAbelKernel}\ N\ q\).
The corpus identifies \(T(N)=\sum_{q<N}F(q)K_N(q)\), proves \(|F(q)|\leq24\sqrt q\), and gives the boundary-free Mertens-gradient identity for K.

If \(|M(D)|\leq C_\beta D^\beta\), \(1/2<\beta<1\), the clipped weight is unimodal with maximum at most \(\sqrt N/q\). Discrete Abel summation therefore gives
\[
|K_N(q)|\leq2C_\beta N^{\beta+1/2}q^{-\beta-1}.
\]
Multiplying by \(24\sqrt q\) and integrating the decreasing power tail proves
\[
\left|\sum_{Q<q<N}F(q)K_N(q)\right|
\leq48C_\beta(\beta-1/2)^{-1}N^{\beta+1/2}Q^{1/2-\beta}.
\]
The accepted boundary \(b_0\) gives Mertens exponents \(b_0+\delta\) through the existing Littlewood theorem. For a one-step target \(b_1\), choosing \(Q=\lceil N^{(b_0-b_1)/(b_0-1/2)}\rceil\) gives the required tail rate. This permits \(N^{1/9}\) for 7/8→5/6, \(N^{1/3}\) for 7/8→3/4, and \(N^{1/4}\) for 5/6→3/4. These are sufficient one-step cutoffs, not necessary thresholds. Absolute estimates of the head recover only the baseline.

Formal support: `CCMFUSuzukiMobiusClippedKernelBound`, `CCMFUSuzukiMobiusQuotientTail`, and `CCMFUSuzukiMobiusQuotientPowerCutoff` prove the tent variation bound, the exact signed head/tail split, and a uniform tail estimate at the actual abscissa Θ. Their one-ninth, one-third, and one-quarter head errors have exponents `(8Θ+5)/9+ε`, `2(Θ+1)/3+ε`, and `3Θ/4+5/8+ε`. These statements assume no zero-free strip. All three leaves pass focused Lean checks without warnings and are imported by `RHTower`. All 15 exported theorems use only `propext`, `Classical.choice`, and `Quot.sound` in scratch-file axiom audits.

Verdict: BRIDGE. The head estimates remain the open arithmetic core. The numerical substitutions use the accepted baseline; it has not been added as an axiom or imported into these leaves. External novelty is unclaimed.

### Self-contracting short heads and their physical boundary

`RHTower.zetaZeroAbscissa_le_of_mobiusDivisorQuotientPowerHead_le_rpow` in `QuasiRHQuotientHeadAndFiniteContactAbscissaLaw.lean` proves the stronger cutoff result: for any fixed θ>0, a one-sided `H(N,ceil(N^θ))/N ≤ C+CN^c` bound gives `Θ≤1/2+max(0,c)`. There is a separate lower one-sided theorem. The tail contracts the unknown width itself: if `a=Θ−1/2>max(0,c)`, choose `δ=min(θ,1)a/2`; the induced bound `a≤max(max(0,c),(1−θ)a+δ)` contradicts strict inequality. Thus the arithmetic targets are `Hθ(N)=O_ε(N^(4/3+ε))` or its lower counterpart for 5/6, and exponent `5/4+ε` for 3/4, at any fixed positive θ. No new numeric strip follows without these estimates.

The exact truncated-source identity must retain its upper boundary. Let `R_M(n)=mobiusDilationRieszTail M n`, `L=min(Q,M−1)`, and `ΔF(n)=log n−τ(n)+2γ`. Since `K_M(n)=R_M(n)−R_M(n+1)`, finite Abel summation gives

`H(M,Q)=Σ_{n=1}^L ΔF(n)R_M(n)−F(L)R_M(L+1)`.

The boundary vanishes for the full physical range, but not for a short head. This is a closed paper proof using `sum_primeFreeDivisorIncrement` and the existing kernel-gradient identity. Shortening θ still leaves the q=1 kernel with Möbius length M. Its exact dyadic recurrence is `K_(2M)(1)=R_(2M)(1)−sqrt(2)R_M(1)`, from the existing dilation law. Dividing by powers of sqrt(2) and telescoping gives

`R_(2^j M)(1)/(sqrt(2))^j = R_M(1)+Σ_{i<j}K_(2^(i+1) M)(1)/(sqrt(2))^(i+1)`.

These identities expose the retained signed source; they do not supply a numerical improvement. The boundary can itself be paid at the intrinsic abscissa. Put β=Θ+ε>1/2. The existing kernel estimate and the decreasing-power integral bound give

`|R_M(Q+1)| ≤ C M^(β+1/2) Σ_{q>Q}q^(-β−1) ≤ (C/β)M^(β+1/2)Q^(-β)`.

Multiplying by `|F(Q)|≤24 sqrt(Q)` gives `O_ε(M^(Θ+1/2+ε)Q^(1/2−Θ−ε))`. If Q exceeds the physical range, the clipped boundary is zero. Consequently the increment head `I(M,Q)=Σ_{n≤min(Q,M−1)}ΔF(n)R_M(n)` approximates the full Abel action with the same intrinsic exponent as H. This is a dependency-closed paper proof; the new arithmetic obligation is cancellation in I, and the boundary need not separately be bounded at a conjectured numerical exponent.

### Mean-square alternative — paper proof

An upper bound \(\sum_{N\leq X}|G_N|^2=O_\varepsilon(X^{2b+\varepsilon})\) suffices for boundary b. Since \(G_N=S(N)/N+O(1)\), the twice-Abel Dirichlet continuation has dyadic absolute blocks bounded by \(X^{b-\Re s+\varepsilon/2}\). Locally uniform convergence for \(\Re s>b\) continues \(-\zeta'/\zeta-\zeta\), excluding a ζ-zero pole there. Targets are \(X^{5/3+\varepsilon}\) and \(X^{3/2+\varepsilon}\). Existing formation-energy increments equal \((N+1)/(N+2)|G_{N+1}|^2\), identifying the exact cumulative observable. The new upper bounds remain open.

### Character-twisted binary correlation — existing receiver

The twisted Möbius–Laplace source and Mellin zero obstruction already exist; do not list them as missing infrastructure. For \(c_\chi(n)=\mu(n)\chi(n)\), let \(\mathcal C_\chi(m)=\sum_{a+b=m}c_\chi(a)\overline{c_\chi(b)}\).
Even-total upper bounds \(O_{\chi,\varepsilon}(m^{2/3+\varepsilon})\) give 5/6; \(O_{\chi,\varepsilon}(m^{1/2+\varepsilon})\) give 3/4. The identity
\(2\sum_m\mathcal C_\chi(2m)r^{2m}=|A_\chi(r)|^2+|A_\chi(-r)|^2\)
and existing even-index theorem supply decay. Arithmetic correlation bounds remain open. Shifted truncated-divisor and fixed-core prime-release estimates are not providers for this source.

### Correction to the upstream Gram opportunity

At fixed original scales, improving only \(P^{1/6}\) to \(P^\nu\) leaves the unit Gram term. The nominal boundary is \(83/96+\max(0,\nu)/16\), so this change alone cannot reach 5/6 or 3/4. The earlier isolated identity \(7/8-u/16\) applies only while the replaced term dominates, \(0\leq u\leq1/6\). This is an upper-bound-method limitation, not an arithmetic lower bound.

The sharp joint classification is formalized in `QuasiRHDetectorGramTradeoff.lean`: retaining `P²/Y` but deleting the exceptional contribution gives minimum `23/27` after retuning both scales. A profile `1+P^ν+P^κ/Y`, with `ν≥0`, reaches the five-sixths budget for some `x≥0,L` exactly when `ν≤1/15` and `κ+4ν≤4/3`. The explicit point `(ν,κ,x,y,L)=(1/30,6/5,5/48,35/48,1/6)` has positive low scales. The retained unit contribution and reflected allowance alone have relaxed minimum `29/36>3/4`. These are constraints and feasible points of the displayed budget; the stronger source estimates and remaining detector assembly are still open. All 14 exported theorems pass focused foreground and standard-axiom audits; the module is wired into `RHTower`.

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

**Replacement target [OPEN CORE]:** prove a joint Gram estimate in the feasible five-sixths region above, or improve the actual reflected source estimate on the zero-retained-length face. Three quarters additionally requires changing the unit term, principal normalization, or reflected allowance. All high/transport estimates must still be checked at the resulting boundary. Constant optimization alone has not supplied the new arithmetic estimates.

Formal status: the exact witness, scale invariant, boundary decomposition, sharp minimum, and Gram-power sensitivity are proved in `QuasiRHDetectorScaleBudget.lean`, with a warning-free foreground leaf check and six standard-axiom audits. This narrow retuning route is closed in [its failed-route card](../5-failed/quasi-rh-detector-scale-retuning.md). The overall task remains in progress.

### Weighted exceptional contribution: exact next arithmetic target

`Detector/GramClassification.lean` defines exceptional frequencies by divisibility of ideal valuations by six outside the fixed modulus. `LowGramExceptional.lean` counts them with exponent `1/6`. `GramSourceDivisors.lean:24` identifies the actual coefficient as the ideal Möbius value on the divisor pool. `GramTruncation.lean:17` preserves that coefficient in `sourceCanonicalSum`, and its splitting theorem isolates the exceptional contribution exactly.

`GramIdealMass.lean:85` then permits arbitrary coefficients of norm at most one and applies `normalized_double_sum_bound`; this loses the actual Möbius signs. The concrete open estimate is for `sourceCanonicalSum` with `exceptionalFrequencies` and `sourceMobiusWeight`, before that norm bound. It is not an estimate for an arbitrary bounded coefficient array. A source-specific cancellation estimate or controlled secondary-term subtraction must preserve the principal residue and all family quantifiers.

`GramCanonicalSource.originalCommonBlock` identifies those Möbius weights as the inversion of a coprimality restriction. Their presence does not by itself prove a saving. Even a complete exceptional-term saving must be accompanied by a nonexceptional improvement to reach five sixths through this profile.

The [prime-mask and cube-root block candidate](quasi-rh-prime-mask-centering.md) develops one concrete construction. Its two Lean leaves prove an optimal mean-preserving prime packet, a uniform finite-prefix square bound, bounded principal bias, and weighted insertion bounds including every Dirichlet character. The arithmetic detector realization, cube-root block estimate, and reflected-source improvement remain open; the card states their separate tests and exponent requirements.

The [additive-shift correlation route](quasi-rh-shift-correlation.md) supplies exact sextic power degeneracies, their `2B²−B` count, cross-ratio normalization, a complete-field mean-square estimate and the literal fourth-moment expansion in Lean. Its new arithmetic conjecture is an interval fourth-moment bound through `B=p^(1/3)`; that range would give conductor factor `p^(1/6)` in the stated amplification calculation. The interval estimate, amplification with errors, and Eisenstein transport remain open. A subfield example rules out extending that conjecture to arbitrary sets over square fields on cardinality alone. Calibration phase variation also has an exact source restriction: `SourceCoefficient.sourceHighCoefficient_eq_bare` removes it from the normalized supported coefficient.

## Research constraints

Use local corpus searches; no external searches under the user's standing instruction. Consequently no external novelty certification is claimed. No numerical experiments. New capstones must not take the desired estimate, RH, or an improved strip as a premise. Finish paper proofs before formalizing. Use sequential foreground leaf checks with `lake --old env lean`; no full or umbrella builds. Preserve other agents' files.

Knowledge ledger: [logs/quasi-rh-fixed-strip.md](../../../../logs/quasi-rh-fixed-strip.md).
