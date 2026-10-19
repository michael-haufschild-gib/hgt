# Can our Lean corpus improve the quasi-RH bound of 7/8?

Date: 19 October 2026. Scope: local Lean corpus, its research search tool, and the repository’s RH research ledger. The reported OpenAI result is accepted as a mathematical premise, as requested; this report does not assess its soundness or attempt to port its proof.

## Verdict

**No unconditional improvement of the fixed strip `1/8 ≤ Re(ρ) ≤ 7/8` was found in the audited corpus routes. We do have substantial machinery that would turn specific new arithmetic estimates into stronger bounds. The most concrete existing specializations are `1/6 ≤ Re(ρ) ≤ 5/6` and `1/4 ≤ Re(ρ) ≤ 3/4`. Their missing hypotheses remain substantive research problems.**

The distinction is between a proved implication and a proved estimate for the actual arithmetic object. Several files prove an implication with no extra axioms while explicitly taking the decisive estimate as an argument. Such a theorem establishes that the estimate would suffice; it does not establish the estimate.

The strongest findings are:

| Finding | What is already in the corpus | What remains missing |
|---|---|---|
| Suzuki finite-contact classification | An explicit family of conditional strip bounds; order three gives `5/6`, order two gives `3/4` | Boundedness of the corresponding residual for the actual completed arithmetic source |
| One-sided prime-lag criteria | Either an upper or a lower prime-lag power bound gives the matching zero strip | A power exponent strictly below `3/8` on all sufficiently large primes |
| Chebyshev and prime-window criteria | Exact transfer between a zero-width bound and the matching arithmetic error spectrum | A strictly better arithmetic exponent; converting the baseline through an equivalence does not improve it |
| Wold signed covariance | An exact characterization of each subcritical zero width | Upper bounds on the signed covariance beyond the baseline radius `1/8` |
| Weighted Möbius moments | A weighted square-integrability condition excludes zeros to the right of `1 − a` | Such a moment at some `a > 1/8`, without assuming RH |
| Dirichlet L-functions | Relevant analytic infrastructure and logarithmic zero-free regions | A character-dependent analogue of the sharper estimates, with a common improved boundary for the entire requested family |

**Recommended research target:** use `5/6` as a concrete first milestone, while allowing any strict improvement below `7/8` to count. Investigate a quantitative Suzuki residual estimate or a one-sided arithmetic bound. Do not start by building another equivalence, and do not describe the missing estimate as routine formalization.

This is a bounded source audit, not a proof that no differently formulated theorem exists anywhere in the million-declaration search index. The conclusion is supported by the inspected theorem statements, their premises, searches for premise providers, and the current [RH frontier ledger](../reports/rh-current-frontier-map.md) and [status document](../reports/STATUS.md).

## 1. Problem statement and normalization

Let the accepted baseline be:

\[
H_0:\qquad \frac18\leq\Re\rho\leq\frac78
\]

for every nontrivial zero in the stated family. The desired improvement is a fixed number \(\eta>0\), independent of zero height, such that

\[
\frac18+\eta\leq\Re\rho\leq\frac78-\eta.
\]

For ζ, the corpus’s convenient interface is

```lean
def XiZeroHalfPlaneBound (alpha : ℝ) : Prop :=
  ∀ rho : ℂ, xi rho = 0 → rho.re ≤ 1 / 2 + alpha
```

See [CCMSourceDivisorEnergySpectrum.lean:27](../../formal/GaloisForLFunctions/RHTower/CCMSourceDivisorEnergySpectrum.lean#L27). Here `alpha` is displacement from the critical line, not the right boundary itself. Thus the baseline is `alpha = 3/8`, and improvement means `alpha < 3/8`.

The functional equation `xi (1 − s) = xi s` supplies the other side: applying the same bound to `1 − ρ` gives

\[
\frac12-\alpha\leq\Re\rho\leq\frac12+\alpha.
\]

The corpus uses this exact reflection argument in [VonMangoldtMinusOneAbscissa.lean:174](../../formal/GaloisForLFunctions/RHTower/VonMangoldtMinusOneAbscissa.lean#L174). Its ζ transfer is [CCMGeneralizedVonKoch.lean:13](../../formal/GaloisForLFunctions/RHTower/CCMGeneralizedVonKoch.lean#L13).

Consequently, for ζ a better right boundary also improves the left boundary. There are not two independent numerical optimization problems. “Zero-free for `Re(s) > b`” permits zeros on `Re(s) = b`; the resulting strip is closed. The statement concerns nontrivial zeros, not ζ’s trivial negative-even zeros. For imprimitive Dirichlet L-functions, zeros introduced by omitted Euler factors also require separate treatment; the natural comparison is the nontrivial divisor of the associated primitive completed L-function.

Useful parameter conversions:

| Right boundary `b` | Symmetric strip | Transverse width `alpha = b − 1/2` | Complementary radius `1 − b` |
|---|---|---|---|
| `7/8` | `[1/8, 7/8]` | `3/8` | `1/8` |
| `5/6` | `[1/6, 5/6]` | `1/3` | `1/6` |
| `4/5` | `[1/5, 4/5]` | `3/10` | `1/5` |
| `3/4` | `[1/4, 3/4]` | `1/4` | `1/4` |
| `1/2` | `{1/2}` | `0` | `1/2` |

These conversions matter because different corpus routes measure different quantities. A larger Wold radius is better; a smaller prime-lag exponent is better.

## 2. Strongest concrete finding: Suzuki finite-contact bounds

### 2.1 Existing theorem and its exact hypothesis

The most directly useful file is [SuzukiTransitionCoreFiniteContactWidthClassification.lean](../../formal/GaloisForLFunctions/RHTower/SuzukiTransitionCoreFiniteContactWidthClassification.lean).

Write:

- \(C_N\) for `suzukiNaturalApertureTransitionCoreCauchyEnergy N`;
- \(E_N\) for `suzukiTransitionCoreAlignedGammaCompletedEnergy N`;
- \(G_N\) for `suzukiNaturalApertureCompletedLowerHardyAmplitude N`.

The finite-contact residual is

\[
P_m(N)=\frac{E_N^m}{C_N^{m-1}}.
\]

The Lean definition totalizes the zero-denominator case; the proof separately obtains eventual positivity of the core. `SuzukiTransitionCoreFiniteContactResidualEventuallyBounded m` means that some nonnegative constant bounds this residual for all sufficiently large integer apertures.

The theorem at [line 407](../../formal/GaloisForLFunctions/RHTower/SuzukiTransitionCoreFiniteContactWidthClassification.lean#L407) is:

```lean
theorem xiZeroHalfPlaneBound_suzukiFiniteContactWidth_of_finiteContactResidualEventuallyBounded
    {m : ℕ} (hm : 1 ≤ m)
    (hcontact : SuzukiTransitionCoreFiniteContactResidualEventuallyBounded m) :
    XiZeroHalfPlaneBound (suzukiFiniteContactWidth m)
```

with `suzukiFiniteContactWidth m = (m − 1)/(2*m)`.

Its numerical consequences are therefore:

| Contact order | Required estimate | Result for nontrivial ζ zeros |
|---|---|---|
| `m = 4` | `E_N^4 / C_N^3 = O(1)` | `[1/8, 7/8]` |
| `m = 3` | `E_N^3 / C_N^2 = O(1)` | **`[1/6, 5/6]`** |
| `m = 2` | `E_N^2 / C_N = O(1)` | **`[1/4, 3/4]`** |
| `m = 1` | `E_N = O(1)` | RH |

The order-two case also has a dedicated theorem in [SuzukiTransitionCoreQuadraticContactWidthLoss.lean:359](../../formal/GaloisForLFunctions/RHTower/SuzukiTransitionCoreQuadraticContactWidthLoss.lean#L359). The classification at [line 441](../../formal/GaloisForLFunctions/RHTower/SuzukiTransitionCoreFiniteContactWidthClassification.lean#L441) identifies order-one boundedness with RH.

**What was not found:** a theorem supplying `hcontact` unconditionally at order two or three. Exact-name searches through the Lean sources found the definition, comparison lemmas, implications, and classification; they did not find a closed producer of the needed residual bound. Nor did the audit find a theorem taking the accepted `7/8` bound alone and producing the order-three hypothesis.

The order-four row is a sufficient criterion for the same numerical endpoint as the baseline. It does **not** identify this residual with the mechanism of the OpenAI proof, and it does not assert that the baseline automatically implies order-four boundedness.

### 2.2 Why these exponents appear

The proof uses eventual inequalities of the form

\[
G_N^2\leq E_N,\qquad C_N\leq K N.
\]

If \(P_m(N)\leq B\), then

\[
|G_N|^{2m}\leq E_N^m\leq B C_N^{m-1}
\leq B K^{m-1}N^{m-1}.
\]

Hence \(|G_N|=O(N^{(m-1)/(2m)})\). The corpus transports this through the exact completed-source identities and logarithmic-lattice interpolation to an exponential bound for the critical Mellin resolvent. The existing continuation theorem then gives the matching Xi width. Relevant interfaces are [finite-contact amplitude transfer:68](../../formal/GaloisForLFunctions/RHTower/SuzukiTransitionCoreFiniteContactWidthClassification.lean#L68), [general interpolation:319](../../formal/GaloisForLFunctions/RHTower/SuzukiTransitionCoreFiniteContactWidthClassification.lean#L319), and [resolvent-to-width:611](../../formal/GaloisForLFunctions/RHTower/CCMCriticalMellinResolventExponentialWidth.lean#L611).

Increasing `m` makes `(m − 1)/(2m)` larger. Higher contact order therefore weakens this particular bound. Orders three and two are useful because their hypotheses are stronger.

The same file proves an [algebraic endpoint obstruction:169](../../formal/GaloisForLFunctions/RHTower/SuzukiTransitionCoreFiniteContactWidthClassification.lean#L169): for every fixed `m ≥ 2`, the abstract finite-contact inequalities with unit-bounded residual permit unbounded amplitudes. This blocks an inference to RH from those inequalities alone. The positive result surviving that obstruction is the explicit nonzero width above. It does not rule out improving the width using additional arithmetic information.

### 2.3 A weaker research target can already beat 7/8

Requiring a bounded quadratic residual is stronger than necessary for a first improvement. Consider instead

\[
P_2(N)=E_N^2/C_N=O(N^r),\qquad 0\leq r<\frac12.
\]

The same inequalities give

\[
|G_N|^4\ll N^{1+r},\qquad
|G_N|\ll N^{(1+r)/4}.
\]

With the existing source transport, the expected sufficient boundary is

\[
b=\frac12+\frac{1+r}{4}=\frac{3+r}{4}<\frac78.
\]

This is a **derived conditional extension to formalize**, not a theorem claimed to have been added or found already in precisely this form. The algebra is explicit; the new mathematical burden is an estimate for the literal residual. Examples:

| Quadratic residual estimate | Resulting target boundary |
|---|---|
| `P_2(N) = O(N^(1/2 − ε))`, fixed `ε > 0` | `7/8 − ε/4` |
| `P_2(N) = O(N^(1/3))` | `5/6` |
| `P_2(N) = O(N^(1/5))` | `4/5` |
| `P_2(N) = O(1)` | `3/4`, already covered by the existing theorem |

A subpower estimate `P_2(N) = O_ε(N^ε)` for every positive ε would likewise aim at the closed `3/4` boundary by taking the infimum of the resulting widths; exact boundedness need not be the only possible route.

There is also useful structure for investigating the estimate: [SuzukiCompletedWardCancellativeBand.lean:75](../../formal/GaloisForLFunctions/RHTower/SuzukiCompletedWardCancellativeBand.lean#L75) proves that a negative completed Ward cross contribution must involve lags comparable within a factor of two. This localizes where energy-lowering cancellation can occur. It supplies a restriction on a possible proof, not a quantitative amount of cancellation.

## 3. One-sided arithmetic bounds: already precise enough

### 3.1 Prime-lag upper or lower bounds

Let `integerLag p` denote the corpus’s real Weil-lag function evaluated at `log p`; see [WeilLagFunctionInteger.lean:103](../../formal/GaloisForLFunctions/RHTower/WeilLagFunctionInteger.lean#L103).

For `0 ≤ a < 1/2`, either of the following on every sufficiently large prime suffices:

\[
\operatorname{integerLag}(p)\leq M p^a,
\qquad\text{or}\qquad
-M p^a\leq\operatorname{integerLag}(p).
\]

The exact conclusions are \(\Re\rho\leq 1/2+a\). The relevant theorems are:

- `re_le_half_add_of_primeLag_ge_rpow`, [PrimeLagPowerSavingLowerBound.lean:70](../../formal/GaloisForLFunctions/RHTower/PrimeLagPowerSavingLowerBound.lean#L70);
- `re_le_half_add_of_primeLag_le_rpow'`, [PrimeLagLandauPowerSaving.lean:472](../../formal/GaloisForLFunctions/RHTower/PrimeLagLandauPowerSaving.lean#L472).

Their arithmetic estimate is the explicit argument `hM`. The exponential notation in Lean, `exp (a * log p)`, equals `p^a` for positive primes.

Thus `a = 1/3` would give `[1/6, 5/6]`; any `a < 3/8` gives a strict improvement. One does not need a two-sided absolute-value bound, nor an estimate at every integer. Either one-sided estimate on all sufficiently large primes is enough. Finite exceptions are allowed through the cutoff `X`.

The corpus has already removed some losses from earlier forms of these criteria. In particular, the final upper theorem works throughout `0 ≤ a < 1/2`; an intermediate appearance of `max(a, 1/4)` is not the final limitation. The task is to improve the arithmetic input, not to optimize that obsolete loss.

### 3.2 Sparse sampling is a real alternative, with a precise coverage requirement

The Möbius-divisor Abel route admits one-sided control on a sampling set `A`. In [MobiusDivisorOneSidedPowerGapBootstrap.lean:508](../../formal/GaloisForLFunctions/RHTower/MobiusDivisorOneSidedPowerGapBootstrap.lean#L508), the hypotheses include

\[
\frac{\operatorname{mobiusDivisorSquareRootAbelMoment}(k)}{k}
\leq M+Mk^c\quad(k\in A,\ k\geq2),
\]

and the requirement that every sufficiently large `n` has a sampled `k ≤ n` satisfying

\[
n-k\leq K n^{1-\delta},\qquad\delta>0.
\]

The conclusion is \(|\Re\rho-1/2|\leq\max(0,c)\). There is a lower-bound counterpart at [MobiusDivisorLowerStripPowerGapBootstrap.lean:779](../../formal/GaloisForLFunctions/RHTower/MobiusDivisorLowerStripPowerGapBootstrap.lean#L779).

This is useful if a structured mesh makes an estimate easier. The bootstrap fills the gaps without losing the target width. It does not produce the improved sampled bound: `hA` still supplies it. A density-one statement does not by itself supply the displayed bound on every sampling gap.

## 4. Exact equivalences: useful interfaces, no automatic numerical gain

### 4.1 Chebyshev error and prime-window energy

`ChebyshevErrorPowerSpectrum alpha` requires, for every `ε > 0`, a constant bounding the literal Chebyshev error by

\[
|\psi(x)-x|\ll_\varepsilon x^{1/2+\alpha+\varepsilon}.
\]

The corpus proves both directions at the same width:

\[
\operatorname{XiZeroHalfPlaneBound}(\alpha)
\quad\Longleftrightarrow\quad
\operatorname{ChebyshevErrorPowerSpectrum}(\alpha),\qquad\alpha\geq0.
\]

The definition and reverse direction are in [CCMSharpPrimeWindowSquareEnergyWidthCollision.lean:37](../../formal/GaloisForLFunctions/RHTower/CCMSharpPrimeWindowSquareEnergyWidthCollision.lean#L37) and [line 393](../../formal/GaloisForLFunctions/RHTower/CCMSharpPrimeWindowSquareEnergyWidthCollision.lean#L393); the forward direction is [CCMGeneralizedVonKoch.lean:971](../../formal/GaloisForLFunctions/RHTower/CCMGeneralizedVonKoch.lean#L971).

Consequently, the accepted baseline supplies `ψ(x) − x = O_ε(x^(7/8+ε))`. Sending that estimate through the reverse implication recovers `7/8`. It does not yield `5/6`. A proof of `O_ε(x^(5/6+ε))` would be a genuine improvement, and the receiving theorem is ready.

The square-sampled prime-window formulation is also quantitative. For its squared positive-excess coefficient, the matching absolute-convergence abscissa is bounded by `1 + 4*alpha`; see [line 262](../../formal/GaloisForLFunctions/RHTower/CCMSharpPrimeWindowSquareEnergyWidthCollision.lean#L262). The factor four comes from sampling at squares and then squaring the excess. Baseline width `3/8` corresponds to abscissa `5/2`; width `1/3` corresponds to `7/3`.

There is a direct sufficient weighted-summability theorem in [CCMSharpPrimeWindowSquareEnergySpectrum.lean:50](../../formal/GaloisForLFunctions/RHTower/CCMSharpPrimeWindowSquareEnergySpectrum.lean#L50). One must distinguish convergence at an endpoint from an abscissa bound: the latter generally only guarantees convergence strictly to its right. Renaming the energy exponent or dropping one of these scaling factors would create a false improvement.

### 4.2 Wold covariance isolates a signed estimate

For the literal natural-cutoff Wold residual `R_N`, define

\[
\mathcal E(t)=\sum_N N^{2t-1}|R_N|^2.
\]

This is `WoldNatResidualSquareEnergy t`, defined in [XiHeatCassiniWoldNaturalSquareEnergyThreeQuarter.lean:26](../../formal/GaloisForLFunctions/RHTower/XiHeatCassiniWoldNaturalSquareEnergyThreeQuarter.lean#L26).

[PaperWoldDirectedCovarianceWidthSpectrum.lean:93](../../formal/GaloisForLFunctions/RHTower/PaperWoldDirectedCovarianceWidthSpectrum.lean#L93) gives

\[
\operatorname{XiZeroHalfPlaneBound}(\alpha)
\Longleftrightarrow
\forall\,0<t<1/2-\alpha,\quad\mathcal E(t)<\infty.
\]

The more useful decomposition is the [raw signed covariance equivalence at line 194](../../formal/GaloisForLFunctions/RHTower/PaperWoldDirectedCovarianceWidthSpectrum.lean#L194). Let `r_n = R_(n+1)`, `Δr_n = r_(n+1) − r_n`, and `w_n = (n+1)^(2t)`. Then

\[
\operatorname{Cov}_t(N)
=\sum_{n<N}w_n\,\Delta r_n
  \sum_{n<j<N}\Delta r_j.
\]

The matching Xi bound is equivalent to upper boundedness of these partial covariances for every `0 < t < 1/2 − alpha`. The increment diagonal is already summable for `t < 1/2`, and the lower covariance bound is available; the unresolved condition is the **upper bound on the signed off-diagonal expression**. See [lines 123 and 170](../../formal/GaloisForLFunctions/RHTower/PaperWoldDirectedCovarianceWidthSpectrum.lean#L123) and the [covariance definition](../../formal/GaloisForLFunctions/RHTower/PaperWoldDirectedCovarianceEnergy.lean#L31).

Baseline `7/8` gives the family `0 < t < 1/8`. Reaching `5/6` asks for the family `0 < t < 1/6`. This is a precise extension target with reusable infrastructure. Controlling absolute values or only the diagonal does not establish it. Nor should one demand energy at `t = 1/2`: the corpus explicitly distinguishes that impossible energy endpoint from the sub-half family equivalent to RH; see [XiHeatCassiniWoldNaturalSquareEnergySubhalf.lean](../../formal/GaloisForLFunctions/RHTower/XiHeatCassiniWoldNaturalSquareEnergySubhalf.lean).

### 4.3 Weighted Möbius moments give another numerical target

The critical Mertens vector here is the reciprocal-weighted sum

\[
m(e^t)=\sum_{n\leq e^t}\frac{\mu(n)}n,
\]

not the unweighted summatory function `M(x) = Σ_(n≤x) μ(n)`. See [MobiusWeightedMertensVector.lean:191](../../formal/GaloisForLFunctions/RHTower/MobiusWeightedMertensVector.lean#L191).

`WeightedMertensMoment a` asserts square integrability of `e^(a*t) m(e^t)` on the positive ray. Equivalently, in real-variable notation the required integral is

\[
\int_1^\infty |m(x)|^2x^{2a-1}\,dx<\infty.
\]

For `a ≥ 0`, [MobiusWeightedMomentZeroFree.lean:52](../../formal/GaloisForLFunctions/RHTower/MobiusWeightedMomentZeroFree.lean#L52) turns this into `ζ(s) ≠ 0` for `Re(s) > 1 − a`, away from the pole. Thus `a = 1/6` would give `5/6`; any `a > 1/8` improves the baseline.

The unconditional moment in that file is at `a = 0`, which yields no such improvement. The provider for every `a < 1/2` in [MobiusRHDecayMoment.lean:385](../../formal/GaloisForLFunctions/RHTower/MobiusRHDecayMoment.lean#L385) explicitly assumes `RiemannHypothesis`. Using it to obtain a new unconditional strip would be circular.

This route is worth retaining if weighted cancellation estimates become available. The audit did not find the required new positive weight already discharged without a stronger zero hypothesis.

## 5. What the accepted baseline activates—and what it does not

The baseline is useful input. It supplies a fixed width below `1/2`, the matching Chebyshev spectrum, and the Wold covariance family below radius `1/8`. These can support estimates, convergence arguments, and parameter choices that previously required a quasi-RH assumption.

One explicit example is [JointAncestryQuasiRHChainExclusion.lean:1173](../../formal/GaloisForLFunctions/RHTower/JointAncestryQuasiRHChainExclusion.lean#L1173):

```text
RH ↔ JasDressedPSD 1 ∧ ∃ alpha ∈ [0, 1/2), XiZeroHalfPlaneBound alpha.
```

The baseline discharges the existential width clause. It does not discharge `JasDressedPSD 1`. Under the baseline, that remaining positivity statement is equivalent to RH, so its removal cannot be treated as a bookkeeping step. The current frontier ledger also records stronger JAS characterizations without the quasi-RH side condition.

Similarly, the power-gap bootstrap theorems perform genuine transport and supremum arguments, but still take a better sampled arithmetic estimate as input. Their internal contraction does not imply that every known zero width contracts automatically.

The most useful next question is therefore specific: **can the accepted fixed gap help prove an independent estimate for a residual, signed covariance, or one-sided source at a strictly better exponent?** The audited corpus supplies places to insert such an estimate, but not a completed argument producing it.

## 6. Dirichlet L-functions require a separate scope of work

The quantitative criteria above concern the particular ζ/Xi arithmetic source. Their theorem parameters do not range over Dirichlet characters. A ζ improvement is already meaningful, but it does not establish the same improvement for every Dirichlet L-function.

The inspected Dirichlet result [DirichletLZeroFreeLogStrip.lean:330](../../formal/GaloisForLFunctions/RHTower/DirichletLZeroFreeLogStrip.lean#L330) proves, for each nonprincipal character, a region of the form

\[
\beta>1-\frac{c_\chi}{\log^9(3+|t|)}.
\]

There is also a large-height result at fixed modulus in the same file. These are height-dependent logarithmic regions whose left boundary approaches `1`. They do not give a fixed all-height boundary below `7/8`.

To obtain an improved common Dirichlet boundary through the opportunities identified here, work would need to include:

1. A precise character-twisted source and its identification with the relevant completed L-function or logarithmic derivative.
2. Correct treatment of the principal-character pole, gamma factors, parity, conjugate characters, and imprimitive Euler factors.
3. An analogue of the quantitative source-to-zero-width theorem.
4. The new arithmetic estimate for every character in the claimed family, at one common improved exponent.

Constants may depend on the character if the final claim only asks for a common zero-free boundary for all characters. Uniform numerical constants in conductor are an additional issue. What must not vary away is the improved exponent itself. An average over characters would also leave an individual-character gap.

There is genuine spectral large-sieve infrastructure: [KuznetsovLargeSieveTheorem.lean:589](../../formal/GaloisForLFunctions/RHTower/KuznetsovLargeSieveTheorem.lean#L589) proves a Γ₀(Q) spectral inequality. However, the `cubic` in that file’s intermediate theorem refers to a cubic spectral weight. That search hit is not evidence of the particular cubic- or sextic-character machinery one might seek for another proof strategy. No direct connection from that inequality to an improved fixed Dirichlet strip was established in this audit.

## 7. Apparent improvements that do not answer the question

| Candidate | Why it does not establish a narrower fixed strip |
|---|---|
| A theorem with `hRH`, `hXi`, `hcontact`, or a stronger power estimate as an argument | The decisive premise still needs proof; its presence is mathematically meaningful even when the implication is a closed Lean theorem |
| Arbitrary fixed logarithmic savings | `N / log^A N` is not `O(N^(1−δ))` for any fixed positive δ; constants depending on A cannot be ignored |
| A logarithmic zero-free strip | Its width shrinks with height; it does not become a fixed `b < 1` |
| Finite-height verification or a bounded central region | Does not exclude zeros at unbounded heights |
| A density-zero exceptional set | Does not exclude every exceptional zero or guarantee the sampling-gap hypothesis |
| Positive or bounded diagonal energy | Does not bound the required signed off-diagonal covariance |
| A round trip through an exact width equivalence | Returns the width supplied at the start |
| Increasing finite-contact order | Increases the resulting right boundary `1 − 1/(2m)` |
| Reusing a ζ theorem for all characters | Omits the character-dependent source identification and estimate |

For a concrete logarithmic-saving example, [EulerDeletionMobiusGlobalLogSaving.lean:232](../../formal/GaloisForLFunctions/RHTower/EulerDeletionMobiusGlobalLogSaving.lean#L232) proves `primitiveEnergy N ≪_q N / log(N)^(q+1)` for each natural `q`. That is useful arithmetic control. It is not the missing fixed power saving.

## 8. Opportunities and todos

These are follow-up research tasks, not claims of work completed by this report. Priority reflects proximity to a precise existing theorem, not a prediction that the missing estimate is easy.

### Priority 1: quantitative Suzuki residual

- [ ] Establish the best available bound for the **literal** `E_N^2 / C_N`, keeping the gamma completion and source signs intact.
- [ ] Aim first for `O(N^r)` with an explicit `r < 1/2`. `r = 1/3` is a concrete route to `5/6`; boundedness reaches the existing `3/4` theorem.
- [ ] Use the factor-two cancellation restriction to identify which cross terms could deliver the saving, then estimate their aggregate contribution. Local sign information alone is insufficient.
- [ ] If such an estimate is proved on paper, formalize the power-growth extension through the existing general interpolation and resolvent-to-width interfaces.
- [ ] Alternatively, prove the existing order-three boundedness hypothesis directly and use the already stated finite-contact theorem.

**Completion criterion:** a proof of the improved arithmetic estimate that does not assume the target strip or RH, followed by the numerical strip consequence. An implication whose only new premise is that estimate is not completion.

### Priority 2: one-sided prime-lag or sampled Abel estimate

- [ ] Choose the more accessible sign and target exponent `a = 1/3`, or any explicit `a < 3/8`.
- [ ] Prove the bound on all sufficiently large primes, or choose the existing Abel sampling theorem and prove its exact coverage condition.
- [ ] Trace every imported estimate’s hypotheses. Separate unconditional logarithmic control from fixed power control.

**Completion criterion:** a source estimate satisfying `hM` or `hA` with the desired exponent and all required quantifiers, not a statement holding only on average or on an inadequately controlled exceptional set.

### Priority 3: extend Wold signed covariance control

- [ ] Seek an upper bound uniform in cutoff `N` for `Cov_t(N)` beyond `t = 1/8`.
- [ ] A clean target is every `0 < t < 1/6`, which feeds the existing `5/6` equivalence directly.
- [ ] Preserve the signs of the cross terms. Use the already proved diagonal and lower-bound results to keep the unresolved task confined to the necessary upper estimate.

**Completion criterion:** the stated covariance bound for the actual Wold residual, at the required radii, with no stronger zero hypothesis hidden in its derivation.

### Priority 4: weighted Möbius moment and family extension

- [ ] If new Möbius cancellation estimates arise, test whether they imply `WeightedMertensMoment a` for some `a > 1/8`; `a = 1/6` is a useful target.
- [ ] Keep a Dirichlet extension as an explicit separate deliverable. First identify the twisted analogue of the successful ζ source and then prove its estimate across the desired character family.

**Stop or redirect a proposed argument** if it only reproduces the baseline exponent, substitutes an RH-dependent provider, discards the signed interaction being estimated, or proves a result for a different source without an identification theorem. Preserve any nontrivial estimate or classification obtained along the way; failure to reach a narrower strip does not erase that mathematical result.

## 9. Search record and limits of verification

The investigation used the documented local corpus tool directly. Searches included:

```bash
scripts/formal_tools.py research '"zero-free" "half-plane"' --mode lexical --no-refresh --per-module 0 --limit 160 --explore 0 --json
scripts/formal_tools.py research '"Dirichlet" "zero-free"' --mode lexical --no-refresh --per-module 0 --limit 80 --explore 0 --json
scripts/formal_tools.py research 'prime lag one sided growth exponent zero free strip' --mode deep --budget-seconds 120 --no-refresh --json
scripts/formal_tools.py research 'Mertens power saving zero free Dirichlet Hecke cubic sextic large sieve' --mode deep --budget-seconds 120 --no-refresh --json
scripts/formal_tools.py research 'Suzuki finite contact residual bounded zero width' --mode lexical --any --module SuzukiTransitionCore --no-refresh --per-module 0 --limit 60 --explore 0 --json
```

The broad lexical searches returned 139 declarations across 86 modules for the half-plane query and 24 declarations across 17 modules for the Dirichlet query. Relevant source declarations and their surrounding proofs were read directly. Exact `rg` searches traced occurrences of residual hypotheses, moment providers, prime-lag bounds, and zero-width interfaces. Additional candidates included the power-gap bootstraps, JAS quasi-RH criterion, prime-window energies, Borel-terminal Wold bounds, and the spectral large sieve.

The deep results were partial because of search/reranking time limits. One reported coverage snapshot inventoried 62,619 Lean files and 1,100,250 declarations, with extensive pending or stale compiler coverage. Candidate and ingredient suggestions were treated as discovery leads, not certified proof compositions. The whole corpus was not read declaration by declaration, and absence from a ranked result was not treated as a nonexistence theorem.

**Verification level:** source inspection and mathematical parameter accounting. Compilation attempts were stopped at the user’s instruction; they produced no successful verification result used here. No Lean implementation was added to the repository. The report does not claim a fresh build or a new formal proof.

The separately run repository lint returned an umbrella-reachability error for `GaloisForLFunctions.ArithmeticCriticalityTheory.ShiftedGroundStateCollarFubini`, alongside existing file-size warnings. That repository-wide state is not evidence for or against the conditional mathematical results above; no unrelated files were changed to address it.

The actionable conclusion is that the corpus already provides several precise ways to turn a new estimate into a better strip. **What is missing is the improved arithmetic estimate itself, not another name or formulation for the desired zero bound.**
