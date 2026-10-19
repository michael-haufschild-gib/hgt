# Can our Lean corpus improve the quasi-RH bound of 7/8?

Date: 19 October 2026. Scope: local Lean corpus, its research search tool, the repository’s RH research ledger, and the upstream Lean source already cached under `tmp/hgt-openai-math/quasirh-source`. The reported OpenAI result is accepted as a mathematical premise, as requested; this report does not assess its soundness or attempt to port its proof. No web research is used.

## Verdict

**No unconditional improvement of the fixed strip `1/8 ≤ Re(ρ) ≤ 7/8` was found in the audited corpus routes. We do have substantial machinery that would turn specific new arithmetic estimates into stronger bounds. The most concrete existing specializations are `1/6 ≤ Re(ρ) ≤ 5/6` and `1/4 ≤ Re(ρ) ≤ 3/4`. Their missing hypotheses remain substantive research problems.**

The distinction is between a proved implication and a proved estimate for the actual arithmetic object. Several files prove an implication with no extra axioms while explicitly taking the decisive estimate as an argument. Such a theorem establishes that the estimate would suffice; it does not establish the estimate.

The strongest findings are:

| Finding | What is already in the corpus | What remains missing |
|---|---|---|
| Suzuki finite-contact classification | Polynomial-growth receivers and an exact exponent law; order three gives `5/6`, order two gives `3/4` | Subpower growth of the corresponding literal residual; boundedness also suffices |
| Quotient-head self-contraction | Either one-sided power bound at any fixed cutoff `ceil(N^θ)`, θ>0, gives the matching strip without a baseline premise | Head exponents `4/3+ε` for `5/6`, or `5/4+ε` for `3/4`, for every ε>0 |
| One-sided prime-lag criteria | Either an upper or a lower prime-lag power bound gives the matching zero strip | A power exponent strictly below `3/8` on all sufficiently large primes |
| Chebyshev and prime-window criteria | Exact transfer between a zero-width bound and the matching arithmetic error spectrum | A strictly better arithmetic exponent; converting the baseline through an equivalence does not improve it |
| Wold signed covariance | An exact characterization of each subcritical zero width | Upper bounds on the signed covariance beyond the baseline radius `1/8` |
| Weighted Möbius moments | A weighted square-integrability condition excludes zeros to the right of `1 − a` | Such a moment at some `a > 1/8`, without assuming RH |
| Cumulative and power-mesh energies | Sharp exponent laws; explicit head and diagonal bounds; exact covariance criteria | Signed covariance estimates `W_6(J)=Oε(J^(5+ε))` or `W_4(J)=Oε(J^(3+ε))` on the exact meshes |
| Dirichlet L-functions | Character-twisted Möbius–Laplace source, Mellin identity, and zero-exclusion theorem | A one-sided bound on the actual twisted binary correlations, with exponent `2/3` for `5/6`, or `1/2` for `3/4` |

Two substantial unconditional results must be accounted for: the existing Suzuki normalization implies `P_2(N) = o(N)`, and the full Wold kernel has vanishing normalized covariance throughout `0 ≤ t < 1/2`. Neither supplies the stronger estimate required for a narrower strip. Sections 2.4 and 4.2 identify the exact losses.

**Developed routes:** Section 8 reduces both targets to one-sided estimates on the actual Möbius–divisor head through `q ≤ ceil(N^θ)` for any fixed θ>0. Self-contraction removes the former cutoff restriction and does not assume the accepted baseline. The sharp cumulative-energy law gives `Θ ≤ r/2`. On every power mesh `N=j^m`, the sharp receiver is `Θ ≤ 1/2+(r−1)/(2m)`. The high-dilation route pays the head and the entire diagonal. Its remaining signed covariance targets are `X^(5/3+ε)` and `X^(3/2+ε)` on all integer scales, or `J^(5+ε)` and `J^(3+ε)` on the exact sixth- and fourth-power meshes. Those arithmetic estimates remain open. The character-twisted binary-correlation receivers and finite-contact polynomial-growth law are also available.

This is a bounded source audit, not a proof that no differently formulated theorem exists anywhere in the million-declaration search index. The conclusion is supported by the inspected theorem statements, their premises, searches for premise providers, and the current [RH frontier ledger](../reports/rh-current-frontier-map.md) and [status document](../reports/STATUS.md).

## 1. Problem statement and normalization

### 1.1 What the accepted upstream result establishes

The locally cached [Nonvanishing.lean:19](../../tmp/hgt-openai-math/quasirh-source/OAI/NumberTheory/DirichletL/Nonvanishing.lean#L19) states:

```lean
theorem LFunction_ne_zero_of_seven_eighths_lt_re
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {s : ℂ}
    (hs : (7 / 8 : ℝ) < s.re) (hpole : ¬ (χ = 1 ∧ s = 1)) :
    _root_.DirichletCharacter.LFunction χ s ≠ 0
```

Thus the boundary is common to **every positive modulus and every Dirichlet character**, at every height. The statement has no primitive-character restriction, no exceptional real-character clause, and no finite-height cutoff. The pole condition concerns the principal character at `s = 1`. The same file states the ζ nonvanishing corollary at line 29; in the classical analytic interpretation, ζ still has its pole at `1`.

Assuming the proof is sound, this excludes every zero strictly to the right of `7/8`, including any exceptional real zero there. It permits zeros on the boundary `Re(s) = 7/8`. It does not establish RH or GRH, zero simplicity, or confinement to `Re(s) = 1/2`.

For primitive completed L-functions, the functional equation relates the character to its conjugate and reflects the real part across `1/2`. Since the bound covers both characters, it supplies the left boundary `1/8` as well. Imprimitive L-functions inherit the primitive nontrivial zeros; their omitted Euler factors can introduce additional zeros on `Re(s) = 0`. Those are not part of the asserted nontrivial strip. Trivial zeros and poles likewise must not be counted as counterexamples to this formulation.

The final assembly explicitly supplies its detector certificate in [FinalAssemblyUnconditional.lean:15](../../tmp/hgt-openai-math/quasirh-source/OAI/NumberTheory/DirichletL/Detector/FinalAssemblyUnconditional.lean#L15). This report takes that assembled result as given. It does not mistake an intermediate certificate hypothesis for the final theorem’s scope.

### 1.2 Normalize the proposed improvement

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

### 1.3 Why the upstream argument does not automatically iterate below 7/8

The cached proof introduces an auxiliary Hecke-family zero supremum `beta`, with a `1/2` sentinel to make its defining set nonempty; see [Hecke/ZeroSupremum.lean:10](../../tmp/hgt-openai-math/quasirh-source/OAI/NumberTheory/DirichletL/Hecke/ZeroSupremum.lean#L10). Its final contradiction assumes `beta > 7/8` and obtains a positive margin below that supremum, uniformly over the relevant zeros. That contradicts the definition of a supremum.

The numerical mechanism is explicit in [Supremum.lean:10](../../tmp/hgt-openai-math/quasirh-source/OAI/NumberTheory/DirichletL/Supremum.lean#L10):

\[
\delta=\min(\beta-7/8-\omega,\sigma),\qquad
\max(3/16+\omega,\beta-11/16-\sigma)
=\beta-11/16-\delta.
\]

Here the argument chooses `0 < ω < β − 7/8` and `σ > 0`. The first normalized error exponent `3/16` corresponds to `7/8 − 11/16`. At `β = 7/8`, the required positive margin is unavailable. Consequently, the contradiction proves `β ≤ 7/8`; it does not secretly give `β < 7/8`, an unspecified uniform improvement, or a repeatable contraction down to `1/2`.

Improving this proof requires changing the estimates that produce its exponent floor and checking every parameter constraint. Section 8 records that as a separate research opportunity.

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

There is also useful structure for investigating the estimate: [SuzukiCompletedWardCancellativeBand.lean:75](../../formal/GaloisForLFunctions/RHTower/SuzukiCompletedWardCancellativeBand.lean#L75) proves that a negative completed Ward cross contribution must involve lags comparable within a factor of two. This localizes cancellation in that Ward cross form. Applying it to the aligned scalar energy requires an exact identity or comparison; local sign information alone supplies neither that comparison nor a quantitative saving.

### 2.4 What the corpus already proves for the actual residual

Let `A_N = unitRieszCoherentPrimeOutgoingCharge N`. The existing [canonical compensation module](../../formal/GaloisForLFunctions/RHTower/SuzukiCanonicalSignedCompensationSaturation.lean#L237) proves, without a zero-width premise,

\[
\frac{A_N}{\sqrt N}\longrightarrow\frac13,\qquad
\frac{G_N}{\sqrt N}\longrightarrow0,\qquad
\frac{G_N}{A_N}\longrightarrow0.
\]

Its [energy identity and limit](../../formal/GaloisForLFunctions/RHTower/SuzukiCanonicalSignedCompensationSaturation.lean#L329) give, eventually,

\[
\frac{E_N}{C_N}=\left(\frac{G_N}{A_N}\right)^2\longrightarrow0.
\]

Together with the [linear core bound](../../formal/GaloisForLFunctions/RHTower/SuzukiTransitionCoreAlignedGammaCompletion.lean#L221), this has the immediate mathematical consequence

\[
\frac{P_2(N)}N
=\frac{C_N}N\left(\frac{E_N}{C_N}\right)^2
\longrightarrow0.
\]

**Existing inputs therefore yield `P_2(N) = o(N)`.** The repository contains this consequence in [SuzukiQuadraticContactUnconditionalDecay.lean:59](../../formal/GaloisForLFunctions/RHTower/SuzukiQuadraticContactUnconditionalDecay.lean#L59), together with the exact fourth-power normalization. Eventual nonzero denominators come from the canonical compensation module. This is a supporting result, not either requested improvement.

This is genuine cancellation for the literal source. But `o(N)` provides no fixed power saving: even `N / log N` is `o(N)` while exceeding every `N^r` with `r < 1` eventually. Beating `7/8` by Section 2.3 requires `r < 1/2`. Normalized convergence cannot supply that exponent.

The actual arithmetic quantity is also identified, rather than left as an abstract energy. For `N ≥ 2`, [SuzukiTransitionCoreAbelSourceMultiGateWeld.lean:29](../../formal/GaloisForLFunctions/RHTower/SuzukiTransitionCoreAbelSourceMultiGateWeld.lean#L29) expresses `G_N` as the signed Selberg square-root Abel moment divided by `N`, with its polar-lattice, polar, and archimedean corrections retained. The same file expresses `E_N` as `C_N` times the square of that corrected scalar divided by `A_N`. This is the concrete source whose rate needs improvement; changing normalization or estimating a different unsigned energy would not settle the task.

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

There is stronger-looking operator machinery which must not be overlooked. [PaperWoldFullKernel.lean:93](../../formal/GaloisForLFunctions/RHTower/PaperWoldFullKernel.lean#L93) proves that the **full** directed kernel is Hilbert–Schmidt for every `0 ≤ t < 1/2`, without a short-window restriction. [PaperWoldFullMeans.lean:173](../../formal/GaloisForLFunctions/RHTower/PaperWoldFullMeans.lean#L173) then proves

\[
\frac1{N+1}\sum_{n,j\leq N}K_t(n,j)\longrightarrow0.
\]

The kernel is `w_n Δr_n Δr_j` for `n < j` and zero otherwise. After shifting the cutoff, the displayed statement is `Cov_t(N) = o(N)`. The required criterion is instead `Cov_t(N) ≤ C_t` for all `N`. The normalization cannot be removed: the finite constant vector has norm `√(N+1)`, and the compact-operator argument uses its unit normalization. Even cutoff-dependent bounded masks have the normalized limit, by the theorem at line 167; that still does not prove a uniform bound for the raw covariance. Thus the operator construction is already available, while the decisive arithmetic size estimate remains open.

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

A related concrete consequence is [Weil positivity on large-prime Euler vectors](../../formal/GaloisForLFunctions/RHTower/JointAncestryWeilEulerUnconditional.lean#L64). Under width `alpha`, its exponent is `1 + alpha + ε`; the baseline therefore gives `11/8 + ε`. This is restricted positivity at that exponent, not the missing level-one JAS statement or positivity of the full Weil form. Likewise, [JointAncestryAbscissaGap.lean:60](../../formal/GaloisForLFunctions/RHTower/JointAncestryAbscissaGap.lean#L60) would combine with the baseline to force RH only after proving its separate premise `jasAbscissa ≤ 1`.

Similarly, the power-gap bootstrap theorems perform genuine transport and supremum arguments, but still take a better sampled arithmetic estimate as input. Their internal contraction does not imply that every known zero width contracts automatically.

The [JAS budget law](../../formal/GaloisForLFunctions/RHTower/JointAncestryBudgetZeroFreeLaw.lean#L258) makes another route quantitative. At dressing level 1, positivity on every dyadic prime set \(P\subset(y,2y]\) with \(\sum_{p\in P}p^{-1/2}\leq y^\lambda\) gives the boundary \(1-\lambda\). Thus \(\lambda=1/6\) gives 5/6 and \(\lambda=1/4\) gives 3/4; a family of exponents approaching those values from below suffices as well. The [existing producer](../../formal/GaloisForLFunctions/RHTower/JointAncestryBudgetZeroFreeLaw.lean#L51) applied to the baseline supplies only \(\lambda<1/8\).

The newer [endpoint budget producer](../../formal/GaloisForLFunctions/RHTower/JointAncestryEndpointBudgetProducer.lean#L326) supplies a budget proportional to \((\log y)^{3/2}/(\log\log y)^4\). This is meaningful progress on its own scale, but is smaller than every fixed positive power of y. It neither reaches the required power budgets nor improves what the accepted baseline supplies here. The cutoff and prime-budget quantifiers cannot be dropped.

The most useful next question is therefore specific: **can the accepted fixed gap help prove an independent estimate for a residual, signed covariance, or one-sided source at a strictly better exponent?** The audited corpus supplies places to insert such an estimate, but not a completed argument producing it.

## 6. Dirichlet L-functions: existing source and remaining estimate

The Suzuki and Wold criteria above concern the particular ζ/Xi arithmetic source. Their theorem parameters do not range over Dirichlet characters. A ζ improvement alone does not establish the same improvement for every Dirichlet L-function. However, the corpus already contains another route with the required character parameters; it is unnecessary to build its analytic infrastructure from scratch.

The inspected Dirichlet result [DirichletLZeroFreeLogStrip.lean:330](../../formal/GaloisForLFunctions/RHTower/DirichletLZeroFreeLogStrip.lean#L330) proves, for each nonprincipal character, a region of the form

\[
\beta>1-\frac{c_\chi}{\log^9(3+|t|)}.
\]

There is also a large-height result at fixed modulus in the same file. These are height-dependent logarithmic regions whose left boundary approaches `1`. They do not give a fixed all-height boundary below `7/8`.

Specifically, [TwistedMobiusMellin.lean:22](../../formal/GaloisForLFunctions/RHTower/TwistedMobiusMellin.lean#L22) defines the literal source

\[
A_\chi(x)=\sum_{n\geq1}\mu(n)\chi(n)e^{-nx}.
\]

The [Mellin identity at line 90](../../formal/GaloisForLFunctions/RHTower/TwistedMobiusMellin.lean#L90) identifies its transform with `Γ(s)/L(s,χ)` on `Re(s)>1`. The [decay receiver](../../formal/GaloisForLFunctions/RHTower/TwistedMobiusZeroObstruction.lean#L24) proves that `A_χ(x)=O(x^(−b))` as `x↓0` excludes every L-zero with real part greater than `b≥0`, for each nonprincipal character. This receiver does not require primitivity. The corresponding ζ obstruction, including pole regularization, is [MobiusDecayZeroObstruction.lean:37](../../formal/GaloisForLFunctions/RHTower/MobiusDecayZeroObstruction.lean#L37).

The [mixed-convolution transfer](../../formal/GaloisForLFunctions/RHTower/TwistedMobiusMellin.lean#L234) supplies this decay from a one-sided coefficient estimate. Section 8.5 develops the order-one specialization and its even-index weakening. **The missing task on this route is a correlation estimate for every requested character, not a missing Mellin identification.** A Suzuki-based family extension would still require its own twisted-source work.

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

This section develops the routes to the two requested endpoints. “Paper reduction” means that the displayed conclusion follows from the stated inputs by the argument given here. It does not mean that the missing arithmetic estimate has been proved, or that new Lean code was checked. The accepted upstream theorem is used as a premise, never added as an axiom to the corpus.

### 8.1 Exact targets, including the endpoint issue

Write \(S(N)=\texttt{coherentSelbergSquareRootAbelMoment}\ N\). Its literal definition is

\[
S(N)=\sum_{k=1}^{N-1}(\sqrt{k+1}-\sqrt k)(\psi(k)-k).
\]

This is [CCMFUSuzukiSelbergOutgoingAbelWeld.lean:32](../../formal/GaloisForLFunctions/RHTower/CCMFUSuzukiSelbergOutgoingAbelWeld.lean#L32). Its exact completion gives \(G_N=S(N)/N+O(1)\): the lattice defect divided by N is \(O(N^{-1/2})\), and the polar and archimedean corrections are uniformly bounded. Those bounds are retained explicitly in the [existing transfer proof](../../formal/GaloisForLFunctions/RHTower/SuzukiTransitionCoreFiniteContactWidthClassification.lean#L255).

Moreover \(A_N^2\asymp N\), \(C_N\asymp N\), and \(E_N\asymp |G_N|^2\), with positive constants independent of N. The lower core bound follows from \(A_N^2\leq C_N\) and the [linear lower bound on \(A_N^2\)](../../formal/GaloisForLFunctions/RHTower/SuzukiTransitionCoreAlignedGammaCompletion.lean#L238); the upper bounds were established in Section 2. Thus, for each fixed \(m\geq1\),

\[
P_m(N)\asymp \frac{|G_N|^{2m}}{N^{m-1}}.
\]

This is a two-sided comparison. It prevents mistaking a change of residual order for an arithmetic saving.

In the following table, an exponent means a bound with an arbitrarily small positive power loss: for every \(\varepsilon>0\), some constant bounds the quantity by \(N^{\text{exponent}+\varepsilon}\). Constants may depend on ε.

| Quantity | Accepted 7/8 baseline | Target 5/6 | Target 3/4 |
|---|---:|---:|---:|
| \(\lvert S(N)\rvert\) | 11/8 | 4/3 | 5/4 |
| \(\lvert G_N\rvert\) | 3/8 | 1/3 | 1/4 |
| \(\lvert G_N/A_N\rvert\) | −1/8 | −1/6 | −1/4 |
| \(P_2(N)\) | 1/2 | 1/3 | 0 |
| \(P_3(N)\) | 1/4 | 0 | −1/2 |
| \(\sum_{2\leq N\leq X}\lvert G_N\rvert^2\) | 7/4 | 5/3 | 3/2 |

The baseline column follows from the existing generalized von Koch theorem and summing the square-root weights. The pointwise target columns are sufficient through the existing continuation machinery. Section 8.4 proves the sufficiency of the weaker mean-square condition in the last row.

**Endpoint correction:** bounded \(P_3\) is sufficient for 5/6, but it is stronger than necessary. Bounds \(P_3(N)=O_\varepsilon(N^\varepsilon)\) for every ε also suffice. Likewise 3/4 needs only subpower \(P_2\), not necessarily bounded \(P_2\). Apply the continuation theorem at every slightly larger amplitude exponent and then take the infimum; no uniform constant at the endpoint is required. A single fixed positive ε gives a slightly worse boundary and does not reach the stated endpoint.

The [formal polynomial-growth receiver](../../formal/GaloisForLFunctions/RHTower/QuasiRHQuotientHeadAndFiniteContactAbscissaLaw.lean#L605) covers every \(m\geq1\) and real r:
\[
P_m(N)=O(N^r)\quad\Longrightarrow\quad
\Theta\leq\frac12+\max\!\left(0,\frac{m-1+r}{2m}\right).
\]
Its [converse upper bound](../../formal/GaloisForLFunctions/RHTower/QuasiRHQuotientHeadAndFiniteContactAbscissaLaw.lean#L711) has exponent \(2m(\Theta-\tfrac12)-(m-1)+\varepsilon\). The [exact exponent law](../../formal/GaloisForLFunctions/RHTower/QuasiRHQuotientHeadAndFiniteContactAbscissaLaw.lean#L806) shows that changing m alone supplies no arithmetic improvement. The missing work is the rate estimate for the literal residual.

### 8.2 Tail control and the self-contracting cutoff

This reduction supplies something the baseline can already pay for. Define

\[
F(q)=\log(q!)-\sum_{d\leq q}\lfloor q/d\rfloor+2\gamma q,
\qquad
T(N)=\texttt{mobiusDivisorSquareRootAbelMoment}\ N.
\]

The corpus proves \(|F(q)|\leq24\sqrt q\) and
\(T(N)=S(N)+2\gamma(\sqrt N-1)\) in [CCMFUSuzukiMobiusDivisorAbelProducer.lean:44](../../formal/GaloisForLFunctions/RHTower/CCMFUSuzukiMobiusDivisorAbelProducer.lean#L44) and [line 86](../../formal/GaloisForLFunctions/RHTower/CCMFUSuzukiMobiusDivisorAbelProducer.lean#L86). It also proves the exact finite decomposition

\[
T(N)=\sum_{q=1}^{N-1}F(q)K_N(q),\qquad
K_N(q)=\sum_{1\leq d,\ qd<N}\mu(d)
\left(\sqrt{\min(N,(q+1)d)}-\sqrt{qd}\right).
\tag{8.1}
\]

See [CCMFUSuzukiMobiusDivisorDilationChannels.lean:638](../../formal/GaloisForLFunctions/RHTower/CCMFUSuzukiMobiusDivisorDilationChannels.lean#L638). Both the complete blocks and the clipped terminal block are present.

**Paper lemma: baseline-dependent tail estimate.** Suppose, for a fixed \(1/2<\beta<1\) and \(C_\beta\geq0\),
\[
|M(D)|=\left|\sum_{d\leq D}\mu(d)\right|\leq C_\beta D^\beta
\quad(D\geq1).
\]
Then, for integers \(N\geq2\), \(q,Q\geq1\),
\[
|K_N(q)|\leq2C_\beta N^{\beta+1/2}q^{-\beta-1},
\]
and
\[
\left|\sum_{Q<q<N}F(q)K_N(q)\right|
\leq\frac{48C_\beta}{\beta-1/2}
N^{\beta+1/2}Q^{1/2-\beta}.
\tag{8.2}
\]

**Proof.** Extend the weight
\(w(d)=\sqrt{\min(N,(q+1)d)}-\sqrt{qd}\)
by zero outside \(1\leq d<N/q\). It rises as
\(\sqrt d(\sqrt{q+1}-\sqrt q)\) until \(d=N/(q+1)\), then falls as
\(\sqrt N-\sqrt{qd}\). Its maximum is at most \(\sqrt N/q\), so its discrete total variation is at most \(2\sqrt N/q\). The corpus's [boundary-free Abel identity](../../formal/GaloisForLFunctions/RHTower/CCMFUSuzukiMobiusDivisorDilationChannels.lean#L377) is
\[
K_N(q)=\sum_{d\leq\lfloor(N-1)/q\rfloor}M(d)(w(d)-w(d+1)).
\]
Every d in this sum is at most \(N/q\); the first bound follows. Multiply by \(24\sqrt q\), sum, and use
\(\sum_{q>Q}q^{-\beta-1/2}\leq Q^{1/2-\beta}/(\beta-1/2)\).
This proves (8.2), including the moving boundary; an empty tail is zero.

The needed Mertens premise is available from the accepted zero-free half-plane: [MobiusMertensAbscissaLittlewood.lean:58](../../formal/GaloisForLFunctions/RHTower/MobiusMertensAbscissaLittlewood.lean#L58) gives \(M(D)=O_\delta(D^{b_0+\delta})\) under zero-freeness right of \(b_0\). Absorb the harmless \(D+1\) into the constant.

**Lean theorem.** With Θ denoting the actual `zetaZeroAbscissa`, [CCMFUSuzukiMobiusQuotientTail.lean](../../formal/GaloisForLFunctions/RHTower/CCMFUSuzukiMobiusQuotientTail.lean#L126) proves the uniform remainder bound
\[
|T(N)-H(N,Q)|\leq C_\varepsilon N^{\Theta+\varepsilon+1/2}
Q^{1/2-\Theta-\varepsilon}
\]
for every ε>0, all N, and Q≥1, with no assumed zero-free strip. The [clipped-kernel bound](../../formal/GaloisForLFunctions/RHTower/CCMFUSuzukiMobiusClippedKernelBound.lean#L116) includes the moving endpoint. The [power-cutoff theorem](../../formal/GaloisForLFunctions/RHTower/CCMFUSuzukiMobiusQuotientPowerCutoff.lean#L16) gives exponent `Θ+1/2−θ(Θ−1/2)+ε` at `Q=ceil(N^θ)`. Its one-ninth, one-third, and one-quarter specializations are unconditional statements about Θ; the numerical substitutions below use the accepted baseline.

For a one-step use of a current boundary \(1/2<b_0<1\), choose a desired \(1/2<b_1<b_0\) and
\[
\theta=\frac{b_0-b_1}{b_0-1/2},\qquad Q_N=\lceil N^\theta\rceil.
\]
Applying (8.2) at \(\beta=b_0+\delta<1\) gives
\[
T(N)=H_{b_0,b_1}(N)+O_\varepsilon(N^{b_1+1/2+\varepsilon}),
\quad
H_{b_0,b_1}(N)=\sum_{1\leq q\leq\min(Q_N,N-1)}F(q)K_N(q).
\tag{8.3}
\]
Indeed the exponent is
\(b_0+1/2-\theta(b_0-1/2)+\delta(1-\theta)
=b_1+1/2+\delta(1-\theta)\); choose δ small enough for the requested ε.

| Current boundary \(b_0\) | Desired boundary \(b_1\) | Sufficient one-step head cutoff | Tail already controlled |
|---|---|---|---|
| 7/8 | 5/6 | \(q\leq\lceil N^{1/9}\rceil\) | \(O_\varepsilon(N^{4/3+\varepsilon})\) |
| 7/8 | 3/4 | \(q\leq\lceil N^{1/3}\rceil\) | \(O_\varepsilon(N^{5/4+\varepsilon})\) |
| 5/6 | 3/4 | \(q\leq\lceil N^{1/4}\rceil\) | \(O_\varepsilon(N^{5/4+\varepsilon})\) |

These cutoffs are sufficient choices for the one-step argument, not necessary thresholds. Taking absolute values in the head with the same Mertens bound only recovers \(O_\varepsilon(N^{11/8+\varepsilon})\). Even its small fixed q terms can carry that cost.

**Any fixed positive power cutoff suffices with self-contraction.** Put
\[
H_\theta(N)=H(N,\lceil N^\theta\rceil),\qquad \theta>0.
\]
The [upper one-sided theorem](../../formal/GaloisForLFunctions/RHTower/QuasiRHQuotientHeadAndFiniteContactAbscissaLaw.lean#L325) and [lower counterpart](../../formal/GaloisForLFunctions/RHTower/QuasiRHQuotientHeadAndFiniteContactAbscissaLaw.lean#L383) prove
\[
\frac{H_\theta(N)}N\leq C+CN^c
\quad\Longrightarrow\quad
\Theta\leq\tfrac12+\max(0,c),
\]
for \(C\geq0\) and all integers \(N\geq2\), with the same conclusion from \(-(C+CN^c)\leq H_\theta(N)/N\). No baseline strip is assumed. To see why, set \(a=\Theta-\tfrac12\). The tail bound and one-sided Abel receiver give \(a\leq\max(c,(1-\theta)a+\delta)\) when \(c\geq0\). If \(a>c\), choose \(\delta=\min(\theta,1)a/2>0\); both entries of that maximum are strictly smaller than a, a contradiction. This argument is formalized in the cited theorems.

Shortening the quotient range does not shorten every Möbius sum: the q=1 kernel still contains dilations \(d<N\). The theorem removes a cutoff restriction; it does not supply cancellation in the retained source. It concerns fixed \(\theta>0\), not \(\theta=0\) or a cutoff varying subpolynomially with N.

**The increment head has the same controlled remainder.** Write \(R_N(n)=\operatorname{mobiusDilationRieszTail}(N,n)\), \(L=\min(Q,N-1)\), and
\[
I(N,Q)=\sum_{n=1}^{L}(\log n-\tau(n)+2\gamma)R_N(n).
\]
The [exact truncated Abel identity](../../formal/GaloisForLFunctions/RHTower/QuasiRHQuotientHeadBoundary.lean#L20) is
\[
H(N,Q)=I(N,Q)-F(L)R_N(L+1).
\]
The boundary cannot be discarded by the full-range identity. It is nevertheless controlled: summing the kernel envelope gives
\[
|R_N(Q+1)|\ll_\varepsilon N^{\Theta+1/2+\varepsilon}Q^{-\Theta-\varepsilon}.
\]
Together with \(|F(Q)|\leq24\sqrt Q\), this bounds the boundary at the same rate as the quotient tail. The [formal increment-head estimate](../../formal/GaloisForLFunctions/RHTower/QuasiRHQuotientHeadBoundary.lean#L141) consequently proves
\[
|T(N)-I(N,Q)|\ll_\varepsilon
N^{\Theta+1/2+\varepsilon}Q^{1/2-\Theta-\varepsilon}
\qquad(Q\geq1).
\]
The same self-contraction argument therefore applies to one-sided estimates for \(I(N,\lceil N^\theta\rceil)\). This offers an explicit source involving the divisor increment; it does not supply its cancellation estimate. The [dyadic reconstruction identity](../../formal/GaloisForLFunctions/RHTower/QuasiRHQuotientHeadBoundary.lean#L53) also shows that the first quotient channel reconstructs the full signed Riesz tail along powers of two. A short cutoff alone therefore supplies no smallness estimate for that channel.

### 8.3 Two concrete proof obligations

Choose any fixed \(\theta>0\), as small as useful for the arithmetic argument. The same choice can serve both targets.

**Route to 5/6.** Prove, for every \(\varepsilon>0\), a constant \(B_\varepsilon\geq0\) such that, for all sufficiently large N,
\[
H_\theta(N)\leq B_\varepsilon N^{4/3+\varepsilon}.
\tag{R5}
\]
An analogous lower bound suffices instead. The estimate must retain the signed sum over the actual \(F(q)\), Möbius coefficients, and clipped weights in (8.1).

The deduction from (R5) is complete: divide by N, absorb finitely many exceptions, and apply the self-contracting theorem at \(c=1/3+\varepsilon\). It gives \(\Theta\leq5/6+\varepsilon\); let ε decrease to zero and use the functional equation for the reflected edge. The resulting strip is \([1/6,5/6]\). The lower one-sided theorem gives the same conclusion from the lower version.

**Route to 3/4.** Replace (R5) with
\[
H_\theta(N)\leq B_\varepsilon N^{5/4+\varepsilon}
\tag{R3}
\]
for every ε and all sufficiently large N, or its lower counterpart. The identical deduction uses \(c=1/4+\varepsilon\) and yields \([1/4,3/4]\).

The one-step choices in Section 8.2 remain available, including \(N^{1/4}\) after establishing 5/6. Self-contraction permits arbitrarily smaller fixed positive powers already, so those choices do not constrain the revised arithmetic target.

**Arithmetic work still required.** Prove joint cancellation between the complete and terminal portions of \(K_N(q)\), and across the retained q range. Their [exact complete/terminal split](../../formal/GaloisForLFunctions/RHTower/CCMFUSuzukiMobiusDivisorDilationChannels.lean#L471) is available. Independent absolute estimates discard the needed information. Relative to the baseline, the first target needs a power saving \(N^{1/24}\) in the Abel action; the second needs \(N^{1/8}\). These are explicit research obligations, not established estimates.

**Verdict:** the tail estimates and self-contracting receivers are formalized. (R5) and (R3) remain the open arithmetic core. Their deduction needs no accepted baseline, but neither estimate has been proved.

### 8.4 Mean-square route: sharp exponent law and paid dilation diagonal

Put \(u(N)=T(N)/N\), with T the literal Möbius–divisor Abel moment, and
\[
\mathcal A(X)=\sum_{N=2}^{X}u(N)^2.
\]
The [sharp mean-square module](../../formal/GaloisForLFunctions/RHTower/QuasiRHMeanSquareAbscissa.lean)
proves, unconditionally,
\[
\mathcal A(X)\leq C X^r\ (r\geq1)
\quad\Longrightarrow\quad \Theta\leq r/2,
\qquad
2\Theta=\inf\{r\geq1:\exists C\geq0,\ \forall X\geq2,\ \mathcal A(X)\leq CX^r\}.
\tag{8.4}
\]
The same sharp receiver and exact infimum law hold for the already defined completed
formation energy \(\mathcal F(X)\). These are laws for the actual abscissa; they supply
no new numerical upper bound for it. The infimum need not be attained.

**Why the full exponent is recovered.** Fix \(0<\theta<1\). The window
\([N-\lfloor N^\theta\rfloor,N]\) eventually lies in \([N/2,N]\) and has at least
\(N^\theta\) points. A bound \(\mathcal A(N)\leq CN^r\) therefore supplies a point k
in every such window with
\[
|u(k)|\ll_{C,r,\theta} k^{(r-\theta)/2}.
\]
The existing one-sided power-gap bootstrap applies to this good-sample set and gives
\(\Theta\leq1/2+(r-\theta)/2\). Letting \(\theta\uparrow1\) gives \(\Theta\leq r/2\).
Conversely, the unconditional bound
\(u(N)=O_\varepsilon(N^{\Theta-1/2+\varepsilon})\) gives the cumulative upper exponent
\(2\Theta+\varepsilon\). This proves the exact infimum formula without adding another
analytic-continuation argument.

For the completed source \(G_N\), the code proves \(|u(N)-G_N|\leq D\), with a constant D
independent of N, and retains the exact production identity
\[
\mathcal F(N+1)-\mathcal F(N)=\frac{N+1}{N+2}G_{N+1}^2.
\]
In particular,
\[
\sum_{N=2}^{X}G_N^2\leq G_2^2+2(\mathcal F(X)-\mathcal F(2)),
\qquad
\mathcal A(X)\leq4\mathcal F(X)+2G_2^2+4|\mathcal F(2)|+2D^2X.
\]
These comparisons transfer the sharp exponent with the initial values and bounded
completion corrections included. For every \(b\geq1/2\), the endpoint criterion is
\[
\Theta\leq b
\quad\Longleftrightarrow\quad
\forall\varepsilon>0,\ \exists C_\varepsilon\geq0,\ \forall X\geq2,
\quad\mathcal F(X)\leq C_\varepsilon X^{2b+\varepsilon}.
\tag{MS}
\]
Thus the target powers are \(5/3+\varepsilon\) for 5/6 and \(3/2+\varepsilon\) for 3/4.
Every positive epsilon is required. Exceptional large individual amplitudes are allowed;
monotonicity of formation energy alone supplies no upper estimate.

**The dilation head and diagonal are already paid for.** Write
\(a_{M,d}=\operatorname{mobiusDivisorDilationChannel}(M,d)\),
\(D_\varphi(M)=\lfloor M^\varphi\rfloor\), and
\(I_{M,\varphi}=\{d:D_\varphi(M)<d<M\}\).
The [dilation/hyperbola module](../../formal/GaloisForLFunctions/RHTower/QuasiRHDilationTailHyperbolaAndOutgoingPotentialAbscissaLaw.lean)
proves \(|a_{M,d}|\leq(3/5)\sqrt M\) and the exact head/tail decomposition.
For \(\varphi\geq1/2\), the cumulative normalized head square is at most
\((9/25)X^{2\varphi}\).

Keep the signed, ordered off-diagonal sum
\[
V_\varphi(X)=\sum_{M=2}^{X}\frac1{M^2}
\sum_{d\in I_{M,\varphi}}\sum_{e\in I_{M,\varphi}\setminus\{d\}}a_{M,d}a_{M,e},
\]
and let \(\mathcal T_\varphi(X)\) be the cumulative square of the normalized high-dilation
tail. The literal diagonal satisfies
\[
0\leq\mathcal T_\varphi(X)-V_\varphi(X)
=\sum_{M=2}^{X}\frac1{M^2}\sum_{d\in I_{M,\varphi}}a_{M,d}^2
\leq\frac9{25}X.
\]
No orthogonality or independence is asserted: all cross terms remain in V. In particular,
\(V_\varphi(X)\geq-9X/25\), and
\[
\mathcal A(X)\leq2\mathcal T_\varphi(X)+\frac{18}{25}X^{2\varphi},
\qquad
\mathcal T_\varphi(X)\leq2\mathcal A(X)+\frac{18}{25}X^{2\varphi}.
\]
The [covariance module](../../formal/GaloisForLFunctions/RHTower/QuasiRHDilationCovarianceAbscissa.lean)
combines these inequalities with the sharp mean-square law. For \(b\geq\varphi\geq1/2\),
\[
\Theta\leq b
\quad\Longleftrightarrow\quad
\forall\varepsilon>0,\ \exists C_\varepsilon\geq0,\ \forall X\geq2,
\quad V_\varphi(X)\leq C_\varepsilon X^{2b+\varepsilon}.
\tag{DC}
\]
At \(\varphi=1/2\), the infimum of upper growth exponents \(r\geq1\) of V is exactly
\(2\Theta\). At the target cutoffs, the concrete remaining obligations are:

| Strip | Dilation cutoff | Active quotient range in the transposed tail | One-sided covariance target |
|---|---|---|---|
| \([1/6,5/6]\) | \(\lfloor M^{5/6}\rfloor\) | \(q\leq M^{1/6}\) | \(V_{5/6}(X)\leq C_\varepsilon X^{5/3+\varepsilon}\) |
| \([1/4,3/4]\) | \(\lfloor M^{3/4}\rfloor\) | \(q\leq M^{1/4}\) | \(V_{3/4}(X)\leq C_\varepsilon X^{3/2+\varepsilon}\) |

The exact quotient support is \(1\leq q\leq\lfloor(M-1)/(D_\varphi(M)+1)\rfloor\).
The complete-rectangle factorization supplies a weighted Möbius square-root sum; its
cancellation still needs proof. The head ceiling, diagonal ceiling, and finite hyperbola
identity do not prove (DC). The open arithmetic work is a signed upper estimate for
these distinct-dilation interactions, with every epsilon and moving cutoff controlled.

**Exact power meshes and averaged covariance targets.** The
[power-mesh module](../../formal/GaloisForLFunctions/RHTower/QuasiRHPowerMeshSquareSampleAndObserverJetAbscissaLaw.lean)
removes the rounding terms altogether. At \(M=j^m\), \(D=j^{m-1}\), with \(m\geq2\),
\[
\left\lfloor\frac{j^m-1}{j^{m-1}+1}\right\rfloor=j-1.
\]
Thus the exact normalized tail is
\[
t_m(j)=j^{-m}\sum_{q=1}^{j-1}F(q)
 \operatorname{mobiusHighDilationClippedAbelKernel}(j^m,j^{m-1},q).
\]
Here \(F(q)=\operatorname{primeFreeDivisorDefect}(q)\); all original signs and clipping
boundaries remain in the kernel.

For every integer \(m\geq1\), put
\(\mathcal A_m(J)=\sum_{j=2}^{J}u(j^m)^2\). The sharp mesh law is
\[
\mathcal A_m(J)\leq CJ^r\ (r\geq1)
\quad\Longrightarrow\quad
\Theta\leq\frac12+\frac{r-1}{2m},
\qquad
\inf\{r\geq1:\mathcal A_m(J)=O(J^r)\}
=1+2m(\Theta-1/2).
\tag{PM}
\]
The [mesh mean-square module](../../formal/GaloisForLFunctions/RHTower/QuasiRHPowerMeshMeanSquareAbscissa.lean)
uses finite-window averaging in the index j. A selected k satisfies
\(j-k\leq j^\theta\) and \(|u(k^m)|\ll k^{(r-\theta)/2}\).
For \(j=\lfloor N^{1/m}\rfloor\), the polynomial difference bound gives
\[
N-k^m\leq m2^m N^{1-(1-\theta)/m}.
\]
The physical power-gap saving stays positive for every \(\theta<1\). Applying the
existing arithmetic bootstrap and letting \(\theta\uparrow1\) proves the receiver
in (PM). The intrinsic bound at \(\Theta\) gives its converse. Taking m=1 recovers
the full-integer mean-square law.

Let \(W_m(J)\) be the ordered covariance above, sampled at these exact M and D:
\[
W_m(J)=\sum_{j=2}^{J}\frac1{j^{2m}}
 \sum_{j^{m-1}<d<j^m}\ \sum_{\substack{j^{m-1}<e<j^m\\ e\ne d}}
 a_{j^m,d}a_{j^m,e}.
\]
For even \(m\geq2\), the head bound is \((3/5)j^{m/2-1}\), and
\[
0\leq\sum_{j=2}^{J}t_m(j)^2-W_m(J)\leq\frac9{25}J,
\qquad
\mathcal A_m(J)\leq2W_m(J)+\frac{36}{25}J^{m-1},
\qquad
W_m(J)\leq2\mathcal A_m(J)+\frac{18}{25}J^{m-1}.
\]
Consequently each row below is an exact equivalence, with every \(\varepsilon>0\)
and every integer \(J\geq2\):

| Zero strip | Exact mesh and dilation cutoff | Remaining one-sided averaged estimate |
|---|---|---|
| \([1/6,5/6]\) | \(M=j^6,\ D=j^5,\ 1\leq q<j\) | \(W_6(J)\leq C_\varepsilon J^{5+\varepsilon}\) |
| \([1/4,3/4]\) | \(M=j^4,\ D=j^3,\ 1\leq q<j\) | \(W_4(J)\leq C_\varepsilon J^{3+\varepsilon}\) |

These permit exceptional large individual samples. They demand an average estimate
for the literal signed covariance, not a pointwise bound at every j. Using the accepted
7/8 baseline as a mathematical premise gives mesh-energy exponents \(11/2+\varepsilon\)
and \(4+\varepsilon\), respectively. The desired average savings are therefore a
half-power and a full power in J. Neither saving is supplied by the diagonal bound.

**Sharp cost of positive normalization after the cutoff.** The
[high-dilation positive-envelope module](../../formal/GaloisForLFunctions/RHTower/QuasiRHHighDilationPositiveEnvelope.lean)
proves an unconditional lower bound for the actual retained coefficients. Write
\(U(M,D)=\sum_{D<d<M}|a_{M,d}|\) and \(Q(M,D)=\sum_{D<d<M}a_{M,d}^2\).
On every power mesh \(M=j^m,D=j^{m-1}\), uniformly for integers \(m\geq1\) and
sufficiently large j,
\[
Q(M,D)\asymp M^2,\qquad U(M,D)\asymp M\sqrt M.
\]
The proof starts from the existing positive full-diagonal lower bound. Deleting D
channels costs at most DM; here \(D/M=1/j\). The channel ceiling then transfers the
remaining diagonal mass to an absolute-mass lower bound. Consequently, for each fixed m,
\[
\mathcal P_m(J):=\sum_{j=2}^{J}
 \left(\frac{U(j^m,j^{m-1})}{j^m}\right)^2
\asymp_m J^{m+1}.
\tag{PE}
\]
Both bounds in (PE) are formalized, as is the impossibility of an eventual upper bound
\(\mathcal P_m(J)\leq CJ^m\).

For every nonnegative probability weight w on the retained channels, positive on each
nonzero coefficient, Cauchy–Schwarz costs
\[
U(M,D)^2\leq\sum_{D<d<M}\frac{a_{M,d}^2}{w_d}.
\]
Zero coefficients can be omitted. The weights \(w_d=|a_{M,d}|/U(M,D)\) attain equality
whenever U is positive. Thus optimizing positive weights on the unprocessed channels
still costs \(J^7\) on the sixth-power mesh and \(J^5\) on the fourth-power mesh.
Each misses its signed target by two powers in J. Small quotient support \(q<j\)
does not reduce the absolute mass to that of j independent channels. The missing
improvement must come from proved signed cancellation or a comparison preserving it;
these positive-envelope bounds impose no corresponding lower bound on the signed tail.

Available short-interval mechanisms still require additional estimates:
[Gallagher's window inequality](../../formal/GaloisForLFunctions/RHTower/Sieve/GallagherSplitIntegral.lean)
takes frequency mean-square and supremum bounds as inputs, while the
[signed Selberg interval identity](../../formal/GaloisForLFunctions/BiScaleUncertainty/SignedLcmFractionalDefectAndCompleteFibreCollapse.lean)
retains an uncontrolled signed fractional-part defect. Applying either mechanism here
requires an exact comparison with the clipped kernel and a bound for the remaining
frequency energy or defect. Neither retrieved statement supplies the two table entries.

These new mean-square statements concern ζ and ξ; the Dirichlet-character extension
remains a separate obligation in Section 8.5.

### 8.5 Binary Möbius correlation route, including Dirichlet characters

This route has the most direct common arithmetic target for ζ and the Dirichlet family. Set \(c_\chi(n)=\mu(n)\chi(n)\) and
\[
\mathcal C_\chi(m)=\sum_{a+b=m}c_\chi(a)\overline{c_\chi(b)}.
\]
The coefficients are real but need not be nonnegative. The definition and conjugation identity are already in [DirichletLMixedAdditiveZeroAbscissaLaw.lean:24](../../formal/GaloisForLFunctions/RHTower/DirichletLMixedAdditiveZeroAbscissaLaw.lean#L24).

It is enough to bound **only even totals**, and only from above:

| Target | Sufficient new arithmetic estimate, for each ε>0 |
|---|---|
| 5/6 | \(\mathcal C_\chi(2m)\leq B_{\chi,\varepsilon}(m+1)^{2/3+\varepsilon}\) for all m |
| 3/4 | \(\mathcal C_\chi(2m)\leq B_{\chi,\varepsilon}(m+1)^{1/2+\varepsilon}\) for all m |

For ζ, use \(c(n)=\mu(n)\). For the family, prove the displayed bound for each nonprincipal χ with the same exponent; constants may depend on χ. Finite exceptions can be absorbed in the constant.

**Proof of the reduction.** For \(A_\chi(r)=\sum_n c_\chi(n)r^n\), absolute convergence on \(|r|<1\) gives, for real \(0<r<1\),
\[
2\sum_{m\geq0}\mathcal C_\chi(2m)r^{2m}
=|A_\chi(r)|^2+|A_\chi(-r)|^2
\geq |A_\chi(r)|^2.
\]
If \(\mathcal C_\chi(2m)\leq B(m+1)^\nu\), substitute \(r=e^{-x}\), \(0<x\leq1/2\), and sum the exponential moment:
\[
|A_\chi(e^{-x})|^2\ll_\nu Bx^{-\nu-1}.
\]
Thus the literal Laplace source in Section 6 is \(O(x^{-(\nu+1)/2})\). Its Mellin identity and zero obstruction exclude zeros to the right of \((\nu+1)/2\). Apply this at \(\nu=2/3+\varepsilon\) or \(1/2+\varepsilon\), then let ε decrease to zero. Principal characters follow from the ζ result and their finite Euler factors, whose extra zeros lie on \(\Re s=0\).

The even-index estimate-to-decay theorem is already [EvenIndexHermitianOrderLowerEdge.lean:141](../../formal/GaloisForLFunctions/RHTower/EvenIndexHermitianOrderLowerEdge.lean#L141). The ζ pole obstruction is already formalized, as is the nonprincipal-character obstruction. The mathematical gap is the displayed correlation bound. No new spectral identification is required.

**Attempted shortcut and its failure.** The corpus's [raw order inequality](../../formal/GaloisForLFunctions/RHTower/RawMobiusHermitianExcursionLaw.lean#L104) gives \(2\Theta-1\leq\Psi_1\leq1\), where Θ is the zero abscissa and \(\Psi_1\) the positive-excursion order of the raw correlation. Substituting \(\Theta\leq7/8\) does not prove \(\Psi_1\leq3/4\): that would reverse an inequality. The trivial correlation estimate remains \(O(m)\), insufficient for either target. A result for adjacent or fixed-shift Möbius correlations also needs a proved transfer to these reflected pairs \(a+b=2m\), uniform in m.

**Verdict:** existing family-aware continuation route, with a concrete one-sided binary-correlation problem. Both target estimates remain open.

### 8.6 Work sequence and completion criteria

The improvements remain open. Checked items refer to supporting source results or the explicitly identified paper reductions, not new zero-free bounds.

- [x] Identify exact arithmetic source, its completion, and the target exponents in Section 8.1.
- [x] Prove the quotient-tail estimate and power-cutoff specializations in Lean at the actual zero abscissa.
- [x] Retain and bound the truncated Abel boundary; prove the same remainder estimate for the literal increment head in Lean.
- [x] Reduce both targets to one-sided bounds on the head through \(N^\theta\) for any fixed \(\theta>0\), using the formal self-contracting receiver. The former numerical cutoffs remain valid one-step choices.
- [x] Formalize the sharp cumulative-energy receiver \(\Theta\leq r/2\), its exact exponent law, and the completed formation-energy endpoint criterion.
- [x] Pay the dilation head and the full normalized diagonal; formalize the exact signed covariance criteria for both strips.
- [x] Preserve power gaps under integer powers; formalize the sharp mesh mean-square law and both averaged covariance criteria with exact quotient support `q<j`.
- [x] Determine the sharp positive-normalization cost on the actual retained channels: exponent `m+1`, even after optimizing weights, versus the signed target `m−1+ε`.
- [x] Identify the existing even-index and character-twisted receivers.
- [ ] Prove (R5), the signed dilation covariance estimate (DC), or the corresponding mean-square or binary-correlation estimate, for the literal arithmetic source.
- [ ] Derive the 5/6 strip with all ε and cutoff quantifiers discharged.
- [ ] Prove (R3), or its alternative, and derive the 3/4 strip.
- [ ] Prove the character-twisted estimates across the claimed Dirichlet family; a ζ-only result does not complete that scope.
- [ ] Complete unconditional Lean proofs of the remaining arithmetic estimates and numerical strip consequences.

Other useful inputs remain available below. Priority reflects proximity to an existing theorem, not a prediction that the missing estimate is easy.

#### Supporting Suzuki work

- [x] Identify and formalize the available normalized decay: `E_N^2 / C_N = o(N)`, with exact energy/amplitude identities and no zero-width premise. See Section 2.4.
- [ ] Improve that rate for the **literal** residual, keeping the gamma completion and source signs intact.
- [ ] Aim first for `O(N^r)` with an explicit `r < 1/2`. `r = 1/3` is a concrete route to `5/6`; boundedness reaches the existing `3/4` theorem.
- [ ] If using the factor-two Ward restriction, first prove its quantitative comparison with the aligned completed Abel scalar, then bound the aggregate contribution. A sign theorem for another cross form is insufficient.
- [x] Formalize the power-growth receiver and exact finite-contact exponent law; the required improved arithmetic rate remains open.
- [ ] Alternatively, prove the existing order-three boundedness hypothesis directly and use the already stated finite-contact theorem.

**Completion criterion:** a proof of the improved arithmetic estimate that does not assume the target strip or RH, followed by the numerical strip consequence. An implication whose only new premise is that estimate is not completion.

#### Alternative one-sided prime-lag estimate

- [ ] Choose the more accessible sign and target exponent `a = 1/3`, or any explicit `a < 3/8`.
- [ ] Prove the bound on all sufficiently large primes, or choose the existing Abel sampling theorem and prove its exact coverage condition.
- [ ] Trace every imported estimate’s hypotheses. Separate unconditional logarithmic control from fixed power control.

**Completion criterion:** a source estimate satisfying `hM` or `hA` with the desired exponent and all required quantifiers, not a statement holding only on average or on an inadequately controlled exceptional set.

#### Alternative Wold signed covariance estimate

- [x] Account for the existing full-kernel and moving-mask results: they prove normalized means vanish, not the raw bound needed here.
- [ ] Seek an upper bound uniform in cutoff `N` for `Cov_t(N)` beyond `t = 1/8`.
- [ ] A clean target is every `0 < t < 1/6`, which feeds the existing `5/6` equivalence directly.
- [ ] Preserve the signs of the cross terms. Use the already proved diagonal and lower-bound results to keep the unresolved task confined to the necessary upper estimate.

**Completion criterion:** the stated covariance bound for the actual Wold residual, at the required radii, with no stronger zero hypothesis hidden in its derivation.

#### Alternative weighted Möbius moment

- [ ] If new Möbius cancellation estimates arise, test whether they imply `WeightedMertensMoment a` for some `a > 1/8`; `a = 1/6` is a useful target.
- [ ] For the character family, prioritize the already identified twisted binary source in Section 8.5. If a different ζ route succeeds first, prove its character-dependent extension separately.

### 8.7 Upstream Gram improvement: useful, but insufficient by itself

The apparent slack in the upstream central budget does not move its low-source floor. [LowGramScale.lean:37](../../tmp/hgt-openai-math/quasirh-source/OAI/NumberTheory/DirichletL/Detector/LowGramScale.lean#L37) traces `3/16` to the square root of a Gram bound. At scales `X=Z^x`, `Y=Z^y`, its leading exponent is `(5x+y)/12`. The [principal normalization](../../tmp/hgt-openai-math/quasirh-source/OAI/NumberTheory/DirichletL/PrincipalSignalComparison.lean#L411) has shift `c=x/3−5/6+L/6`, where L is total prime-slot length.

With `x+y=5/6` and `L=1/6`, subtracting c gives exactly `7/8` for every redistribution of x and y. Retuning to `x+y=1−L` would nominally give `11/12−L/4`, but the displayed reflected-energy inequalities admit a zero-retained-length configuration requiring loss at least `max(0,(6L−1)/5)`. Paying half that energy loss gives

\[
B(L)=\frac{11}{12}-\frac L4+\frac12\max\left(0,\frac{6L-1}{5}\right)
\geq\frac78,
\]

with equality only at `L=1/6`. The exact witness and sharp minimum are formalized in [QuasiRHDetectorScaleBudget.lean:44](../../formal/GaloisForLFunctions/RHTower/QuasiRHDetectorScaleBudget.lean#L44) and [line 92](../../formal/GaloisForLFunctions/RHTower/QuasiRHDetectorScaleBudget.lean#L92). **This is an obstruction to the stated exponent-budget retuning, not a lower bound on actual arithmetic energy or a proof that the upstream strategy cannot improve.** Its paper proof and scope are recorded in the [route card](../drafts/pipeline/5-failed/quasi-rh-detector-scale-retuning.md).

The actual arithmetic target is now more precise. [GramClassification.lean:24](../../tmp/hgt-openai-math/quasirh-source/OAI/NumberTheory/DirichletL/Detector/GramClassification.lean#L24) identifies exceptional frequencies by valuations divisible by six away from a fixed modulus. Their count supplies the power `P^(1/6)`, where `P=Y²/Q`. [GramIdealMass.lean:85](../../tmp/hgt-openai-math/quasirh-source/OAI/NumberTheory/DirichletL/Detector/GramIdealMass.lean#L85) bounds the weighted sum after discarding coefficient signs. The actual coefficients are the Möbius weights in [GramSourceDivisors.lean:24](../../tmp/hgt-openai-math/quasirh-source/OAI/NumberTheory/DirichletL/Detector/GramSourceDivisors.lean#L24), and the exceptional contribution is retained explicitly by [GramTruncation.lean:17](../../tmp/hgt-openai-math/quasirh-source/OAI/NumberTheory/DirichletL/Detector/GramTruncation.lean#L17). These weights implement the coprimality restriction in [GramCanonicalSource.lean](../../tmp/hgt-openai-math/quasirh-source/OAI/NumberTheory/DirichletL/Detector/GramCanonicalSource.lean); their signs alone do not imply a power saving or eliminate sixth-power frequencies.

- [x] Locate the estimate producing `3/16` and distinguish it from the slack high-row budgets.
- [x] Prove the scale-redistribution invariant and reflected-budget obstruction, including their positive sharp-boundary statement.
- [ ] Estimate the actual Möbius-weighted exceptional contribution before taking absolute values, or identify and remove a controlled secondary term while preserving the principal signal.
- [x] Classify the joint Gram improvements needed for five sixths, retaining the unit and nonexceptional terms and allowing both scales to change.
- [ ] Prove such a joint bound for the actual source. An exceptional-only saving cannot reach five sixths within the retained profile.
- [ ] Once a stronger arithmetic estimate exists, propagate the same explicit boundary through conductor geometry, moments, transport errors, source correction, and continuation. Distinguish zero-boundary constants from auxiliary slot ratios.

**Completion criterion:** a stronger estimate for the actual source and all remaining estimates needed by the assembled nonvanishing argument at one explicit improved boundary, for the claimed character family. The parameter audit alone does not meet this criterion.

There is a further restriction relevant to the requested endpoints. The [actual Gram estimate](../../tmp/hgt-openai-math/quasirh-source/OAI/NumberTheory/DirichletL/Detector/LowGramApplied.lean#L24) contains `1 + P^(1/6) + P²/Y`. Replacing only the exceptional exponent by `ν` leaves the unit term. At the original compensated scales, `Y/X = Z^(1/8)`, so the low-source exponent from this estimate is at least `17/96 + max(0,ν)/16`. After the principal normalization, its best possible boundary is therefore

\[
b(\nu)=\frac{83}{96}+\frac{\max(0,\nu)}{16}.
\]

It reproduces `7/8` at `ν=1/6` and stalls at `83/96` once `ν≤0`. Since `5/6=80/96` and `3/4=72/96`, even eliminating the exceptional contribution completely does not reach either milestone through this unchanged estimate. Formally substituting `u=2/3` or `u=2` into the isolated exponent identity would discard the dominating unit term. Those substitutions are not valid improvement arguments. This is a limitation of the retained upper bound and scales, not an arithmetic lower bound on the actual source.

**Joint scale classification, proved in Lean.** Write `X=Z^x`, `Y=Z^(1−L−x)`, and propose the profile `1+P^ν+P^κ/Y`. With

\[
e=\max\{0,\nu(1-L-2x),(\kappa-1)(1-L)-(2\kappa-1)x\},
\qquad
B=\frac56+\frac{x-L}{6}+\frac e2+
\frac12\max\left(0,\frac{6L-1}{5}\right),
\]

[QuasiRHDetectorGramTradeoff.lean](../../formal/GaloisForLFunctions/RHTower/QuasiRHDetectorGramTradeoff.lean) proves:

| Retained estimates | Exact consequence |
|---|---|
| Unchanged nonexceptional power `κ=2`, arbitrary exceptional power | `B≥23/27>5/6`. Deleting the exceptional term attains this bound at `L=1/6`, `x=5/18`, `y=5/9`. |
| Both powers variable, `ν≥0` | Some `x≥0,L∈ℝ` gives `B≤5/6` **iff** `ν≤1/15` and `κ+4ν≤4/3`. |
| Only the unit term, current reflected allowance, `x≥0` | Minimum `29/36>3/4`, attained at the relaxed boundary `x=0,L=1/6`. |

An explicit five-sixths witness has `ν=1/30`, `κ=6/5`, `x=5/48`, `y=35/48`, and `L=1/6`; both low scales have positive exponents. Thus the requested first milestone has a precise joint arithmetic-estimate target. The feasibility theorem classifies this displayed budget, with arbitrarily small exponent losses suppressed. It does not provide the stronger Gram estimate or certify the remaining conductor, high-row, and transport constraints at the new scales.

The three-quarters route requires a further change to the reflected allowance, principal normalization, or unit contribution. Improving the two nonunit powers alone cannot suffice within this model. The native routes in Sections 8.2–8.5 specify separate arithmetic targets for that endpoint.

**A specific arithmetic conjecture.** The [shift-correlation route](../drafts/pipeline/1-in-progress/quasi-rh-shift-correlation.md) proposes
\[
\mathcal M_4(\chi,S):=\sum_{x\in\mathbb F_p}
\left|\sum_{h\in S}\chi(x-h)\right|^4
\ll_\varepsilon p^{1+\varepsilon}|S|^2
\quad (|S|\leq p^{1/3})
\]
for residue intervals S and order-six characters. The card derives the candidate conductor factor \(p^{1/6}\) under this estimate and the required amplification bounds. Matching-pair degeneracies, their exact \(2|S|^2-|S|\) count, cross-ratio normalization, and the fourth-moment expansion are formalized; the signed off-diagonal estimate and its transport to the detector are not.

Window geometry is essential. [QuasiRHSubfieldMoment.lean](../../formal/GaloisForLFunctions/RHTower/QuasiRHSubfieldMoment.lean#L142) constructs fields of size \(q=5^{12n+6}\), characters of exact order six, and sets of size \(B=5^{4n+2}\), with \(B^3=q\) and \(\mathcal M_4\geq4\cdot5^{2n}qB^2\). Thus the cardinality-only extension to arbitrary square-field sets is false. The surviving [affine-line projection identity](../../formal/GaloisForLFunctions/RHTower/QuasiRHSubfieldProjection.lean#L121) identifies the line-occupancy contribution exactly. A narrower pilot conjecture uses balanced boxes \(S=I+\omega J\subset\mathbb F_{p^2}\), \(p\equiv5\bmod6\), comparable side lengths, and \(|S|\leq q^{1/3}\); it asks for the same \(q^{1+\varepsilon}|S|^2\) bound. These boxes avoid the exhibited concentration on a single subfield line, but their fourth-moment estimate remains open.

**Stop or redirect a proposed argument** if it only reproduces the baseline exponent, substitutes an RH-dependent provider, discards the signed interaction being estimated, or proves a result for a different source without an identification theorem. Preserve any nontrivial estimate or classification obtained along the way; failure to reach a narrower strip does not erase that mathematical result.

## 9. Evidence and verification

The sources are the native Lean corpus, the RH frontier ledger, and the cached upstream Lean tree. Local research search covered theorem statements, proof bodies, dependencies, and research notes; exact `rg` searches and source reads checked candidate applicability. Reproducible entry points include:

```bash
scripts/formal_tools.py research '"zero-free" "half-plane"' --mode lexical --no-refresh --per-module 0 --limit 160 --explore 0 --json
scripts/formal_tools.py research 'mobiusClippedAbelKernel Mertens variation tail quotient' --mode deep --budget-seconds 180 --no-refresh --json
scripts/formal_tools.py research 'one sided upper bound reflected Mobius binary correlation sum mu n mu N minus n power saving' --mode deep --budget-seconds 120 --no-refresh --json
```

Search suggestions are leads, not proof compositions. In particular, shifted truncated-divisor correlations, fixed-core prime-release limits, and Selberg-sieve bounds with an unproved residual-variance premise do not supply the actual estimates required here. Ranked results and incomplete compiler coverage cannot establish the absence of every possible theorem elsewhere in the corpus.

**Formal verification:** the three quotient-tail modules and `QuasiRHQuotientHeadBoundary` linked in Section 8.2 pass focused `lake --old env lean` checks without warnings and are wired into `RHTower`. Section 8.4 has checked Lean proofs in `QuasiRHMeanSquareAbscissa`, `QuasiRHDilationCovarianceAbscissa`, `QuasiRHPowerMeshMeanSquareAbscissa`, and `QuasiRHHighDilationPositiveEnvelope`, also wired into `RHTower`. Their 43 public theorem audits use only `propext`, `Classical.choice`, and `Quot.sound`. The statements retain the actual zero abscissa and literal arithmetic sources. The decisive head, dilation covariance, and character-twisted correlation estimates remain open; neither improved strip is proved. Existing Suzuki normalization and detector-budget leaves are supporting results with the scopes stated above.

The recorded global formal lint run flags one unrelated module absent from its theorem-area umbrella: `SquareRootThreshold.WeilGroundStateLawOnLagLattices`. It reports no error in these quasi-RH leaves. No full or umbrella build was run.

The upstream theorem's soundness is assumed. External novelty of these reductions is unclaimed; no web research is used.
