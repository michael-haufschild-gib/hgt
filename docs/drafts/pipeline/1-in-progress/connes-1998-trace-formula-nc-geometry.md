# Connes 1998 — Trace formula in noncommutative geometry and the zeros of the Riemann zeta function

- **ID:** connes-9811068
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean) — formalization programme
- **Source:** arXiv:math/9811068 (Selecta Math. NS 5 (1999) 29–106). Local LaTeX copy fetched from
  `https://arxiv.org/e-print/math/9811068` (single file `zeta.tex`, 5468 lines).
- **Statement:** Formalize unconditionally in Lean 4 every lemma / theorem / provable proposition of
  the paper that mathlib or the HGT corpus does not already own.

## Goal
Own, as closed Lean theorems with no hypotheses beyond the literal mathematical data, the
self-contained mathematical content of Connes' adele-class trace formula paper. The deep global
statements (Thm III.1, Thm VII.4, Thm VIII.5) sit on a large adelic-analysis stack; the programme
builds that stack bottom-up, and every intermediate brick is itself a closed theorem.

## Paper statement inventory

Labels below are `§sec (eq)` or `App X Lemma n`. Status column is maintained here — this card is the
compaction-surviving ledger.

### Tier A — elementary / self-contained
| Tag | Statement | Lean module | Status |
|---|---|---|---|
| A1 | §III(17), App I(2): `ρ(u)=(1+u²)^{δ/2}` submultiplicative up to `2^{δ/2}` | `ConnesSobolevWeight` | DONE |
| A2 | App I(4)(5): weighted translation norm `‖V(v)‖ ≤ (c ρ(v))^{1/2}`; `V(f)` defined | `ConnesSobolevWeight` | DONE |
| A3 | App I(29): `∫ (log|x|)^{2k}(1+log²|x|)^{-δ/2} d*x < ∞ ↔ 2k − δ < −1` | `ConnesSobolevWeight` | DONE |
| A4 | §VII(8): S-unit lattice sup bound `Sup_S y_v ≥ (1/2n)∑|y_v|` on `∑ y_v = 0` | `ConnesSUnitSupBound` | DONE |
| A5 | §VII(43): `|a⁺ − b⁺| ≤ |a − b|` | `ConnesSUnitSupBound` | DONE |
| A6 | §VIII(39)(43): semiclassical area `∫_{D'_+} ω = (2E/2π)logΛ − (E/2π)(log(E/2π) − 1)` | `ConnesSemiclassicalArea` | DONE |
| A7 | App II Lemma 2: `A + B = 0`, i.e. `(1−1/q)² ∑ (−n log q) q^{-n} = −q^{-1} log q` | `ConnesNonArchPrincipalValue` | DONE |
| A8 | App IIb: unique Haar on modulated group; `N=ℝ*₊ ⟹ dλ/λ`; `N=μ^ℤ ⟹ α=log μ`; (9)–(12) | `ConnesModulatedHaar` | DONE |
| A9 | App I(34): `W(λ)^t η_{t,a} = ∑_b C(a,b) λ^{it}(log λ)^b η_{t,a−b}` | `ConnesJordanTriangular` | DONE |
| A10 | §V(28): `g(λ) = h((λ+1)^{-1})|λ+1|^{-1}` is `C_c^∞` on `K` when `h ∈ C_c^∞(K^*)` | `ConnesSymbolChart` | DONE |
| A11 | §III(19): `E U(a) = |a|^{1/2} V(a) E` | `ConnesPeriodizationEquivariance` | DONE |
| A12 | App I(37)(38): `E(f)(x) = E(f̂)(1/x)` for `f ∈ 𝒮(A)₀` from Poisson summation | `ConnesPeriodizationEquivariance` | DONE |
| A13 | App II(44): `(1/2π)∫₀^{2π} dθ/|1−e^{iθ}z|² = 1/(1−|z|²)` (`|z|<1`), `1/(|z|²−1)` (`|z|>1`) | `ConnesComplexFiberIntegral` | DONE |
| A14 | App II(53): `−4∫₀^{π/2} log sin u du = 2π log 2` | `ConnesComplexFiberIntegral` | DONE |
| A15 | App II(49)(51): `j(ε) = 4∫_{log ε}^{log 2} arccos(e^x/2) dx = 2π log(1/ε) + o(1)` | `ConnesComplexLogAreaAsymptotics` | DONE |
| A16 | App II(35): `lim(∫_{|x|≥ε} f d*x + log ε f(0)) = lim(∫ f\|x\|^ε d*x − f(0)/ε)` | `ConnesArchPrincipalValue` | PARTIAL — both indicator computations `A_ε(1_box)=0`, `B_ε(1_box)=0` proved; the limit form needs DCT (moved to B9) |
| A17 | App II(32): `⟨−log|u|, e^{−πu²}⟩ = ½log π + γ/2 + log 2` | `ConnesGaussianLogMoment` | DONE |
| A18 | App II(41): `⟨−log|z|_ℂ, e^{−2π|z|²}⟩ = log 2π + γ` | `ConnesGaussianLogMoment` | DONE |
| A19 | §V(35): `P(f_a) = P(f) − log|a| f(0)` for the log-regularized principal value | `ConnesArchPrincipalValue` | DONE |
| A20 | §VIII(30): pairs of projections; `sin Θ = |P₁−P₂|`; `Θ` commutes with `P_i`; ℤ/2∗ℤ/2 irreps ≤ 2-dim | `ConnesProjectionPair` | DONE |
| A21 | App I(15)–(20): `⟨1_R,Δ'_s⟩=1`, homogeneity `⟨f^a,Δ'_s⟩=|a|^{-s}⟨f,Δ'_s⟩`, `Δ'_s=(1−q^{-s})Δ_s` | `ConnesLocalHomogeneousDistribution` | DONE |
| A22 | App III: graph δ-section, `∫δ(y−f(x))ξ(y)dy = ξ(f(x))`; transversality ⟺ `1−P` invertible; symbol `\|det(1−A)\|⁻¹` | `ConnesGraphDelta` | DONE |
| A23 | §IV(19)–(21): 1-D flow trace `∫ h(t)/|1−e^t| dt`; multiplicative form `∫ h(u)/|1−u| d*u` | `ConnesFlowTrace` (reuses corpus `MellinL2.exp_measurePreserving`) | DONE |
| A24 | §V(7): `(φ∘L)^ = |det L|^{-1} φ̂∘(L^{-1})^t` | `ConnesLinearFourier` | DONE |
| A25 | §V(10)(11): convolution of the two line measures gives the constant `|1−λ|^{-1}` | `ConnesLinearFourier` | DONE |
| A26 | §VIII Lemma 3 model: geometric-ratio limit + Poisson reproducing `∫ P_w(u)u^k du/2π = w^k` | `ConnesResonanceModel` | DONE |
| A27 | App I(27)(28): `φ·α = 0` for `α ∈ 𝒟'`, `φ` smooth with finite-order zeros ⟹ `α ∈ span{δ^{(k)}_{x_i}}` | `ConnesDivisionDistribution` (reuses corpus `HTGeometry.exists_delta_representation`, `jetTest`) | DONE |

### Tier B — heavy analytic layers
| Tag | Statement | Status |
|---|---|---|
| B1 | §V Thm 3 (local trace formula) | **analytic chain DONE at the real place.** `ConnesSymbolChangeOfVariables.connes_symbol_changeOfVariables` = (29)→(31) (window mass (30), inner substitution, Fubini with the product integrability proved); `ConnesLocalTraceCore.connes_traceCore_tendsto` = (31)→(33) (Schwartz tails (32)); `connes_symbolIntegral_tendsto` chains them.  Also `ConnesSymbolChart` = (28), `ConnesGaussianLogMoment` = (34)-(36).  **Open:** the operator step (23)(24) identifying `Trace(R_Λ U(h))` with the symbol integral — a trace-class Schwartz-kernel layer for an operator that is not Hilbert–Schmidt |
| B2 | §VII Lemma 1 | (8) done (A4).  For `k = ℚ` the corpus already owns Lemma 1(a) as `FieldOneFiniteStageBruhatOrbit_summable` / `…BruhatPeriodization` (= Connes–Marcolli Lemma 2.29).  **Open:** (10) and Lemma 1(b) (Fourier unitary on `L²(X_S)`) |
| B3 | §VII Thm 4 | **Open**; needs B1 + B2 + B4 |
| B4 | §VII Lemma 2 | (43) done (A5); (44) done (`ConnesLogShiftKernel.connes_integrable_logShiftKernel`, finiteness of `c'_α` for `0<α<1` at the real place); (45) done (`connes_logShift_substitution`, `connes_logShift_bound`).  **Open:** the Besov estimate (42) and its assembly on `A_S` |
| B5 | App I Lemmas 1–5 | (1)–(6) of the Sobolev layer done (`ConnesSobolevWeight`, `ConnesApproximateUnit.connes_approxUnit_mass_le` = the uniform bound of Lemma 4).  **Open:** the strong convergence `V(f_n) → 1`, and Lemmas 1–3 (Tate/Iwasawa homogeneous distributions on `A`) |
| B6 | App I / Thm III.1 | the *conclusion* steps are Lean-owned: (15)–(20) local homogeneity (A21), (27)(28) division (A27), (29) Sobolev membership (A3), (34) Jordan form (A9).  **Open:** Lemmas 1–3 and the growth of `L(χ₀,½+it)` |
| B7 | App II Thm 6 | Lemma 2's `A+B=0` done (A7); Lemma 3 done (`ConnesCharacterRescaling.connes_logDistribution_character_rescale`); (54) done at all three place types; (18)(19) done (`ConnesWeilRewriting.connesHatMoment_zero_add_one`, `connes_weilD_inversion`).  **Open:** Weil's explicit formula itself, which the paper *quotes* from [W3] |
| B8 | §VIII Lemma 1, Cor 2, Thm 5, Lemma 3 | window count (9)/(12)/(13) done (`ConnesFunctionFieldWindow`); (22)/(23) support done (`ConnesPeriodizationEquivariance.connesPeriodization_support_window`); (23)/(25) positivity mechanism done (`ConnesPositiveTypeCutoff`); Lemma 3's model computation done (A26); §VIII (30) pair-of-projections done (A20); §VIII (35)–(43) semiclassical area done (A6).  **Open:** the full Theorem 5, which needs B3 + B6 |
| B9 | App II (35) in limit form | **DONE** — `ConnesArchPrincipalValue.connes_logPV_sub_powerPV_tendsto` |

Note: App II Theorem 1 (Weil's explicit formula) is *quoted*, not proved, in this paper; it is not in
the "provable propositions of this paper" scope except through the corpus's own explicit-formula
layer (`XiGuinandWeilExplicitFormula`, `xi_explicitFormula_logDeriv`).

## Corpus assets found before building (do not rebuild)
- `RHTower/FieldOneFiniteStage*` (≈65 modules): `A_S = ℝ × ∏_{v∈S} ℚ_v`, self-dual Haar, S-units,
  Bruhat–Schwartz carrier, orbit summability/periodization (Connes–Marcolli Lemma 2.29 = §VII Lemma 1a
  for `k=ℚ`), idele-class module, fundamental domain, multiplicative-from-additive Haar.
- `RHTower/Slepian*`, `Prolate*`, `CCMRadialProlate*`: the Landau–Pollak–Slepian layer of §VIII.
- `RHTower/XiGuinandWeilExplicitFormula`, `XiExplicitFormulaLogDeriv`: explicit formulas.
- `HTGeometry/PoissonBoundaryPositivity`, `Bottcher/PoissonBoundary`: Poisson kernel.
- `RHTower/ArchimedeanMellinFourier`: Poisson summation (even/dilated).
- `RHTower/CCMRationalAdelicBruhatSchwartzSpace`: Bruhat–Schwartz on `𝔸_ℚ`.

## Log
- 2026-08-21 — created; paper read in full; statement inventory frozen; corpus audit done.
- 2026-08-21 — A1-A3 landed (`ConnesSobolevWeight`); A4, A5 landed (`ConnesSUnitSupBound`);
  A6 landed (`ConnesSemiclassicalArea`); A7 landed (`ConnesNonArchPrincipalValue`);
  A13, A14 landed (`ConnesComplexFiberIntegral`).
- 2026-08-21 — A9 (`ConnesJordanTriangular`), A10 (`ConnesSymbolChart`), A24/A25
  (`ConnesLinearFourier`), A11/A12 (`ConnesPeriodizationEquivariance`) landed.
- 2026-08-21 — A8 (`ConnesModulatedHaar`), A20 (`ConnesProjectionPair`),
  A21 (`ConnesLocalHomogeneousDistribution`), A19 + A16-indicators
  (`ConnesArchPrincipalValue`) landed.  A16's limit form split off as B9.
- 2026-08-21 — A23 (`ConnesFlowTrace`) and A27 (`ConnesDivisionDistribution`) landed, both built on
  existing corpus assets (`RHTower.MellinL2` exponential measure-preserving equivalence;
  `HTGeometry.PointSupportStructure.exists_delta_representation` + `jetTest`) rather than rebuilt.
- 2026-08-21 — A17, A18 landed (`ConnesGaussianLogMoment`), reusing mathlib's
  `Complex.hasDerivAt_GammaIntegral` / `digamma_one_half` and the corpus's
  `HTGeometry.integral_log_mul_exp_neg_Ioi` and `HTGeometry.integral_Ioi_rpow_mul_gaussian`.
- 2026-08-21 — **Tier A complete: 27/27.**  A15 (`ConnesComplexLogAreaAsymptotics`),
  A22 (`ConnesGraphDelta`), A26 (`ConnesResonanceModel`) landed.  All 19 modules build, are wired
  into `GaloisForLFunctions.RHTower`, and every capstone `#print axioms` shows only
  `propext, Classical.choice, Quot.sound`.  `scripts/formal_tools.py lint` reports no error against
  any `Connes*` module (the three umbrella-reachability errors it prints belong to other agents'
  modules `EulerSquarefreeWickInteractionCohomology`, `GaussianRealMoments`,
  `MultilinearPolarization`).

## Landed modules (all in `formal/GaloisForLFunctions/RHTower/`)
`ConnesSobolevWeight`, `ConnesSUnitSupBound`, `ConnesSemiclassicalArea`,
`ConnesNonArchPrincipalValue`, `ConnesComplexFiberIntegral`, `ConnesJordanTriangular`,
`ConnesSymbolChart`, `ConnesLinearFourier`, `ConnesPeriodizationEquivariance`,
`ConnesProjectionPair`, `ConnesLocalHomogeneousDistribution`, `ConnesModulatedHaar`,
`ConnesArchPrincipalValue`, `ConnesFlowTrace`, `ConnesDivisionDistribution`,
`ConnesGaussianLogMoment`, `ConnesGraphDelta`, `ConnesResonanceModel`,
`ConnesComplexLogAreaAsymptotics`.
- 2026-08-21 — Tier B batch 1: B9 complete (`connes_logPV_sub_powerPV_tendsto`);
  B7a (`ConnesCharacterRescaling`), B8a (`ConnesFunctionFieldWindow`),
  B4a-scaling (`ConnesLogShiftKernel`), and the whole analytic chain of Theorem V.3 at the real
  place (`ConnesLocalTraceCore` + `ConnesSymbolChangeOfVariables`).  5 new modules wired into
  `GaloisForLFunctions.RHTower`.
- 2026-08-21 — Tier B batch 2: (44)+(45) complete (`ConnesLogShiftKernel`), App I Lemma 4 uniform
  bound (`ConnesApproximateUnit`), App II (18)(19) rewriting (`ConnesWeilRewriting`),
  §VIII (23)(25) positivity mechanism (`ConnesPositiveTypeCutoff`), §VIII (22) support window
  (added to `ConnesPeriodizationEquivariance`).  26 Connes modules total, all wired into
  `GaloisForLFunctions.RHTower`, all `#print axioms` clean, lint clean.

## What remains genuinely open (named external inputs)
1. **Trace-class Schwartz kernels.**  `Trace(R_Λ U(h)) = ∫∫ σ` for `R_Λ U(h)` trace class but not
   Hilbert–Schmidt.  Blocks the last step of B1 and hence B3.
2. **`L²(X_S)` for a non-type-I quotient.**  Blocks B2(b), hence B3.
3. **Tate/Iwasawa homogeneous distributions on `A`** (App I Lemmas 1–3) plus polynomial growth of
   `L(χ₀,½+it)`.  Blocks B6, hence B8's Theorem 5.
4. **Weil's explicit formula** (App II Theorem 1, quoted from [W3]).  Blocks B7's Theorem 6.
Everything in the paper that does not reduce to one of these four is now Lean-closed.

- 2026-08-21 — Tier B batch 3 (open item 4, non-archimedean half of Weil's explicit formula).
  Six new modules, all wired into `GaloisForLFunctions.RHTower` and built:
  * `ConnesPadicWeilKernel` — the ultrametric equality `|1-u| = max(1,|u|)` off the unit sphere, and
    the shell form `|1-u|^{-1} = min(1, p^m)` on `‖u‖ = p^{-m}`, `m ≠ 0`  (App II (9)/(10)).
  * `ConnesPadicWeilShellIntegral` — the chart valuation/norm identities, the exact one-shell Weil
    integral, and the local Weil integral as a series over valuation shells.  Built on the corpus's
    `FieldOnePadicMultiplicativeHaarDecomposition` / `…ShellIntegral`.
  * `ConnesPadicWeilRadial` — radial functions on `ℚ_p^*`: integrability ⟺ shell-profile
    summability, `∫ = ∑' shell values`, and the closed form
    `∫ f(u)|1-u|^{-1} d^*u = ∑'_m min(1,p^m) h(m)` for a profile vanishing on the unit shell.
  * `ConnesPadicWeilVonMangoldt` — the half-density weight identity
    `min(1,p^m)·p^{-m/2} = p^{-|m|/2}` (with `√p` only as an integer power), the two-half-line split
    of the shell sum, and the local term in von Mangoldt form
    `∑_{n≥1} p^{-n/2}(G(n)+G(-n))`.
  * `ConnesPadicWeilEulerFactor` — the geometric profile `h(m) = w^m` (`m ≥ 1`), its summability,
    local Weil term `w/(1-w)`, and at `w = p^{-s}` the local Euler factor `(p^s-1)^{-1}`.
  * `ConnesWeilPrimeSide` — **the finite part of Connes' geometric side is the prime side of the
    explicit formula**: for `σ > 1`,
    `∑'_p log p · (local Weil term at p) = -ζ'(σ)/ζ(σ)`, using the corpus's
    `HTGeometry.tsum_vonMangoldt_eq_tsum_primes` and `HTGeometry.ofReal_tsum_vonMangoldt_eq`.
  This reduces open item 4: the zero-sum side is already corpus-owned
  (`RHTower.xiGuinandWeilExplicitFormula` on the regularized-Cauchy test algebra), and the finite
  places of the geometric side are now Lean-closed.  What is left of item 4 is the archimedean local
  term and the assembly for a general Bruhat–Schwartz test function.

- 2026-08-21 — Tier B batch 4 (open item 4, archimedean half + global assembly).  Two new modules:
  * `ConnesArchWeilTerm` — the archimedean Weil kernel in logarithmic coordinates,
    `e^{t/2}|1-e^t|^{-1} = (2 sinh(t/2))^{-1}`; the Gauss-regularized local term
    `∫_0^∞ ( e^{-t}/t − e^{-(s−1/2)t}(2 sinh(t/2))^{-1} ) dt = ψ(s)` and its integrability; and the
    completed form `∫_0^∞ ( e^{-t}/t − e^{-(s/2−1/2)t}(2 sinh(t/2))^{-1} ) dt
    = 2·(Γ_ℝ'/Γ_ℝ)(s) + log π`.  Built on the corpus's `RHTower.digamma_eq_integral_gauss`
    (Gauss's integral representation) and `logDeriv_Gammaℝ`.
  * `ConnesTraceFormulaResolvent` — **`connesGeometricSide σ`** (finite places + the two polar
    terms + the archimedean term) and the capstone
    **`connes_traceFormula_resolvent`**: for real `σ > 1`,
    `∑'_q (a_q^{-1} − (a_q − z)^{-1}) = −i · connesGeometricSide σ`, `z` the centred coordinate of
    `σ`.  This is Connes' Theorem 6 for the regularized-Cauchy test algebra: the spectral sum over
    the multiplicity-exact centred Xi divisor equals `−i` times the sum over the places of `ℚ` of
    the local Weil terms.  Assembled from `connes_weil_primeSide`,
    `connes_archWeil_eq_logDeriv_Gammaℝ`, `RHTower.logDeriv_archFactor_closed_off_poles`,
    `RHTower.xiGuinandWeilExplicitFormula_single`.
  All new capstones `#print axioms` clean (`propext, Classical.choice, Quot.sound`).
  **Open item 4 is now closed for the resolvent test class at a real abscissa.**  What remains of
  it is only the general Bruhat–Schwartz test function (a Fourier/Mellin extension of the same
  identity), not any new arithmetic input.

- 2026-08-21 — Tier B batch 5: `ConnesTraceFormulaComplex` extends the trace formula from a real
  abscissa to **every admissible centred base point**.  Corpus assets reused rather than rebuilt
  (`RHTower.support_vonMangoldtTerm_subset_primePow`, `RHTower.primeGradeSource_term_eq`,
  mathlib's `tsum_eq_tsum_primes_of_support_subset_prime_powers`,
  `ArithmeticFunction.LSeriesSummable_vonMangoldt`):
  * `connes_weil_primeSide_complex` — for every `Re s > 1`,
    `∑_p log p · (local Weil term at p) = L(Λ, s)`.
  * `connesGeometricSideC` / `connesGeometricSideC_eq` — Connes' geometric side at an arbitrary
    abscissa equals `L(Λ,s) − (logDeriv archFactor)(s)`.
  * `connes_traceFormula_resolvent_complex` — for every `z` with `Re(1/2 + zi) > 1`,
    `∑'_q (a_q^{-1} − (a_q − z)^{-1}) = −i · connesGeometricSideC (1/2 + zi)`.
  All `#print axioms` clean; `scripts/formal_tools.py lint` exits 0 with no errors.

- 2026-08-21 — Tier B batch 6 (open item 3, App I Lemma 1 local half; and the B5 Sobolev layer).
  * `ConnesTateLocalZeta` — **App I (25)**: with `vol(ℤ_p^*) = 1`,
    `∫_{ℤ_p ∩ ℚ_p^*} |x|^s d^*x = (1 - p^{-s})^{-1}` (`connes_padic_tate_local_zeta`), and
    `connes_tate_local_zeta_tprod`: the product of these local integrals over the primes is
    `riemannZeta s` for `Re s > 1` (mathlib's `riemannZeta_eulerProduct_tprod`).  This is
    Appendix I Lemma 1 for `k = ℚ`, `Χ_0 = 1`, in the shape the paper proves it.
    NOTE: the *other* half of open item 3 — polynomial growth of `L(χ₀,½+it)` — is already
    corpus-owned for `k = ℚ` (`RHTower.exists_bound_norm_riemannZeta_vertical`,
    `…_strip`); it does not need to be rebuilt.
  * `ConnesSobolevMeasure` — the measure `ρ_δ(u) du`, its finiteness on compacts (hence
    regularity, hence density of `C_c`), the `eLpNorm` form of the translation bound
    `‖V(v)‖ ≤ (2^{δ/2} ρ_δ(v))^{1/2}`, and `ρ_δ ≤ 2^{δ/2}` on `[-1,1]`.
  * `ConnesSobolevTranslationContinuity` — **continuity of translation on `L²_δ(ℝ)`**:
    `connes_translation_tendsto_of_compactSupport` (dominated convergence against a fixed
    compact neighbourhood) and `connes_translation_tendsto` (density + the uniform operator
    bound on `|v| ≤ 1`).
  * `ConnesSobolevTranslationOperator` — `connesTranslate` as an operator of
    `Lp ℂ 2 (ρ_δ du)`, its a.e. formula, `V(0) = 1`, the norm bound, the identity
    `V(v) − V(w) = V(w)(V(v−w) − 1)` in `eLpNorm` form, and **strong continuity**
    `continuous_connesTranslate`.
  Remaining for B5: assemble `V(f) = ∫ f(v)V(v)dv` as a Bochner integral in `L²_δ` and prove
  `V(f_n) → 1` strongly for `f_n(v) = n f(nv)` (approximate identity + dominated convergence,
  using `ρ_δ(v/n) ≤ ρ_δ(v)`).

- 2026-08-21 — **B5 CLOSED.**  `ConnesApproximateUnitStrong` completes Appendix I Lemma 4:
  * `connesTranslateBound δ v = (2^{δ/2} ρ_δ(v))^{1/2}`, its continuity, monotonicity in `|v|`,
    and `1 ≤ connesTranslateBound`.
  * `connesV hδ f ξ = ∫ f(v) V(v)ξ dv` as a Bochner integral in `L²_δ(ℝ)`, with
    `connes_integrable_smul_translate`, `connesV_sub` (`V(f)ξ − ξ = ∫ f(v)(V(v)ξ − ξ)dv` when
    `∫ f = 1`) and `norm_connesV_sub_le`.
  * `connesDilate f a v = a f(av)`, `integral_connesDilate` (mass is preserved),
    `connes_integrable_dilate` (the same profile dominates every dilate, via
    `connesTranslateBound_mono`).
  * **`connes_approxUnit_tendsto`**: for `f` with `∫ |f(v)| ρ_δ(v)^{1/2} dv < ∞` and `∫ f = 1`,
    `V(f_n) → 1` strongly on `L²_δ(ℝ)` with `f_n(v) = n f(nv)`.  Proof: change of variables plus
    dominated convergence against `‖f(w)‖(ρ_δ(w)^{1/2}·2^{δ/4} + 1)‖ξ‖`, using the strong
    continuity of the translation group.
  Everything unconditional; all `#print axioms` clean.  Open item 3 is now reduced to Appendix I
  Lemmas 2–3 for the adele class space (the `E(f)` periodization decay and the analytic
  continuation of `Δ_s`); the local Lemma-1 computation and the `L(χ₀,½+it)` growth are done.

- 2026-08-22 — Tier B batch 7 (App I Lemma 2's decay, §VII Lemma 2's Besov chain, §VII Lemma 1(b)).
  Five new modules, all built and wired:
  * `ConnesLatticeRapidDecay` — **App I (46)**: `connesLatticeSum f a = ∑_{n ≠ 0} ‖f(a n)‖` for a
    Schwartz `f`, its summability (reusing the corpus's
    `ccmRationalArchimedeanSchwartz_lattice_summable`), and
    `connes_latticeSum_rapidDecay`: `λ^k · ∑_{n ≠ 0} ‖f(λ c n)‖ → 0` for every `k`.  This is the
    archimedean estimate that makes `E(f)` decay faster than every power of `|x|`.
  * `ConnesCutoffCommutator` — **§VII (43)/(46)**: `connesCutoffExcess L x = (log|x| − L)^+`, its
    1-Lipschitz bound in `log|x|`, the exact commutator identity (the two leading terms cancel),
    the integrability of the cut-off logarithmic-difference kernel, and
    `connes_cutoff_commutator_bound`: the commutator is at most
    `c'_α |x|^{-α} · sup_{|ε| ≤ 1} ‖η(x+ε)‖`.
  * `ConnesCutoffTailDecay` — **§VII (47)**: `connesUnitSup`, the thickened Schwartz bound
    `connesUnitSup η x ≤ 2^m σ_m(η)/|x|^m` for `|x| ≥ 2`, and `connes_cutoff_tail_rapidDecay`:
    `L^N ∫_{Ioi L} x^{-α} sup_{|ε|≤1}‖η(x+ε)‖ dx → 0` for every `N`.
  * `ConnesOrbitFormFourier` — **§VII Lemma 1(b), the mechanism**: `connesOrbitForm U f g =
    ∑'_q ⟪f, U(q)g⟫` and `connes_orbitForm_invariant`: an ambient isometry intertwining the group
    action with inversion preserves the orbit form (the inversion is a bijection of the group, so
    it only reindexes the sum).  Also the summability transfer.
  * `ConnesFourierUnitaryExtension` — `connesCompletionUnitary`: an isometric linear automorphism
    of a pre-Hilbert space extends to a unitary of its Hilbert completion, agreeing with it on the
    dense subspace (mathlib's `LinearEquiv.extendOfIsometry`).  Together with the previous item
    this is Lemma 1(b) for any concrete realization of `L²(X_S)`.
  All `#print axioms` clean.  Remaining in this lane: §VII (41) (the Besov–Fourier sup inequality),
  (48), and the adelic realization of `E(f)` for `k = ℚ`.

- 2026-08-22 — Tier B batch 8.  Three more modules:
  * `ConnesLogExcessTail` — **§VII (48)**: the exact tail integral
    `∫_T^∞ (log x − log T) x^{-δ-1} dx = T^{-δ}/δ²` (substitution `x = Tu` plus the corpus's
    `integral_rpow_mul_log_Ioi_one`), and `connes_logExcess_schwartz_rapidDecay`:
    `T^N ∫_{Ioi T}(log x − log T)‖η x‖ dx → 0` for every `N`.
  * `ConnesOrbitGeometricConvergence` — **§VII Lemma 1(a)**: `connes_exp_neg_le_rpow_inv`
    (an exponential is dominated by every reciprocal power), `connes_summable_exp_neg_latticeL1`
    (exponentially decaying families on `ℤ^d` are summable, via the corpus's
    `summable_polyDecay_fin`), and `connes_summable_of_exp_bound`: an orbit family bounded by
    `C·exp(−c·d(q,1))` is absolutely summable — the geometric convergence Lemma 1(a) asserts.
  * `ConnesFlowTransverseMap` — **App III (37)-(42)**: `connesOneSubDescend` (the descent of
    `1 − (F_t)_*` to `N_x = T_x/ℝv_x`), `connesFlowTransverseMap` (App III (41)
    `φ_*(X, λ∂_t) = (1 − (F_t)_*)X − λv`), and
    `connesFlowTransverseMap_bijective_iff`: along a periodic orbit `φ_*` is an isomorphism
    exactly when `1 − P` is one on the transverse space.  This is the periodic-orbit half of the
    transversality condition, complementing A22's fixed-point half.
  All `#print axioms` clean; lint shows no error against any `Connes*` module.
  **Corpus assets found for the remaining B1 step** (do not rebuild): `HTGeometry.HilbertSchmidtTrace`
  (`opTrace_comp_eq_hsInner`, `opTrace_comp_comm`, `norm_opTrace_comp_le`) and
  `RHTower.KernelOperatorPolarization` (`hsInner_kernelOperator`) already give
  `Trace(A∘B) = ∫∫ kernel pairing` for Hilbert–Schmidt kernel operators — but only for a *finite*
  base measure, so §V (23) still needs that layer generalized to Lebesgue measure on a local field.

- 2026-08-22 — Tier B batch 9 (**the finiteness obstruction in B1's trace step removed**).
  * `ConnesKernelOperatorGeneral` — the corpus's kernel-operator layer is built with
    `Lp.const ∞ μ e`, which forces `[IsFiniteMeasure μ]` and therefore excludes the additive Haar
    measure of a local field.  The constant field is only a Hölder device: for `K ∈ L²(μ; E* )`
    the function `x ↦ K x e` is already in `L²` because `‖K x e‖ ≤ ‖K x‖‖e‖`.  Rebuilt that way:
    `connesKernelApply`, `connesKernelOperator`, `connes_norm_l2_sq`,
    `norm_connesKernelApply_sq`, and **`isHilbertSchmidt_connesKernelOperator`** — the
    Hilbert–Schmidt kernel theorem over an *arbitrary* base measure.
  * `ConnesKernelTracePairing` — `connes_inner_kernelApply`,
    **`connes_hsInner_kernelOperator`** (the polarized kernel energy over an arbitrary measure),
    `connes_opTrace_comp_kernelOperator`, and the hypothesis-free
    **`connes_opTrace_adjoint_kernel`**: `Trace(T_K† ∘ T_L) = ∫ ⟪l_x, k_x⟫ dμ(x)` — Connes'
    §V (23) `Trace(R_Λ T) = ∫∫ k(x,y) r_Λ^t(x,y) dx dy`, no longer restricted to finite measures.
  * `ConnesScalingSymbol` — **§V (25)-(27)**: `connes_symbol_translate`, the symbol of the scaling
    operator is the Fourier transform of the chart function `g(λ) = h((λ+1)^{-1})|λ+1|^{-1}`,
    by translation invariance of the additive Haar measure alone (no property of the character).
  Also noted: **§V (24)** — the Parseval step turning the kernel pairing into the symbol integral —
  is literally mathlib's `VectorFourier.integral_fourierIntegral_smul_eq_flip`, valid for any
  locally compact abelian group with a character and a bilinear pairing, hence for every local
  field; it does not need to be rebuilt.
  What remains of B1: exhibiting `R_Λ = P̂_Λ P_Λ` and `U(h)` concretely as `connesKernelOperator`s
  over the additive Haar measure of `K`, i.e. the Schwartz-kernel identification (19)/(21).
  All `#print axioms` clean.

- 2026-08-22 — Tier B batch 10 (**§V (21) identified; the cut-off trace in closed form**).
  * `ConnesConvolutionKernelField` — `connesL2Translate` (translation on `L²(ℝ)`, via mathlib's
    `DomAddAct` action: `connesL2Translate_ae`, `norm_connesL2Translate`,
    `continuous_connesL2Translate`), then **§V (21)**: `connesConvField`,
    `memLp_connesConvField`, `connesConvKernel`, and
    `connesKernelOperator_convKernel_integral` — an operator of the shape "convolve with `k`,
    then multiply by `a`" *is* a `connesKernelOperator` over the additive Haar measure of the
    line, acting by `ξ ↦ a(x)·∫ conj(c(y−x)) ξ(y) dy`.  With `c(y) = conj ρ̂_Λ(−y)` and `a = ρ_Λ`
    this is Connes' `r_Λ^t(x,y) = ρ_Λ(x) ρ̂_Λ(x−y)`.  Strong measurability of the field is exactly
    the norm continuity of translation on `L²`; square integrability is `‖field x‖ = |a x|·‖c‖`.
  * `ConnesConvolutionTrace` — `inner_connesL2Translate` (translation preserves the `L²` inner
    product), `toDual_symm_connesConvField`, and the closed form
    **`connes_trace_convKernel`**: `Trace(T_{a,c}† ∘ T_{b,d}) = ⟪d,c⟫ · ∫ b(x) conj(a(x)) dx`.
    That is Connes' `∫∫ k(x,y) r^t(x,y) dx dy` evaluated for two convolution cut-off kernels.
  All `#print axioms` clean.  §V's remaining gap is now only (19): `U(h)` is *not*
  Hilbert–Schmidt, so its trace pairing against `R_Λ` needs the trace-class (not HS) kernel
  theorem — the one genuinely missing analytic input of B1.

- 2026-08-22 — Tier B batch 11 (**App I Lemma 2 closed at the archimedean place**).
  Corpus search found `RHTower.ccmRationalArchimedeanLatticeTrace_poisson` (the scaled Poisson
  identity `∑_n f(an) = a^{-1}∑_n f̂(n/a)` for Schwartz `f`) and
  `ccmRationalArchimedeanSchwartz_lattice_summable`; both are reused, not rebuilt.
  * `ConnesArchPeriodization` — `connesArchPunctured`, its summability, the zero-mode split, and
    **App I (37)**: `connes_archPoisson_punctured`,
    `a·∑_{n≠0} f(an) = ∑_{n≠0} f̂(n/a) + (−a f(0) + ∫f)`.  Then `connesArchPeriodization`
    (`E(f)(a) = √a ∑_{n≠0} f(an)`) and **App I (38)**:
    `connes_archPeriodization_reflect`, `E(f)(a) = E(f̂)(1/a)` on `𝒮(ℝ)_0`.
  * `ConnesArchPeriodizationDecay` — `norm_connesArchPunctured_le` and **App I Lemma 2**:
    `connes_archPeriodization_rapidDecay` (`a^k‖E(f)(a)‖ → 0` for every `k`, from App I (46)) and
    `connes_archPeriodization_rapidDecay_zero` (the same at the other end, by the reflection).
  This closes Lemma 2 — statement and proof — in the archimedean model `A = ℝ`, `k = ℤ`.  What is
  left of it is only the adelic bookkeeping (39)-(45): the tensor splitting `f = f_0 ⊗ f_1`, the
  compact-support confinement of the finite denominators, and the resulting lattice `Γ`.
  All `#print axioms` clean; lint reports no error against any `Connes*` module.

  CORRECTION to an earlier line in this log: B5's `V(f_n) → 1` is **not** open — it was closed on
  2026-08-21 as `ConnesApproximateUnitStrong.connes_approxUnit_tendsto`.

- 2026-08-22 — Tier B batch 12 (**App I (39)-(46) closed for `k = ℚ`; Lemma 2 complete**).
  Corpus search found `RHTower.ccmRationalFiniteAdele_isCompact_rationalDiagonalDenominator`
  ("diagonal rationals in a compact finite-adele set lie in one fractional integer lattice"),
  which *is* Connes' (42)/(45) for `k = ℚ`; it is reused, not rebuilt.
  * `ConnesAdelicLatticeDecay` — `connesLatticeSum_neg` (the punctured lattice sum is even in the
    spacing), `connes_latticeSum_rapidDecay'` (App I (46) for any nonzero spacing),
    `connes_rationalDiagonal_lattice` (**(42)/(45)** in the form `q = m/d`), and
    **`connes_adelicShadow_rapidDecay`** = **App I (44)-(46)**: for a weight bounded and supported
    on the rational diagonal of a compact set of finite adeles, tested against the archimedean
    Schwartz factor,
    `λ^k · ∑_{q ∈ ℚ^*} |w(q)| ‖f₁(q λ x_∞)‖ → 0` for every `k`.
    The proof reindexes the `ℚ`-sum along the injection `m ↦ m/d` (`Function.Injective.tsum_eq`,
    the support condition being exactly the denominator confinement) and then applies the
    Schwartz lattice decay.
  With this, **Appendix I Lemma 2 is closed for `k = ℚ`**: (36)/(37) and the reflection (38) in
  `ConnesArchPeriodization`, the two-sided rapid decay in `ConnesArchPeriodizationDecay`, and the
  tensor-splitting/denominator-confinement chain (39)-(46) here.
  All `#print axioms` clean.

- 2026-08-22 — Tier B batch 13 (**App I Lemma 3's continuation step closed**).
  Corpus search found `RHTower.RapidDecayRay` and
  `RHTower.differentiable_mellin_of_rapidDecayRay` ("rapid decay at both ends makes the Mellin
  transform entire") in `BoundedExponentPoissonNonlanding`; reused, not rebuilt.
  * `ConnesMellinContinuation` —
    `connes_archPunctured_continuousOn` / `connes_archPeriodization_continuousOn` (local uniform
    convergence of the punctured lattice series, via the second Schwartz seminorm and
    `continuous_tsum` on `↥(Ioi c)`);
    `connes_archPeriodization_isBigO_atTop` and `connes_archPeriodization_isBigO_zero`
    (the two Tendsto decay statements of batch 11 converted to `IsBigO` against every real power);
    `connes_archPeriodization_rapidDecayRay`; **`connes_differentiable_mellin_archPeriodization`**
    — the Mellin transform of `E(f)` for `f ∈ 𝒮(ℝ)_0` is **entire**; and
    **`connes_entire_eq_of_eqOn_halfPlane`** — two entire functions agreeing on `Re s > 1` agree
    everywhere (mathlib's identity theorem on the preconnected `univ`).
  Together these are exactly Connes' *"since both sides are analytic in `s` it holds in general"*:
  Lemma 3's continuation from `Re s > 1` (where Lemma 1 gives it) to the whole plane.
  Note: `f 0 = 0` and `∫ f = 0` are the definition of `𝒮(A)_0` (App I (31)), not added premises.
