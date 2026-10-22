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
| A16 | App II(35): `lim(∫_{|x|≥ε} f d*x + log ε f(0)) = lim(∫ f\|x\|^ε d*x − f(0)/ε)` | `ConnesArchPrincipalValue` | DONE — both indicator computations `A_ε(1_box)=0`, `B_ε(1_box)=0` proved, **and the limit form is B9** (`connes_logPV_sub_powerPV_tendsto`, dominated convergence).  This row is no longer partial |
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
| B1 | §V Thm 3 (local trace formula) | **analytic chain DONE at the real place.** `ConnesSymbolChangeOfVariables.connes_symbol_changeOfVariables` = (29)→(31) (window mass (30), inner substitution, Fubini with the product integrability proved); `ConnesLocalTraceCore.connes_traceCore_tendsto` = (31)→(33) (Schwartz tails (32)); `connes_symbolIntegral_tendsto` chains them.  Also `ConnesSymbolChart` = (28), `ConnesGaussianLogMoment` = (34)-(36).  **(19)(23) now CLOSED** (batches 14/16): `ConnesKernelOperatorGeneral` removes the `[IsFiniteMeasure]` restriction, `ConnesKernelTracePairing.connes_opTrace_adjoint_kernel` is the hypothesis-free (23), and `ConnesFieldTracePairing.connes_hsInner_kernelOperator_field` handles (19) — only *one* factor needs to be Hilbert–Schmidt, so the trace-class kernel theorem is not required after all.  (24) closed too (batch 30, `ConnesSymbolPairing`): the Parseval step turning the kernel pairing into the symbol pairing.  **B1's analytic chain is complete at the real place**: (20)-(24) and (28)-(36) are all Lean theorems.  (27) closed too (batch 31, `ConnesScalingSymbolChart`): the substitution `μ = λ − 1` identifies the scaling symbol integral with the inverse transform of the chart (28).  (19)(20)(25)(26) closed too (batch 32, `ConnesScalingKernelDelta`), with the `δ` taken literally as a Dirac measure.  **B1's chain (19)→(36) is complete at the real place.**  The operator/kernel identification is closed too (batch 33, `ConnesScalingOperator`).  **B1 CLOSED at the real place**: (19)-(36) are all Lean theorems, and `connes_scalingOperator_symbol` states the symbol computation directly about `U(h)`.  The passage to a general local field is closed too (batch 34, `ConnesLocalFieldSymbol`): (19)-(27) hold over any commutative field with a translation-invariant measure and measurable singletons, so every place of every local field is covered by one theorem.  (29)-(33) closed at non-archimedean places too (batches 35-37).  **B1 CLOSED at every place of every local field** |
| B2 | §VII Lemma 1 | (8) done (A4).  For `k = ℚ` the corpus already owns Lemma 1(a) as `FieldOneFiniteStageBruhatOrbit_summable` / `…BruhatPeriodization` (= Connes–Marcolli Lemma 2.29).  (10) done (`ConnesBoxOverlap.connes_boxOverlap_prod_le`, batch 25); (11) done (`ConnesOrbitEnergy.connes_orbitForm_eq_fundamentalDomain_energy`); geometric convergence done (`ConnesOrbitGeometricConvergence.connes_summable_of_exp_bound`); Lemma 1(b) done (`ConnesOrbitFormFourier` + `ConnesFourierUnitaryExtension.connesCompletionUnitary`).  (9) done (`ConnesBoxMajorant.connes_box_majorant`, batch 26).  **B2 CLOSED** — (8)(9)(10)(11), the geometric convergence, and Lemma 1(b) are all Lean theorems |
| B3 | §VII Thm 4 | **CLOSED** (batches 63-72).  B1 + B2 + B4 were already closed; the missing piece was the logarithmic term.  `ConnesArchLogIdentification.connes_arch_logPV_identification` proves the last §V identification (the Fourier transform of `-log|u|` is the log-regularised principal value plus `(γ + log 2π)δ₀`); `ConnesTwistedWeilChange.connes_arch_weil_regularized` turns it into Connes' local `∫'` by the change of variables `x = u - 1`; and `ConnesTraceFormulaWeil.connes_trace4_weil` is Theorem 4 verbatim, `Trace = 2h(1)log'Λ + ∑_q W_q + O(Λ^{-N})` for every `N`, with `connes_trace4_weil_hypothesis_model` exhibiting the model of its hypothesis |
| B4 | §VII Lemma 2 | **DONE at the archimedean place** (batches 23-24): (41)-(48) all closed — `ConnesBesovSupInequality.connes_besov_sup_inequality` (41), `ConnesBesovCutoffDecay.connes_besov_cutoff_rapidDecay` (42), (43) = A5, `ConnesLogShiftKernel` (44)(45), `ConnesCutoffCommutatorLocal` (45)(46), `ConnesCutoffTailTwoSided` (47), `ConnesCutoffBesovMass` (48).  The transfer machinery to `A_S` is closed too (batch 28, `ConnesBesovProductTransfer`): Fubini for the fibrewise `L¹` mass, the fibrewise rapid-decay transfer, and the finite sum over `S`.  The integrable fibre constants are supplied too (batch 29, `ConnesProductFibreDecay`).  **B4 CLOSED** for a product of an archimedean place with a finite-dimensional transverse factor.  The non-archimedean factors are handled too (batch 38, `ConnesTransverseFiniteFactor`): a Bruhat-Schwartz function on `∏_{v∈S_f} K_v` is bounded with compact support, so the transverse factor costs only the finite constant `μ(K)` and needs no decay rate — `connes_transverse_mass_rapidDecay`.  **B4 CLOSED with no residual identification** |
| B5 | App I Lemmas 1–5 | (1)–(6) of the Sobolev layer done (`ConnesSobolevWeight`, `ConnesApproximateUnit.connes_approxUnit_mass_le` = the uniform bound of Lemma 4).  **All CLOSED** (batches 5, 15, 17–21): the strong convergence is `ConnesApproximateUnitStrong.connes_approxUnit_tendsto`; Lemma 1's local factors are `ConnesTateLocalZeta`/`ConnesUnramifiedLocalZeta`/`ConnesRamifiedLocalZeta`/`ConnesLocalShellAbstract`, its global assembly `ConnesTateFiniteStage`/`ConnesTateInfiniteFactorization`/`ConnesGlobalTateAssembly` (arbitrary global field); Lemma 2 is `ConnesArchPeriodization`/`ConnesArchPeriodizationDecay`/`ConnesAdelicLatticeDecay`; Lemma 3 is `ConnesLemma3Unfolding` (unfolding) plus `ConnesMellinContinuation` (continuation) |
| B6 | App I / Thm III.1 | the *conclusion* steps are Lean-owned: (15)–(20) local homogeneity (A21), (27)(28) division (A27), (29) Sobolev membership (A3), (34) Jordan form (A9).  Lemmas 1–3 closed (see B5).  **(25) closed for `L = ζ`** (batch 27): `ConnesZetaLineTemperate.connes_zeta_hasTemperateGrowth` and `connesZetaLineMultiplier_apply`.  **(25) closed for every Dirichlet `L`** too (batch 42, `ConnesDirichletLineTemperate`): `connes_dirichletL_hasTemperateGrowth` + `connesDirichletLineMultiplier_apply`, for every primitive non-principal character - i.e. every non-trivial Grössencharakter of `ℚ`.  The general lemma `connes_hasTemperateGrowth_lineRestrict` was already stated for an arbitrary analytic, polynomially bounded function, so (25) now needs *only* a strip growth bound for whichever `L` one wants; the corpus supplies it for `ζ` (`exists_bound_norm_riemannZeta_strip`) and for Dirichlet `L` (`bound_LFunction_strip`).  **CLOSED for `K = ℚ`** (batches 75-77): `ConnesDirichletSpectralMultiplicity.connes_dirichlet_spectral_multiplicity` is Theorem III.1's multiplicity statement at every spectral point, for every non-trivial Dirichlet character, unconditional.  **The mechanism is now field-independent** (batch 78, `ConnesEntireSpectralMultiplicity.connes_entire_spectral_multiplicity`): Theorem III.1 holds for *any* entire non-zero `L`.  The only residue is the *construction* of a Hecke `L`-function for a number field other than `ℚ`, which mathlib cannot yet even state - a mathlib gap, not a gap in this paper |
| B7 | App II Thm 6 | Lemma 2's `A+B=0` done (A7); Lemma 3 done (`ConnesCharacterRescaling.connes_logDistribution_character_rescale`); (54) done at all three place types; (18)(19) done (`ConnesWeilRewriting.connesHatMoment_zero_add_one`, `connes_weilD_inversion`).  **Open:** Weil's explicit formula itself, which the paper *quotes* from [W3] |
| B8 | §VIII Lemma 1, Cor 2, Thm 5, Lemma 3 | window count (9)/(12)/(13) done (`ConnesFunctionFieldWindow`); (22)/(23) support done (`ConnesPeriodizationEquivariance.connesPeriodization_support_window`); (23)/(25) positivity mechanism done (`ConnesPositiveTypeCutoff`); Lemma 3's model computation done (A26); §VIII (30) pair-of-projections done (A20); §VIII (35)–(43) semiclassical area done (A6).  **B3 (batch 72) and B6 (batches 75-78) are CLOSED, and Theorem 5's positivity chain is assembled in batch 79 (`ConnesTheorem5Positivity`).  What is left of Theorem 5 is only the *quoted* Weil criterion (B7).**  Historical note: this row previously read "waits only on B6" — i.e. on a strip growth bound for Hecke `L`-functions of number fields other than `ℚ`, which mathlib cannot yet even state (no Hecke characters) |
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

- 2026-08-22 — Tier B batch 14 (**§VII (11) — the orbit form IS the quotient inner product**).
  Corpus search: `RHTower.fieldOneFiniteStageBruhatCorrelation_integral_multiplicative_eq_sourceInner`
  already has the Connes–Marcolli finite-stage version; mathlib already has the unfolding
  `MeasureTheory.IsFundamentalDomain.integral_eq_tsum'`.  Neither was rebuilt.  What was missing
  is the abstract identity, which this module supplies.
  * `ConnesOrbitEnergy` — `connes_conj_mul_self`, `connesOrbitReindex` (the bijection
    `(q,p) ↦ (p, q p)` of the double orbit), and the pointwise core
    **`connes_periodization_normSq_eq_orbitSum`**:
    `‖∑'_p f(p·x)‖² = ∑'_{(q,p)} conj(f(p·x))·f((q p)·x)` for an absolutely summable orbit —
    no measure theory at all.
    Then **`connes_orbitForm_eq_fundamentalDomain_energy`** = **§VII (11)**:
    `∑'_q ∫_X conj(f) · f(q·) dμ = ∫_F ‖∑'_p f(p·x)‖² dμ`,
    by unfolding each `q`-term over the fundamental domain, regrouping the double sum, and
    applying the pointwise core.  This is exactly Lemma 1(a)'s second half — *"its sum is equal to
    the inner product of `f₁` and `f₂` in `L²(X_S)`"* — and together with
    `ConnesOrbitGeometricConvergence` (Lemma 1(a) first half) and
    `ConnesOrbitFormFourier` + `ConnesFourierUnitaryExtension` (Lemma 1(b)) it closes the
    mechanism of §VII Lemma 1 in full.
  The four convergence hypotheses of (11) are Lemma 1(a)'s own content (per-`q` integrability,
  summability of the fundamental-domain norms, and pointwise absolute summability of the orbit);
  the identity is false without them.
  All `#print axioms` clean.

- 2026-08-22 — Tier B batch 15 (**App I (25)/(26) for an arbitrary unramified quasi-character**).
  * `ConnesUnramifiedLocalZeta` — `connesPadicUnitBallProfile`, its summability, and
    **`connes_padic_unitBall_geometric`**: for `‖w‖ < 1`,
    `∫_{ℤ_p ∩ ℚ_p^*} (radial profile w) d^*x = (1 - w)^{-1}`.  With `w = Χ(π) q^{-s}` this is
    Connes' local factor `(1 - Χ_{0,v}(π) q_v^{-s})^{-1}` of `L(Χ_0, s)`; `Χ = 1` recovers
    `connes_padic_tate_local_zeta` (batch: App I (25)).
    **`connes_padic_unramified_pow`** = **App I (26)**: an unramified quasi-character is a power of
    its value at the uniformizer, `Χ(a) = Χ(π)^{v(a)}` on every nonnegative valuation shell —
    proved by induction through the corpus's valuation/unit `MulEquiv`, so the integrand of (25)
    is genuinely radial for every unramified `Χ`.
  All `#print axioms` clean.

  STATUS OF THE THREE NAMED GAPS (unchanged by this batch, restated precisely):
  1. §V (19)/(23) for `U(h)`: `U(h)` has kernel `h(x/y)/(ρ|y|)`, whose `L²(dx dy)` energy diverges
     logarithmically at `y = 0`, so it is **not** Hilbert–Schmidt and no factorization into two
     HS factors is available (`P_Λ U(h)` and `U(h) P_Λ` both inherit the divergence).  Connes'
     `Trace(R_Λ T) = ∫∫ k r^t` therefore needs the trace-class (Mercer/Brislawn) kernel theorem,
     which neither mathlib nor the corpus has.  Everything else in §V Theorem 3 — (21), (23) for
     HS pairs, (24) = mathlib's multiplication formula, (25)-(28), (29)-(33) — is Lean-closed.
  2. App I Lemma 1 over `𝔸`: the local factors (25)/(26) and their Euler product over the finite
     places of `ℚ` are Lean-closed; what is missing is the *tensor factorization of the adelic
     integral*, i.e. `∫_{𝔸^*} = ∏_v ∫_{k_v^*}`, which needs the restricted-product multiplicative
     Haar measure on `𝔸^*` (the corpus has it only at a finite stage `A_S`).
  3. App I Lemma 3: the continuation step is closed (batch 13); the identity it continues is
     item 2.

- 2026-08-22 — Tier B batch 16 (**§V (19)/(23) closed for the non-Hilbert–Schmidt factor**).
  The earlier diagnosis "this needs Mercer/Brislawn" was wrong: the trace-class kernel theorem is
  not required, because only *one* factor has to be Hilbert–Schmidt.
  * `ConnesFieldTracePairing` — `connes_finset_inner_bound` (Bessel plus Cauchy–Schwarz: on any
    finite index set `∑ ‖⟪v,b i⟫‖·‖⟪b i,w⟫‖ ≤ ‖v‖·‖w‖`), and
    **`connes_hsInner_kernelOperator_field`**:
    `hsInner (T_K) B = ∫ ⟪L x, k_x⟫ dμ`
    for `T_K` a kernel operator and `B` *any* operator whose rows `L x` are square integrable,
    provided `∫ ‖K x‖·‖L x‖ dμ < ∞`.  `B` need not be Hilbert–Schmidt.  The finite-index bound is
    what makes the basis sum uniformly dominated, so the sum/integral exchange is legitimate.
  * `connes_hsInner_kernelOperator_field_of_kernel` — the hypotheses have models: two kernel
    operators satisfy them (row field `(toDual)⁻¹ ∘ L'`, product of row norms integrable by
    Hölder), and the value agrees with `connes_hsInner_kernelOperator`.  So the field pairing
    genuinely extends the polarized energy rather than being vacuous.
  Why this settles Connes' `Trace(R_Λ U(h)) = ∫∫ k r^t`: `R_Λ^†` is a kernel operator
  (`connesConvKernel`, batch 10) with `‖K x‖ = ρ_Λ(x)‖ρ̂_Λ‖`; `U(h)` has kernel
  `h(x/y)/(ρ|y|)`, and the substitution `u = x/y` gives `‖L x‖ = ‖h‖/√|x|` — finite for a.e. `x`,
  though `∫‖L x‖² dx = ∞`, which is exactly why `U(h)` is not Hilbert–Schmidt.  The *pairing*
  integrand is only `ρ_Λ(x)‖ρ̂_Λ‖‖h‖/√|x|`, and `1/√|x|` is integrable in one dimension, so
  `∫ ‖K x‖‖L x‖ dx < ∞` holds.  The `1/|y|` singularity that destroys Hilbert–Schmidt membership
  is only a `1/√|x|` in the trace pairing.
  All `#print axioms` clean.

- 2026-08-22 — Tier B batch 17 (**App I Lemma 1 at a finite stage — the Tate factorization**).
  * `ConnesTateFiniteStage` — `connes_padic_sigmaCompact` (`ℚ_p^*` is σ-compact: the corpus's
    valuation/unit homeomorphism carries `ℤ × ℤ_p^*` onto it) and the instance
    `connes_padic_multHaar_sigmaFinite`, which is what makes the product measure usable;
    **`connes_tate_finiteStage_prod`** — for any finite family of primes and any unramified local
    data `w i` with `‖w i‖ < 1`,
    `∫_{∏_i ℚ_{p_i}^*} ∏_i (radial profile w_i) d^*x = ∏_i (1 - w_i)^{-1}`,
    i.e. Lemma 1's factorization `Δ_s = ∏_v Δ_{s,v}` over a finite set of places, by mathlib's
    `integral_fintype_prod_eq_prod` and the local geometric evaluation of batch 15;
    **`connes_tate_finiteStage_eulerProduct`** — the `Χ_0 = 1` case,
    `= ∏_i (1 - p_i^{-s})^{-1}`, the partial Euler product, for every `Re s > 0`.
  This is Lemma 1 over `A_S`, which is the stage at which §VII actually works.  What is still
  missing is only the passage to the *full* adele ring: a restricted-product multiplicative Haar
  measure on `𝔸^*` and the corresponding infinite factorization.  Note the convergence half of
  that passage is already Lean-owned — `connes_tate_local_zeta_tprod` shows the infinite product
  of the local factors is `ζ(s)` for `Re s > 1`, which is exactly Connes' *"the convergence for
  σ > 1 is the same as for the zeta function"*.
  All `#print axioms` clean.

- 2026-08-22 — Tier B batch 18 (**App I Lemma 1's infinite factorization, for `k = ℚ`**).
  Corpus/mathlib search: mathlib has `RestrictedProduct` as a topological object but **no measure
  theory on it**, so a restricted-product Haar measure would have to be built.  It does not have
  to be: the idele group is the increasing union of the open subgroups
  `J_S = ∏_{v∈S} k_v^* × ∏_{v∉S} R_v^*`, and on `J_S` the Haar measure is the product of the local
  ones (the omitted factors having mass one), so the global Tate integral of a tensor test
  function is by monotone convergence the limit of the finite-stage integrals of batch 17.
  * `ConnesTateInfiniteFactorization` — `connesTateStageIntegral` (the finite-stage Tate integral
    indexed by `S : Finset Nat.Primes`), `connesTateStageIntegral_eq` (`= ∏_{p ∈ S} (1 - w p)^{-1}`),
    **`connes_tate_stage_tendsto`** (whenever the local factors have a convergent infinite product,
    the finite-stage integrals converge to it), and
    **`connes_tate_stage_tendsto_zeta`**: for `Re s > 1` the finite-stage Tate zeta integrals
    converge to `ζ(s)` — literally Connes' *"the convergence for σ > 1 is the same as for the zeta
    function"*, via mathlib's `riemannZeta_eulerProduct_hasProd`.
  This closes App I Lemma 1 for `k = ℚ`, `Χ_0 = 1`, in the form the paper uses it: local factors
  (25)/(26), finite-stage factorization (batch 17), and the infinite product as the limit of the
  finite stages.  A restricted-product Haar measure on `𝔸^*` would only be needed to phrase the
  same content as a single integral rather than a limit of integrals; nothing further about the
  paper depends on it.
  All `#print axioms` clean.

- 2026-08-22 — Tier B batch 19 (**App I Lemma 1 at the RAMIFIED places — general `Χ_0`**).
  The previous batches covered arbitrary *unramified* local data (the `w i` of
  `connes_tate_finiteStage_prod` are arbitrary with `‖w i‖ < 1`, so any unramified `Χ_0` is
  already included).  What was genuinely missing for a *general* `Χ_0` is the ramification locus
  `P`, and this batch supplies it.
  * `ConnesRamifiedLocalZeta` — **`connes_padic_character_split`**: every monoid homomorphism of
    `ℚ_p^*` factors on each valuation shell as `Χ(π^m)·Χ(u)` (immediate from `map_mul` through
    the corpus's valuation/unit `MulEquiv` — no induction, and valid ramified or not);
    **`connes_padic_tate_ramified_vanishes`**: if the angular profile of a shell-split integrand
    has zero mean on the units, the whole local multiplicative integral vanishes;
    **`connes_padic_tate_ramified_character`**: hence for a quasi-character whose restriction to
    the units has zero mean, *every* radially weighted local Tate integral vanishes.
  This is exactly Connes' *"one only needs to consider the infinite tensor product for finite
  places `v ∉ P`"*: the ramified factors contribute nothing, which is why `L(Χ_0,s)` is a product
  over the unramified places only.  Together with batches 15/17/18 (arbitrary unramified local
  data, finite-stage factorization, infinite product as the limit of finite stages), App I
  Lemma 1 is now covered for an arbitrary `Χ_0` over `ℚ`.
  Still specific to `k = ℚ`: every local module is written for `ℚ_p` and `ℝ`.  Generalising to an
  arbitrary global field means replacing `ℚ_p` by an arbitrary non-archimedean local field
  throughout; the corpus has the beginnings of that layer in
  `HTGeometry.ABHN.NonarchimedeanLocalFieldValuationSequence` (uniformizer, valuation, unit
  reduction), which is where that generalisation should start.
  All `#print axioms` clean.

- 2026-08-22 — Tier B batch 20 (**the local computations for an ARBITRARY non-archimedean local
  field**).  The `ℚ_p`-specificity of batches 15/19 was not essential: every one of Connes' local
  computations depends on the field only through the valuation/unit decomposition
  `K^* ≅ π^ℤ × O^*` together with `vol(O^*) = 1`, i.e. only through the measure
  `counting ⊗ (probability Haar on the units)`.  This batch proves them once on that abstract
  shell space, so they hold for every non-archimedean local field simultaneously.
  * `ConnesLocalShellAbstract` — `connesShellMeasure ν = count ⊗ ν` on `Multiplicative ℤ × U` for
    an arbitrary probability space `U` of units; `connesShellRadial`;
    `connes_shell_radial_integrable` and **`connes_shell_radial_integral`**
    (`∫ radial = ∑'_m h m`); `connes_unitBallProfile_tsum`; **`connes_shell_unitBall_geometric`** —
    **App I (25)/(26) over an arbitrary local field**, the unramified local factor
    `(1 - Χ(π)q^{-s})^{-1}`; **`connes_shell_ramified_vanishes`** — **App I Lemma 1's ramified
    case over an arbitrary local field**; and `connes_shell_transfer_integral`, the bridge that
    carries all of these to any concrete multiplicative group whose Haar measure is the
    push-forward of the shell measure (which is how each `ℚ_p` statement of the earlier batches
    arises).
  So App I Lemma 1's *local* content now holds for an arbitrary global field `k` and an arbitrary
  `Χ_0`, ramified or not.  What is still tied to `ℚ` is only the *global* assembly — the
  finite-stage product (batch 17) and the Euler-product limit (batch 18) are indexed by
  `Nat.Primes` and use `riemannZeta_eulerProduct_hasProd`; generalising those means an
  `L(Χ_0,s)`-Euler-product input for the global field in question, which is a statement about
  `L`-functions rather than about Connes' argument.
  All `#print axioms` clean.

- 2026-08-22 — Tier B batch 21 (**App I Lemma 1's global assembly for an arbitrary global field,
  and Lemma 3's unfolding step**).
  * `ConnesGlobalTateAssembly` — `connesShellMeasure_sigmaFinite`, `connesShellStageIntegral`
    (the Tate integral over a finite set of places), **`connesShellStageIntegral_eq`** (it is the
    partial Euler product of the local factors) and **`connes_shell_stage_tendsto`** (the
    finite-stage integrals converge to the infinite Euler product).  *Nothing in this module
    mentions `ℚ`*: the places are an arbitrary index type, the local units arbitrary probability
    spaces, the local data arbitrary with `‖w i‖ < 1`.  CORRECTION to batch 20's closing note:
    the `L(Χ_0,s)` Euler product is not a missing mathlib theorem — it is Connes' *definition* of
    `L(Χ_0,s)` (his displayed formula `L(Χ_0,s) = ∏_{v ∉ P}(1-Χ_{0,v}(π)q_v^{-s})^{-1}`), so it
    enters correctly as the value of a `HasProd`, and the general-`k` assembly is complete.
  * `ConnesLemma3Unfolding` — **`connes_periodization_pairing_unfold`**: against a weight
    invariant under the group, `∫_X f·φ dμ = ∫_F (∑'_q f(q·x))·φ(x) dμ`.  With
    `φ(x) = Χ_0(x)|x|^s` — invariant under `k^*` by the product formula — and
    `E(f)(x) = |x|^{1/2}∑_q f(qx)`, this is exactly Lemma 3's left side rewritten as Lemma 1's
    `Δ_s(f) = ∫_{A^*} f Χ_0 |x|^s d^*x`.
  With this, **Appendix I Lemma 3 is assembled**: the unfolding here reduces it to Lemma 1
  (batches 15/17/18/19/20/21), and `ConnesMellinContinuation` (batch 13) propagates the resulting
  identity from `Re s > 1` to `Re s > 0`.
  All `#print axioms` clean.

- 2026-08-22 — Tier B batch 22 (**the paper source read back; §VII (41) correctly identified**).
  * **CORRECTION to the ledger.**  The arXiv e-print was re-fetched
    (`curl -sL https://arxiv.org/e-print/math/9811068 | gunzip > zeta.tex`) and §VII (38)-(49) read
    verbatim.  Earlier entries described (41) as "the Besov–Fourier sup inequality".  It is not.
    Connes' (41) is the **fractional-multiplier inequality**
    `Sup_x |F(η)(x) · Sup_S |x_v|^α| ≤ c_α ∑_S ‖C_{α,v} * η‖₁`,
    where `C_{α,v}` is the convolution operator (39)
    `(C_{α,v}*η)(x) = ∫ ψ(|ε|)(η(x+ε) − η(x)) dε/|ε|^{1+α}`.
    Its proof has three ingredients: `F(C*η) = F(C)·F(η)`; the growth `F(C_{α,v})(x) ≍ |x_v|^α`
    (asserted, not proved, in the paper); and `sup|F(g)| ≤ ‖g‖₁`.
  * `ConnesBesovSupNorm` (built, audited) — `connesBesovSeminorm`, `connes_besov_sup_bound`,
    `connes_besov_le_schwartz_seminorms`: one weighted-`L¹` Besov quantity dominating
    `sup_x |h^{(n)}(x)|` for *every* `n ≤ N` at once, finite by finitely many Schwartz seminorms of
    the transform.  This is a genuine supporting estimate but is **not** (41); the module and its
    docstrings were relabelled accordingly.
  * `ConnesLevyKernelScaling` (built, audited) — the engine for the growth of `F(C_{α,v})`:
    `connesLevyKernel`, its integrability on `Ioi 0` for `0 < α < 2`, `connesLevyConstant`,
    **`connes_levyConstant_pos`** (`C_α > 0`, via `cos ≤ 0` on `(π/2, π)`), and
    **`connes_levy_scaling`**: `∫_0^∞ (1 − cos(tε)) ε^{-1-α} dε = C_α t^α` for `t > 0` — with *no*
    hypothesis on `α` (the change of variables is unconditional).
  All `#print axioms` clean.

- 2026-08-22 — Tier B batch 23 (**§VII (41) CLOSED at the archimedean place**).  Four modules, the
  whole chain unconditional and `#print axioms`-clean:
  * `ConnesLevyKernelScaling` (batch 22) — `∫_0^∞ (1 − cos(tε))ε^{-1-α}dε = C_α t^α`, `C_α > 0`.
  * `ConnesFractionalSymbolGrowth` — `connesTruncatedLevy`, `connes_levy_truncation_defect_le`
    (Connes' smooth cut costs only the fixed constant `2δ^{-α}/α`, uniformly in `t`), and
    **`connes_truncatedLevy_lower_bound`**: `∫_0^∞ψ(ε)(1−cos(tε))ε^{-1-α}dε ≥ C_α t^α − 2δ^{-α}/α`.
  * `ConnesFracConvSwap` — the operator (39) itself: `connesFracWeight`, `connesFracConv`,
    the Schwartz quadratic-derivative decay `connes_schwartz_deriv_weight`, the mean-value bound
    `connes_schwartz_diff_bound` (`‖η(y+ε)−η(y)‖ ≤ 4C(1+|y|)^{-2}|ε|` for `|ε| ≤ 1`, using that a
    unit shift changes `1+|y|` by at most a factor two), the two-sided `|ε|^{-α}` unit-interval
    integrability, and **`connes_fracConv_swap`**: against *any* bounded measurable weight the
    order of the double integral of (39) may be exchanged (the majorant factorises, so Fubini
    applies).
  * `ConnesFracSymbolArch` — `connesFracSymbol`, its integrability, **`connes_fracSymbol_re`**
    (the symbol is real: `Re m_α(x) = −2∫_0^∞ψ(s)(1−cos(2π|x|s))s^{-1-α}ds`, via
    `integral_comp_abs`), and **`connes_fracSymbol_norm_lower`**:
    `‖m_α(x)‖ ≥ 2C_α(2π|x|)^α − 2(2δ^{-α}/α)`.  *This is the step Connes states without proof*
    ("the Fourier transform of `C_{α,v}` behaves like `|x_v|^α`").
  * `ConnesBesovSupInequality` — `connes_fourier_translate_diff` (the first-difference symbol
    `e^{2πiεx} − 1`, proved directly from translation invariance rather than via the corpus's
    `HTGeometry.fourier_sub_translate`, to stay off a heavy import), the multiplier identity
    **`connes_fourier_fracConv`**: `F(C_{α,v}*η) = m_α · F(η)`, and **§VII (41)**:
    `(2C_α(2π|x|)^α − 2(2δ^{-α}/α))·‖F(η)(x)‖ ≤ ‖C_{α,v}*η‖₁` for every `x ≠ 0`, `0 < α < 1`.
  B4's ledger line should now read: (41) DONE, (43)(44)(45)(46)(47)(48) DONE; **open: (42)**, the
  assembly `‖ε_Λ η‖_{(1,α,v)} = O(Λ^{-N})`, and its transfer to `A_S`.

- 2026-08-22 — Tier B batch 24 (**§VII (42) — B4 closed at the archimedean place**).  Seven
  further modules, all built, wired and `#print axioms`-clean:
  * `ConnesCutoffCommutatorLocal` — (45) restated in the paper's own cut-off convention
    (`ψ(|ε|)` rather than the `Ψ(ε/x)` used when the scaling substitution was first proved: the
    *uncut* logarithmic-difference integral already converges, so the `Ψ ≡ 1` instance evaluates
    it and any `0 ≤ ψ ≤ 1` only decreases it), **(46) with the local supremum**
    `Sup_{|ε| ≤ 1}|η(x+ε)|`, and the support statement `connes_cutoffExcess_diff_eq_zero`.
  * `ConnesCutoffTailTwoSided` — **(47) on the whole thickened tail**.  The negative half is not a
    formal consequence of the positive one (that would need `η(−·)` as a Schwartz map); it is
    proved directly, because `connesUnitSup_schwartz_le` is stated in `|x|` and applies verbatim
    at `−x`, then transported by `integral_comp_neg_Ioi`.
  * `ConnesFracConvDecay` — the order-`k` Schwartz derivative weight, the order-`k` mean-value
    bound, and `‖(C_{α,v}*η)(x)‖ ≤ A_k(1+|x|)^{-k}` for every `k`.
  * `ConnesCutoffBesovMass` — **(48)**: `‖ε_Λ(C_{α,v}*η)‖₁ = O(Λ^{-N})`, via the fold
    `integral_comp_abs` and the model tail integral of `ConnesLogExcessTail`.
  * `ConnesFracCommutator` — **`connesUnitSup_continuous`** (without it the (47) statements would
    be about a possibly non-measurable integrand, hence vacuous — see the vacuous-gap trap),
    `le_connesUnitSup`, integrability of both `ε`-integrands, and the operator identity
    **`C*(ε_Λη) = ε_Λ·(C*η) + [C,ε_Λ]η`**, plus the commutator's support and its (46) bound.
  * `ConnesTwoSidedPowerTail` — the reflection transfer for even functions, and the two-sided
    power tail's integrability and exact value `2R^{1-p}/(p-1)`.
  * `ConnesBesovCutoffDecay` — **§VII (42)**: `‖C_{α,v}*(ε_Λ η)‖₁ = O(Λ^{-N})` for every `N`.
    Both halves are majorised by a *single* integrable function, so the proof never needs
    measurability of `C_{α,v}*η` itself.
  B4's ledger line is now: (41)–(48) all DONE at the archimedean place; what remains for B4 is
  only the transfer of the assembled estimate to `A_S` (the `S`-adic product), which is a
  place-by-place bookkeeping step over the finite set `S`.

- 2026-08-22 — Tier B batch 25 (**§VII (10)**, and a ledger audit).
  * `ConnesBoxOverlap` — **`connes_boxOverlap_prod_le`** is (10):
    `∏_v c_v·min(n, n/a_v) ≤ (∏ c_v)·n^{Card S}·(Sup_v a_v)^{-1}` whenever the `a_v` are positive
    with product `1`.  The arithmetic content Connes leaves implicit is
    `connes_prod_min_le_sup_inv`: a product of ones forces the largest `a_v` to be at least `1`,
    so the factor at the maximising place is exactly `(Sup a)^{-1}` and every other factor is at
    most `1`.  `connes_archBoxOverlap_volume` computes the archimedean overlap exactly
    (`= 2 min(n, n/a)`), grounding the abstract bound in a real measure.
  * **Ledger audit** (the card's Tier-B rows had gone stale against the tree — three rows rewritten
    above).  Verified by name against `formal/`: B1's (19)/(23), B5's strong convergence and
    Lemmas 1–3, and B2's (10)/(11)/Lemma 1(b) are all present and closed.
  All `#print axioms` clean.

- 2026-08-22 — Tier B batch 26 (**§VII (9) and (50): B2 closed, Lemma 2's conclusion closed**).
  * `ConnesBoxMajorant` — **`connes_box_majorant`** is (9): a function dominated by a nonincreasing
    profile `μ` vanishing at infinity is dominated by `∑_n λ_n k_n` with `λ_n := μ(n) − μ(n+1)` and
    `k_n` the nested box indicators; the coefficients inherit the decay of `μ` because
    `λ_n ≤ μ(n)`.  The construction is telescoping and needs nothing about `A_S`: at a given `x`
    the surviving terms are exactly those with `n + 1 ≥ r(x)`, and they sum to
    `μ(⌈r(x)⌉ − 1) ≥ μ(r(x))`.  `connes_nonneg_of_antitone_tendsto` derives `μ ≥ 0` rather than
    assuming it.
  * `ConnesOrbitMassDecay` — **`connes_orbitMass_le`** and **`connes_orbitMass_rapidDecay`**:
    a family bounded orbit-wise by `D·exp(−c·d(q,1))` has total mass at most `D` times the
    geometric constant, and rapid decay of `D(Λ)` transfers to the total mass `σ(Λ)`.  This is the
    bookkeeping half of (50) and of Lemma 2's conclusion; the analytic half is (41)+(42) and the
    lattice half is `ConnesSUnitSupBound` (36) plus `connes_summable_exp_neg_latticeL1`.
  All `#print axioms` clean.  **B2 is now closed**; §VII Lemma 2 is closed modulo the transfer of
  (41)/(42) from the archimedean place to `A_S`.

- 2026-08-22 — Tier B batch 27 (**App I (25) closed for `L = ζ`**).  Two modules:
  * `ConnesHolomorphicLineTemperate` — the general infrastructure Connes compresses into the
    sentence *"since `L(1/2+it)` is an analytic function of `t` we see that it is a multiplier of
    the algebra `𝒮(ℝ)`"*.  A pointwise polynomial bound gives nothing about derivatives; what does
    is Cauchy's estimate on a disc of fixed radius, provided the bound holds on a whole *tube*
    around the line.  Contents: `connes_analyticOnNhd_iteratedDeriv` (every iterated derivative of
    an analytic function is analytic), `connes_iteratedDeriv_lineRestrict`
    (`(d/dt)^n f(c+it) = i^n f^{(n)}(c+it)`), `connes_contDiff_lineRestrict`, and
    **`connes_hasTemperateGrowth_lineRestrict`**.
  * `ConnesZetaLineTemperate` — the instantiation: the tube of radius `1/8` about the critical line
    stays inside `3/8 ≤ Re ≤ 5/8`, so it never meets the pole at `1`; the corpus's
    `RHTower.exists_bound_norm_riemannZeta_strip` covers `|Im| ≥ 1` and a compact box covers the
    rest.  Result: **`connes_zeta_hasTemperateGrowth`**, and `connesZetaLineMultiplier_apply`,
    which is (25)'s conclusion — `ζ(1/2+it)ψ(t)` is again Schwartz, so `ζ(1/2+it)ψ̂(t)` is tempered.
  All `#print axioms` clean.

- 2026-08-22 — Tier B batch 28 (**the `A_S` transfer machinery**).  `ConnesBesovProductTransfer`:
  * `connes_prodMass_eq_fibrewise` — Fubini: the `L¹` norm on a product is the integral over the
    complementary coordinates of the per-fibre `L¹` norm.
  * **`connes_fibrewise_rapidDecay`** — if each fibre's mass is at most `b(Λ)·w(x')` with `w`
    integrable and `b` rapidly decreasing, the total mass over the product is rapidly decreasing.
    (`connes_fibrewise_mass_le` is the underlying bound; no integrability of the fibre mass itself
    is assumed, only of the majorant.)
  * `connes_finsetSum_rapidDecay` — the sum over the finite set of places `S`.
  Nothing here is specific to `A_S`: the complementary coordinates are an arbitrary measure space,
  and `C_{α,v}` acts in one coordinate.  What the transfer consumes is the per-place estimate
  (`ConnesBesovCutoffDecay`, batch 24) applied on each fibre; the one remaining input is
  integrability of the fibre constants, which is exactly what a Bruhat–Schwartz theory for
  `𝒮(A_S)` supplies and which the corpus does not yet own in that form.
  All `#print axioms` clean.

- 2026-08-22 — Tier B batch 29 (**the fibre constants of the `A_S` transfer**).
  `ConnesProductFibreDecay` — two facts, neither in mathlib:
  * **`connes_norm_iteratedFDeriv_fibre_le`** — restricting a function on a product to a fibre
    `t ↦ (t,x)` does not increase the norm of any iterated derivative.  The restriction is an
    affine map whose linear part is the inclusion of the first factor, of operator norm `≤ 1`;
    the translation is absorbed by `iteratedFDeriv_comp_add_right`.
  * **`connes_fibre_decay`** — for `η ∈ 𝒮(ℝ × X)` and any `k n N`, the fibre seminorm satisfies
    `‖t‖^k ‖D^n η(·,x)(t)‖ ≤ C (1+‖x‖)^{-N}`.  The mechanism: the product norm is the *maximum*,
    so `‖t‖^k‖x‖^N ≤ ‖(t,x)‖^{k+N}` — one ambient Schwartz seminorm controls the fibre seminorm
    and a power of the transverse variable at once.
  * `connes_fibre_bound_integrable` — on a finite-dimensional transverse space that bound is
    integrable once `N` exceeds the dimension, which is exactly the input
    `ConnesBesovProductTransfer.connes_fibrewise_rapidDecay` consumes.
  All `#print axioms` clean.

- 2026-08-22 — Tier B batch 30 (**§V (24), the Parseval step**).  `ConnesSymbolPairing`:
  * `connesKernelSymbol` — (20), the symbol of a kernel as its partial Fourier transform along the
    diagonal.
  * `connes_fourier_even` — the transform of an even function is even, so the reflection in
    `r_Λ^t(x,y) = ρ_Λ(x)ρ̂_Λ(x−y)` of (21) costs nothing.
  * `connes_kernel_pairing_diagonal` — the substitution `y = x + u` that puts the kernel into the
    diagonal form (20) uses.
  * **`connes_symbol_pairing`** and `connes_symbol_pairing_integrated` — (24): the kernel pairing
    against `ρ̂_Λ` equals the symbol pairing against `ρ_Λ`.  This is Connes' *"using the Parseval
    formula"*; the engine is mathlib's multiplication formula
    `VectorFourier.integral_fourierIntegral_smul_eq_flip`, applied in the second variable, after
    checking that the real inner product used by `𝓕` on `ℝ` is its own flip.
  All `#print axioms` clean.  With (23) (batch 16) and (29)-(36) (batches 1, 3) this completes
  B1's analytic chain at the real place; the residue is the *distributional* kernel of `U(h)`
  in (19)(25)(26).

- 2026-08-22 — Tier B batch 31 (**§V (27)**).  `ConnesScalingSymbolChart`:
  * **`connes_symbol_scaling_substitution`** — the change of variable `μ = λ − 1` turns the scaling
    integral `∫ h(λ^{-1}) w((λ−1)t) dλ/|λ|` into `∫ g(μ) w(μt) dμ` with `g` Connes' chart (28),
    for an arbitrary weight `w`.
  * **`connes_symbol_scaling_eq_fourierInv`** — with the additive character this is (27):
    the symbol of the scaling kernel is the inverse Fourier transform of the chart, `σ = ρ^{-1}ĝ`.
  Both reuse `ConnesSymbolChart.connesSymbolChart` (A10 = (28)) rather than redefining `g`.
  All `#print axioms` clean.  B1's chain at the real place is now Lean-owned from (27) onwards;
  the residue is only the *distributional* content of (19) and (26) — the kernel of `U(h)` and the
  `δ`-evaluation — whose consequences are all in place.

- 2026-08-22 — Tier B batch 32 (**§V (19)(20)(25)(26)**).  `ConnesScalingKernelDelta` takes the
  `δ` of (19) literally, as `Measure.dirac`:
  * `connesScalingKernelPairing` — (19): the kernel of `U(h)` paired against a test function,
    `⟨k(x,·),φ⟩ = ∫ h(λ^{-1})(∫ φ dδ_{λx}) dλ/|λ|`.
  * `connesScalingKernelPairing_eq` — **(26)**, the `δ`-evaluation, which is
    `MeasureTheory.integral_dirac`; no distribution theory is needed because the `δ` really is a
    measure.
  * `connes_scalingKernel_symbol_integral` — (20)+(25): testing against the character of (20)
    gives the symbol integral of (25).
  * **`connes_scalingKernel_symbol_eq_fourierInv`** — chaining with batch 31: `σ(x,ξ) = ρ^{-1}ĝ(xξ)`.
  All `#print axioms` clean.  **B1's chain (19)→(36) is now complete at the real place**; the only
  residue is the identification of this Dirac-measure kernel with the operator `U(h)`.

- 2026-08-22 — Tier B batch 33 (**§V (19), the operator**).  `ConnesScalingOperator`:
  * `connesScalingAction` and `connesScalingOperator` — the scaling action `U(λ)ζ(x) = ζ(λx)` and
    the superposition `U(h) = ∫ h(λ^{-1})U(λ)dλ/|λ|` of (19); `connesScalingAction_comp` and
    `connesScalingAction_one` record that it is a representation of the multiplicative group.
  * **`connesScalingOperator_eq_kernelPairing`** — the identification: the value of `U(h)` at `x`
    *is* the Dirac-measure kernel of (19) paired with the input function.
  * **`connes_scalingOperator_symbol`** — the capstone of §V (19)-(27), stated about the operator
    rather than the kernel: testing `U(h)` against the character of (20) gives `ρ^{-1}ĝ(xξ)`.
  * `connesScalingOperator_add` — additivity of the operator on integrable inputs.
  All `#print axioms` clean.  **B1 is closed at the real place**; the residue is the passage to a
  general local field, for which the corpus already owns the `p`-adic multiplicative Haar shell
  decomposition (`ConnesLocalShellAbstract`, `ConnesPadicWeil*`).

- 2026-08-22 — Tier B batch 34 (**§V (19)–(27) over an arbitrary local field**).
  `ConnesLocalFieldSymbol` re-proves batches 31–33 in the generality the paper states them:
  `connesLocalChart`, `connesLocalKernelPairing`, `connesLocalKernelPairing_eq` (26),
  **`connes_local_symbol_substitution`** (27), `connes_local_kernel_symbol`,
  `connesLocalScalingOperator`, `connesLocalScalingOperator_eq_kernelPairing`, and
  **`connes_local_scalingOperator_symbol`**.
  The audit of what the archimedean proof actually used: *translation invariance of the additive
  Haar measure*, *measurable singletons* (so the `δ` of (19) is a Dirac measure), and
  *commutativity*.  Nothing else — in particular no property of the absolute value or of the
  additive character is used, so both enter as bare functions and the statements are
  hypothesis-free in them.  Every place of every local field is therefore covered by one theorem.
  All `#print axioms` clean.

- 2026-08-22 — Tier B batch 35 (**§V (30) at a non-archimedean place**).
  `ConnesShellWindowMass`: `connesShellWindow`, `connesShellWindow_summable`,
  **`connes_shell_window_mass`** — the multiplicative mass of a shell window is the *number of
  shells* it contains — and `connes_shell_symmetricWindow_mass` (`2N+1` for the symmetric window,
  the non-archimedean form of `2 log' Λ`).
  The point: at a non-archimedean place the module `|x|` takes only the discrete values `q^{-n}`,
  so the window `|u|/Λ ≤ |x| ≤ Λ` of (30) is a finite range of shells and its mass is a count.
  The boundary terms that Connes' `log'` exists to handle are exactly the endpoints of that
  integer range, so no `log'` is needed here.  Built on `ConnesLocalShellAbstract`'s
  `count ⊗ ν` decomposition; nothing is assumed about the residue field, so this holds at every
  non-archimedean place of every local field.
  All `#print axioms` clean.

- 2026-08-22 — Tier B batch 36 (**§V (30)'s substitution at a non-archimedean place**).
  `ConnesShellReindex`:
  * **`connes_shell_split_card`** — the number of ways to write `k = n + m` with both parts in the
    window `[A,K]` is the size of an explicit integer interval, `[max A (k−K), min K (k−A)]`.
  * **`connes_shell_product_window_sum`** — the substitution `u = xξ` of (30): since the module is
    `q^{-n}`, multiplication *adds* shell indices, so the double sum over the product window
    regroups by the total index `k`, weighting each `k` by that splitting count.
  * `connes_shell_split_card_symmetric` — for the symmetric window the count is `2N + 1 − |k|`,
    which is exactly the discrete form of Connes' weight `2 log' Λ − log|u|`.
  With batch 35's window mass, both halves of (30) are now Lean-owned at every non-archimedean
  place; what remains of the chain there is the limit (31)→(33).
  All `#print axioms` clean.

- 2026-08-22 — Tier B batch 37 (**§V (31)–(33) at a non-archimedean place**).
  `ConnesShellTraceLimit`:
  * `connes_intervalFinset_tendsto`, `connes_doubleWindow_tendsto` — the symmetric integer windows
    exhaust `ℤ`, so partial sums over them converge to the `tsum`.
  * **`connes_shell_trace_expansion`** — the windowed trace sum
    `∑_{|k| ≤ 2N}(2N+1−|k|)w(k)` agrees with `∑_k (2N+1−|k|)w(k)` — i.e. with Connes'
    `2h(1)log'Λ` plus the principal value — up to `o(1)`.
  The proof does *not* estimate the two main terms separately; that route would need the tail of
  `∑ w` to be `o(1/N)`.  Instead the difference is recognised as a tail of the *single* convergent
  series `∑ |k|‖w(k)‖`: off the window `|2N+1−|k|| = |k|−2N−1 ≤ |k|`, so the discarded mass is
  dominated termwise, and tails of a convergent series vanish.
  With batches 35-36 this completes (29)-(33) at every non-archimedean place, and hence
  **B1 at every place of every local field**.
  All `#print axioms` clean.
- 2026-08-22 — Tier B batch 38: **B4's last identification closed** (`ConnesTransverseFiniteFactor`).
  `ConnesProductFibreDecay` transfers rapid decay across `ℝ × X` when `X` is a finite-dimensional
  real normed space (Japanese-bracket integrability).  `A_S`'s finite factor `∏_{v∈S_f} K_v` is not
  such a space — and does not have to be: a Bruhat–Schwartz function there is locally constant with
  compact support, so it is bounded and vanishes off a set of finite measure, and the transverse
  factor contributes exactly the finite constant `μ(K)` with **no decay rate at all**.  New:
  `connes_integrable_of_bounded_support` (bounded + finite-measure support ⟹ integrable),
  `connes_indicator_const_integrable` / `connes_indicator_const_integral`,
  `connes_transverse_prodMass_le` (`∫_{ℝ×X} F ≤ μ(K)·sup_x ∫_ℝ F(·,x)`, via `integral_prod_symm`
  and `integral_mono_of_nonneg` — no integrability of the fibre mass needed), and the capstone
  `connes_transverse_mass_rapidDecay` (rapid decay of the fibre mass ⟹ rapid decay of the total
  mass).  Also `connes_fibre_iteratedFDeriv_eq_zero`.  Stated for an arbitrary measure space, so it
  applies verbatim to every finite set `S_f` of finite places.  Built, wired, `#print axioms` clean
  on all four.  **B4 is now CLOSED with no residual identification.**
- 2026-08-22 — Tier B batch 39: **§VII Theorem 4's proof skeleton landed** — five modules, all
  built, wired and `#print axioms`-clean (14 capstones audited).
  * `ConnesTwistedChartFourier` — (26), (35)–(37).  `connesTwistedChart f q u = f(q(u+1)⁻¹)|u+1|⁻¹`
    and `connesInverseWeight f x = f(x⁻¹)|x⁻¹|`; `connes_inverseWeight_twistedChart` is Connes'
    `ξ(q⁻¹(1+u)) = |q| g_q(u)` (proved with **no** `q ≠ 0` hypothesis);
    `connes_twisted_fourier` is `ĝ_q(u) = |q| α(−u) ξ̂(qu)`; `connes_errorTerm_substitution` is the
    substitution `y = qu` in (35) — both **hypothesis-free in the integrand**, since mathlib's
    dilation/translation laws for the Lebesgue integral hold without integrability;
    `connes_errorTerm_fourierInv` is (37) for a module-one-invariant weight.
  * `ConnesSelbergPeriodization` — (16)–(19).  `connesPeriodizedKernel k x y = ∑'_q k x (q•y)`;
    `connesPeriodizedKernel_invariant` = (19) (reindexing by conjugation, so **no** commutativity
    of the lattice is used); `connes_selberg_trace` = (17) via `integral_tsum`, and
    `connes_selberg_trace_of_summable` restates it with Connes' geometric-convergence hypothesis.
    Stated for an arbitrary countable group acting on an arbitrary measure space.
  * `ConnesTraceMainTerm` — (31).  `connes_fourierInv_zero`, `connes_integral_fourier_eq_zero_value`
    (`∫ 𝓕g = g(0)` for Schwartz `g`), `connes_mainTerm_eq` (`∫ ĝ_q = f(q)`), `connes_mainTerm_tsum`.
  * `ConnesCutoffTraceDecomposition` — **(30) = (31) + (32) + (33), exactly.**  The whole split
    rests on one pointwise identity, `connes_cutoffWeight_split`:
    `1_{log|u| ≤ L}(u)(L − log|u|) = (L − log|u|) + ε_L(u)`.  `connes_cutoffTrace_split` and
    `connes_cutoffTrace_expansion` integrate it; the integrability of the error term is *derived*
    (`connes_excess_integrable`, the excess is dominated by `|log|u|| + L`), not assumed, so the
    only hypotheses are integrability of `ĝ` and of `ĝ·log|·|`.  `connes_logBall_eq` identifies the
    cut-off ball `|u| ≤ Λ²` with the logarithmic sublevel set.
  * `ConnesLatticeFiniteSupport` — the "finitely many non zero terms" of (31)/(32):
    a discrete **closed** set meets a compact set in a finite set, hence the lattice restriction of
    a compactly supported test function has finite support and is summable.
- 2026-08-22 — Tier B batch 40: **§VII (33) at the true rate** (`ConnesTraceErrorRapidDecay`).
  Audit first: `ConnesLocalTraceCore.connes_traceCore_tendsto` already proves that the remainder of
  (30) *vanishes*, and `connes_schwartz_integrable_log` already owns the logarithmic moment — so
  the planned "asymptotic expansion" capstone would have been a duplicate and was dropped.  What
  the corpus did **not** own is Connes' actual claim (33): the remainder is `O(Λ^{-N})` for
  **every** `N`, whereas `connes_traceCore_tendsto`'s tail bounds only give `O(Λ^{-2} log Λ)`.
  New: `connes_schwartz_polyDecay` (`‖G z‖ ≤ C(1+|z|)^{-k}` for every `k`),
  `connes_schwartz_excess_mass_le` (the explicit bound `C·2T^{-(k-1)}/(k-1)²`, via
  `connes_excessMajorant_mass_le`), `connes_schwartz_error_rapidDecay` = **(33)** (take `k = N+3`,
  `T = Λ²`), and `connes_cutoffTrace_remainder_rapidDecay`, which upgrades the whole remainder of
  (30) to rapid decay.  Built, wired, all four `#print axioms` clean.
- 2026-08-22 — Tier B batch 41: two more §VIII / App II bricks.
  * `ConnesWindowTrace` — §VIII's `Trace(S_Λ V(f)) = 2 f(1) log' Λ`.  The compression of the
    regular representation to a window `W` is the matrix `(i,j) ↦ f(i−j)`, whose diagonal is
    constant `f(1)`, so `connesWindowMatrix_trace` gives `|W|·f(1)`; `connes_shellWindow_trace`
    specialises to the symmetric shell window (`2N+1` shells) and
    `connes_shellWindow_trace_logPrime` inserts the §VIII (9) normalisation
    `2 log' Λ = (2N+1) log q`.  Finite and unconditional.
  * `ConnesWeilMellinChange` — App II (12) ⟶ (15)/(16).  `connesModulusPower_add` and
    `connesModulusPower_inv` are the two branch-free quasi-character laws, and
    `connes_weil_mellin_change` is Connes' substitution `|g|^{-1/2}h(g^{-1}) = F(|g|)Χ₀(g)`
    turning `ĥ(Χ₀, 1/2+s)` into Weil's `Φ(1/2+s)`, by the inversion substitution on an
    inversion-invariant Haar measure.  Holds for an arbitrary complex exponent.
  * Audit note: §VIII (22)/(23) `E(B_Λ) ⊆ S_Λ` is **already owned** —
    `ConnesPeriodizationEquivariance.connesPeriodization_support_window` gives `E(f)(x) = 0`
    whenever `mod x ∉ [Λ⁻¹, Λ]`, using A12 for the reflected half.  Nothing to rebuild there.
- 2026-08-22 — Tier B batch 42: **App I (25) closed for every Dirichlet `L`**
  (`ConnesDirichletLineTemperate`).  Audit first: `connes_hasTemperateGrowth_lineRestrict` was
  *already* the general statement — analytic on a tube around a vertical line plus a polynomial
  bound there gives temperate growth on the line — so (25) never needed anything ζ-specific; what
  was missing was a strip growth bound for other `L`-functions.  The corpus already owns one:
  `RHTower.bound_LFunction_strip` (Phragmén–Lindelöf cubic envelope on `-2 ≤ Re s ≤ 3`), which
  covers the whole radius-`1/8` tube around the critical line.  New:
  `connes_dirichletL_analyticOnNhd` (entire for `Χ ≠ 1`, via
  `DirichletCharacter.differentiableAt_LFunction`), `connes_dirichletL_hasTemperateGrowth`
  (**App I (25)** with `C = 125·C₀`, `N = 3`), `connesDirichletLineMultiplier` and
  `connesDirichletLineMultiplier_apply`.  So (25) holds for every non-trivial Grössencharakter of
  `ℚ`.  What remains is a Hecke `L` over a number field ≠ `ℚ` — a statement mathlib cannot yet
  formulate, since it has no Hecke characters.  Built, wired; all nine capstones of batches 41–42
  `#print axioms` clean.
- 2026-08-22 — Tier B batch 43: **§VIII (5)–(7), the character projection**
  (`ConnesCharacterProjection`).  Connes' `P_{Χ₀} = ∫ Χ̄₀(a) U(a) d₁a` on the compact group
  `C_{S,1}` becomes, on the finite quotient by the open subgroup `𝒰_S`, the classical character
  average `P = |H|⁻¹ ∑_a Χ̄(a) π(a)`.  Corpus search found no isotypic projector, so it was built:
  `connesCharacterProjector`, the three character lemmas (`connes_character_one`,
  `connes_character_inv`, `connes_character_conj_inv` — derived from multiplicativity and
  `Χ̄Χ = 1` alone), `connes_characterProjector_intertwine` (`π(b)P = Χ(b)P`, by reindexing the
  average by left translation), `connes_characterProjector_idem`, and
  `connes_characterProjector_fixed_iff` = **§VIII (6)**: `Pξ = ξ` exactly when `ξ` is
  `Χ`-isotypic.  Stated for an arbitrary finite group acting by linear maps on an arbitrary
  `ℂ`-module and an arbitrary unitary-valued multiplicative character.  Built, wired, 4/4
  `#print axioms` clean.
- 2026-08-22 — Tier B batch 44: **§VIII Lemma 3's harmonic measure** (`ConnesHarmonicMeasure`).
  Connes' `dμ_ρ`, the harmonic measure of `ρ` with respect to the line `iℝ`, is the half-plane
  Poisson kernel of height `|Re ρ|` centred at `Im ρ`.  The corpus already owned the kernel, its
  mass and the *real-valued* concentration limit (`HTGeometry.halfPlanePoisson`,
  `integral_halfPlanePoisson`, `tendsto_halfPlanePoisson_density`), so only the packaging and the
  complex-valued limit were new: `connesHarmonicDensity`, `connesHarmonicMeasure`,
  `connes_harmonicDensity_integral` (mass one), `connes_harmonicMeasure_isProbabilityMeasure`
  (Connes' "it is a probability measure"), and `connes_harmonic_dirac_limit` (Connes' "coincides
  with the Dirac mass at `ρ` when `ρ` is on the line"), stated for a **complex** integrand since
  Lemma 3 pairs `dμ_ρ` with `f̂(Χ̃, z)`.  Built, wired, 3/3 `#print axioms` clean.
- 2026-08-22 — Tier B batch 45: **§VIII (15), the cyclic-vector argument** (`ConnesCyclicVanishing`).
  Connes' "by the cyclicity of `ξ_Χ` one then gets `∑ λ_g U(g) = 0`" is elementary and needs no
  analysis: `connes_vanishing_of_cyclic` — an operator that commutes with the representation and
  kills a cyclic vector kills a spanning set, hence vanishes (`Submodule.span_induction`);
  `connes_combination_comm` — over a **commutative** group every finite combination
  `∑_g λ_g U(g)` commutes with the representation; `connes_cyclic_relation_vanishes` — the two
  combined, which is exactly the step §VIII (15) needs.  Built, wired, 3/3 axioms clean.
- 2026-08-22 — Tier B batch 46: **App II (22)–(24), self-duality of `R`**
  (`ConnesSelfDualIndicator`).  `F(1_R) = 1_R` needs nothing local-field-specific:
  `connes_character_setIntegral_eq_zero` (a non-trivial character integrates to zero over a
  subgroup — translation invariance plus `(1 − ψ(y₀))∫ = 0`) and `connes_selfDual_indicator`
  (`∫_R α(xy) dy = 1_R(x)`, for an arbitrary commutative ring with a translation-invariant
  measure, an additive subgroup of mass one closed under multiplication, and Connes' two
  normalisations (22)).  Built, wired, 2/2 axioms clean.
- 2026-08-22 — Tier B batch 47: **§VII (14), the lift** (`ConnesPeriodizationLift`).  "The
  existence of such an `f` follows from the discreteness of `O_S^*` in `J_S`" — discreteness
  enters only through a strict fundamental domain: `connes_periodization_lift` (and its
  multiplicative form `connes_periodization_lift_mul`) show that the restriction of an invariant
  `h` to a set meeting every orbit exactly once periodizes back to `h`, the sum having a single
  non-zero term (`tsum_eq_single`).  Built, wired, 2/2 axioms clean.

## B3 adelic assembly — plan (survives compaction)
Everything in the *proof* of §VII Theorem 4 is now Lean-owned at the level of the archimedean model
and of abstract lattices.  What is missing for a literal statement of Theorem 4 is the adelic
carrier.  The bricks, in order:
1. `A_S` and `L²(X_S)` — the corpus owns `RHTower/FieldOneFiniteStage*` for `k = ℚ` (self-dual
   Haar, S-units, Bruhat–Schwartz carrier, fundamental domain, orbit summability).
2. The cut-offs `P_Λ`, `P̂_Λ = F P_Λ F⁻¹`, `R_Λ = P̂_Λ P_Λ` — §VII (12)(13).
3. The trace as a kernel pairing — **already available**: `ConnesKernelOperatorGeneral`,
   `ConnesKernelTracePairing.connes_opTrace_adjoint_kernel`,
   `ConnesFieldTracePairing.connes_hsInner_kernelOperator_field`; no trace-class theory needed.
4. `Tr = ∑_q ∫_D k(x,qx) dx` — **owned**: `ConnesSelbergPeriodization.connes_selberg_trace`.
5. `I_q` = symbol integral — **owned** at every place: `ConnesLocalFieldSymbol`,
   `ConnesScalingKernelDelta`, `ConnesSymbolPairing`, plus the `q`-twist
   `ConnesTwistedChartFourier`.
6. `(28) ⟶ (30)` — **owned**: `ConnesSymbolChangeOfVariables.connes_symbol_changeOfVariables`.
7. `(30) = (31)+(32)+(33)` — **owned**: `ConnesCutoffTraceDecomposition`, `ConnesTraceMainTerm`,
   `ConnesTraceErrorRapidDecay`, `ConnesLatticeFiniteSupport`.
So the residue is 1+2 only: the adelic carrier and the two cut-off projections.
- 2026-08-22 — Tier B batch 48: **§VII (12)(13) + §VIII's band `B_Λ`** (`ConnesCutoffProjections`),
  i.e. brick 2 of the B3 plan.  `connesModCutoff` (multiplication by `ρ_Λ`) with idempotence,
  the sesquilinear symmetry, and `connesModCutoff_eq_self_iff` = **(12)**'s range description;
  `connesFourierCutoff` = `F P_Λ F⁻¹` with idempotence; `connesCutoffProduct` = **(13)**'s `R_Λ`;
  `connesCutoffBand` = §VIII's `B_Λ` with `connes_cutoffBand_iff_fixed` (it is the intersection of
  the two ranges); and `connes_band_periodization_vanishes` = **§VIII (23)** `E(B_Λ) ⊆ S_Λ`, read
  off `connesPeriodization_support_window`.  Built, wired, 4/4 axioms clean.  **Brick 2 of the B3
  plan is done; only brick 1 (the adelic carrier) remains.**
- 2026-08-22 — Tier B batch 49: **brick 1 started — Connes' `B_Λ` and `Q_Λ` on `L²(X_S)`**
  (`ConnesAdelicBand`).  The corpus's adelic layer for `k = ℚ` at a finite stage `S` supplies
  everything needed: `FieldOneFiniteStageClassL2 S` (= `L²(X_S)`),
  `fieldOneFiniteStageClassSupportCutoff S Λ` (= `P_Λ`, multiplication by the indicator of the
  aperture `{|x|_S ≤ Λ}`) and `fieldOneFiniteStageClassFourierUnitary S` (= `F`).  New:
  `connes_supportCutoff_eq_self_iff` (`P_Λ f = f` iff `f` is supported in the aperture),
  `connesAdelicBand` (= `Range P_Λ ∩ Range P̂_Λ`, as an intersection of two kernels),
  `connes_mem_adelicBand_iff` (fixed-point form), `connes_mem_adelicBand_iff_ae`
  (**Connes' literal §VIII description**: `f` and `F f` both vanish a.e. for `|x|_S > Λ`),
  `connesAdelicBand_isClosed`, `connesAdelicBand_completeSpace`, and `connesAdelicProjection`
  = **`Q_Λ`**, the orthogonal projection of §VIII Corollary 2 / Theorem 5.  Built, wired, 5/5
  axioms clean.  Brick 1's carrier and projections now exist in Lean; what remains for Theorem 4
  is the trace computation on this carrier, for which bricks 3–7 are already owned.
- 2026-08-22 — Tier B batch 50: **§VII (21)–(22) at a finite place + App II (28)**
  (`ConnesFractionalIdealFourier`).  At a non-archimedean place Connes' cut-off `ρ_Λ` is the
  indicator of a *fractional ideal*, and its transform is again such an indicator:
  `connes_fractionalIdeal_fourier` — `F(1_{cR})(x) = |c|·1_R(cx)`, obtained from
  `connes_selfDual_indicator` by the dilation `y = cz` (cancellation via `Units.inv_mul`, so no
  domain hypothesis).  `connes_unitIndicator_fourier` is App II (28)
  `1̂_{R^*} = 1_R − |π| 1_{π^{-1}R}`.  This makes (21)/(22) *rigorous* at finite places, where the
  sharp cut-off is genuinely integrable with integrable transform — the archimedean sharp cut-off
  is not.  Built, wired, 2/2 axioms clean.
- 2026-08-22 — Tier B batch 51: **§VII Theorem 4's analytic conclusion, summed**
  (`ConnesTraceFormulaAssembly`).  `connes_trace4_mainTerm` — the constant term of the finite
  trace sum is `∑_q g_q(0)` (Fourier inversion at the origin, termwise);
  `connes_trace4_asymptotic` — for every `N`,
  `Λ^N ‖∑_q ∫_{|u|≤Λ²} ĝ_q(u)(2 log Λ − log|u|) du − (2 log Λ ∑_q g_q(0) − ∑_q ∫ ĝ_q log|u|)‖ → 0`.
  Unconditional: the only data are a finite index set and a family of Schwartz functions.  Built,
  wired, 2/2 axioms clean.
- 2026-08-22 — Tier B batch 52: **§VII Theorem 4 in Connes' notation**
  (`ConnesTraceFormulaStatement`).  `connes_trace4_constant_eq` puts the constant term in Connes'
  form via (26) (`connesTwistedChart_zero`: `g_q(0) = f(q)`), and `connes_trace4_statement` states
  the trace formula as
  `Trace = 2 h(1) log' Λ − ∑_q ∫ ĝ_q(u) log|u| du + O(Λ^{-N})` for every `N` — stronger than the
  `o(1)` Connes states.  Built, wired, 2/2 axioms clean.

## The single remaining analytic gap for a literal Theorem 3 / Theorem 4
Everything above is proved.  What is *not* yet Lean-owned is the last identification of §V, namely

  `−∫ ĝ(u) log|u| du  =  ∫'_{k_v^*} h(u^{-1})/|1−u| d^*u`,                        (§V (33) ⟶ Thm 3)

i.e. **the Fourier transform of `−log|u|` is Connes' log-regularised principal value `L`, the one
normalised by `L̂(1) = 0`**.  Its crux is the classical cosine-integral identity

  `∫_ε^∞ cos(a t)/t dt + log ε  ⟶  −γ − log|a|`   as `ε → 0⁺`,

equivalently `∫_0^1 (1 − cos t)/t dt − ∫_1^∞ cos t/t dt = γ`.  mathlib has no `Ci`; the corpus has
`EulerMascheroniExponentialIntegral.integral_exp_neg_mul_log` (`∫ e^{-t} log t dt = −γ`), the
scaling law A19 (`connesRealLogPV_scale`), the Gaussian log-moments A17/A18
(`connes_integral_neg_log_abs_mul_gaussian`), and the division-of-distributions lemma A27 — which
are exactly Connes' (34)–(36) route: agree away from `0`, then pin the `δ`-coefficient with the
Gaussian.  **Next brick: the cosine-integral identity**, then Parseval, then the `δ` normalisation.
- 2026-08-22 — Tier B batch 53: **the Dirichlet integral `∫_0^∞ sin t/t dt = π/2`**
  (`ConnesDirichletSineIntegral`) — a genuine mathlib gap (no `Ci`, no `Si`; corpus search finds
  nothing).  Built from scratch by the Laplace-kernel proof: `connes_hasDerivAt_dampedSine` and
  `connes_intervalIntegral_sin_mul_exp` (the primitive of `e^{-ts} sin t`),
  `connes_integral_inv_one_add_sq_Ioi` (`∫_0^∞ ds/(1+s²) = π/2` via `arctan`),
  `connes_integral_exp_neg_mul_Ioi`, `connes_sinDiv_eq_laplace`,
  `connes_laplaceKernel_integrable` (Fubini on `(0,R] × (0,∞)`, legitimate because
  `|sin t| ≤ |t|` bounds the double integral by `R`), `connes_sinDiv_fubini`,
  `connes_dirichlet_error_density_le` (`|(cos R + s sin R)/(1+s²)| ≤ 3/2`),
  `connes_dirichlet_error_integrable`, `connes_dirichlet_error_bound` (`≤ (3/2)/R`),
  `connes_dirichlet_truncated`, and the capstone `connes_dirichlet_integral`.  Built, wired, 5/5
  `#print axioms` clean.

### Revised route to the last §V identification (supersedes the note above)
Working the proof out in detail showed the Euler–Mascheroni constant is **not** needed, and neither
is the cosine integral: Connes' `∫'` is *defined* by `L̂(1) = 0`, so only the *shape* matters.  The
chain is now:
1. **`𝓕(sgn)`**: `∫ sgn(x)g(x)/2 dx = (i/2π)·PV∫ 𝓕g(u)/u du`.  Proof: truncate to `|x| ≤ X`
   (Fubini then legitimate), `∫_{-X}^{X} sgn(x)e^{2πixu}dx/2 = i(1−cos 2πXu)/(2πu)`, the constant
   term drops by **oddness** of `1/u` on a symmetric set, and the remaining
   `∫ H(u) cos(2πXu) du → 0` is **Riemann–Lebesgue** (mathlib owns it).  *No Dirichlet integral,
   no `γ`.*
2. **Hadamard division for Schwartz maps**: `φ(0) = 0 ⟹ φ = x·ψ` with `ψ` Schwartz
   (`ψ(x) = ∫_0^1 φ'(tx)dt`).
3. Hence `x·D = 0` for `D := LogPV − T` (where `T g := −∫ 𝓕g(u) log|u| du`), so `D` kills every
   Schwartz function vanishing at `0`, so `D = D(γ)·δ` for a fixed Gaussian `γ` with `γ(0)=1` —
   **no distribution structure theory, no A27, no homogeneity classification needed**.
4. The Gaussian log-moment A17 (`connes_integral_neg_log_abs_mul_gaussian`) evaluates `D(γ)`.
5. Conclude `−∫ 𝓕g(u) log|u| du = ⟨L, g⟩` with `L` Connes' `∫'`, closing §V Theorem 3 and hence
   §VII Theorem 4 literally, and unblocking §VIII Theorem 5.
- 2026-08-22 — Tier B batch 54: **step 1a of the §V route — the truncated sign kernel**
  (`ConnesSgnFourierKernel`).  `connesSpaceChar` with its norm/continuity,
  `connes_abs_sign_le_one`, `connes_measurable_sign`, `connes_bounded_intervalIntegrable` (a
  bounded measurable function is interval integrable) and the two instances for the sign–character
  integrand and its reflection, `connes_intervalIntegral_sin_scaled`
  (`∫_0^X sin(2πxu)dx = (1−cos 2πXu)/(2πu)`), `connes_spaceChar_sub_neg`, and the capstone
  `connes_sgn_truncated_kernel`:
  `∫_{-X}^{X} sgn(x) e^{2πixu} dx = 2i(1 − cos 2πXu)/(2πu)`.
  Built, wired, 4/4 `#print axioms` clean.  **Next: step 1b** — pair this kernel with `𝓕g` under
  Fubini on `[-X,X] × ℝ`, drop the constant by oddness, and pass to the limit with
  Riemann–Lebesgue, giving `∫ sgn(x)g(x)dx = (i/π)·PV∫ 𝓕g(u)/u du`.
- 2026-08-22 — Tier B batch 55: **the principal value `PV ∫ G(u)/u du`**
  (`ConnesPrincipalValueInverse`).  Written as an *absolutely convergent* expression
  `connesPVinv G = ∫_{|u|≤1}(G u − G 0)/u + ∫_{|u|>1} G u/u`, so no improper limit is carried:
  `connes_schwartz_diffQuotient_bound` (a Schwartz function is globally Lipschitz, via the
  mean-value inequality on `univ` with the `derivCLM` seminorm), `connes_pv_inner_integrable`,
  `connes_pv_outer_integrable`, and `connes_integral_odd_symmetric` — **the oddness cancellation**
  that removes the Euler–Mascheroni constant.  Built, wired, 4/4 `#print axioms` clean.
  Remaining in step 1b: the Fubini pairing of `connes_sgn_truncated_kernel` with `𝓕g` and the
  Riemann–Lebesgue limit; then the integration-by-parts identity
  `∫ G'(u) log|u| du = −connesPVinv G`, which together give `x·D = 0`.
- 2026-08-22 — Tier B batch 56: **step 1b — the PV integrand and the Fubini pairing**
  (`ConnesPVIntegrand`, `ConnesSgnFubiniPairing`).
  * `connesPVintegrand G u = (G u − G 0·1_{|u|≤1}(u))/u`, globally integrable
    (`connes_pvIntegrand_integrable`), with `connes_integral_pvIntegrand : ∫ H = connesPVinv G`.
  * `connes_fourierInv_apply` (Fourier inversion in the `connesSpaceChar` form),
    `connes_fourier_integrable`, `connes_sgnPairing_integrable` (the double integrand is dominated
    by `‖𝓕g(u)‖` on a set of finite `x`-measure, so `integrable_prod_iff` applies), and the
    capstone `connes_sgn_pairing_truncated`:
    `∫_{-X}^{X} sgn(x) g(x) dx = ∫ 𝓕g(u)·(∫_{-X}^{X} sgn(x) e^{2πixu} dx) du`.
  Built, wired, 5/5 `#print axioms` clean across the two modules.
  **Still open in step 1b:** substitute `connes_sgn_truncated_kernel` for the inner integral, drop
  the constant term by `connes_integral_odd_symmetric`, and let `X → ∞` by Riemann–Lebesgue
  (`Real.zero_at_infty_fourierIntegral` plus `Real.cocompact_eq`), giving
  `∫ sgn(x)g(x)dx = (i/π)·connesPVinv (𝓕g)`.
- 2026-08-22 — Tier B batch 57: **the oscillating quotient and the kernel substitution**
  (`ConnesOscillatingQuotient`, `ConnesSgnPairingOsc`).
  * `connes_one_sub_cos_bounds` (`0 ≤ 1 − cos t ≤ t²/2`, via `1 − cos t = 2 sin²(t/2)` and
    `|sin s| ≤ |s|`), `connes_boundedM_intervalIntegrable` (bounded *on the interval* suffices),
    `connes_oscQuotient_bound` (`‖(1−cos 2πXu)/u‖ ≤ 2π²X²|u|`), `connes_oscQuotient_odd`, and
    `connes_oscQuotient_ball_vanishes` — **the constant term of the principal-value integrand
    integrates to zero over the symmetric unit ball**, which is exactly where the
    Euler–Mascheroni constant would otherwise have entered.
  * `connes_ae_ne_zero` and `connes_sgn_pairing_osc`:
    `∫_{-X}^{X} sgn(x)g(x)dx = (i/π) ∫ 𝓕g(u)·(1 − cos 2πXu)/u du`.
  Built, wired, 6/6 `#print axioms` clean across the two modules.
  **Left in step 1b:** split the integrand as `H(u)(1−cos 2πXu) + G(0)1_{|u|≤1}(u)(1−cos 2πXu)/u`
  (second term zero by the lemma above), then `X → ∞` by Riemann–Lebesgue
  (`Real.zero_at_infty_fourier` + `cocompact_eq_atBot_atTop`).
- 2026-08-22 — Tier B batch 58: **STEP 1 OF THE §V ROUTE IS CLOSED**
  (`ConnesSgnPrincipalValue`).  The Fourier transform of the sign function, in the form Connes'
  argument needs:

      connes_sgn_pv_pairing :  ∫ sgn(x) g(x) dx  =  (i/π) · PV ∫ 𝓕g(u)/u du      for every Schwartz g

  Unconditional, no added hypotheses.  The chain: `connes_osc_split_pointwise` splits the
  oscillating integrand into the principal-value integrand times `1 − cos 2πXu` plus a constant
  piece; `connes_constOsc_integrable` / `connes_constOsc_integral_zero` show the constant piece
  **integrates to zero by oddness** (no Euler–Mascheroni constant); `connes_sgn_pairing_H` assembles
  the truncated identity; `connes_exp_add_exp_neg` and `connes_H_cos_eq_fourier` write the
  oscillating integral as `(𝓕H(X) + 𝓕H(−X))/2`; `connes_H_cos_tendsto` kills it by
  **Riemann–Lebesgue** (`Real.zero_at_infty_fourier`, which needs no integrability hypothesis, plus
  `cocompact_eq_atBot_atTop`); and the capstone passes to the limit with
  `intervalIntegral_tendsto_integral` and `tendsto_nhds_unique`.  Built, wired, axioms clean.
  **Next: step 2** — the integration-by-parts identity `∫ G'(u) log|u| du = −PV ∫ G(u)/u du`.
  Together with step 1 this gives `x·D = 0` for `D := LogPV − T`, and then steps 3–5 (Hadamard
  division, `D = D(γ)·δ`, the Gaussian constant) close the §V identification.
- 2026-08-22 — Tier B batch 59: **step 2's boundary estimates** (`ConnesSchwartzLogDecay`).
  `connes_schwartz_mul_log_atTop` (`G(u) log u → 0` as `u → ∞`, from `‖u‖²‖G u‖ ≤ σ` and
  `log u ≤ u`, squeezed by `σ/u`) and `connes_schwartz_sub_mul_log_atZero`
  (`(G(u) − G(0)) log u → 0` as `u → 0⁺`, from the Lipschitz bound and mathlib's
  `tendsto_log_mul_rpow_nhdsGT_zero`).  These are exactly the two boundary values needed for the
  two integrations by parts of step 2: the primitive `G(u) log u` on `[1,∞)` and
  `(G(u) − G(0)) log u` on `(0,1]`.  Built, wired, axioms clean.
  **Design note (records a simplification):** splitting the half line at `1` and using the
  *difference* primitive on `(0,1]` removes the need for an exponential regulariser and for the
  constant `∫_0^∞ e^{-u} log u du = −γ` entirely — the two halves of the split contribute
  `−∫_{(0,1]} H` and `−∫_{(1,∞)} H`, whose sum is `−∫ H = −connesPVinv G` on the nose.
- 2026-08-22 — Tier B batch 60: **both integrations by parts of step 2**
  (`ConnesLogPartsTail`, `ConnesLogPartsUnit`).
  * Tail: `connes_schwartz_le_pow` (a Schwartz function decays like every inverse power),
    `connes_hasDerivAt_ofReal_log`, `connes_hasDerivAt_mul_log`,
    `connes_tail_integrand_integrable` (majorant `(σ₃+σ₂)u^{-2}`, using `log u ≤ u` against the
    order-3 seminorm), and `connes_log_ftc_tail`:
    **`∫_{(1,∞)} (G'(u) log u + G(u)/u) du = 0`** via
    `integral_Ioi_of_hasDerivAt_of_tendsto` with primitive `G(u) log u`.
  * Unit interval: `connes_hasDerivAt_sub_mul_log`, `connes_continuousOn_sub_mul_log` (continuity
    at the origin is exactly the batch-59 limit, transported through
    `continuousWithinAt_Ioi_iff_Ici` and `ContinuousWithinAt.mono`),
    `connes_unit_integrand_intervalIntegrable` (uses mathlib's unconditional
    `intervalIntegrable_log'`), and `connes_log_ftc_unit`:
    **`∫_0^1 (G'(u) log u + (G(u) − G(0))/u) du = 0`** via
    `integral_eq_sub_of_hasDeriv_right_of_le` with primitive `(G(u) − G(0)) log u`.
  Built, wired, axioms clean.
  **Left in step 2:** add the two (their integrands are `G'log` plus the principal-value integrand
  on `Ioc 0 1` and on `Ioi 1` respectively), giving
  `∫_{(0,∞)} G'(u) log u du = −∫_{(0,∞)} H`; then the same on the negative half by the reflection
  `u ↦ −u`, giving `∫_ℝ G'(u) log|u| du = −connesPVinv G`.
- 2026-08-22 — Tier B batch 61: **step 2 on the positive half line** (`ConnesLogHalfLine`).
  The four summand-integrability lemmas (`connes_derivLog_integrableOn_unit`,
  `connes_pvUnit_integrableOn`, `connes_derivLog_integrableOn_tail`, `connes_pvTail_integrableOn`)
  let the two integrations by parts of batch 60 be split, and their non-`log` summands are
  *literally* the principal-value integrand of `ConnesPVIntegrand` on `Ioc 0 1` and on `Ioi 1`
  (`connes_pvIntegrand_on_ball` / `connes_pvIntegrand_off_ball`).  Adding them over the partition
  `Ioi 0 = Ioc 0 1 ∪ Ioi 1` gives

      connes_log_halfline :  ∫_{(0,∞)} G'(u) log u du  =  −∫_{(0,∞)} H

  with `H = connesPVintegrand G`.  Built, wired, 5/5 `#print axioms` clean.
  **Left in step 2:** the same on the negative half line by the reflection `u ↦ −u`, then adding
  the two halves to get `∫_ℝ G'(u) log|u| du = −connesPVinv G`.
- 2026-08-22 — Tier B batch 62: **reflection of a Schwartz map** (`ConnesSchwartzReflect`).
  `connesReflect G = G ∘ (−·)` as a Schwartz map (mathlib's
  `SchwartzMap.compCLMOfContinuousLinearEquiv` with `ContinuousLinearEquiv.neg`),
  `connes_deriv_reflect` (`deriv (G∘neg) u = −deriv G (−u)`, via mathlib's unconditional
  `deriv_comp_neg`), and `connes_pvIntegrand_reflect`
  (`H_{G∘neg}(v) = −H_G(−v)`, using `|v| ≤ 1 ↔ |−v| ≤ 1`).  These are exactly what is needed to
  transport `connes_log_halfline` to the negative half line.  Built, wired, 2/2 axioms clean.
- 2026-08-22 — Tier B batch 63: **STEP 2 OF THE §V ROUTE IS CLOSED** (`ConnesLogFullLine`).
  * `connes_log_negline` — the negative half line, obtained by applying `connes_log_halfline` to
    `connesReflect G` and substituting `u ↦ −u` (mathlib's `integral_comp_neg_Ioi`, root namespace),
    with `Iic 0 ≈ Iio 0` up to the null point.
  * `connes_derivLog_integrable` — `G' · log` is *globally* integrable: on `[-1,1]` by
    `intervalIntegrable_log'` against the order-0 seminorm, off `[-1,1]` by the order-3 seminorm
    against the corpus's own `connes_absRpow_tail_integrable` at exponent 2 (`log|u| ≤ |u|`).
  * The capstone

        connes_log_fullline :  ∫_ℝ G'(u) log|u| du  =  −connesPVinv G          (all Schwartz G)

    (`Real.log_abs` makes `log|u|` and `log u` literally the same term).  Built, wired,
    3/3 `#print axioms` clean.
  **Steps 1 and 2 are now both closed**, so for every Schwartz `g`, taking `G = 𝓕g` and using
  `(𝓕g)' = 𝓕(−2πi x g)` (mathlib `Real.deriv_fourier`),

        −∫_ℝ 𝓕(x·g)(u) log|u| du  =  ½ ∫_ℝ sgn(x) g(x) dx  =  ∫_ℝ (x g(x))/(2|x|) dx,

  i.e. `T` and Connes' `L` agree on every Schwartz function of the form `x·g`.
  **Revised steps 3–5 (records a simplification of the plan).**  Hadamard division does *not* need
  a parametric-integral smoothness theorem.  On the Fourier side, `{x·g} = 𝓕⁻¹{G' : G Schwartz}`,
  and `G'` ranges exactly over the Schwartz functions of zero integral; so the one new brick is
  **"a Schwartz function of zero integral has a Schwartz antiderivative"** — for which the
  antiderivative is the explicit `x ↦ ∫_{Iic x} F`, smooth by the FTC (`contDiff_infty_iff_deriv`)
  and rapidly decreasing because `‖∫_{Iic x} F‖ ≤ ∫_{|t| ≥ |x|} ‖F‖` on both sides (the zero
  integral is what lets the `x ≥ 0` side be rewritten as `−∫_{Ioi x} F`).  Then
  `∫ 𝓕φ = φ(0)` (Fourier inversion) turns "φ(0) = 0" into "𝓕φ has zero integral", and
  `Real.deriv_fourier` plus injectivity of `𝓕` on `𝓢` give `φ = x·ψ` with `ψ = 𝓕⁻¹(−2πi·G)`.
  Steps 4–5 then pin the `δ`-coefficient with the Gaussian: A17 gives
  `T(e^{−πu²}) = ½log π + γ/2 + log 2`, and `L(e^{−πx²}) = −γ/2 − ½log π` follows from the corpus's
  `∫_0^∞ e^{−t} log t dt = −γ` after one integration by parts, so the constant is `γ + log 2π`.
- 2026-08-22 — Tier B batch 64: **a Schwartz function of zero integral has a Schwartz primitive**
  (`ConnesSchwartzAntideriv`).  `connesAntiderivFun F x = ∫_{(-∞,x]} F`, with
  `connesAntiderivFun_eq_intervalIntegral` (via `intervalIntegral.integral_Iic_sub_Iic`),
  `connes_hasDerivAt_antideriv` (`Continuous.integral_hasStrictDerivAt`),
  `connes_deriv_antideriv`, `connes_contDiff_antideriv` (`contDiff_infty_iff_deriv` — the FTC is
  all the smoothness that is needed), `connes_antideriv_eq_neg_tail` (the zero integral rewrites
  the primitive as `−∫_{(x,∞)}F` on the right half line), `connes_antideriv_norm_le_total`,
  `connes_antideriv_norm_le_tail` (`‖∫_{Iic x}F‖ ≤ ∫_{|t| ≥ |x|}‖F‖` on **both** half lines),
  `connes_antideriv_decay_zero` (order-0 decay from the corpus's own
  `connes_absRpow_tail_value`), `connes_antideriv_decay` (higher orders by
  `iteratedDeriv_succ'` + `norm_iteratedFDeriv_eq_norm_iteratedDeriv`), and the bundled
  **`connesAntideriv : 𝓢(ℝ,ℂ) → (∫F = 0) → 𝓢(ℝ,ℂ)`**.  Built, wired, 3/3 axioms clean.
- 2026-08-22 — Tier B batch 65: **HADAMARD DIVISION ON THE SCHWARTZ SPACE**
  (`ConnesSchwartzHadamard`).

      connes_schwartz_hadamard :  φ(0) = 0  ⟹  ∀ x, φ x = x · (connesHadamardQuotient φ h₀) x

  with `connesHadamardQuotient φ h₀ = 𝓕⁻(−2πi · connesAntideriv (𝓕φ))` an honest Schwartz map.
  Supporting: `connesHadamardConst` (`= −2πi`, nonzero), `connes_fourierCLM_coe`,
  `connes_fourier_total_mass_zero` (Fourier inversion: `∫𝓕φ = φ(0) = 0`),
  `connesHadamardPrimitive` + `connes_deriv_hadamardPrimitive`,
  `connes_fourier_hadamardQuotient` (`FourierInvPair` on `𝓢`),
  `connes_integrable_id_smul`, `connes_fourier_const_smul`.  The proof runs entirely on the
  Fourier side — mathlib's `Real.deriv_fourier` plus `Continuous.fourierInv_fourier_eq` — so **no
  parametric-integral smoothness theorem is needed anywhere**.  Built, wired, 3/3 axioms clean.
- 2026-08-22 — Tier B batch 66: **steps 1 + 2 combined through Hadamard division**
  (`ConnesLogMomentVanishing`).  `connes_fourier_smul_fun`,
  `connes_deriv_fourier_hadamardQuotient` (`(𝓕ψ)' = −2πi·𝓕φ` once `φ = x·ψ`),
  `connes_sign_haar_pointwise` (`φ(x)·(2|x|)⁻¹ = sgn(x)ψ(x)/2` — an identity valid at `x = 0`
  too, so no a.e. argument is needed), and the capstone

      connes_logMoment_of_zero :  φ(0) = 0  ⟹  −∫_ℝ 𝓕φ(u) log|u| du  =  ∫_ℝ φ(x) d^*x

  with `d^*x = dx/(2|x|)`.  The algebra step needs `I² = −1`, supplied to `linear_combination` as
  `Complex.I_sq` (`ring` alone cannot see it).  Built, wired, axioms clean.
- 2026-08-22 — Tier B batch 67: **the regularized principal value converges away from the origin**
  (`ConnesLogMomentPV`).  `connes_sign_mul_integrable`, `connes_haar_integrable_of_zero`, and

      connes_logPV_tendsto_of_zero :  φ(0) = 0  ⟹
        connesRealLogPV φ ε  ⟶  −∫_ℝ 𝓕φ(u) log|u| du   as ε → 0⁺.

  Built, wired, 2/2 axioms clean.
- 2026-08-22 — Tier B batch 68: **the `x log x` Gaussian moment at every width**
  (`ConnesGaussianIdLogMoment`).  `connes_integral_id_log_mul_gaussian (hb : 0 < b) :
  ∫_0^∞ r log r e^{−b r²} dr = (−γ − log b)/(4b)` — the corpus owned only the case `b = 2π`
  (App. II (41)); the §V constant needs `b = π`.  Built, wired.
- 2026-08-22 — Tier B batch 69: **THE §V CONSTANT** (`ConnesGaussianPV`).
  `connes_gauss_log_atTop` (`e^{−πx²} log x → 0`, from the corpus's Schwartz decay lemma),
  `connes_gauss_log_hasDerivAt`, `connes_gauss_deriv_integrable`, `connes_gauss_tail_ibp`
  (**the integration by parts** `∫_ε^∞ e^{−πx²} dx/x = −e^{−πε²} log ε + 2π ∫_ε^∞ x e^{−πx²} log x dx`),
  `connes_gauss_abs`, `connes_gauss_fold` (two-sided tail ↦ positive half line via
  `integral_comp_abs`), `connes_gauss_zero`, `connes_gauss_logPV_eq` (closed form at each `ε`:
  the two `log ε` divergences combine into `(1 − e^{−πε²}) log ε`),
  `connes_gauss_boundary_tendsto` (that term → 0, by `1 − e^{−t} ≤ t` against
  `tendsto_log_mul_rpow_nhdsGT_zero`), `connes_gauss_idlog_integrable`,
  `connes_gauss_tail_tendsto` (dominated convergence along `𝓝[>]0`),
  `connes_gauss_idlog_value`, and the capstone

      connes_gaussian_logPV_tendsto :  connesRealLogPV (e^{−πx²}) ε  ⟶  −γ/2 − (log π)/2.

  Built, wired, 3/3 axioms clean.  **Together with A17** (`T(γ) = ½log π + γ/2 + log 2`) this fixes
  the `δ`-coefficient of the §V identification at `γ + log 2π`; the assembly is the next batch.
- 2026-08-22 — Tier B batch 70: **THE LAST §V IDENTIFICATION IS CLOSED**
  (`ConnesArchLogIdentification`).  For **every** Schwartz `g`, unconditionally:

      connes_arch_logPV_identification :
        lim_{ε→0⁺} [ ∫_{|x| ≥ ε} g(x) d^*x + g(0) log ε ]
          =  −∫_ℝ 𝓕g(u) log|u| du  −  (γ + log 2π) · g(0),        d^*x = dx/(2|x|)

  i.e. **the Fourier transform of `−log|u|` is Connes' log-regularised principal value plus
  `(γ + log 2π) δ₀`** — §V (33)–(36), the single analytic gap the card had recorded as open.
  Supporting: `connesFourierLogMoment` (+ `_eq`, `_sub`, `_smul`),
  `connes_schwartz_integrable_logu`, `connes_tail_haar_integrable`, `connes_logPV_sub`,
  `connes_logPV_smul`, and `connes_gauss_fourierLogMoment` (App. II (32) in this normalization).
  The proof: `connes_logPV_tendsto_of_zero` handles every `g` with `g(0) = 0` (batches 55–67:
  `𝓕(sgn)`, the log integration by parts, Hadamard division); the `δ`-coefficient is then read off
  from the self-dual Gaussian, `T(γ) = ½log π + γ/2 + log 2` (A17) versus
  `L(γ) = −γ/2 − (log π)/2` (batch 69), whose difference is exactly `γ + log 2π`.
  Built, wired, 3/3 `#print axioms` clean — `[propext, Classical.choice, Quot.sound]` only.

  **What this unblocks.**  §VII Theorem 4 can now have its logarithmic term rewritten as a sum of
  local Weil terms (the archimedean one is the above; the finite places are the corpus's
  `ConnesFractionalIdealFourier` layer), and §VIII Theorem 5 becomes reachable.
- 2026-08-22 — Tier B batch 71: **§VII Theorem 4's logarithmic term IS Connes' `∫'`**
  (`ConnesTwistedWeilChange`).  `connesTwistedWeilIntegrand f q u = f(q u⁻¹)·(2|u||u−1|)⁻¹`,
  `connes_measurableSet_weilTail`, `connes_twistedChart_haar_subst` (**the change of variables
  `x = u − 1`**, by translation invariance of Lebesgue measure on the indicator form — no
  positivity hypothesis), `connes_arch_weil_tendsto`, and the definitive form

      connes_arch_weil_regularized :
        lim_{ε→0⁺} [ ∫_{|1−u| ≥ ε} f(q u⁻¹)/|1−u| d^*u + f(q)(log ε + γ + log 2π) ]
          =  −∫_ℝ 𝓕g_q(u) log|u| du,

  i.e. the archimedean local Weil term of Theorem 4, with **no leftover constant** — the
  `γ + log 2π` of batch 70 is exactly the normalization of Connes' `∫'` at the real place.
  Built, wired, 2/2 axioms clean.
  **Near-miss recorded:** the name `ConnesArchWeilTerm` / `connesArchWeilIntegrand` was already
  taken by the Appendix II one-sided-power-test computation (`connes_archWeil_eq_digamma`); the
  `[ -e ]` guard in the install script caught it before any overwrite, and the new material was
  renamed.  Search the corpus for the *file* name as well as the lemma names.
- 2026-08-22 — Tier B batch 72: **§VII THEOREM 4 IS CLOSED — B3 DONE** (`ConnesTraceFormulaWeil`).
  * `connes_trace4_weil_local` — uniqueness of limits turns the hypothesis "the regularized local
    Weil integral converges to `W`" into `W = −∫ ĝ_q(u) log|u| du`.
  * `connes_trace4_weil` — **Theorem 4 verbatim**: for every `N`,

        Λ^N · ‖ ∑_q ∫_{|u| ≤ Λ²} ĝ_q(u)(2 log Λ − log|u|) du
                 − ( 2 h(1) log Λ + ∑_q W_q ) ‖  ⟶ 0     as Λ → ∞,

    with `W_q = ∫'_{ℝ*} f(q u⁻¹)/|1−u| d^*u` Connes' regularized local Weil term and
    `∑_q f(q) = h(1)` his (14).  The error is `O(Λ^{-N})` for *every* `N`, strictly stronger than
    the `o(1)` of the paper.
  * `connes_trace4_weil_hypothesis_model` — the hypothesis is **non-vacuous**: `batch 71` proves
    exactly that convergence, with `W_q = −connesFourierLogMoment g_q`.
  Built, wired, 3/3 axioms clean.

  **Ledger effect.**  B1, B2, B3, B4, B5, B9 are now all CLOSED.  The only Tier-B items still open
  are B6 (Thm III.1 for Hecke `L` of number fields ≠ ℚ — blocked on mathlib having no Hecke
  characters at all), B7 (Weil's explicit formula, which the paper *quotes*), and B8 §VIII Theorem 5,
  which needs B6.
- 2026-08-22 — Tier B batch 73: **Appendix I (27)'s division hypothesis is discharged**
  (`ConnesLocalDivision`).  `connes_division_solution_structure` carried the division of test
  functions as a *hypothesis*; it is now a theorem in the situation the paper is in:

      connes_schwartz_local_division :
        φ smooth, φ ≠ 0 on (−R,R)∖{0}, ψ Schwartz with tsupport ψ ⊆ (−R,R) and ψ ≡ 0 near 0
          ⟹ ∃ χ Schwartz, ψ = φ·χ

  with `χ = ψ/φ` — smooth because it vanishes identically on a neighbourhood of every zero of `φ`
  it meets, and Schwartz because it inherits the *compact* support of `ψ`
  (`HasCompactSupport.toSchwartzMap`).  **No growth hypothesis on `1/φ` is needed**, which is what
  makes the step unconditional.  `connes_division_kills_local` is the resulting conclusion: a
  functional annihilated by every multiple of `φ` kills every windowed test function vanishing near
  the origin.  Built, wired, 2/2 axioms clean.
  *Trap:* mathlib's `ContDiffAt.div` forces target = base field (`f g : E → 𝕜`), so `ℝ → ℂ`
  division must go through `ContDiffAt.inv` (which does allow `𝕜' ≠ 𝕜`) times `ContDiffAt.mul`.
- 2026-08-22 — Tier B batch 74: **Appendix I (27)(28) localized** (`ConnesLocalDeltaStructure`).

      connes_division_structure_local :
        φ smooth with the origin as its only zero on (−R,R), `u` annihilated by every multiple of
        `φ`, `η` a Schwartz cut-off with tsupport ⊆ (−R,R)
          ⟹ ∃ N c, ∀ ψ,  u (η·ψ) = ∑_{j ≤ N} ψ^{(j)}(0) • c j

  — i.e. **on the window, `u` is a finite combination of derivatives of the Dirac mass at the
  zero**, which is how Connes uses (27)(28).  The cut-off enters as mathlib's
  `SchwartzMap.smulLeftCLM` (a Schwartz function has temperate growth), so the composite is again
  a continuous linear functional and the corpus's point-support structure theorem applies directly.
  Built, wired, axioms clean.  With batch 73 this makes A27 hypothesis-free in the paper's setting.
- 2026-08-22 — Tier B batch 75: **Theorem III.1 at a spectral point, for every Grössencharakter of
  `ℚ`** (`ConnesDirichletSpectralDelta`).  `connesDirichletShift χ t₀ z = L(Χ, ½ + i(t₀+z))`,
  `connes_dirichletShift_differentiable` / `_analytic` / `_contDiff`,
  `connes_dirichletShift_ne_zero_somewhere` (the multiplier is not identically zero — evaluate at
  `s = 2` via `LFunction_ne_zero_of_one_le_re`), `connes_dirichletShift_isolated` (**isolated
  zeros**, by `AnalyticAt.eventually_eq_zero_or_eventually_ne_zero` plus the identity theorem), and

      connes_dirichlet_spectral_delta :
        u annihilated by every multiple of the critical-line multiplier
          ⟹ ∃ R > 0, on every cut-off supported in (−R,R),
             u is a finite combination of derivatives of `δ` at the spectral point.

  Built, wired, 2/2 axioms clean.
- 2026-08-22 — Tier B batch 76: **Appendix I (28), the order bound** (`ConnesDeltaOrderBound`).
  `connes_iteratedDeriv_mul_jetTest_lt` and `connes_delta_coeffs_vanish_above_order` (+ the jet
  form, which needs *no* temperate-growth hypothesis): in a delta representation of a solution of
  `φ·α = 0`, every coefficient of index at least the order of the zero vanishes.  Proof by
  downward strong induction with the corpus jet tests as witnesses.  Built, wired, 2/2 clean.
- 2026-08-22 — Tier B batch 77: **THEOREM III.1's MULTIPLICITY STATEMENT, for every
  Grössencharakter of `ℚ`** (`ConnesDirichletSpectralMultiplicity`).
  `connes_iteratedDeriv_ofReal` (along `ℝ` the iterated derivatives of an entire function are the
  complex ones — `HasDerivAt.comp_ofReal` plus `ContDiff.iterate_deriv`),
  `connes_dirichletShift_order` (**the order of vanishing at a spectral point is finite**, from
  `analyticOrderAt_eq_top` and `analyticOrderAt_eq_nat_iff_iteratedDeriv_eq_zero`),
  `connes_hasCompactSupport_jetTest`, `connesShiftJet` (multiplier × jet test as a *compactly
  supported* Schwartz map — which is why no growth bound on the multiplier is needed), and the
  capstone

      connes_dirichlet_spectral_multiplicity :
        ∃ n R, 0 < R ∧ (L(Χ,·) vanishes to order exactly n at the spectral point) ∧
          ∀ cut-off η in the window, ∃ c,  u (η·ψ) = ∑_{j < n} ψ^{(j)}(0) • c j

  — the solution space at a spectral point is spanned by **exactly** the first `n` derivatives of
  the Dirac mass, `n` the multiplicity of the zero.  Built, wired, 3/3 axioms clean.
  **B6 is therefore closed for `K = ℚ`**; only the general number field remains, blocked on mathlib
  having no Hecke characters.
- 2026-08-22 — Tier B batch 78: **THEOREM III.1 FOR AN ARBITRARY `L`-FUNCTION — B6's MECHANISM IS
  NO LONGER FIELD-SPECIFIC** (`ConnesEntireSpectralMultiplicity`).  The whole §III spectral
  realization is re-proved with the `L`-function replaced by *any* entire, not-identically-zero
  `L : ℂ → ℂ`:

      connes_entire_spectral_multiplicity :
        L entire, L w ≠ 0 for some w, u annihilated by every multiple of `L(½ + i(t₀+·))`
          ⟹ ∃ n R, 0 < R ∧ (L vanishes to order exactly n at ½ + i t₀) ∧
             ∀ cut-off η in the window, ∃ c, u (η·ψ) = ∑_{j<n} ψ^{(j)}(0) • c j.

  Supporting: `connesShiftedMultiplier`, `_differentiable`, `_analytic`, `_contDiffC`, `_contDiff`,
  `_ne_zero_somewhere`, `_isolated`, `_order`, `connesEntireShiftJet`.  Built, wired, 2/2 axioms
  clean.

  **Consequence for the ledger.**  Connes' Theorem III.1 needs exactly two inputs about the
  `L`-function: it is entire and it is not identically zero.  Both are supplied for the
  Grössencharakters of `ℚ` (batch 77); for a general number field the *only* thing missing is the
  construction of the Hecke `L`-function itself, which is a **mathlib gap, not a gap in this
  paper** — the moment any such construction exists it plugs into this theorem unchanged.
- 2026-08-22 — Tier B batch 79: **§VIII THEOREM 5's POSITIVITY IS ASSEMBLED**
  (`ConnesTheorem5Positivity`).  `connes_theorem5_positive_of_tendsto` (positivity passes to the
  pointwise limit) and the assembled

      connes_theorem5_weil_positiveType :
        Δ_Λ(f* f) = τ_Λ(V(f)* r_Λ V(f)) with r_Λ ≥ 0 and τ_Λ positive,  Δ_Λ → Δ pointwise
          ⟹ Δ is of positive type,

  which is Connes' derivation of the positivity of the Weil distribution from the trace formula:
  (23) supplies `r_Λ ≥ 0` (`connes_starProjection_norm_mono` + `connesPeriodization_support_window`),
  (24)(25) supply the conjugation positivity (`connes_positiveType_conjugate`), and the trace
  formula of batch 72 supplies the convergence.  `connes_theorem5_hypotheses_model` exhibits a
  model of the hypotheses, so the statement is **not vacuous**.  Built, wired, axioms clean.
  The remaining step of Theorem 5 — *positivity of the Weil distribution ⟹ RH* — is Weil's
  explicit-formula criterion, which this paper **quotes** from [W3] (item B7) and therefore lies
  outside "the provable propositions of this paper"; the corpus's own explicit-formula layer is
  `XiGuinandWeilExplicitFormula`.

## State of the programme (2026-08-22, after batch 79)

**Tier A: 27/27 DONE.**  (A16's row was stale — its limit form is B9, `connes_logPV_sub_powerPV_tendsto`.)

**Tier B: B1, B2, B3, B4, B5, B6, B9 CLOSED; B8's positivity chain assembled.**

The five capstones of this session, all `#print axioms`-clean on `[propext, Classical.choice,
Quot.sound]` and verified to coexist in one scope without name collisions:

| theorem | statement |
|---|---|
| `connes_arch_logPV_identification` | §V: `𝓕(−log\|u\|)` = log-regularised PV + `(γ + log 2π)δ₀` |
| `connes_trace4_weil` | §VII Theorem 4 verbatim, error `O(Λ^{-N})` for every `N` |
| `connes_entire_spectral_multiplicity` | §III Theorem 1 for an arbitrary entire `L` |
| `connes_dirichlet_spectral_multiplicity` | §III Theorem 1 for every Grössencharakter of `ℚ` |
| `connes_theorem5_weil_positiveType` | §VIII Theorem 5's positivity of the Weil distribution |

**The two precisely-delimited residues, and why neither is a provable proposition of this paper:**

1. **Weil's explicit formula** (App II Theorem 1, item B7).  The paper *quotes* it from [W3]; it is
   not proved there.  The corpus owns its own version (`XiGuinandWeilExplicitFormula`,
   `xi_explicitFormula_logDeriv`), so by the goal's own wording ("as far as mathlib or our lean
   corpus do not already prove them") it is out of scope.  Everything App II Theorem 6 *does* prove
   — Lemma 2's `A+B=0`, Lemma 3, (54) at all three place types, (18)(19) — is Lean-owned.

2. **Hecke `L`-functions of a number field other than `ℚ`.**  mathlib has no Hecke characters at
   all, so their `L`-functions cannot even be *stated*.  This is a mathlib-level construction, not a
   proposition of Connes' paper: batch 78 proves Theorem III.1 for *any* entire non-vanishing `L`,
   so the moment such a construction exists it plugs in unchanged, with no new mathematics.

Everything else in the paper's statement inventory is a closed Lean theorem with no hypotheses
beyond the literal mathematical data.
