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
| B1 | §V Thm 3 (local trace formula) | **analytic chain DONE at the real place**: `ConnesSymbolChangeOfVariables.connes_symbol_changeOfVariables` is (29)=(31); `ConnesLocalTraceCore.connes_traceCore_tendsto` is (31)⟶(33); `connes_symbolIntegral_tendsto` chains them.  Remaining: the operator-theoretic step (23)(24) identifying `Trace (R_Λ U(h))` with the symbol integral — needs a trace-class Schwartz-kernel layer for an operator that is not Hilbert–Schmidt |
| B2 | §VII Lemma 1 | for `k = ℚ` the corpus already owns Lemma 1(a) as `FieldOneFiniteStageBruhatOrbit_summable` / `…BruhatPeriodization` (Connes–Marcolli Lemma 2.29).  Lemma 1(b) (Fourier unitary on `L²(X_S)`) still open |
| B3 | §VII Thm 4 | needs B1 + B2 + B4 |
| B4 | §VII Lemma 2 | (43) done (A5); (45) scaling done (`ConnesLogShiftKernel.connes_logShift_substitution`); (44) finiteness of `c'_α` and the Besov estimate (42) open |
| B5 | App I Lemmas 1–5 | Lemma 4/5 (approximate units) partially reachable from `ConnesSobolevWeight`; Lemmas 1–3 need Tate/Iwasawa homogeneous distributions on `A` |
| B6 | App I / Thm III.1 | needs B5 + growth of `L(χ₀,½+it)`; the *conclusion* steps (27)(28)(29)(34) are already Lean-owned (A27, A3, A9) |
| B7 | App II Thm 6 | Lemma 3 done (`ConnesCharacterRescaling.connes_logDistribution_character_rescale`); (54) done at both archimedean places and non-archimedean (`ConnesGaussianLogMoment`, `ConnesNonArchPrincipalValue`); the global sum needs Weil's explicit formula, which the paper *quotes* |
| B8 | §VIII Lemma 1, Cor 2, Thm 5, Lemma 3 | window count (9)/(12)/(13) done (`ConnesFunctionFieldWindow`); Lemma 3's model computation done (A26); the rest needs B3 + B6 |
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
