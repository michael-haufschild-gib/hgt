# Gamma folder — stage-3 formalization ledger

- **ID:** `gamma-folder-stage3-formalization-ledger`
- **Stage:** 1-in-progress (meta / sweep ledger)
- **Scope:** every card in `docs/drafts/pipeline/2-fully-proven/not_new_scientific_knowledge/gamma/`
- **Goal:** each card's `[PROVED]` content unconditionally Lean-certified, then promote to
  `3-formalized/not_new_scientific_knowledge/gamma/`.
- **Opened:** 2026-08-19

## Card inventory and Lean target

| # | Card | Lean state at open | Remaining target |
|---|---|---|---|
| C1 | `gamma-affine-stieltjes-log-independence` | `SeamNonSplitting`, `StieltjesLaneCutoffDivergence` own the divergence floor + seam class | the **banked** γ-affine structure of `A_β`: exact `A_{1,p}=γ/(p−1)−(log p)p/(p−1)²` and the general finite-support ℚ-span statement |
| C2 | `gamma-damped-stationary-prime-log-covariance-law` | `SoninSemilocalTwoPlaceAssociation` (kernel, entry positivity, diagonal, exp bound), `GammaDampedPrimeLogCauchyDomain` (packet domain) | finite-matrix **positive semidefiniteness** of `K_Γ` via the corpus Gamma cyclic spectral measure; the exponential two-sided diagonal bound `e^{-t} ≤ φ(2t) ≤ √2 e^{-t}`; strict cross-term/nonadditivity |
| C3 | `gamma-factorial-fock-polarization-boundary-charge` | NONE | full module: `D_N`,`A_N`, factorial metric, adjoint pair, uniqueness of the diagonal weight, `[D,A]=I−N·P_top`, positivity of `N·P_top`, `E_N=exp D_N` entries, `E_N^*=exp A_N`, `Z_N(z)^*`, passivity failure, Green boundary-excess law |
| C4 | `gamma-meixner-abel-mertens-corona-probe` | `WeightedEulerCoefficientSpaces` owns `M_log`/`M_0`/unit field | `w_θ` exact factorization, uniform dual bound, vanishing on `M_0`, unit limit `L_θ(1)→1`, singular (non-norm) boundary |
| C5 | `gamma-module-construction` | `ArchimedeanGamma` owns scalar recurrence + connection compat | rank-one `(σ_∞,∂_s)` module packaging; Lerch `Γ(a)·exp(−ζ_H'(0,a))=√(2π)`; completed object `M_Λ` diagonal |
| C6 | `gamma-tail-law-shifted-square-tests` | `XiZeroCountingFunction` exists | unit-window zero count `O(log T)` and the dyadic tail law `O(G^{1−2r−4j} log G)` |
| C7 | `multiple-elliptic-gamma-generic-spectrum` | `MultipleEllipticGammaHypertranscendence` + `MultipleEllipticGammaPeriodRankDichotomy` own source HT | exact translation spectrum `= ℤ` for order ≥ 2; hierarchy spectrum-descent inclusion |
| C8 | `multiple-gamma-cyclotomic-deletion-multiplicity` | none for this card | deletion ideal `D=(x₁, x₀x₂)` group-algebra factorization; `x₀²F` HT on the dependent frame |

## Reusable corpus assets located (do not rebuild)

- `HTGeometry.GammaCyclicSpectralMeasure` — nonneg density `gammaCyclicDensity`, probability measure
  `gammaCyclicMeasure`, characteristic function `integral_exp_gammaCyclicMeasure h = (cosh h)^{-1/2}`.
  This is the exact spectral input C2's PSD gate needed.
- `HTGeometry.CoshFourierInversion` — `coshHalf`, integrability, Fourier inversion.
- `HTGeometry.HarmonicLogWindow.abs_harmonic_sub_log_sub_eulerMascheroni_le` — `|H_n − log n − γ| ≤ 1/n`.
  This is the exact input C1's regularized-limit needs.
- `RHTower.WeightedEulerCoefficientSpaces` — `primeLogMass`, `marcinkiewiczLogQuotient`,
  `MemMarcinkiewiczLogLayer`, `MemVanishingTailLayer`, `MemCriticalSummableLayer`, unit-field membership.
- `RHTower.MertensPrimeWindowWeakConvergence`, `RHTower.MertensSecondPrimeRecipSum`,
  `RHTower.MertensThirdTheorem` — Mertens first/second/third.
- `RHTower.ArchimedeanGamma` — `gammaReal_shift_two`, `digamma_half_add_one`,
  `gammaRealLogConnection_shift_compat`.

## Progress log

- 2026-08-19 — ledger opened; corpus inventory above completed.
