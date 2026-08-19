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
- 2026-08-19 — **C3 CLOSED in Lean.** New module
  `formal/GaloisForLFunctions/HTGeometry/GammaFactorialFockPolarization.lean`, wired into the
  HTGeometry umbrella, axiom-clean (only `propext`, `Classical.choice`, `Quot.sound`).
  Contents: `factorialForm_shiftOp_left` (exact adjoint pair), `factorialForm_createOp_left`,
  `weightForm_forced_recurrence` + `weightForm_eq_div_factorial` (uniqueness of the diagonal
  factorial weights), `commutator_eq` / `one_sub_commutator_eq` (`[D,A] = I − N·P_top`),
  `factorialForm_topProj_self`, `factorialForm_boundaryCharge_eq`,
  `factorialForm_boundaryCharge_re_nonneg` (positive top-boundary charge with exact value),
  `shiftOp_iterate_eq_zero`, `taylorTranslate_eq_exp_series`, `taylorTranslate_coordVec_apply`
  (entries `1_{j≤k}/(k−j)!`), `factorialForm_taylorTranslate_left` (`E* = exp A`),
  `factorialForm_coordMulOp_left` (`Z(z)* = conj z + D`), `factorialForm_coordOne_self` +
  `factorialForm_taylorTranslate_coordOne_self` (passivity no-go `2 > 1`),
  `greenBoundaryExcess` + `greenBoundaryExcess_pos` (exact positive boundary excess).
- 2026-08-19 — **C2 CLOSED in Lean.** New module
  `formal/GaloisForLFunctions/RHTower/SoninSemilocalDampedCovariancePositivity.lean`, wired into the
  RHTower umbrella, axiom-clean. Contents: `charFun_gammaCyclicMeasure`,
  `positiveDefiniteOnReal_semilocalArchimedeanCharacteristic`,
  `semilocalArchimedeanDampedCovarianceKernel_posSemidef` (the finite-matrix PSD gate the card left
  open), `exp_neg_le_semilocalArchimedeanCharacteristic_two_mul` (lower half of the two-sided
  exponential diagonal decay), `semilocalArchimedeanCharacteristic_two_mul_log_le`,
  `semilocalArchimedeanDampedCovariance_gram_strict_superadditive` (exact additivity obstruction).
  Reused the corpus's `HTGeometry.gammaCyclicMeasure` + `positiveDefiniteOnReal_charFun`; no new
  Fourier/Gamma-integral work was needed.
- 2026-08-19 — **C1 stage A closed in Lean.** New module
  `formal/GaloisForLFunctions/RHTower/StieltjesGammaAffineFirstOrder.lean`, wired, axiom-clean.
  `sum_padicValNat_div_eq_ladder` (prime-power ladder identity),
  `abs_harmonic_sub_log_div_le` (floor-harmonic vs exact-quotient log),
  `tsum_modelTerm` (closed form of the two-lane model ladder),
  `abs_tsum_ladderSubModel_le` (explicit `O((log N)/N)` comparison error),
  `tendsto_stieltjesFirstOrderCutoff` (**the exact regularized limit
  `A_{1,p} = γ/(p−1) − (log p)·p/(p−1)²`**), `firstOrderStieltjes_eq_rat_combination`
  (explicit ℚ-coefficients).
  REMAINING for C1: the general finite-support `A_β` statement. Plan:
  (i) a reusable *regularized divisor-harmonic limit* device with hypotheses
      `Summable (fun d => |a d|(1 + log d)/d)` and `(∑_{d ≤ N}|a d|)/N → 0`;
  (ii) single prime, arbitrary order `β`, via `a_{p^i} = i^β − (i−1)^β`;
  (iii) multi-prime via Dirichlet-convolution of coprime-supported ladders;
  (iv) rationality of `R_β(p) = ∑_i i^β p^{-i}` from `(p−1)R_β = 1 + ∑_{m<β} C(β,m) R_m`.
- 2026-08-19 — **C4 CLOSED in Lean; C2, C3, C4 PROMOTED to stage 3.**
  New modules `formal/GaloisForLFunctions/RHTower/PrimeLogZetaAbelPole.lean` and
  `formal/GaloisForLFunctions/RHTower/GammaMeixnerAbelCoronaProbe.lean`, wired, axiom-clean.
  The Abelian pole `δ·∑_p (log p)p^{-1-δ} → 1` was proved **without PNT**, by Abel summation
  against Mertens' first theorem plus `∫_1^∞ t^{-δ-1} log t dt = 1/δ²`.
  Reusable by-products: `weightedDirichlet_eq_abel_integral`,
  `mul_tsum_weightedDirichlet_le`, `summable_and_mul_tsum_weightedDirichlet_le`,
  `integral_rpow_mul_log_Ioi_one`.
  Cards moved to `docs/drafts/pipeline/3-formalized/not_new_scientific_knowledge/gamma/`:
  `gamma-factorial-fock-polarization-boundary-charge`,
  `gamma-damped-stationary-prime-log-covariance-law`,
  `gamma-meixner-abel-mertens-corona-probe`.

## Remaining work (5 cards)

| # | Card | What is still needed |
|---|---|---|
| C1 | `gamma-affine-stieltjes-log-independence` | (i) single prime, arbitrary order — **DONE** (`StieltjesGammaAffineSinglePrime.lean`); (iii) rationality — **DONE** (`GeometricMomentRational.lean`); remaining: (ii) multi-prime, via the coprime-support divisor-sum product `∑_{d∣k}(a⋆b)_d = (∑_{d∣k}a_d)(∑_{d∣k}b_d)` and the corresponding product formulas for `coeffDensity`/`coeffLogMass` |
| C5 | `gamma-module-construction` | rank-one `(σ_∞,∂_s)` module packaging; **Lerch** `ζ_H'(0,a) = log Γ(a) − ½log(2π)` (NOT in mathlib — must be built); the completed object `M_Λ` |
| C6 | `gamma-tail-law-shifted-square-tests` | unit-window Riemann–von Mangoldt zero count `N(T+1)−N(T)=O(log T)` and the dyadic tail law `O(G^{1−2r−4j} log G)` |
| C7 | `multiple-elliptic-gamma-generic-spectrum` | exact translation spectrum `= ℤ` at order ≥ 2; depends on the order-one exact spectrum |
| C8 | `multiple-gamma-cyclotomic-deletion-multiplicity` | deletion ideal `D=(x₁,x₀x₂)` group-algebra factorization; `x₀²F` HT on the dependent frame (same order-one parent) |

- 2026-08-19 — **C1 single-prime arbitrary-order closed in Lean.** New modules, wired, axiom-clean:
  * `formal/GaloisForLFunctions/RHTower/GeometricMomentRational.lean` —
    `geomMoment r m = ∑_{i≥0} i^m r^i`, the binomial shift recurrence
    `(1−r)R_m = r ∑_{t<m} C(m,t) R_t` (`geomMoment_recurrence`), and
    `exists_rat_geomMoment` : `R_m(q) ∈ ℚ` for every rational `q` with `|q| < 1`.
  * `formal/GaloisForLFunctions/RHTower/StieltjesGammaAffineSinglePrime.lean` —
    the order-`β` ladder `c_i = i^β − (i−1)^β`, its telescoping `sum_ladderCoeff`,
    the divisor identity `sum_divisors_primePowerLadder` (`∑_{d∣k} a_d = v_p(k)^β`),
    the two device hypotheses (`summable_logWeight_primePowerLadder`,
    `tendsto_primePowerLadder_mass_div`, the latter through the sharp ladder-mass identity
    `sum_Icc_primePowerLadder` and `(log N)^β/N → 0`), the lane identities
    `stieltjesSinglePrimeDensity_eq` = `(1−1/p)R_β`,
    `stieltjesSinglePrimeLogMass_eq` = `R_{β+1} − (1/p)(R_{β+1}+R_β)`,
    and the two capstones
    `tendsto_stieltjesSinglePrimeCutoff` (the exact regularized limit
    `A_{β,p} = γ·D_{β,p} − (log p)·L_{β,p}`) and
    `tendsto_stieltjesSinglePrimeCutoff_rat` (**with rational `D`, `L`**).
- 2026-08-19 — **C1 CLOSED and PROMOTED to stage 3.** Multi-prime case landed:
  `CoprimeDirichletDivisorProduct.lean` (coprime-support convolution: divisor-sum product,
  density product, log-mass Leibniz law, summability and mass-bound propagation) and
  `StieltjesGammaAffineMultiPrime.lean` (`multiLadder` by iterated convolution over a nodup list
  of primes, `sum_divisors_multiLadder`, and the capstone
  `tendsto_stieltjesMultiPrimeCutoff_rat` = the card's `A_β ∈ ℚ·γ ⊕ ⊕_p ℚ·log p`).
  **4 of 8 gamma cards are now at stage 3.**

## Remaining work (4 cards)

| # | Card | What is still needed |
|---|---|---|
| C5 | `gamma-module-construction` | rank-one `(σ_∞,∂_s)` module packaging; **Lerch** `ζ_H'(0,a) = log Γ(a) − ½log(2π)` (NOT in mathlib — must be built); the completed object `M_Λ` |
| C6 | `gamma-tail-law-shifted-square-tests` | a sum-over-Xi-zeros-with-multiplicity framework, then the dyadic tail law `O(G^{1−2r−4j} log G)` from the corpus's `exists_xiZeroCount_upper_bound` (`N(T) ≪ T log T`) |
| C7 | `multiple-elliptic-gamma-generic-spectrum` | exact translation spectrum `= ℤ` at order ≥ 2; the order-one parent card is already stage-3 formalized (`ellipticGammaExternalDefectFamily_differentialMatroid_eq_periodCosetPartitionMatroid_rationalBase`) |
| C8 | `multiple-gamma-cyclotomic-deletion-multiplicity` | deletion ideal `D=(x₁,x₀x₂)` group-algebra factorization; `x₀²F` HT on the dependent frame (same order-one parent) |

## C7 / C8 route (reconnaissance done 2026-08-19) — no new analysis needed

The corpus already owns every analytic input; C7 reduces to hierarchy bookkeeping plus one
ℚ-linear-algebra intersection.  Exact anchors:

| Need | Corpus anchor |
|---|---|
| face coordinate `Ψ_J` of the all-order hierarchy | `GaloisForLFunctions.multipleEllipticGammaLogDerivFaceMero` (`HTGeometry/MultipleEllipticGammaFaceHierarchy.lean`) |
| coface equation `Δ_{τ_q} Ψ_J = Ψ_{insert q J}` | `multipleEllipticGammaLogDerivFaceMero_addTranslation_sub` |
| `Δ_n Ψ_J = 0` for `n ∈ ℤ` (1-periodicity) | `addTranslationMeroEquiv_intCast_multipleEllipticGammaLogDerivFaceMero`, `addTranslationMeroEquiv_one_multipleEllipticGammaLogDerivFaceMero` |
| order-one exact DA spectrum | `differentialAlgebraicOver_ellipticGammaExternalLogDerivDefectMero_iff_resonant` (`HTGeometry/EllipticGammaStructuralGeneratorSpectrum.lean`), with the `ℂ(z)` transport in `EllipticCompositumRationalBase` / `EllipticCompositumMatroidTransport` |
| DA stable under translation | `differentialAlgebraicOver_addTranslationMeroEquiv` (`HTGeometry/TranslationStableDifferentialAlgebraicity.lean`) |
| order-two face ≅ classical elliptic gamma | `multipleEllipticGammaLogDerivMero_fin_two` (`HTGeometry/MultipleEllipticGammaHypertranscendence.lean`) |
| transverse DA depth of the hierarchy | `multipleEllipticGammaTransverseDADepth_eq_card_sub_one` (`HTGeometry/MultipleGammaTransverseDepthValue.lean`) |

**C7 proof to formalize.**  `Spec_DA(Ψ_∅) = ℤ` for `r ≥ 2`:
* `⊇` from integer-translation invariance;
* `⊆`: if `Δ_h Ψ_∅` is DA then, translating by `τ_q` and using `Δ_{τ_q}Δ_h = Δ_h Δ_{τ_q}`,
  `Δ_h Ψ_{q}` is DA for every `q`; at `r = 2` the order-one exact spectrum gives
  `h ∈ ℤ + ∑_{k ≠ q} ℤ τ_k`, and intersecting over the three `q` under ℚ-independence of
  `1, τ_0, …, τ_r` gives `h ∈ ℤ`; higher orders by induction.

**C8 proof to formalize.**  On the dependent frame `(α, β, mα)`:
`x₁ F` DA and `x₀x₂ F` DA by descent to a rank-two / order-zero face;
`x₀² F = Δ_α Ψ_1(z; β, mα)` is HT because `α ∉ ℤ + ℤβ + ℤ(mα)` (a relation
`α = k + lβ + n·mα` contradicts ℚ-independence of `1, α, β` since `1 − nm ≠ 0` for `m ≥ 2`);
hence the cyclotomic factor `1 + g₀ + … + g₀^{m−1}` cannot be cancelled from the deletion ideal
`D = (x₁, x₀x₂) = (x₁, (g₀−1)²(1+g₀+…+g₀^{m−1}))`.

### C7 progress

Landed: `formal/GaloisForLFunctions/HTGeometry/MultipleEllipticGammaGenericSpectrum.lean`
(wired, axiom-clean) — `augmentedPeriods`, `MemDeletedPeriodGroup`, and
`exists_int_of_forall_memDeletedPeriodGroup`: under ℚ-independence of `1, τ_0, …, τ_r`, the
deleted-coordinate integer period groups intersect exactly in `ℤ`.  This is the arithmetic half of
the order-two collapse; it needs no analysis and is now unconditional.

Also landed in that module (all axiom-clean):
`meroTranslationDefect`, `meroTranslationDefect_comm`,
`differentialAlgebraicOver_meroTranslationDefect`,
`meroTranslationDefect_face` (the coface descent of a defect),
`meroTranslationDefect_addTranslation`, `differentialAlgebraicOver_addTranslation_iff`,
`linearIndependent_ellipticGammaSourcePeriods_of_augmented`,
`exists_int_of_da_defect_fin_two` (**the order-one bridge**: a DA translation defect of the
two-parameter multiple elliptic gamma forces the shift into the rank-three period group), and
**`exists_int_of_da_faceDefect_card_three`** — the order-two collapse: with three ℚ-independent
structural periods, `Δ_h Ψ` differentially algebraic over `ℂ(z)` forces `h ∈ ℤ`.

Still to write:

```text
meroTranslationDefect h x := addTranslationMeroEquiv h x - x
meroTranslationDefect_comm                    -- from GaloisForLFunctions.addTranslationMeroEquiv_add
differentialAlgebraicOver_meroTranslationDefect
      -- from differentialAlgebraicOver_addTranslationMeroEquiv + differentialAlgebraicOver_sub
meroTranslationDefect_face                    -- from multipleEllipticGammaLogDerivFaceMero_addTranslation_sub
orderOneBridge : two surviving parameters ⇒ resonance
      -- multipleEllipticGammaLogDerivMero_reindex → multipleEllipticGammaLogDerivMero_fin_two
      -- → ellipticGammaExternalLogDerivDefectMero (definitionally the defect)
      -- → differentialAlgebraicOver_compositum_of_ratFunc
      -- → differentialAlgebraicOver_ellipticGammaExternalLogDerivDefectMero_iff_resonant
general face version of the card-three collapse (same proof, face J instead of ∅)
capstone : Spec_DA(Ψ_J) = ℤ whenever at least three parameters survive
      -- strong induction on card {i // i ∉ J}; the m ≥ 4 step is one application of
      -- meroTranslationDefect_face + differentialAlgebraicOver_meroTranslationDefect
reverse inclusion ℤ ⊆ Spec_DA
      -- addTranslationMeroEquiv_intCast_multipleEllipticGammaLogDerivFaceMero gives Δ_m Ψ = 0

NOTE (defeq trap): `multipleEllipticGammaLogDerivFaceMero τ hτ ∅ = multipleEllipticGammaLogDerivMero τ hτ`
via `multipleEllipticGammaLogDerivMero_reindex` blows up `whnf` even at 1e6 heartbeats.  State
everything on faces (`… hτ ∅`) instead — that is the same object and avoids the reindex.
```

All of these live in the plain `GaloisForLFunctions` namespace (not `.HTGeometry`).
