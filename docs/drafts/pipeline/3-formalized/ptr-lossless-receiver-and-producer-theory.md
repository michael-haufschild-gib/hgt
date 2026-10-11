# PTR: lossless receiver and producer theory

- **ID:** ptr-lossless-producer
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** route PTR (frontier map, "Physical realization"); loop log `1-in-progress/ptr-goal-loop-2026-10-09.md` rows 1–24
- **Statement:** The PTR receiver (lossless temporal Maxwell stacks, multiplicative port) is RH-complete; its producers are the even real-rooted order-one functions; the arithmetic producers `cos(hD)Ξ` (h ≥ ½) and `H_t` (t > Λ, Λ < 1/8) are unconditional; RH ⇔ the producer exists for every h > 0 (every t > 0); defects are confined, counted and power-sparse.

## Goal
Discharge the PTR "variable-coefficient Maxwell transmission law" need on the receiver side and locate exactly where the divisor information must enter (the producer).

## Gates
- [x] 0 → 1  in-progress
- [x] 1 → 2  fully-proven
- [x] 2 → 3  formalized: all theorems below, leaf builds green, `#print axioms` = [propext, Classical.choice, Quot.sound]
- [ ] 3 → 4  publication-ready (not pursued: no stage 4, only the RH proof)

## Lean theorems (all in `formal/GaloisForLFunctions/RHTower/`)
Receiver:
- `riemannHypothesis_iff_XiC_limit_losslessProductPort` (PhotonicLosslessProductPortRH) — RH ⇔ Ξ is a locally uniform limit of lossless product ports.
- `ptrLosslessProductPort_slab_le_of_tendsto_XiC` (…ThinSlab), `exists_integerDensity_law`, `not_tendsto_XiC_of_halfRate_integerClock_losslessStacks` (PhotonicIntegerClockHalfRate), `exists_ptrLosslessProductPort_density_law`, `exists_ptrLosslessProductPort_longSlab_scarcity` (…DensityLaw).
- `ptrLosslessStackEntry_scale`, `ptrPrimePairEntry_eq_zero_iff` (PhotonicLosslessImpedanceScaleInvisibility) — impedance scale is receiver-invisible; the PTR prime pair is prime-blind and its phase datum cos = 3/5 is a resonance.

Producer:
- `isPtrProductPortLimit_of_even_realZeros`, `isPtrProductPortLimit_const_mul_canonicalProduct`, `isPtrProductPortLimit_of_tendstoLocallyUniformly`, `isPtrProductPortLimit_cosineShift` (h ≥ ½), `riemannHypothesis_iff_forall_isPtrProductPortLimit_cosineShift` (PhotonicLosslessProductPortCosineShiftProducer).
- `exists_riemannHeat_eq_defect_mul_ptr`, `riemannHypothesis_iff_forall_isPtrProductPortLimit_riemannHeat`, `riemannHeat_defect_transition` (PhotonicLosslessHeatFlowFiniteDefect).
- `exists_isPtrProductPortLimit_riemannHeat_below_eighth`, `riemannHypothesis_iff_forall_isPtrProductPortLimit_heatCosine` (PhotonicLosslessHeatCosinePhaseDiagram); `exists_heatCosine_eq_defect_mul_ptr` (PhotonicLosslessHeatCosineFiniteDefect).

Defects of `cos(hD)Ξ`:
- `DeBruijn.cosineShift_nonreal_zero_mem_defectDisk`, `cosineShift_zero_real_of_abs_re_le` (XiCosineShiftDefectDisks); `cosineShift_zero_real_of_vinogradovKorobov` (XiCosineShiftVinogradovKorobovWindow).
- `exists_card_cosineShift_nonrealZeros_le` (XiCosineShiftNonrealZeroCount; Ingham–Huxley power saving, counted with multiplicity).
- `exists_criticalScale_cosineShift_lossless_ae` (XiCosineShiftCriticalScaleProducer), `eventually_volume_cosineShift_anyDepth_nonrealHeight_le` (XiCosineShiftUniformLosslessHeights; ≥ 86.6% of heights lossless at every depth).
- `deriv_cosineShiftXi_ne_zero_of_local`, `deriv_cosineShiftXi_ne_zero_of_rh` (XiCosineShiftExceptionalPointConfinement).
- `cosineShift_quartic_zeros_real`, `cosineShift_quartic_exists_nonreal` (PhotonicCosineProducerNonMonotone) — single-depth losslessness is no depth bound.
- `riemannHypothesis_iff_cosProducer_no_exceptionalPoint` (XiCosineShiftExceptionalPointCriterion) — RH ⇔ the cosine producer has no multiple real zero for 0 < h < ½ (no exceptional points).
- `riemannHypothesis_iff_re_xi_eq_zero_imp_im_deriv_xi_ne_zero`, `exists_offline_zero_disc_of_curve_intersection` (XiRealPartDerivativeCurvesCriterion); `curves_disjoint_of_vinogradovKorobov` (XiCurveIntersectionVinogradovKorobov) — RH ⇔ {Re ξ=0} ∩ {Im ξ'=0} = ∅ in ½<Re s<1; intersections lie in off-line discs; none in the VK region.
- `exists_card_cosineShift_degenerateZeros_le` (XiCosineShiftDegenerateZeroCount) — non-real and multiple real zeros are power-sparse at every depth.
- `twoPort_zeroCount_le` (XiTwoPortProducerTransport, with …Edges, …LinePeel) — sharp transport: in windows between shadow-free heights, #zeros of ξ(s)+ξ(s−2h) right of Re s=½+h ≤ #zeros of ξ with Re s ≥ ½+h, +1 (error O(1), no log T).
- `exists_exceptionalPoint_of_shadowFree_window` (XiCosineShiftExceptionalPointWindow) — every shadow-free window containing an off-line zero carries an exceptional point.
- `windowDefectCount_zero_le_exceptional_mass` (XiCosineShiftExceptionalPointIndex) — exceptional-point index law: total EP multiplicity in a shadow-free window ≥ #non-real zeros of Ξ there (or infinitely many EP depths).
- `offline_mass_below_onset_le_one` (XiCosineShiftExceptionalOnset) — onset law: below the first exceptional depth of a window, at most one off-line zero (with multiplicity) is shallower; `windowDefectCount_le_transport` — transport law in cos(hD)Ξ language.
- `two_mul_shallow_mass_le_exceptional_mass` (XiCosineShiftExceptionalDepthIndex) — depth-resolved index: EP mass up to depth h ≥ 2#{off-line zeros shallower than h} − 2.
- `eventually_windowDefectCount_le_transport` (XiCosineShiftDefectTransportAllHeights) — for all large T: defects in [T,2T] ≤ 2#{Re ρ ≥ ½+h, T/2 ≤ Im ρ ≤ 3T} + 2 (frontier-map W1C [P] item, sharp); `volume_shadowBad_le` — shadow union measure ≤ 2·offLineMoment.
- `windowRH_iff_no_exceptionalPoint`, `windowRH_iff_no_defect` (XiCosineShiftWindowRHCriterion) — RH localises to shadow-free windows.
- `not_tendsto_ptrEulerPartialProduct` (PhotonicPrimePortHorizon) — prime-port horizon: partial Euler products converge to no nonzero limit on ½<Re s<1; the PTR prime port reaches only grades h>½, so the strip handoff must be nonlocal.
- `eventually_not_xiExceptional`, `windowDefectCount_zero_le_exceptional_mass_finite` (XiExceptionalPointDiscrete) — exceptional points are isolated; the EP index law holds with finitely many exceptional depths per window.
- `fold_law` (XiExceptionalPointFoldLaw) — a nondegenerate exceptional point is a square-root fold; the sign of Re ξ'·Re ξ'' decides whether defects close or open as h grows.
- `cosProducer_exists_nonreal_zero_of_logDeriv_bound` (XiCosineShiftDefectPersistence) — first lower bound: an off-line zero keeps its defect pair until depth b(1−O(Mb)).
- `XiC_eq_integral_sech_mul_re_xi_one` (XiCosineShiftSechHandoff) — exact handoff: Ξ is the sech (Pólya-frequency) smoothing of the horizon producer Re ξ(1+i·); RH ⇔ the port loses no real zero.
- `cosProducer_eq_integral_poissonPort_mul_re_xi_one` (XiCosineShiftPoissonFlow) — every producer A_h, 0 ≤ h < ½, is a positive unit-mass Poisson average of the horizon producer Re ξ(1+i·).
- `riemannHypothesis_iff_strict_laguerre_strip` (XiCosineShiftStrictLaguerre) — RH ⇔ (Im ξ')² + Re ξ·Re ξ'' > 0 on ½ < Re s < 1; every producer has a real zero.
- `laguerre_nonneg_of_trace`, `eventually_volume_laguerreFail_le` (XiCosineShiftLaguerreTraces) — Q ≥ 0 off doubled traces of deep zeros; failure heights have measure ≤ 0.268(V+1) (Q ≥ 0 at every depth on ≥ 73% of heights).
- `exists_volume_laguerreFail_criticalScale_le` (XiCosineShiftLaguerreCriticalScale) — at depths ≥ c/log U the criterion fails on an O(1/c) proportion of heights; exponential form `exists_volume_laguerreFail_criticalScale_le_exp` (O(e^{−c/28})) via `exists_offLineTailMoment_window_le_exp` (ZetaCriticalScaleTailMomentExponential); `exists_laguerre_nonneg_vinogradovKorobov` — Q ≥ 0 throughout the VK region.
- `ptrEulerPartialProduct_converges_iff` (PhotonicPrimePortHorizonSharp) — sharp horizon: Euler products converge to a nonzero limit iff Re s ≥ 1 (Im s ≠ 0, Re s > ½).
- `exists_criticalScale_windowDefectCount_le` (XiCosineShiftCriticalScaleDefectCount) — at depth 2a/log U the producer's defects in [U/3,2U/5] are O(U log U·rate(a)/a): lossless on all but O(1/a²) of the spectrum (Selberg near-line density + sharp transport).

## No-go closure
- **Exact killing mechanism:** every producer statement that implies RH is equivalent to "ξ has no zero with Re ρ > ½ + h for every h > 0"; the photonic structure adds no leverage on deep zeros (energy/flux identities = Littlewood/Carleman, phase monotonicity = Hadamard sign). The exact defect↔deep-zero transport fails in general: defects can hide (clusters within ~k/log T of the line) and escape to infinity (no compactness for the cosine family).
- **Strongest positive survivor:** the producer theory above (unconditional producers, finite polynomial defects on the open heat–cosine quadrant, defect disks, power-sparse counts, critical-scale a.e. losslessness, exceptional-point confinement).
- **New insight:** Ξ is the critical medium of the heat flow (finite defects for t > 0, infinitely many for t < 0); PTR's quantitative frontier is the off-line first-moment constant (lossless proportion ≥ 1 − 2μ, μ = 67/1000), i.e. the corpus's mollifier common terminus.
- **Status:** all Lean, standard axioms. Correction 2026-10-10: fixed-depth height-measure statements restated over unions of depths (single-depth sets are countable).

## Log
- 2026-10-09 — created (loop rows 1–7, receiver reduction)
- 2026-10-10 — producer theory rows 8–24; moved to 3-formalized
- 2026-10-10 — row 28: exceptional-point criterion (RH ⇔ no collisions of the producer's real resonances)
- 2026-10-10 — rows 29–35: curve criterion, VK disjointness, degenerate sparsity, sharp O(1) transport law, windowed EP law and EP index law
- 2026-10-10 — rows 36–39: onset law, depth-resolved index, all-heights sharp transport, window-local RH criterion. All producer laws are class-generic (they hold for any even real order-one function with strip zeros — quartic countermodel); arithmetic enters only through Selberg/Ingham–Huxley/VK inputs.

## Gapless realization law (2026-10-11, rows 60–62)
- `RHTower.not_rigidOrdinates` (anti-crystal law): the ordered zeta ordinates are never `h`-rigid at a fixed scale. Pair correlation (`tendsto_montgomeryForm_div_leadingOrder`) forbids it.
- `RHTower.not_exists_lowerPolyaClass_realization`: no Hermite–Biehler realization `Ξ = Re G(·+ih)` with `G` lower Pólya, for any `h > 0`. Every lossless PTR port must be gapless (critical).
- Card: 3-formalized/ptr-anti-crystal-gapless-realization.md.

## Terminal reduction of route PTR (2026-10-11, rows 43–54)

Everything below is Lean-certified with standard axioms only.

- **Source.** The horizon producer A_½(v) = Re ξ(1+iv) is lossless (Laguerre–Pólya, simple real zeros), unconditionally. On Re s = 1 the Euler product converges (`ptrEulerPartialProduct_converges_iff`).
- **Handoff.** For 0 ≤ h < ½, A_h = P_{h,½} ∗ A_½ with a positive, unit-mass Poisson kernel (`cosProducer_eq_integral_poissonPort_mul_re_xi_one`). Ξ = sech(π·) ∗ A_½ is the Pólya-frequency endpoint (`XiC_eq_integral_sech_mul_re_xi_one`). This meets the frontier-map "Needs: exact arithmetic source-to-continuum handoff retaining the Ξ divisor".
- **Open core.** RH ⇔ the flow trades no real zero for a conjugate pair ⇔ no exceptional point (row 28). Equivalently, ⇔ Q(s) = (Im ξ')² + Re ξ·Re ξ'' > 0 on ½ < Re s < 1 (`riemannHypothesis_iff_strict_laguerre_strip`).
- **Unconditional side.**
  - Q > 0 on Re s ≥ 1.
  - Q ≥ 0 off the doubled traces of zeros deeper than h.
  - Q ≥ 0 at every depth on ≥ 73% of heights (`eventually_volume_laguerreFail_le`).
  - Defects are confined to defect disks (upper bound) and persist to depth b(1 − O(Mb)) (lower bound).
  - Exceptional points are isolated folds.
  - Exact Littlewood transport: defect height moment − deep moment = phase deficit + edges.
- **Verdict.** PTR is a complete reformulation. The arithmetic needed is exactly "no deep zeros". PTR's producer, port and receiver add no leverage there: every positivity mechanism found is line-rigid (row 47) or limited by constants (row 51). The quantitative statements scale with the off-line moment Σ(β−½)⁺ ≤ 0.067T. Improving that constant is the common-terminus problem (mollified second moment).
