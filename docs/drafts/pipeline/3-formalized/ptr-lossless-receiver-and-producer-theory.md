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

## No-go closure
- **Exact killing mechanism:** every producer statement that implies RH is equivalent to "ξ has no zero with Re ρ > ½ + h for every h > 0"; the photonic structure adds no leverage on deep zeros (energy/flux identities = Littlewood/Carleman, phase monotonicity = Hadamard sign). The exact defect↔deep-zero transport fails in general: defects can hide (clusters within ~k/log T of the line) and escape to infinity (no compactness for the cosine family).
- **Strongest positive survivor:** the producer theory above (unconditional producers, finite polynomial defects on the open heat–cosine quadrant, defect disks, power-sparse counts, critical-scale a.e. losslessness, exceptional-point confinement).
- **New insight:** Ξ is the critical medium of the heat flow (finite defects for t > 0, infinitely many for t < 0); PTR's quantitative frontier is the off-line first-moment constant (lossless proportion ≥ 1 − 2μ, μ = 67/1000), i.e. the corpus's mollifier common terminus.
- **Status:** all Lean, standard axioms. Correction 2026-10-10: fixed-depth height-measure statements restated over unions of depths (single-depth sets are countable).

## Log
- 2026-10-09 — created (loop rows 1–7, receiver reduction)
- 2026-10-10 — producer theory rows 8–24; moved to 3-formalized
- 2026-10-10 — row 28: exceptional-point criterion (RH ⇔ no collisions of the producer's real resonances)
