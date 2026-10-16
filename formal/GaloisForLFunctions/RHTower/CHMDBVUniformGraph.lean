import GaloisForLFunctions.RHTower.ThetaBVArithmeticAdmission
import GaloisForLFunctions.HTGeometry.BoundedVariationUniformJump

/-! # BV control of the complete arithmetic graph norm

The uniform error enters both terms of the bound. Thus bounded variation,
without convergence of derivatives or variation, suffices to upgrade a
uniformly converging compact family to the original complete jump graph.
-/

noncomputable section
open MeasureTheory Set Filter Topology

namespace RHTower.CHMDDoobGraph
open GaloisForLFunctions.HTGeometry CHMDClosedJump

theorem stationaryEnergy_bv_le_of_bound {v : ℝ → ℝ}
    (hv : BoundedVariationOn v univ) (hc : HasCompactSupport v)
    {M : ℝ} (hM : 0 ≤ M) (hb : ∀ x, |v x| ≤ M) :
    stationaryEnergy v ≤ 4 * M * (eVariationOn v univ).toReal *
      ∫ t in Ioi (0 : ℝ), t * archLevyDensity t := by
  have hm := measurable_of_boundedVariation_univ hv
  have hi := integrable_stationaryJump hm hc
    (bounded_compact_memLp_volume hm hc hM hb) (bv_memLp_difference hv)
  rw [stationaryEnergy_eq_iterated hi, ← integral_const_mul]
  apply integral_mono_ae (integrable_stationary_outer hi)
    (integrable_archLevy_firstMoment.const_mul _)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have h := mul_le_mul_of_nonneg_left
    (boundedVariation_translation_sq_le_of_bound hv hM hb ht.le)
    (archLevyDensity_pos ht).le
  nlinarith only [h]

theorem bvLift_norm_sq_le_of_bound {v : ℝ → ℝ}
    (hv : BoundedVariationOn v univ) (hc : HasCompactSupport v)
    {M C : ℝ} (hM : 0 ≤ M) (hb : ∀ x, |v x| ≤ M)
    (hC : 0 ≤ C) (hθ : ∀ x, riemannKernelReal x ≤ C) :
    ‖bvLift v hv‖ ^ 2 ≤
      (massMeasure.real univ + 4 * (Measure.sum primeMeasure).real univ) * M ^ 2 +
        (4 * C ^ 2 * ∫ t in Ioi (0 : ℝ), t * archLevyDensity t) *
          M * (eVariationOn v univ).toReal := by
  have hm := measurable_of_boundedVariation_univ hv
  have hvi := integrable_stationaryJump hm hc
    (bounded_compact_memLp_volume hm hc hM hb) (bv_memLp_difference hv)
  have hmass : (∫ x, v x ^ 2 ∂massMeasure) ≤
      massMeasure.real univ * M ^ 2 := by
    have h := integral_mono (bv_memLp_mass hv).integrable_sq
      (integrable_const (M ^ 2) : Integrable (fun _ : ℝ => M ^ 2) massMeasure)
      (fun x => by simpa only [sq_abs] using
        (sq_le_sq₀ (abs_nonneg _) hM).mpr (hb x))
    simpa only [integral_const, smul_eq_mul] using h
  have harch : (∫ e, difference v e ^ 2 ∂archMeasure) ≤
      C ^ 2 * stationaryEnergy v := by
    rw [archMeasure, integral_weighted archBase measurable_archWeight archWeight_nonneg_ae,
      stationaryEnergy, ← integral_const_mul]
    apply integral_mono_ae (bv_integrable_arch_weighted_sq hv) (hvi.const_mul _)
    have ht : ∀ᵐ e ∂archBase, e.1 ∈ Ioi (0 : ℝ) :=
      Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem measurableSet_Ioi)
    filter_upwards [ht] with e he
    have hp := mul_le_mul (hθ e.2) (hθ (e.2 + e.1)) (riemannKernelReal_pos _).le hC
    have hmul := mul_le_mul_of_nonneg_right hp
      (mul_nonneg (archLevyDensity_pos he).le (sq_nonneg (difference v e)))
    dsimp only [archWeight, stationaryJump]
    nlinarith only [hmul]
  have hprime : (∫ e, difference v e ^ 2 ∂Measure.sum primeMeasure) ≤
      (Measure.sum primeMeasure).real univ * (4 * M ^ 2) := by
    have h := integral_mono (bv_memLp_prime_difference hv).integrable_sq
      (integrable_const (4 * M ^ 2) :
        Integrable (fun _ : ℝ × ℝ => 4 * M ^ 2) (Measure.sum primeMeasure))
      (fun e => by
        have habs : |difference v e| ≤ 2 * M :=
          (abs_sub _ _).trans (by linarith [hb (left e), hb (right e)])
        simpa only [sq_abs, mul_pow, show (2 : ℝ) ^ 2 = 4 by norm_num] using
          (sq_le_sq₀ (abs_nonneg _) (by positivity)).mpr habs)
    simpa only [integral_const, smul_eq_mul] using h
  have hs := mul_le_mul_of_nonneg_left (stationaryEnergy_bv_le_of_bound hv hc hM hb)
    (sq_nonneg C)
  have ha : Integrable (fun e => difference v e ^ 2) archMeasure := by
    rw [archMeasure, integrable_weighted_iff archBase measurable_archWeight archWeight_nonneg_ae]
    exact bv_integrable_arch_weighted_sq hv
  change ‖(bvLift v hv).val‖ ^ 2 ≤ _
  rw [WithLp.prod_norm_sq_eq_of_L2]
  change ‖(bv_memLp_mass hv).toLp v‖ ^ 2 +
    ‖(bv_memLp_difference hv).toLp (difference v)‖ ^ 2 ≤ _
  rw [norm_toLp_sq, norm_toLp_sq, edgeMeasure,
    integral_add_measure ha (bv_memLp_prime_difference hv).integrable_sq]
  nlinarith only [hmass, harch, hprime, hs]

end RHTower.CHMDDoobGraph
