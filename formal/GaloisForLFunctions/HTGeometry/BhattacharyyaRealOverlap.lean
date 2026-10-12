import GaloisForLFunctions.HTGeometry.HellingerAffinityFactorization
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Measure.Decomposition.IntegralRNDeriv

/-! Real square-root likelihood overlap and decay of varying independent products. -/

noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal

namespace GaloisForLFunctions.HTGeometry

theorem integrable_sqrt_rnDeriv {α : Type*} [MeasurableSpace α] (P Q : Measure α)
    [IsFiniteMeasure P] [IsFiniteMeasure Q] :
    Integrable (fun x => Real.sqrt ((Q.rnDeriv P x).toReal)) P := by
  have hr : Integrable (fun x => (Q.rnDeriv P x).toReal) P :=
    Measure.integrable_toReal_rnDeriv
  apply ((integrable_const (1 : ℝ)).add hr).mono'
    (Real.continuous_sqrt.comp_aestronglyMeasurable hr.aestronglyMeasurable)
  filter_upwards [] with x
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  change Real.sqrt ((Q.rnDeriv P x).toReal) ≤ 1 + (Q.rnDeriv P x).toReal
  have hz : 0 ≤ (Q.rnDeriv P x).toReal := ENNReal.toReal_nonneg
  nlinarith [Real.sq_sqrt hz, sq_nonneg (Real.sqrt ((Q.rnDeriv P x).toReal) - 1)]

theorem bhattacharyya_eq_ofReal_integral_sqrt_rnDeriv
    {α : Type*} [MeasurableSpace α] (P Q : Measure α)
    [IsFiniteMeasure P] [IsFiniteMeasure Q] :
    bhattacharyya P Q = ENNReal.ofReal (∫ x, Real.sqrt ((Q.rnDeriv P x).toReal) ∂P) := by
  let lam : Measure α := P + Q
  have hP : P ≪ lam := Measure.absolutelyContinuous_of_le (Measure.le_add_right le_rfl)
  have hQ : Q ≪ lam := Measure.absolutelyContinuous_of_le (Measure.le_add_left le_rfl)
  have hmul : (fun x => (P.rnDeriv lam x * Q.rnDeriv lam x) ^ (1 / 2 : ℝ))
      =ᵐ[lam] fun x => (Q.rnDeriv lam x / P.rnDeriv lam x) ^ (1 / 2 : ℝ) * P.rnDeriv lam x := by
    filter_upwards [Measure.rnDeriv_lt_top P lam] with x hx
    by_cases hz : P.rnDeriv lam x = 0
    · simp only [hz, zero_mul, mul_zero, ENNReal.zero_rpow_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    · simpa only [one_mul, ENNReal.div_mul_cancel hz hx.ne] using
        rpow_half_mul_sq 1 (Q.rnDeriv lam x / P.rnDeriv lam x) (P.rnDeriv lam x)
  rw [ofReal_integral_eq_lintegral_ofReal (integrable_sqrt_rnDeriv P Q)
      (Filter.Eventually.of_forall (fun x => Real.sqrt_nonneg _))]
  calc
    _ = ∫⁻ x, (Q.rnDeriv lam x / P.rnDeriv lam x) ^ (1 / 2 : ℝ) * P.rnDeriv lam x ∂lam :=
      lintegral_congr_ae hmul
    _ = ∫⁻ x, (Q.rnDeriv lam x / P.rnDeriv lam x) ^ (1 / 2 : ℝ) ∂P :=
      lintegral_rnDeriv_mul' hP (by fun_prop)
    _ = ∫⁻ x, Q.rnDeriv P x ^ (1 / 2 : ℝ) ∂P := by
      apply lintegral_congr_ae
      filter_upwards [Measure.rnDeriv_eq_div hQ hP] with x hx
      rw [hx]
    _ = _ := by
      apply lintegral_congr_ae
      filter_upwards [Measure.rnDeriv_lt_top Q P] with x hfin
      rw [Real.sqrt_eq_rpow,
        ← ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg (by norm_num),
        ENNReal.ofReal_toReal hfin.ne]

theorem tendsto_varying_ennreal_pow_zero {f : ℕ → ℝ≥0∞} {c : ℝ≥0∞}
    (hf : Tendsto f atTop (𝓝 c)) (hc : c < 1) :
    Tendsto (fun r => f r ^ r) atTop (𝓝 0) := by
  obtain ⟨b, hcb, hb⟩ := exists_between hc
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hb)
    (Filter.Eventually.of_forall (fun r => (zero_le : 0 ≤ f r ^ r)))
  filter_upwards [hf.eventually (gt_mem_nhds hcb)] with r hr
  exact pow_le_pow_left' hr.le r

end GaloisForLFunctions.HTGeometry
