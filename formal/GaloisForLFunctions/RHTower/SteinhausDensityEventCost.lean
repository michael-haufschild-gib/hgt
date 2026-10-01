import GaloisForLFunctions.HTGeometry.SquareIntegrableKernelOperator
import Mathlib.MeasureTheory.Measure.Real

open MeasureTheory
open scoped ENNReal

noncomputable section
namespace RHTower

/-- Squared event mass under an explicit density is bounded by original event mass times density energy. -/
theorem sq_withDensity_event_le_densityCost {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) {ρ : Ω → ℝ≥0∞} (hρ : Measurable ρ) {E : Set Ω} (hE : MeasurableSet E) :
    ((μ.withDensity ρ) E) ^ 2 ≤ μ E * ∫⁻ ω, ρ ω ^ 2 ∂μ := by
  have h := GaloisForLFunctions.HTGeometry.sq_lintegral_mul_le_mul
    (m := μ.restrict E) (a := fun _ => (1 : ℝ≥0∞)) (b := ρ)
    aemeasurable_const hρ.aemeasurable
  rw [withDensity_apply _ hE]
  calc
    _ ≤ μ E * ∫⁻ ω in E, ρ ω ^ 2 ∂μ := by
      simpa only [one_mul, one_pow, lintegral_const, Measure.restrict_apply_univ] using h
    _ ≤ _ := mul_le_mul' le_rfl (lintegral_mono' μ.restrict_le_self le_rfl)

/-- A concrete second-density-moment cost transfers a positive tilted event mass to the original law. -/
theorem measureReal_event_ge_sq_div_densityCost {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] {ρ : Ω → ℝ≥0∞} (hρ : Measurable ρ)
    {E : Set Ω} (hE : MeasurableSet E) {q C : ℝ} (hq : 0 ≤ q) (hC : 0 < C)
    (hmass : ENNReal.ofReal q ≤ (μ.withDensity ρ) E)
    (hcost : (∫⁻ ω, ρ ω ^ 2 ∂μ) ≤ ENNReal.ofReal C) :
    q ^ 2 / C ≤ μ.real E := by
  have h := (pow_le_pow_left' hmass 2).trans
    ((sq_withDensity_event_le_densityCost μ hρ hE).trans (mul_le_mul' le_rfl hcost))
  have hr := ENNReal.toReal_mono
    (ENNReal.mul_ne_top (measure_ne_top μ E) ENNReal.ofReal_ne_top) h
  simp only [ENNReal.toReal_pow, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal hq, ENNReal.toReal_ofReal hC.le] at hr
  exact (div_le_iff₀ hC).mpr hr

/-- Half the biased law's mass costs at most one quarter times the reciprocal exponential density energy. -/
theorem measureReal_event_ge_quarter_exp_neg_densityCost {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] {ρ : Ω → ℝ≥0∞} (hρ : Measurable ρ)
    {E : Set Ω} (hE : MeasurableSet E) (A : ℝ)
    (hmass : ENNReal.ofReal (1 / 2 : ℝ) ≤ (μ.withDensity ρ) E)
    (hcost : (∫⁻ ω, ρ ω ^ 2 ∂μ) ≤ ENNReal.ofReal (Real.exp A)) :
    (1 / 4 : ℝ) * Real.exp (-A) ≤ μ.real E := by
  have h := measureReal_event_ge_sq_div_densityCost μ hρ hE
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (Real.exp_pos A) hmass hcost
  have he : (1 / 2 : ℝ) ^ 2 / Real.exp A = (1 / 4 : ℝ) * Real.exp (-A) := by
    rw [Real.exp_neg]
    ring
  rwa [he] at h

end RHTower
