import GaloisForLFunctions.RHTower.SteinhausAffineCircleMeasure

open MeasureTheory Complex
open scoped ENNReal ComplexConjugate

noncomputable section
namespace RHTower
open SteinhausModel

/-- Every circle character remains integrable under the concrete biased probability law. -/
theorem integrable_charFactor_affineCircle {m : ℂ} (hm : ‖m‖ ≤ 1 / 2) (k : ℤ) :
    Integrable (charFactor k) (steinhausAffineCircleMeasure m) := by
  letI := isProbabilityMeasure_steinhausAffineCircleMeasure hm
  exact (integrable_const (1 : ℝ)).mono'
    (continuous_charFactor k).aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => (norm_charFactor k x).le)

/-- Subtracting the prescribed mean centers the literal circle phase. -/
theorem integral_centered_phase_affineCircle {m : ℂ} (hm : ‖m‖ ≤ 1 / 2) :
    (∫ x, charFactor 1 x - m ∂steinhausAffineCircleMeasure m) = 0 := by
  letI := isProbabilityMeasure_steinhausAffineCircleMeasure hm
  rw [integral_sub (integrable_charFactor_affineCircle hm 1) (integrable_const m),
    integral_phase_steinhausAffineCircleMeasure hm]
  simp

/-- Prescribing a circle mean decreases the exact centered second moment by its squared norm. -/
theorem integral_norm_sq_centered_phase_affineCircle {m : ℂ} (hm : ‖m‖ ≤ 1 / 2) :
    (∫ x, ‖charFactor 1 x - m‖ ^ 2 ∂steinhausAffineCircleMeasure m) = 1 - ‖m‖ ^ 2 := by
  letI := isProbabilityMeasure_steinhausAffineCircleMeasure hm
  have hp := integrable_charFactor_affineCircle hm 1
  have hc : Integrable (fun x => conj (charFactor 1 x)) (steinhausAffineCircleMeasure m) := by
    have he : (fun x => conj (charFactor 1 x)) = charFactor (-1) :=
      funext (fun x => (charFactor_neg 1 x).symm)
    rw [he]
    exact integrable_charFactor_affineCircle hm (-1)
  have h1 : Integrable (fun x => (1 : ℂ) - m * conj (charFactor 1 x))
      (steinhausAffineCircleMeasure m) := (integrable_const 1).sub (hc.const_mul m)
  have h2 : Integrable (fun x => (1 : ℂ) - m * conj (charFactor 1 x) -
      conj m * charFactor 1 x) (steinhausAffineCircleMeasure m) :=
    h1.sub (hp.const_mul (conj m))
  have heq (x : ℝ) : ((‖charFactor 1 x - m‖ ^ 2 : ℝ) : ℂ) =
      1 - m * conj (charFactor 1 x) - conj m * charFactor 1 x + (‖m‖ : ℂ) ^ 2 := by
    calc
      _ = conj (charFactor 1 x - m) * (charFactor 1 x - m) := by
        rw [Complex.conj_mul', Complex.ofReal_pow]
      _ = conj (charFactor 1 x) * charFactor 1 x - m * conj (charFactor 1 x) -
          conj m * charFactor 1 x + conj m * m := by rw [map_sub]; ring
      _ = _ := by rw [Complex.conj_mul', norm_charFactor, Complex.conj_mul']; norm_num
  apply Complex.ofReal_injective
  rw [← integral_complex_ofReal]
  simp_rw [heq]
  rw [integral_add h2 (integrable_const _), integral_sub h1 (hp.const_mul (conj m)),
    integral_sub (integrable_const 1) (hc.const_mul m), integral_const_mul,
    integral_const_mul, integral_conj, integral_phase_steinhausAffineCircleMeasure hm]
  simp only [integral_const, probReal_univ, one_smul, Complex.mul_conj',
    Complex.conj_mul', Complex.ofReal_sub, Complex.ofReal_one, Complex.ofReal_pow]
  ring

end RHTower
