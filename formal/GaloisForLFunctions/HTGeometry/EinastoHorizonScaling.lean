import GaloisForLFunctions.HTGeometry.EinastoHorizonClassification

/-!
# Einasto horizon similarity and dimensionless critical mass

Closes the rescaled-mass claim in section 4.1 of arXiv:2608.23600v1 against
the actual integrated source and the proved zero/one/two horizon classification.
The peak radius scales with length, critical density scales inversely with
length squared, and critical total mass scales linearly with length. Hence the
critical mass-to-length ratio depends only on the Einasto shape.

The full lapse obeys the same similarity law. Its actual radial derivative,
and consequently the signed temperature expression of section 6, scale
inversely with length. Critical total mass is identified with the limit of the
actual enclosed-mass integral. All statements are closed for real logarithmic
parameters and use exact algebra and derivatives, without computations.
-/

noncomputable section
open Real Set MeasureTheory Filter
open scoped Topology
namespace GaloisForLFunctions.HTGeometry

theorem einastoDensity_length_scale (d l a r : ℝ) :
    einastoDensity d l a (exp l * r) = einastoDensity d 0 a r := by
  unfold einastoDensity
  simp only [exp_zero, div_one, mul_div_cancel_left₀ r (exp_ne_zero l)]

theorem einastoCore_length_scale (d l a r : ℝ) :
    einastoCore d l a (exp l * r) = einastoCore d 0 a r := by
  unfold einastoCore
  congr 1
  apply intervalIntegral.integral_congr
  intro u hu
  dsimp only
  rw [mul_assoc, einastoDensity_length_scale]

theorem einastoLogCompactness_length_scale (l a t : ℝ) :
    einastoLogCompactness l a (l + t) = exp l ^ (2 : ℕ) * einastoLogCompactness 0 a t := by
  rw [einastoLogCompactness_core, exp_add, einastoCore_length_scale, einastoLogCompactness_core]
  ring

theorem einastoHorizonBalance_length_scale (d l a t : ℝ) :
    einastoHorizonBalance d l a (exp (l + t)) =
      exp l ^ (3 : ℕ) * einastoHorizonBalance d 0 a (exp t) := by
  rw [einastoHorizonBalance, einastoHorizonBalance, einastoMass_core, einastoMass_core,
    exp_add, einastoDensity_length_scale, einastoCore_length_scale]
  ring

/-- The compactness peak radius scales exactly with the Einasto length. -/
theorem einastoBalanceZeroLogRadius_length_scale (d l a : ℝ) :
    einastoBalanceZeroLogRadius d l a = l + einastoBalanceZeroLogRadius d 0 a := by
  apply Eq.symm
  apply (einastoHorizonBalance_zero_iff d l a _).mp
  rw [einastoHorizonBalance_length_scale, einastoBalanceZeroLogRadius_eq, mul_zero]

/-- Critical central density scales as inverse length squared. -/
theorem einastoCriticalLogDensity_length_scale (l a : ℝ) :
    einastoCriticalLogDensity l a = einastoCriticalLogDensity 0 a - 2 * l := by
  rw [einastoCriticalLogDensity, einastoBalanceZeroLogRadius_length_scale,
    einastoLogCompactness_length_scale]
  rw [log_mul (by positivity : exp l ^ (2 : ℕ) ≠ 0) (einastoLogCompactness_pos _ _ _).ne']
  rw [log_pow, log_exp, einastoCriticalLogDensity]
  ring

/-- The full lapse, including its horizon structure, obeys the same similarity law. -/
theorem einastoMetric_length_similarity (d l a t : ℝ) :
    einastoMetric (d - 2 * l) l a (exp (l + t)) = einastoMetric d 0 a (exp t) := by
  rw [einastoMetric_compactness, einastoLogCompactness_length_scale, einastoMetric_compactness,
    exp_sub]
  have he : exp (2 * l) = exp l ^ (2 : ℕ) := exp_nat_mul l 2
  rw [he]
  field_simp

/-- Total mass at the unique critical central density. -/
def einastoCriticalTotalMass (l a : ℝ) : ℝ :=
  4 * Real.pi * exp (einastoCriticalLogDensity l a) * exp l ^ (3 : ℕ) * exp a * Gamma (3 * exp a)

/-- Critical mass scales linearly with length, exactly as the paper's `M/η` parameter requires. -/
theorem einastoCriticalTotalMass_length_scale (l a : ℝ) :
    einastoCriticalTotalMass l a = exp l * einastoCriticalTotalMass 0 a := by
  rw [einastoCriticalTotalMass, einastoCriticalLogDensity_length_scale, einastoCriticalTotalMass,
    exp_sub]
  have he : exp (2 * l) = exp l ^ (2 : ℕ) := exp_nat_mul l 2
  rw [he, exp_zero]
  field_simp

/-- The critical mass-to-length ratio depends only on the shape parameter. -/
theorem einastoCriticalTotalMass_dimensionless (l a : ℝ) :
    einastoCriticalTotalMass l a / exp l = einastoCriticalTotalMass 0 a := by
  rw [einastoCriticalTotalMass_length_scale]
  field_simp

/-- The critical mass is the limit of the actual enclosed-mass integral. -/
theorem einastoCriticalTotalMass_integral_limit (l a : ℝ) :
    Tendsto (einastoMass (einastoCriticalLogDensity l a) l a) atTop
      (𝓝 (einastoCriticalTotalMass l a)) := by
  unfold einastoCriticalTotalMass
  exact einastoMass_total (einastoCriticalLogDensity l a) l a

theorem einastoMetric_length_similarity_radial (d l a r : ℝ) :
    einastoMetric (d - 2 * l) l a (exp l * r) = einastoMetric d 0 a r := by
  rw [einastoMetric_core, einastoMetric_core, einastoCore_length_scale,
    einastoCore_amplitude (d - 2 * l), einastoCore_amplitude d, exp_sub]
  have he : exp (2 * l) = exp l ^ (2 : ℕ) := exp_nat_mul l 2
  rw [he]
  field_simp

/-- Actual radial lapse derivatives scale inversely with length. -/
theorem einastoMetric_derivative_length_scale (d l a t : ℝ) :
    deriv (einastoMetric (d - 2 * l) l a) (exp (l + t)) =
      exp (-l) * deriv (einastoMetric d 0 a) (exp t) := by
  have hs := (einastoMetric_derivative (d - 2 * l) l a (l + t)).differentiableAt.hasDerivAt
  rw [exp_add] at hs
  have hl : HasDerivAt (fun r : ℝ => exp l * r) (exp l) (exp t) := by
    simpa only [id_eq, mul_one] using (hasDerivAt_id (exp t)).const_mul (exp l)
  have h := hs.comp (exp t) hl
  have he : (fun r => einastoMetric (d - 2 * l) l a (exp l * r)) = einastoMetric d 0 a :=
    funext (einastoMetric_length_similarity_radial d l a)
  change HasDerivAt (fun r => einastoMetric (d - 2 * l) l a (exp l * r))
    (deriv (einastoMetric (d - 2 * l) l a) (exp l * exp t) * exp l) (exp t) at h
  rw [he] at h
  have hv := h.unique (einastoMetric_derivative d 0 a t).differentiableAt.hasDerivAt
  rw [exp_add, exp_neg]
  field_simp
  nlinarith [hv]

/-- The paper's signed Hawking-temperature expression has inverse-length scaling. -/
theorem einastoTemperature_length_scale (d l a t : ℝ) :
    deriv (einastoMetric (d - 2 * l) l a) (exp (l + t)) / (4 * Real.pi) =
      exp (-l) * (deriv (einastoMetric d 0 a) (exp t) / (4 * Real.pi)) := by
  rw [einastoMetric_derivative_length_scale]
  ring

end GaloisForLFunctions.HTGeometry
