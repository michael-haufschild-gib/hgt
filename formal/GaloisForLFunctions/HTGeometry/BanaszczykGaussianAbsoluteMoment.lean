import GaloisForLFunctions.HTGeometry.ExpSquareRayTail

/-!
# Gaussian absolute moment for vector balancing

The sharp factor in Lemma 2.4 of Guo--Fang--Lu is the elementary identity
`E |G| = sqrt (2 / pi)` for a standard real Gaussian.  The corpus already
contains the exact positive-ray primitive for `x * exp (-b x^(2 : ℕ))`; this module
normalizes it and records the arbitrary-scale form used after conditioning.
-/

noncomputable section

open MeasureTheory Set

namespace GaloisForLFunctions.HTGeometry

/-- Standard real Gaussian density with variance one. -/
def banaszczykStandardGaussianDensity (x : ℝ) : ℝ :=
  (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(1 / 2) * x ^ (2 : ℕ))

theorem banaszczykStandardGaussianDensity_nonneg (x : ℝ) :
    0 ≤ banaszczykStandardGaussianDensity x := by
  unfold banaszczykStandardGaussianDensity
  positivity

theorem continuous_banaszczykStandardGaussianDensity :
    Continuous banaszczykStandardGaussianDensity := by
  unfold banaszczykStandardGaussianDensity
  fun_prop

theorem integrable_banaszczykStandardGaussianDensity :
    Integrable banaszczykStandardGaussianDensity := by
  unfold banaszczykStandardGaussianDensity
  exact (integrable_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1 / 2)).const_mul _

/-- Standard Gaussian density has total mass one. -/
@[simp]
theorem integral_banaszczykStandardGaussianDensity :
    ∫ x : ℝ, banaszczykStandardGaussianDensity x = 1 := by
  unfold banaszczykStandardGaussianDensity
  rw [integral_const_mul, integral_gaussian]
  rw [show Real.pi / (1 / 2 : ℝ) = 2 * Real.pi by ring]
  have hsqrt : Real.sqrt (2 * Real.pi) ≠ 0 := by positivity
  field_simp

theorem integrable_abs_mul_banaszczykStandardGaussianDensity :
    Integrable (fun x : ℝ => |x| * banaszczykStandardGaussianDensity x) := by
  have h := (integrable_mul_exp_neg_mul_sq
    (by norm_num : (0 : ℝ) < 1 / 2)).norm.const_mul (Real.sqrt (2 * Real.pi))⁻¹
  refine h.congr ?_
  exact Filter.Eventually.of_forall fun x => by
    unfold banaszczykStandardGaussianDensity
    change (Real.sqrt (2 * Real.pi))⁻¹ *
        ‖x * Real.exp (-(1 / 2) * x ^ (2 : ℕ))‖ =
      |x| * ((Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(1 / 2) * x ^ (2 : ℕ)))
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
    ring

private theorem integral_abs_mul_standardGaussianKernel :
    ∫ x : ℝ, |x| * Real.exp (-(1 / 2) * x ^ (2 : ℕ)) = 2 := by
  have htail := GaloisForLFunctions.integral_Ioi_id_mul_expNegSq
    (b := (1 / 2 : ℝ)) (a := (0 : ℝ)) (by norm_num)
  have htail' :
      ∫ x in Ioi (0 : ℝ), x * Real.exp (-(1 / 2) * x ^ (2 : ℕ)) = 1 := by
    convert htail using 1 <;> simp
  calc
    (∫ x : ℝ, |x| * Real.exp (-(1 / 2) * x ^ (2 : ℕ))) =
        ∫ x : ℝ, (fun y => y * Real.exp (-(1 / 2) * y ^ (2 : ℕ))) |x| := by
      congr 1
      funext x
      simp only
      rw [sq_abs]
    _ = 2 * ∫ x in Ioi (0 : ℝ),
          x * Real.exp (-(1 / 2) * x ^ (2 : ℕ)) := by
      simpa only using
        (integral_comp_abs (f := fun y => y * Real.exp (-(1 / 2) * y ^ (2 : ℕ))))
    _ = 2 := by rw [htail']; norm_num

/-- Exact sharp standard-Gaussian absolute moment. -/
@[simp]
theorem integral_abs_mul_banaszczykStandardGaussianDensity :
    ∫ x : ℝ, |x| * banaszczykStandardGaussianDensity x = Real.sqrt (2 / Real.pi) := by
  rw [show (fun x : ℝ => |x| * banaszczykStandardGaussianDensity x) =
      fun x => (Real.sqrt (2 * Real.pi))⁻¹ *
        (|x| * Real.exp (-(1 / 2) * x ^ (2 : ℕ))) by
    funext x
    unfold banaszczykStandardGaussianDensity
    ring]
  rw [integral_const_mul, integral_abs_mul_standardGaussianKernel]
  rw [Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 2),
    Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
  have h2 : Real.sqrt (2 : ℝ) ≠ 0 := by positivity
  have hpi : Real.sqrt Real.pi ≠ 0 := by positivity
  field_simp
  nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]

/-- Absolute moment of any scalar multiple of a standard Gaussian. -/
@[simp]
theorem integral_abs_smul_banaszczykStandardGaussianDensity (a : ℝ) :
    ∫ x : ℝ, |a * x| * banaszczykStandardGaussianDensity x =
      |a| * Real.sqrt (2 / Real.pi) := by
  rw [show (fun x : ℝ => |a * x| * banaszczykStandardGaussianDensity x) =
      fun x => |a| * (|x| * banaszczykStandardGaussianDensity x) by
    funext x
    rw [abs_mul]
    ring]
  rw [integral_const_mul, integral_abs_mul_banaszczykStandardGaussianDensity]

end GaloisForLFunctions.HTGeometry
