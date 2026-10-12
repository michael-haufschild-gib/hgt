import GaloisForLFunctions.RHTower.PaperThetaExponentialEnvelope

/-! # Arbitrary right decay and exact-rate left bounds for the theta mode -/

noncomputable section

open MeasureTheory Set Filter Topology
open scoped NNReal

namespace RHTower.PaperThetaEndpoint

open HedenmalmThetaSource GaloisForLFunctions.HTGeometry

theorem norm_flatPrimitiveMode_le_mass (z : ℂ) (x : ℝ) :
    ‖flatPrimitiveMode z x‖ ≤ flatCharMass z * Real.exp (z.im * x) := by
  rw [flatPrimitiveMode, norm_mul, norm_exp_neg_I_mul, mul_comm]
  apply mul_le_mul_of_nonneg_right _ (Real.exp_nonneg _)
  exact (norm_integral_le_integral_norm _).trans
    (setIntegral_le_integral (integrable_flatCharDensity_all z).norm
      (Eventually.of_forall fun y => norm_nonneg _))

theorem norm_flatMode_le_left (z : ℂ) {x : ℝ} (hx : x ≤ 0) :
    ‖flatMode z x‖ ≤ (‖z‖ * flatCharMass z + exponentialEnvelopeConstant z.im) *
      Real.exp (z.im * x) := by
  have hρ := normalized_le_exponential z.im x
  rw [abs_of_nonpos hx, neg_mul_neg] at hρ
  calc
    ‖flatMode z x‖ ≤ ‖z‖ * ‖flatPrimitiveMode z x‖ + thetaSource.normalized x := by
      simpa only [flatMode, norm_mul, norm_neg, Complex.norm_I, one_mul,
        Complex.norm_real, Real.norm_eq_abs, abs_of_pos (thetaSource.normalized_pos x)]
        using norm_sub_le (-(Complex.I * z) * flatPrimitiveMode z x)
          (thetaSource.normalized x : ℂ)
    _ ≤ ‖z‖ * (flatCharMass z * Real.exp (z.im * x)) +
        exponentialEnvelopeConstant z.im * Real.exp (z.im * x) :=
      add_le_add (mul_le_mul_of_nonneg_left (norm_flatPrimitiveMode_le_mass z x)
        (norm_nonneg z)) hρ
    _ = _ := by ring

/-- On the right, the mode primitive inherits every nonnegative exponential rate. -/
theorem norm_flatPrimitiveMode_le_right (z : ℂ) (b : ℝ≥0) {x : ℝ} (hx : 0 ≤ x) :
    ‖flatPrimitiveMode z x‖ ≤ exponentialEnvelopeConstant (b + |z.im| + 1) *
      Real.exp (-(b : ℝ) * x) := by
  let K := exponentialEnvelopeConstant (b + |z.im| + 1)
  have hK : 0 ≤ K := (exponentialEnvelopeConstant_pos _).le
  have hmajor : IntegrableOn (fun y : ℝ => K * Real.exp (-(b : ℝ) * x) * Real.exp (-y))
      (Ioi x) := by
    have h0 : IntegrableOn (fun y : ℝ => Real.exp (-1 * y)) (Ioi x) :=
      exp_neg_integrableOn_Ioi x one_pos
    exact IntegrableOn.congr_fun (h0.const_mul (K * Real.exp (-(b : ℝ) * x)))
      (fun y _ => by simp only [neg_mul, one_mul]) measurableSet_Ioi
  have hbound : ∀ y ∈ Ioi x,
      Real.exp (z.im * x) * ‖flatCharDensity z y‖ ≤
        K * Real.exp (-(b : ℝ) * x) * Real.exp (-y) := by
    intro y hy
    have hxy : x ≤ y := le_of_lt hy
    have hy0 := hx.trans hxy
    rw [norm_flatCharDensity]
    have hρ := normalized_le_exponential ((b : ℝ) + |z.im| + 1) y
    rw [abs_of_nonneg hy0] at hρ
    calc
      _ ≤ Real.exp (z.im * x) *
          (K * Real.exp (-((b : ℝ) + |z.im| + 1) * y) * Real.exp (-z.im * y)) := by
        gcongr
      _ = K * Real.exp (z.im * (x - y) - ((b : ℝ) + |z.im| + 1) * y) := by
        rw [mul_left_comm, mul_assoc, ← Real.exp_add, ← Real.exp_add]
        congr 2
        ring
      _ ≤ K * Real.exp (-(b : ℝ) * x - y) := by
        apply mul_le_mul_of_nonneg_left _ hK
        apply Real.exp_le_exp.mpr
        have hz := neg_abs_le z.im
        nlinarith [mul_nonneg b.coe_nonneg (sub_nonneg.mpr hxy),
          mul_nonneg (abs_nonneg z.im) hx]
      _ = _ := by rw [Real.exp_sub, Real.exp_neg]; ring
  calc
    ‖flatPrimitiveMode z x‖ = Real.exp (z.im * x) *
        ‖∫ y in Ioi x, flatCharDensity z y‖ := by
      rw [flatPrimitiveMode, norm_mul, norm_exp_neg_I_mul]
    _ ≤ ∫ y in Ioi x, Real.exp (z.im * x) * ‖flatCharDensity z y‖ := by
      rw [integral_const_mul]
      exact mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _) (Real.exp_nonneg _)
    _ ≤ ∫ y in Ioi x, K * Real.exp (-(b : ℝ) * x) * Real.exp (-y) :=
      setIntegral_mono_on ((integrable_flatCharDensity_all z).norm.integrableOn.const_mul _)
        hmajor measurableSet_Ioi hbound
    _ = K * Real.exp (-(b : ℝ) * x) * Real.exp (-x) := by
      rw [integral_const_mul, integral_exp_neg_Ioi]
    _ ≤ K * Real.exp (-(b : ℝ) * x) :=
      mul_le_of_le_one_right (by positivity) (Real.exp_le_one_iff.mpr (by linarith))

theorem norm_flatMode_le_right (z : ℂ) (b : ℝ≥0) {x : ℝ} (hx : 0 ≤ x) :
    ‖flatMode z x‖ ≤
      (‖z‖ * exponentialEnvelopeConstant (b + |z.im| + 1) + exponentialEnvelopeConstant b) *
        Real.exp (-(b : ℝ) * x) := by
  have hρ := normalized_le_exponential b x
  rw [abs_of_nonneg hx] at hρ
  calc
    ‖flatMode z x‖ ≤ ‖z‖ * ‖flatPrimitiveMode z x‖ + thetaSource.normalized x := by
      simpa only [flatMode, norm_mul, norm_neg, Complex.norm_I, one_mul,
        Complex.norm_real, Real.norm_eq_abs, abs_of_pos (thetaSource.normalized_pos x)]
        using norm_sub_le (-(Complex.I * z) * flatPrimitiveMode z x)
          (thetaSource.normalized x : ℂ)
    _ ≤ ‖z‖ * (exponentialEnvelopeConstant (b + |z.im| + 1) * Real.exp (-(b : ℝ) * x)) +
        exponentialEnvelopeConstant b * Real.exp (-(b : ℝ) * x) :=
      add_le_add (mul_le_mul_of_nonneg_left (norm_flatPrimitiveMode_le_right z b hx)
        (norm_nonneg z)) hρ
    _ = _ := by ring

end RHTower.PaperThetaEndpoint
