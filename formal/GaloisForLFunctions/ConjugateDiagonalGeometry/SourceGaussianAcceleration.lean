import GaloisForLFunctions.ConjugateDiagonalGeometry.SourceTransformGrowth
import GaloisForLFunctions.HTGeometry.BorelResurgence.GaussianAcceleration

/-!
# Gaussian acceleration of compact arithmetic sources

Every translated and ordinate-shifted compact source has a convergent Gaussian acceleration on
the positive ray. The time parameter ranges over `(0, 1/4)`: its excess inverse variance absorbs
the linear growth caused by translation. The proof supplies an explicit Gaussian majorant.
-/

open MeasureTheory Set

namespace GaloisForLFunctions.ConjugateDiagonalGeometry

open HTGeometry Zeta23 ArithmeticPolarization

noncomputable section

/-- Positive acceleration times strictly below the quadratic source-growth threshold. -/
def sourceAccelerationTime (s : ℝ) : ℝ := (4 * (1 + Real.exp s))⁻¹

theorem sourceAccelerationTime_mem (s : ℝ) :
    sourceAccelerationTime s ∈ Ioo (0 : ℝ) (1 / 4) := by
  unfold sourceAccelerationTime
  constructor
  · positivity
  · rw [inv_lt_iff₀ (by positivity)]
    nlinarith only [Real.exp_pos s]

/-- A translated source retains a Gaussian majorant after acceleration, with positive decay. -/
theorem shiftedSource_acceleration_gaussian_bound (f : CompactTest) (u τ s : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ,
      ‖(gaussianAccelerationKernel (sourceAccelerationTime s) x : ℂ) *
        shiftedSourceTransform f u τ x‖ ≤
          C * Real.exp (-(Real.exp s / 2) * x ^ 2) := by
  obtain ⟨A, hA, hbound⟩ := norm_tr_le_sourceGaussian f
  let q := (Real.sqrt (Real.pi * sourceAccelerationTime s))⁻¹
  let B := τ ^ 2 + |u| / 2 + u ^ 2 / (2 * Real.exp s)
  have hq : 0 < q := by
    dsimp [q]
    exact inv_pos.mpr (Real.sqrt_pos.mpr
      (mul_pos Real.pi_pos (sourceAccelerationTime_mem s).1))
  refine ⟨q * A * Real.exp B, by positivity, fun x => ?_⟩
  have hrate : (4 * sourceAccelerationTime s)⁻¹ = 1 + Real.exp s := by
    unfold sourceAccelerationTime
    field_simp
  have hnorm : ‖(x : ℂ) - (τ : ℂ) * Complex.I‖ ^ 2 = x ^ 2 + τ ^ 2 := by
    rw [Complex.sq_norm]
    simp [Complex.normSq_apply]
  have hlin : |u| * |x| ≤ Real.exp s / 2 * x ^ 2 + u ^ 2 / (2 * Real.exp s) := by
    apply (mul_le_mul_iff_right₀ (show 0 < 2 * Real.exp s by positivity)).mp
    have he : (Real.exp s / 2 * x ^ 2 + u ^ 2 / (2 * Real.exp s)) *
        (2 * Real.exp s) = (Real.exp s) ^ 2 * x ^ 2 + u ^ 2 := by
      field_simp
      <;> ring
    rw [he]
    have h := sq_nonneg (Real.exp s * |x| - |u|)
    nlinarith only [h, sq_abs x, sq_abs u]
  have hs := norm_shiftedSourceTransform_le f hbound u τ (x : ℂ)
  rw [hnorm, Complex.norm_real, Real.norm_eq_abs] at hs
  rw [norm_mul, Complex.norm_real,
    abs_of_nonneg (gaussianAccelerationKernel_nonneg _ _)]
  calc
    gaussianAccelerationKernel (sourceAccelerationTime s) x *
        ‖shiftedSourceTransform f u τ x‖ ≤
      gaussianAccelerationKernel (sourceAccelerationTime s) x *
        (A * Real.exp (x ^ 2 + τ ^ 2 + |u| * (|x| + 1 / 2))) :=
      mul_le_mul_of_nonneg_left hs (gaussianAccelerationKernel_nonneg _ _)
    _ = q * A * Real.exp
        (-(1 + Real.exp s) * x ^ 2 + (x ^ 2 + τ ^ 2 + |u| * (|x| + 1 / 2))) := by
      rw [gaussianAccelerationKernel, hrate, Real.exp_add]
      ring
    _ ≤ q * A * Real.exp (B - Real.exp s / 2 * x ^ 2) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Real.exp_le_exp.mpr
      dsimp [B]
      linarith only [hlin]
    _ = q * A * Real.exp B * Real.exp (-(Real.exp s / 2) * x ^ 2) := by
      rw [Real.exp_sub, Real.exp_neg]
      ring

/-- Every compact source, with arbitrary real translation and ordinate shift, is accelerable. -/
theorem integrable_shiftedSource_acceleration (f : CompactTest) (u τ s : ℝ) :
    Integrable (fun x : ℝ =>
      (gaussianAccelerationKernel (sourceAccelerationTime s) x : ℂ) *
        shiftedSourceTransform f u τ x) := by
  obtain ⟨C, _, hbound⟩ := shiftedSource_acceleration_gaussian_bound f u τ s
  have hmajor := (integrable_exp_neg_mul_sq (by positivity : 0 < Real.exp s / 2)).const_mul C
  apply hmajor.mono' _ (ae_of_all _ hbound)
  have hs := (differentiable_shiftedSourceTransform f u τ).continuous
  have hk : Continuous (gaussianAccelerationKernel (sourceAccelerationTime s)) := by
    unfold gaussianAccelerationKernel
    fun_prop
  exact ((Complex.continuous_ofReal.comp hk).mul
    (hs.comp Complex.continuous_ofReal)).aestronglyMeasurable

/-- The positive-ray integral is a genuine convergent complex acceleration of the source. -/
theorem integrableOn_shiftedSource_acceleration (f : CompactTest) (u τ s : ℝ) :
    IntegrableOn (fun x : ℝ =>
      (gaussianAccelerationKernel (sourceAccelerationTime s) x : ℂ) *
        shiftedSourceTransform f u τ x) (Ioi 0) :=
  (integrable_shiftedSource_acceleration f u τ s).integrableOn

end

end GaloisForLFunctions.ConjugateDiagonalGeometry
