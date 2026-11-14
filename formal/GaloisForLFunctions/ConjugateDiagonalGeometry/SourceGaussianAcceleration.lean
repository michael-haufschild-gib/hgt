import GaloisForLFunctions.ConjugateDiagonalGeometry.SourceTestApertureBounds
import GaloisForLFunctions.HTGeometry.BorelResurgence.GaussianAcceleration

/-!
# Gaussian acceleration of compact arithmetic sources

Compact support gives exponential, rather than quadratic-exponential, growth on every
horizontal ray. Gaussian acceleration therefore converges at every positive time, after
arbitrary real translation and ordinate shift. The accelerated source retains uniform
inverse-square decay in the ordinate shift.
-/

open MeasureTheory Set

namespace GaloisForLFunctions.ConjugateDiagonalGeometry

open HTGeometry Zeta23 ArithmeticPolarization _root_.RHTower

noncomputable section

/-- Compactness supplies a finite exponential type, uniformly over all ordinate shifts. -/
theorem shiftedSource_realRay_exponential_bound (f : CompactTest) (u : ℝ) :
    ∃ C R : ℝ, 0 ≤ C ∧ 0 ≤ R ∧ ∀ τ x : ℝ,
      ‖shiftedSourceTransform f u τ x‖ ≤
        C / (1 + |τ|) ^ 2 * Real.exp (R * |x|) := by
  obtain ⟨a, ha, hsupport⟩ := f.2.2.isBounded.exists_pos_norm_le'
  have hsupp : ∀ x, f.1 x ≠ 0 → |x| ≤ a := by
    intro x hx
    simpa only [Real.norm_eq_abs] using hsupport x (subset_tsupport f.1 hx)
  let R := a + |u|
  have hR : 0 ≤ R := add_nonneg ha.le (abs_nonneg u)
  have hS := sourceTestSize_nonneg f
  refine ⟨sourceTestSize f * Real.exp (R / 2), R, by positivity, hR, fun τ x => ?_⟩
  have ht := norm_tr_le_sourceTestSize f hsupp ((x : ℂ) - (τ : ℂ) * Complex.I)
  have hre : ((x : ℂ) - (τ : ℂ) * Complex.I).re = x := by simp
  have him : ((x : ℂ) - (τ : ℂ) * Complex.I).im = -τ := by simp
  rw [hre, him, abs_neg] at ht
  have hlin : u * (x - 1 / 2) ≤ |u| * |x - 1 / 2| := by
    simpa only [abs_mul] using le_abs_self (u * (x - 1 / 2))
  have habs : |x - 1 / 2| ≤ |x| + 1 / 2 := by
    simpa only [abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)] using abs_sub x (1 / 2)
  have hexponent : u * (x - 1 / 2) + |x - 1 / 2| * a ≤ R / 2 + R * |x| := by
    have h := mul_le_mul_of_nonneg_left habs hR
    dsimp [R] at h ⊢
    nlinarith only [hlin, h]
  rw [shiftedSourceTransform, norm_mul, Complex.norm_exp]
  have he : (((x : ℂ) - 1 / 2) * (u : ℂ)).re = u * (x - 1 / 2) := by
    simp
    <;> ring
  rw [he]
  calc
    Real.exp (u * (x - 1 / 2)) * ‖tr f.1 ((x : ℂ) - (τ : ℂ) * Complex.I)‖ ≤
      Real.exp (u * (x - 1 / 2)) *
        (Real.exp (|x - 1 / 2| * a) * sourceTestSize f / (1 + |τ|) ^ 2) :=
      mul_le_mul_of_nonneg_left ht (Real.exp_pos _).le
    _ = sourceTestSize f / (1 + |τ|) ^ 2 *
        Real.exp (u * (x - 1 / 2) + |x - 1 / 2| * a) := by rw [Real.exp_add]; ring
    _ ≤ sourceTestSize f / (1 + |τ|) ^ 2 * Real.exp (R / 2 + R * |x|) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexponent) (by positivity)
    _ = _ := by rw [Real.exp_add]; ring

/-- Every positive acceleration time leaves a positive Gaussian decay margin. -/
theorem shiftedSource_acceleration_gaussian_bound (f : CompactTest) (u s : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ τ x : ℝ,
      ‖(gaussianAccelerationKernel (Real.exp s) x : ℂ) * shiftedSourceTransform f u τ x‖ ≤
        C / (1 + |τ|) ^ 2 * Real.exp (-((4 * Real.exp s)⁻¹ / 2) * x ^ 2) := by
  obtain ⟨C, R, hC, _, hsource⟩ := shiftedSource_realRay_exponential_bound f u
  let b := (4 * Real.exp s)⁻¹
  let q := (Real.sqrt (Real.pi * Real.exp s))⁻¹
  have hb : 0 < b := by dsimp [b]; positivity
  have hq : 0 ≤ q := by dsimp [q]; positivity
  refine ⟨q * C * Real.exp (R ^ 2 / (2 * b)), by positivity, fun τ x => ?_⟩
  have hlin : R * |x| ≤ b / 2 * x ^ 2 + R ^ 2 / (2 * b) := by
    apply (mul_le_mul_iff_right₀ (show 0 < 2 * b by positivity)).mp
    have he : (b / 2 * x ^ 2 + R ^ 2 / (2 * b)) * (2 * b) = b ^ 2 * x ^ 2 + R ^ 2 := by
      field_simp
      <;> ring
    rw [he]
    have hsq := sq_nonneg (b * |x| - R)
    rw [sub_sq, mul_pow, sq_abs] at hsq
    nlinarith only [hsq]
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (gaussianAccelerationKernel_nonneg _ _)]
  calc
    gaussianAccelerationKernel (Real.exp s) x * ‖shiftedSourceTransform f u τ x‖ ≤
        gaussianAccelerationKernel (Real.exp s) x *
          (C / (1 + |τ|) ^ 2 * Real.exp (R * |x|)) :=
      mul_le_mul_of_nonneg_left (hsource τ x) (gaussianAccelerationKernel_nonneg _ _)
    _ = q * C / (1 + |τ|) ^ 2 * Real.exp (-b * x ^ 2 + R * |x|) := by
      rw [gaussianAccelerationKernel, Real.exp_add]
      dsimp [q, b]
      ring
    _ ≤ q * C / (1 + |τ|) ^ 2 * Real.exp (R ^ 2 / (2 * b) + -(b / 2) * x ^ 2) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact Real.exp_le_exp.mpr (by linarith only [hlin])
    _ = _ := by rw [Real.exp_add]; ring

/-- All compact sources and all real translations have convergent acceleration at every positive time. -/
theorem integrable_shiftedSource_acceleration (f : CompactTest) (u τ s : ℝ) :
    Integrable (fun x : ℝ => (gaussianAccelerationKernel (Real.exp s) x : ℂ) *
      shiftedSourceTransform f u τ x) := by
  obtain ⟨C, _, hbound⟩ := shiftedSource_acceleration_gaussian_bound f u s
  have hmajor := (integrable_exp_neg_mul_sq
    (by positivity : 0 < (4 * Real.exp s)⁻¹ / 2)).const_mul (C / (1 + |τ|) ^ 2)
  apply hmajor.mono' _ (ae_of_all _ (hbound τ))
  have hs := (differentiable_shiftedSourceTransform f u τ).continuous
  have hk : Continuous (gaussianAccelerationKernel (Real.exp s)) := by
    unfold gaussianAccelerationKernel
    fun_prop
  exact ((Complex.continuous_ofReal.comp hk).mul
    (hs.comp Complex.continuous_ofReal)).aestronglyMeasurable

/-- The positive-ray integral is a genuine convergent complex acceleration. -/
theorem integrableOn_shiftedSource_acceleration (f : CompactTest) (u τ s : ℝ) :
    IntegrableOn (fun x : ℝ => (gaussianAccelerationKernel (Real.exp s) x : ℂ) *
      shiftedSourceTransform f u τ x) (Ioi 0) :=
  (integrable_shiftedSource_acceleration f u τ s).integrableOn

/-- Acceleration preserves uniform inverse-square decay under ordinate modulation. -/
theorem shiftedSource_acceleration_vertical_decay (f : CompactTest) (u s : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ τ : ℝ,
      ‖∫ x in Ioi (0 : ℝ), (gaussianAccelerationKernel (Real.exp s) x : ℂ) *
        shiftedSourceTransform f u τ x‖ ≤ C / (1 + |τ|) ^ 2 := by
  obtain ⟨C, hC, hbound⟩ := shiftedSource_acceleration_gaussian_bound f u s
  let b := (4 * Real.exp s)⁻¹ / 2
  refine ⟨C * (Real.sqrt (Real.pi / b) / 2), by positivity, fun τ => ?_⟩
  calc
    _ ≤ ∫ x in Ioi (0 : ℝ), ‖(gaussianAccelerationKernel (Real.exp s) x : ℂ) *
        shiftedSourceTransform f u τ x‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ x in Ioi (0 : ℝ), C / (1 + |τ|) ^ 2 * Real.exp (-b * x ^ 2) := by
      apply integral_mono_ae (integrableOn_shiftedSource_acceleration f u τ s).norm
        ((integrable_exp_neg_mul_sq (by dsimp [b]; positivity)).integrableOn.const_mul _)
      exact ae_of_all _ (hbound τ)
    _ = _ := by rw [integral_const_mul, integral_gaussian_Ioi]; ring

end

end GaloisForLFunctions.ConjugateDiagonalGeometry

#print axioms GaloisForLFunctions.ConjugateDiagonalGeometry.shiftedSource_realRay_exponential_bound
#print axioms GaloisForLFunctions.ConjugateDiagonalGeometry.shiftedSource_acceleration_gaussian_bound
#print axioms GaloisForLFunctions.ConjugateDiagonalGeometry.integrable_shiftedSource_acceleration
#print axioms GaloisForLFunctions.ConjugateDiagonalGeometry.integrableOn_shiftedSource_acceleration
#print axioms GaloisForLFunctions.ConjugateDiagonalGeometry.shiftedSource_acceleration_vertical_decay
