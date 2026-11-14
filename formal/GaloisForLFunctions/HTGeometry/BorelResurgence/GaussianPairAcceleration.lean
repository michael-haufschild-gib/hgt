import GaloisForLFunctions.HTGeometry.BorelResurgence.GaussianAcceleration
import GaloisForLFunctions.HTGeometry.GaussianPairControlQuotient
import GaloisForLFunctions.HTGeometry.CenterMixedEvenReduction

/-!+# Acceleration of the two-bump Gaussian control

The even Gaussian control and the symmetric Gaussian-Weil test have closed acceleration
formulas. Their separation parameter remains Gaussian, with variance increased by the
acceleration time. Evenness reduces the half-line integral to the existing full-line heat
convolution identity.
-/

open MeasureTheory Set

namespace GaloisForLFunctions.HTGeometry

noncomputable section

private def weightedGaussianBump (s a x : ℝ) : ℝ :=
  Real.exp (-((4 * Real.exp s)⁻¹) * x ^ 2) * Real.exp (-((x - a) ^ 2))

private theorem integrable_weightedGaussianBump (s a : ℝ) :
    Integrable (weightedGaussianBump s a) := by
  have h := RiemannGaussian.integrable_translatedGaussian_product
    (a := 1) (b := (4 * Real.exp s)⁻¹) zero_lt_one (by positivity) a 0
  apply h.congr
  refine ae_of_all _ fun x => ?_
  simp only [weightedGaussianBump, RiemannGaussian.translatedGaussian,
    zero_sub, neg_sq, neg_one_mul]
  rw [sub_sq_comm a x]

private theorem integral_weightedGaussianBump (s a : ℝ) :
    (∫ x, weightedGaussianBump s a x) =
      Real.exp (-((4 * Real.exp s)⁻¹ / (1 + (4 * Real.exp s)⁻¹)) * a ^ 2) *
        Real.sqrt (Real.pi / (1 + (4 * Real.exp s)⁻¹)) := by
  simpa only [weightedGaussianBump, RiemannGaussian.translatedGaussian,
    zero_sub, neg_sq, neg_one_mul, one_mul, sub_zero, sub_sq_comm] using
    RiemannGaussian.integral_translatedGaussian_mul_translatedGaussian
      (a := 1) (b := (4 * Real.exp s)⁻¹) zero_lt_one (by positivity) a 0

private theorem weightedGaussPair_expansion (s a x : ℝ) :
    gaussianAccelerationKernel (Real.exp s) x * _root_.HTGeometry.gaussPairSource a x =
      (Real.sqrt (Real.pi * Real.exp s))⁻¹ / 2 *
        (weightedGaussianBump s a x + weightedGaussianBump s (-a) x) := by
  unfold gaussianAccelerationKernel _root_.HTGeometry.gaussPairSource weightedGaussianBump
  rw [show x - -a = x + a by ring]
  ring

/-- The Gaussian control is accelerable on the entire real axis at every positive time. -/
theorem integrable_gaussianAcceleration_gaussPairSource (s a : ℝ) :
    Integrable (fun x => gaussianAccelerationKernel (Real.exp s) x *
      _root_.HTGeometry.gaussPairSource a x) := by
  have h := ((integrable_weightedGaussianBump s a).add
    (integrable_weightedGaussianBump s (-a))).const_mul
      ((Real.sqrt (Real.pi * Real.exp s))⁻¹ / 2)
  apply h.congr
  exact ae_of_all _ fun x => (weightedGaussPair_expansion s a x).symm

private theorem gaussianAcceleration_gaussPair_raw (s a : ℝ) :
    gaussianAcceleration (_root_.HTGeometry.gaussPairSource a) (Real.exp s) =
      (Real.sqrt (Real.pi * Real.exp s))⁻¹ *
        Real.exp (-((4 * Real.exp s)⁻¹ / (1 + (4 * Real.exp s)⁻¹)) * a ^ 2) *
          Real.sqrt (Real.pi / (1 + (4 * Real.exp s)⁻¹)) / 2 := by
  unfold gaussianAcceleration
  rw [_root_.HTGeometry.integral_Ioi_zero_of_even
    (fun x => by
      simp only [gaussianAccelerationKernel, neg_sq, _root_.HTGeometry.gaussPairSource_neg])
    (integrable_gaussianAcceleration_gaussPairSource s a)]
  simp_rw [weightedGaussPair_expansion]
  rw [integral_const_mul, integral_add (integrable_weightedGaussianBump s a)
    (integrable_weightedGaussianBump s (-a)), integral_weightedGaussianBump,
    integral_weightedGaussianBump]
  simp only [neg_sq]
  ring

/-- Acceleration broadens the Gaussian separation profile by exactly `4t`. -/
theorem gaussianAcceleration_gaussPairSource (s a : ℝ) :
    gaussianAcceleration (_root_.HTGeometry.gaussPairSource a) (Real.exp s) =
      Real.exp (-(a ^ 2 / (1 + 4 * Real.exp s))) /
        Real.sqrt (1 + 4 * Real.exp s) := by
  have hzero : _root_.HTGeometry.gaussPairSource 0 =
      fun x => RiemannGaussian.translatedGaussian (1 ^ 2) 0 x := by
    funext x
    simp only [_root_.HTGeometry.gaussPairSource, RiemannGaussian.translatedGaussian,
      sub_zero, add_zero, one_pow, neg_one_mul]
    ring
  have hbase := gaussianAcceleration_gaussPair_raw s 0
  rw [hzero, gaussianAcceleration_gaussian] at hbase
  simp only [one_pow, mul_one, zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_zero,
    Real.exp_zero] at hbase
  have hD : 1 + 4 * Real.exp s ≠ 0 := by positivity
  have hrate : (4 * Real.exp s)⁻¹ / (1 + (4 * Real.exp s)⁻¹) =
      (1 + 4 * Real.exp s)⁻¹ := by
    field_simp [Real.exp_ne_zero, hD]
    <;> ring
  rw [gaussianAcceleration_gaussPair_raw, hrate]
  rw [show -(1 + 4 * Real.exp s)⁻¹ * a ^ 2 =
      -(a ^ 2 / (1 + 4 * Real.exp s)) by ring]
  calc
    _ = Real.exp (-(a ^ 2 / (1 + 4 * Real.exp s))) *
        ((Real.sqrt (Real.pi * Real.exp s))⁻¹ *
          Real.sqrt (Real.pi / (1 + (4 * Real.exp s)⁻¹)) / 2) := by ring
    _ = _ := by
      simpa only [div_eq_mul_inv] using
        congrArg (Real.exp (-(a ^ 2 / (1 + 4 * Real.exp s))) * ·) hbase.symm

/-- The symmetric Gaussian-Weil test has twice the normalized control's acceleration. -/
theorem gaussianAcceleration_symmetricGaussian_unit (s a : ℝ) :
    gaussianAcceleration (RiemannGaussian.symmetricGaussian 1 a) (Real.exp s) =
      2 * (Real.exp (-(a ^ 2 / (1 + 4 * Real.exp s))) /
        Real.sqrt (1 + 4 * Real.exp s)) := by
  have he : RiemannGaussian.symmetricGaussian 1 a =
      fun x => 2 * _root_.HTGeometry.gaussPairSource a x := by
    funext x
    simp only [RiemannGaussian.symmetricGaussian, RiemannGaussian.translatedGaussian,
      _root_.HTGeometry.gaussPairSource, neg_one_mul]
    rw [show (-x - a) ^ 2 = (x + a) ^ 2 by ring]
    ring
  rw [he]
  unfold gaussianAcceleration
  simp_rw [mul_left_comm (gaussianAccelerationKernel _ _) (2 : ℝ)]
  rw [integral_const_mul]
  exact congrArg (2 * ·) (gaussianAcceleration_gaussPairSource s a)

end

end GaloisForLFunctions.HTGeometry

#print axioms GaloisForLFunctions.HTGeometry.integrable_gaussianAcceleration_gaussPairSource
#print axioms GaloisForLFunctions.HTGeometry.gaussianAcceleration_gaussPairSource
#print axioms GaloisForLFunctions.HTGeometry.gaussianAcceleration_symmetricGaussian_unit
