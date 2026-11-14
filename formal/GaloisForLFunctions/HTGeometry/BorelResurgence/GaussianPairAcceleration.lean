import GaloisForLFunctions.HTGeometry.BorelResurgence.GaussianAcceleration
import GaloisForLFunctions.HTGeometry.GaussianPairControlQuotient
import GaloisForLFunctions.HTGeometry.CenterMixedEvenReduction

/-!
# Acceleration of symmetric Gaussian tests and the two-bump control

Every positive-bandwidth symmetric Gaussian-Weil test has an exact acceleration formula.
Its separation parameter remains Gaussian, with reciprocal bandwidth increased by `4t`.
The two-bump control is half the unit-bandwidth test. Evenness
reduces these half-line integrals to the existing full-line heat convolution identity.
-/

open MeasureTheory Set

namespace GaloisForLFunctions.HTGeometry

noncomputable section

private def weightedGaussianBump (s v a x : ℝ) : ℝ :=
  Real.exp (-((4 * Real.exp s)⁻¹) * x ^ 2) * Real.exp (-Real.exp v * (x - a) ^ 2)

private theorem integrable_weightedGaussianBump (s v a : ℝ) :
    Integrable (weightedGaussianBump s v a) := by
  have h := RiemannGaussian.integrable_translatedGaussian_product
    (a := Real.exp v) (b := (4 * Real.exp s)⁻¹) (Real.exp_pos v) (by positivity) a 0
  apply h.congr
  refine ae_of_all _ fun x => ?_
  simp only [weightedGaussianBump, RiemannGaussian.translatedGaussian, zero_sub, neg_sq]
  rw [sub_sq_comm a x]

private theorem integral_weightedGaussianBump (s v a : ℝ) :
    (∫ x, weightedGaussianBump s v a x) =
      Real.exp (-(Real.exp v * (4 * Real.exp s)⁻¹ /
        (Real.exp v + (4 * Real.exp s)⁻¹)) * a ^ 2) *
          Real.sqrt (Real.pi / (Real.exp v + (4 * Real.exp s)⁻¹)) := by
  simpa only [weightedGaussianBump, RiemannGaussian.translatedGaussian,
    zero_sub, neg_sq, sub_zero, sub_sq_comm] using
    RiemannGaussian.integral_translatedGaussian_mul_translatedGaussian
      (a := Real.exp v) (b := (4 * Real.exp s)⁻¹) (Real.exp_pos v) (by positivity) a 0

private theorem weightedSymmetricGaussian_expansion (s v a x : ℝ) :
    gaussianAccelerationKernel (Real.exp s) x *
      RiemannGaussian.symmetricGaussian (Real.exp v) a x =
      (Real.sqrt (Real.pi * Real.exp s))⁻¹ *
        (weightedGaussianBump s v a x + weightedGaussianBump s v (-a) x) := by
  unfold gaussianAccelerationKernel RiemannGaussian.symmetricGaussian
    RiemannGaussian.translatedGaussian weightedGaussianBump
  rw [show (-x - a) ^ 2 = (x - -a) ^ 2 by ring]
  ring

/-- Every positive-bandwidth symmetric Gaussian is accelerable at every positive time. -/
theorem integrable_gaussianAcceleration_symmetricGaussian (s v a : ℝ) :
    Integrable (fun x => gaussianAccelerationKernel (Real.exp s) x *
      RiemannGaussian.symmetricGaussian (Real.exp v) a x) := by
  have h := ((integrable_weightedGaussianBump s v a).add
    (integrable_weightedGaussianBump s v (-a))).const_mul
      (Real.sqrt (Real.pi * Real.exp s))⁻¹
  apply h.congr
  exact ae_of_all _ fun x => (weightedSymmetricGaussian_expansion s v a x).symm

private theorem gaussianAcceleration_symmetricGaussian_raw (s v a : ℝ) :
    gaussianAcceleration (RiemannGaussian.symmetricGaussian (Real.exp v) a) (Real.exp s) =
      (Real.sqrt (Real.pi * Real.exp s))⁻¹ *
        Real.exp (-(Real.exp v * (4 * Real.exp s)⁻¹ /
          (Real.exp v + (4 * Real.exp s)⁻¹)) * a ^ 2) *
            Real.sqrt (Real.pi / (Real.exp v + (4 * Real.exp s)⁻¹)) := by
  unfold gaussianAcceleration
  rw [_root_.HTGeometry.integral_Ioi_zero_of_even
    (fun x => by
      simp only [gaussianAccelerationKernel, neg_sq, RiemannGaussian.symmetricGaussian_even])
    (integrable_gaussianAcceleration_symmetricGaussian s v a)]
  simp_rw [weightedSymmetricGaussian_expansion]
  rw [integral_const_mul, integral_add (integrable_weightedGaussianBump s v a)
    (integrable_weightedGaussianBump s v (-a)), integral_weightedGaussianBump,
    integral_weightedGaussianBump]
  simp only [neg_sq]
  ring

/-- Gaussian acceleration adds exactly `4t` to the reciprocal bandwidth of the separation profile. -/
theorem gaussianAcceleration_symmetricGaussian (s v a : ℝ) :
    gaussianAcceleration (RiemannGaussian.symmetricGaussian (Real.exp v) a) (Real.exp s) =
      2 * (Real.exp (-(Real.exp v * a ^ 2 / (1 + 4 * Real.exp s * Real.exp v))) /
        Real.sqrt (1 + 4 * Real.exp s * Real.exp v)) := by
  have hzero : gaussianAcceleration (RiemannGaussian.symmetricGaussian (Real.exp v) 0)
      (Real.exp s) =
      2 * gaussianAcceleration (fun x => Real.exp (-Real.exp v * x ^ 2)) (Real.exp s) := by
    have hz (x : ℝ) : RiemannGaussian.symmetricGaussian (Real.exp v) 0 x =
        2 * Real.exp (-Real.exp v * x ^ 2) := by
      simp only [RiemannGaussian.symmetricGaussian, RiemannGaussian.translatedGaussian,
        sub_zero, neg_sq]
      ring
    unfold gaussianAcceleration
    simp_rw [hz, mul_left_comm (gaussianAccelerationKernel _ _) (2 : ℝ)]
    rw [integral_const_mul]
  have hbase := gaussianAcceleration_symmetricGaussian_raw s v 0
  rw [hzero, gaussianAcceleration_quadratic] at hbase
  simp only [mul_neg, sub_neg_eq_add, zero_pow (by norm_num : (2 : ℕ) ≠ 0),
    mul_zero, Real.exp_zero, mul_one] at hbase
  have hD : 1 + 4 * Real.exp s * Real.exp v ≠ 0 := by positivity
  have hden : Real.exp v + (4 * Real.exp s)⁻¹ ≠ 0 := by positivity
  have hrate : Real.exp v * (4 * Real.exp s)⁻¹ /
      (Real.exp v + (4 * Real.exp s)⁻¹) =
        Real.exp v / (1 + 4 * Real.exp s * Real.exp v) := by
    field_simp [Real.exp_ne_zero, hD, hden]
    ring
  rw [gaussianAcceleration_symmetricGaussian_raw, hrate]
  rw [show -(Real.exp v / (1 + 4 * Real.exp s * Real.exp v)) * a ^ 2 =
      -(Real.exp v * a ^ 2 / (1 + 4 * Real.exp s * Real.exp v)) by ring]
  calc
    _ = Real.exp (-(Real.exp v * a ^ 2 / (1 + 4 * Real.exp s * Real.exp v))) *
        ((Real.sqrt (Real.pi * Real.exp s))⁻¹ *
          Real.sqrt (Real.pi / (Real.exp v + (4 * Real.exp s)⁻¹))) := by ring
    _ = _ := by rw [← hbase]; ring

private theorem symmetricGaussian_unit_eq_gaussPair (a x : ℝ) :
    RiemannGaussian.symmetricGaussian 1 a x = 2 * _root_.HTGeometry.gaussPairSource a x := by
  simp only [RiemannGaussian.symmetricGaussian, RiemannGaussian.translatedGaussian,
    _root_.HTGeometry.gaussPairSource, neg_one_mul]
  rw [show (-x - a) ^ 2 = (x + a) ^ 2 by ring]
  ring

/-- The two-bump Gaussian control is accelerable on the whole real axis. -/
theorem integrable_gaussianAcceleration_gaussPairSource (s a : ℝ) :
    Integrable (fun x => gaussianAccelerationKernel (Real.exp s) x *
      _root_.HTGeometry.gaussPairSource a x) := by
  have h := (integrable_gaussianAcceleration_symmetricGaussian s 0 a).const_mul (1 / 2 : ℝ)
  apply h.congr
  refine ae_of_all _ fun x => ?_
  simp only [Real.exp_zero, symmetricGaussian_unit_eq_gaussPair]
  ring

/-- The normalized two-bump control retains an exact Gaussian profile in its separation. -/
theorem gaussianAcceleration_gaussPairSource (s a : ℝ) :
    gaussianAcceleration (_root_.HTGeometry.gaussPairSource a) (Real.exp s) =
      Real.exp (-(a ^ 2 / (1 + 4 * Real.exp s))) /
        Real.sqrt (1 + 4 * Real.exp s) := by
  have hsym : gaussianAcceleration (RiemannGaussian.symmetricGaussian 1 a) (Real.exp s) =
      2 * gaussianAcceleration (_root_.HTGeometry.gaussPairSource a) (Real.exp s) := by
    unfold gaussianAcceleration
    simp_rw [symmetricGaussian_unit_eq_gaussPair,
      mul_left_comm (gaussianAccelerationKernel _ _) (2 : ℝ)]
    rw [integral_const_mul]
  have h := gaussianAcceleration_symmetricGaussian s 0 a
  simp only [Real.exp_zero, mul_one, one_mul] at h
  rw [hsym] at h
  linarith only [h]

end

end GaloisForLFunctions.HTGeometry

#print axioms GaloisForLFunctions.HTGeometry.integrable_gaussianAcceleration_symmetricGaussian
#print axioms GaloisForLFunctions.HTGeometry.gaussianAcceleration_symmetricGaussian
#print axioms GaloisForLFunctions.HTGeometry.integrable_gaussianAcceleration_gaussPairSource
#print axioms GaloisForLFunctions.HTGeometry.gaussianAcceleration_gaussPairSource
