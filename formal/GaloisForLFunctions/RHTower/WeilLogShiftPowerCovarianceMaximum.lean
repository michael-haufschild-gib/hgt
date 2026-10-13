import GaloisForLFunctions.RHTower.WeilLogShiftPowerCovarianceEntropy

/-! # Uniform benchmark, equality and stability for finite power covariance -/

namespace RHTower

open MeasureTheory
open GaloisForLFunctions.HTGeometry GaloisForLFunctions.HTGeometry.FourierLLogL

local notation "E" => EuclideanSpace ℝ (Fin 2)

theorem finiteWeilCanonicalJointQuadraticTilt_powerCovarianceMatrix_det_le_uniform
    (r k : ℕ) (a b d : ℝ) :
    (powerCovarianceMatrix (finiteWeilCanonicalJointQuadraticTilt r k a b d : Measure E)
      (fun z : E => z 0) r).det ≤ finiteWeilPowerCovarianceUniformBenchmark r := by
  have hdom : (Law.uniform (Fin (r + 1))).dominated
      (finiteWeilCanonicalJointQuadraticTiltIndexLaw r k a b d) :=
    fun i _ => finiteWeilCanonicalJointQuadraticTiltWeight_pos r k a b d i
  rw [finiteWeilCanonicalJointQuadraticTilt_powerCovarianceMatrix_det_entropy]
  have he := Real.exp_le_one_iff.mpr
    (neg_nonpos.mpr (mul_nonneg
      (show (0 : ℝ) ≤ ((r + 1 : ℕ) : ℝ) by positivity) (Law.kl_nonneg hdom)))
  simpa using mul_le_mul_of_nonneg_left he
    (finiteWeilPowerCovarianceUniformBenchmark_pos r).le

/-- Equality with the benchmark detects precisely uniform actual atom weights. -/
theorem finiteWeilCanonicalJointQuadraticTilt_powerCovarianceMatrix_det_eq_uniform_iff
    (r k : ℕ) (a b d : ℝ) :
    (powerCovarianceMatrix (finiteWeilCanonicalJointQuadraticTilt r k a b d : Measure E)
      (fun z : E => z 0) r).det = finiteWeilPowerCovarianceUniformBenchmark r ↔
    ∀ i, finiteWeilCanonicalJointQuadraticTiltWeight r k a b d i =
      ((r + 1 : ℕ) : ℝ)⁻¹ := by
  have hdom : (Law.uniform (Fin (r + 1))).dominated
      (finiteWeilCanonicalJointQuadraticTiltIndexLaw r k a b d) :=
    fun i _ => finiteWeilCanonicalJointQuadraticTiltWeight_pos r k a b d i
  rw [finiteWeilCanonicalJointQuadraticTilt_powerCovarianceMatrix_det_entropy]
  constructor
  · intro h
    have he : Real.exp (-(((r + 1 : ℕ) : ℝ) *
        (Law.uniform (Fin (r + 1))).kl
          (finiteWeilCanonicalJointQuadraticTiltIndexLaw r k a b d))) = 1 :=
      mul_left_cancel₀ (finiteWeilPowerCovarianceUniformBenchmark_pos r).ne'
        (by simpa using h)
    have hz := neg_eq_zero.mp ((Real.exp_eq_one_iff _).mp he)
    have hkl := (mul_eq_zero.mp hz).resolve_left (by positivity)
    have hw := (Law.kl_eq_zero_iff_of_dominated hdom).mp hkl
    intro i
    change finiteWeilCanonicalJointQuadraticTiltIndexLaw r k a b d i = _
    rw [← hw, Law.uniform_apply, Fintype.card_fin]
  · intro h
    have hw : Law.uniform (Fin (r + 1)) =
        finiteWeilCanonicalJointQuadraticTiltIndexLaw r k a b d := by
      apply Law.ext
      intro i
      rw [Law.uniform_apply, Fintype.card_fin]
      exact (h i).symm
    have hkl := (Law.kl_eq_zero_iff_of_dominated hdom).mpr hw
    rw [hkl, mul_zero, neg_zero, Real.exp_zero, mul_one]

/-- Nonuniformity forces a quantitative determinant loss through the existing Pinsker bound. -/
theorem finiteWeilCanonicalJointQuadraticTilt_powerCovarianceMatrix_det_le_tv
    (r k : ℕ) (a b d : ℝ) :
    (powerCovarianceMatrix (finiteWeilCanonicalJointQuadraticTilt r k a b d : Measure E)
      (fun z : E => z 0) r).det ≤
    finiteWeilPowerCovarianceUniformBenchmark r *
      Real.exp (-(((r + 1 : ℕ) : ℝ) *
        (Law.uniform (Fin (r + 1))).tv
          (finiteWeilCanonicalJointQuadraticTiltIndexLaw r k a b d) ^ 2)) := by
  have hdom : (Law.uniform (Fin (r + 1))).dominated
      (finiteWeilCanonicalJointQuadraticTiltIndexLaw r k a b d) :=
    fun i _ => finiteWeilCanonicalJointQuadraticTiltWeight_pos r k a b d i
  rw [finiteWeilCanonicalJointQuadraticTilt_powerCovarianceMatrix_det_entropy]
  apply mul_le_mul_of_nonneg_left _ (finiteWeilPowerCovarianceUniformBenchmark_pos r).le
  apply Real.exp_le_exp.mpr
  exact neg_le_neg (mul_le_mul_of_nonneg_left (Law.tv_sq_le_kl hdom) (by positivity))

end RHTower
