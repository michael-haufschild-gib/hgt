import GaloisForLFunctions.RHTower.WeilLogShiftQuadraticTiltMomentBounds
import GaloisForLFunctions.RHTower.WeilLogShiftQuadraticTiltLimit
import GaloisForLFunctions.HTGeometry.WeakContinuousMomentTransfer

/-! Every mixed moment of the actual tilted law converges; its full covariance has an explicit rank-one limit. -/

open MeasureTheory ProbabilityTheory Set Filter Topology
open GaloisForLFunctions.HTGeometry

namespace RHTower

theorem tendsto_finiteWeilCanonicalJointQuadraticTilt_mixed_moment
    (t : ℕ → ℕ) (a b : ℝ) (d : {d : ℝ // a + 2 * b + d < 2}) (p q : ℕ) :
    Tendsto (fun r => ∫ z : EuclideanSpace ℝ (Fin 2), z 0 ^ p * z 1 ^ q
      ∂(finiteWeilCanonicalJointQuadraticTilt r (2 * (r + 1) ^ 2 + t r) a b d.val : Measure _))
        atTop (𝓝 (∫ x : ℝ, x ^ (p + q) ∂(gaussianReal 0
          (finiteWeilQuadraticTiltVariance ⟨a + 2 * b + d.val, d.property⟩)))) := by
  obtain ⟨C, hC⟩ := bddAbove_finiteWeilCanonicalJointQuadraticTilt_mixed_square t a b d p q
  have h := tendsto_integral_continuous_of_uniform_square_bound
    (tendsto_finiteWeilCanonicalJointQuadraticTilt_gaussian t a b d)
    (f := fun z : EuclideanSpace ℝ (Fin 2) => z 0 ^ p * z 1 ^ q) (by fun_prop)
    (fun r => finiteWeilCanonicalJointQuadraticTilt_integrable r _ a b d.val _)
    (finiteWeilQuadraticTiltGaussian_mixed_square_integrable
      ⟨a + 2 * b + d.val, d.property⟩ p q)
    (C := C) (Eventually.of_forall fun r => hC ⟨r, rfl⟩)
  simpa only [finiteWeilQuadraticTiltGaussian_mixed_pow_integral] using h

theorem tendsto_finiteWeilCanonicalJointQuadraticTilt_mean_zero
    (t : ℕ → ℕ) (a b : ℝ) (d : {d : ℝ // a + 2 * b + d < 2}) (i : Fin 2) :
    Tendsto (fun r => ∫ z : EuclideanSpace ℝ (Fin 2), z i
      ∂(finiteWeilCanonicalJointQuadraticTilt r (2 * (r + 1) ^ 2 + t r) a b d.val : Measure _))
        atTop (𝓝 0) := by
  fin_cases i
  · simpa using tendsto_finiteWeilCanonicalJointQuadraticTilt_mixed_moment t a b d 1 0
  · simpa using tendsto_finiteWeilCanonicalJointQuadraticTilt_mixed_moment t a b d 0 1

theorem tendsto_finiteWeilCanonicalJointQuadraticTilt_second_moment
    (t : ℕ → ℕ) (a b : ℝ) (d : {d : ℝ // a + 2 * b + d < 2}) (i j : Fin 2) :
    Tendsto (fun r => ∫ z : EuclideanSpace ℝ (Fin 2), z i * z j
      ∂(finiteWeilCanonicalJointQuadraticTilt r (2 * (r + 1) ^ 2 + t r) a b d.val : Measure _))
        atTop (𝓝 (1 / (4 - 2 * (a + 2 * b + d.val)))) := by
  have h00 := tendsto_finiteWeilCanonicalJointQuadraticTilt_mixed_moment t a b d 2 0
  have h01 := tendsto_finiteWeilCanonicalJointQuadraticTilt_mixed_moment t a b d 1 1
  have h11 := tendsto_finiteWeilCanonicalJointQuadraticTilt_mixed_moment t a b d 0 2
  norm_num only [gaussianZero_integral_sq] at h00 h01 h11
  have hvar : (finiteWeilQuadraticTiltVariance ⟨a + 2 * b + d.val, d.property⟩ : ℝ) =
      1 / (4 - 2 * (a + 2 * b + d.val)) := rfl
  rw [hvar] at h00 h01 h11
  fin_cases i <;> fin_cases j
  · simpa [sq] using h00
  · simpa using h01
  · simpa [mul_comm] using h01
  · simpa [sq] using h11

theorem tendsto_finiteWeilCanonicalJointQuadraticTilt_covariance
    (t : ℕ → ℕ) (a b : ℝ) (d : {d : ℝ // a + 2 * b + d < 2}) (i j : Fin 2) :
    Tendsto (fun r => covariance (fun z : EuclideanSpace ℝ (Fin 2) => z i) (fun z => z j)
      (finiteWeilCanonicalJointQuadraticTilt r (2 * (r + 1) ^ 2 + t r) a b d.val : Measure _))
        atTop (𝓝 (1 / (4 - 2 * (a + 2 * b + d.val)))) := by
  have hmem (r : ℕ) (k : Fin 2) : MemLp (fun z : EuclideanSpace ℝ (Fin 2) => z k) 2
      (finiteWeilCanonicalJointQuadraticTilt r (2 * (r + 1) ^ 2 + t r) a b d.val : Measure _) :=
    (memLp_two_iff_integrable_sq (by fun_prop)).mpr
      (finiteWeilCanonicalJointQuadraticTilt_integrable r _ a b d.val _)
  have h := (tendsto_finiteWeilCanonicalJointQuadraticTilt_second_moment t a b d i j).sub
    ((tendsto_finiteWeilCanonicalJointQuadraticTilt_mean_zero t a b d i).mul
      (tendsto_finiteWeilCanonicalJointQuadraticTilt_mean_zero t a b d j))
  simp only [mul_zero, sub_zero] at h
  exact h.congr fun r => (covariance_eq_sub (hmem r i) (hmem r j)).symm

end RHTower
