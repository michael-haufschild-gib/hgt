import GaloisForLFunctions.RHTower.WeilLogShiftQuadraticTiltLaw

/-! # Explicit positive weights of every finite quadratic tilt -/

namespace RHTower

open MeasureTheory
open scoped BigOperators

noncomputable section

local notation "E" => EuclideanSpace ℝ (Fin 2)

def finiteWeilCanonicalJointQuadraticTiltWeight (r k : ℕ) (a b d : ℝ)
    (i : Fin (r + 1)) : ℝ :=
  (finiteWeilCanonicalEdgeMass r k i *
    Real.exp (finiteWeilJointQuadratic a b d (finiteWeilCanonicalFluctuationPoint r k i))) /
  ∑ j, finiteWeilCanonicalEdgeMass r k j *
    Real.exp (finiteWeilJointQuadratic a b d (finiteWeilCanonicalFluctuationPoint r k j))

theorem finiteWeilCanonicalJointQuadraticTiltWeight_pos
    (r k : ℕ) (a b d : ℝ) (i : Fin (r + 1)) :
    0 < finiteWeilCanonicalJointQuadraticTiltWeight r k a b d i := by
  apply div_pos (mul_pos (finiteWeilCanonicalEdgeMass_pos r k i) (Real.exp_pos _))
  exact Finset.sum_pos
    (fun j _ => mul_pos (finiteWeilCanonicalEdgeMass_pos r k j) (Real.exp_pos _))
    Finset.univ_nonempty

/-- Every real observable has its exact finite weighted-sum formula. -/
theorem finiteWeilCanonicalJointQuadraticTilt_integral_sum
    (r k : ℕ) (a b d : ℝ) (f : E → ℝ) :
    (∫ z, f z ∂(finiteWeilCanonicalJointQuadraticTilt r k a b d : Measure E)) =
      ∑ i, finiteWeilCanonicalJointQuadraticTiltWeight r k a b d i *
        f (finiteWeilCanonicalFluctuationPoint r k i) := by
  rw [finiteWeilCanonicalJointQuadraticTilt_integral]
  simp only [finiteWeilCanonicalJointProbabilityLaw,
    finiteWeilCanonicalObservableLaw_integral_real]
  simp only [finiteWeilCanonicalJointQuadraticTiltWeight, div_mul_eq_mul_div]
  rw [← Finset.sum_div]
  congr 1
  exact Finset.sum_congr rfl fun i _ => by ring

theorem finiteWeilCanonicalJointQuadraticTiltWeight_sum
    (r k : ℕ) (a b d : ℝ) :
    ∑ i, finiteWeilCanonicalJointQuadraticTiltWeight r k a b d i = 1 := by
  have h := finiteWeilCanonicalJointQuadraticTilt_integral_sum r k a b d (fun _ => 1)
  simpa using h.symm

end

end RHTower
