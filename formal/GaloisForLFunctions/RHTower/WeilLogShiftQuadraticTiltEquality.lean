import GaloisForLFunctions.HTGeometry.TiltedEqualityRigidity
import GaloisForLFunctions.RHTower.WeilLogShiftObservableSupport
import GaloisForLFunctions.RHTower.WeilLogShiftQuadraticTiltLaw

/-! Exact finite quadratic-potential tests for equality of the actual tilted laws. -/

open MeasureTheory GaloisForLFunctions.HTGeometry
local notation "E" => EuclideanSpace ℝ (Fin 2)

namespace RHTower

theorem finiteWeilCanonicalJointQuadraticTilt_eq_iff_constant
    (r k : ℕ) (a b d A B D : ℝ) :
    (finiteWeilCanonicalJointQuadraticTilt r k a b d : Measure E) =
      (finiteWeilCanonicalJointQuadraticTilt r k A B D : Measure E) ↔
        ∃ c : ℝ, ∀ i : Fin (r + 1),
          finiteWeilJointQuadratic (a - A) (b - B) (d - D)
            (finiteWeilCanonicalFluctuationPoint r k i) = c := by
  have hdiff (z : E) : finiteWeilJointQuadratic a b d z -
      finiteWeilJointQuadratic A B D z = finiteWeilJointQuadratic (a - A) (b - B) (d - D) z := by
    simp only [finiteWeilJointQuadratic]
    ring
  change (finiteWeilCanonicalJointProbabilityLaw r k : Measure E).tilted
    (finiteWeilJointQuadratic a b d) =
      (finiteWeilCanonicalJointProbabilityLaw r k : Measure E).tilted
        (finiteWeilJointQuadratic A B D) ↔ _
  rw [tilted_eq_iff_sub_ae_const _ _ _
    (finiteWeilCanonicalJoint_quadratic_exponential_integrable r k a b d)
    (finiteWeilCanonicalJoint_quadratic_exponential_integrable r k A B D)]
  simp only [finiteWeilCanonicalJointProbabilityLaw,
    finiteWeilCanonicalObservableLaw_ae_iff, hdiff]

theorem finiteWeilCanonicalJointQuadraticTilt_eq_iff_values
    (r k : ℕ) (a b d A B D : ℝ) :
    (finiteWeilCanonicalJointQuadraticTilt r k a b d : Measure E) =
      (finiteWeilCanonicalJointQuadraticTilt r k A B D : Measure E) ↔
        ∀ i : Fin (r + 1),
          finiteWeilJointQuadratic (a - A) (b - B) (d - D)
            (finiteWeilCanonicalFluctuationPoint r k i) =
          finiteWeilJointQuadratic (a - A) (b - B) (d - D)
            (finiteWeilCanonicalFluctuationPoint r k 0) := by
  rw [finiteWeilCanonicalJointQuadraticTilt_eq_iff_constant]
  constructor
  · rintro ⟨c, hc⟩ i
    exact (hc i).trans (hc 0).symm
  · intro h
    exact ⟨_, h⟩

theorem finiteWeilCanonicalJointQuadraticTilt_ne_iff_witness
    (r k : ℕ) (a b d A B D : ℝ) :
    (finiteWeilCanonicalJointQuadraticTilt r k a b d : Measure E) ≠
      (finiteWeilCanonicalJointQuadraticTilt r k A B D : Measure E) ↔
        ∃ i : Fin (r + 1),
          finiteWeilJointQuadratic (a - A) (b - B) (d - D)
            (finiteWeilCanonicalFluctuationPoint r k i) ≠
          finiteWeilJointQuadratic (a - A) (b - B) (d - D)
            (finiteWeilCanonicalFluctuationPoint r k 0) := by
  classical
  simpa only [not_forall] using
    not_congr (finiteWeilCanonicalJointQuadraticTilt_eq_iff_values r k a b d A B D)

end RHTower
