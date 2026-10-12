import GaloisForLFunctions.HTGeometry.VarianceGaugeRigidity
import GaloisForLFunctions.RHTower.WeilLogShiftObservableSupport
import GaloisForLFunctions.RHTower.WeilLogShiftQuadraticTiltResponse

/-! Every finite quadratic tilt has the same almost-everywhere predicates and zero-variance observables. -/

open MeasureTheory ProbabilityTheory GaloisForLFunctions.HTGeometry
local notation "E" => EuclideanSpace ℝ (Fin 2)

namespace RHTower

theorem finiteWeilCanonicalJointQuadraticTilt_ae_iff
    (r k : ℕ) (a b d : ℝ) (p : E → Prop) :
    (∀ᵐ z ∂(finiteWeilCanonicalJointQuadraticTilt r k a b d : Measure E), p z) ↔
      ∀ i, p (finiteWeilCanonicalFluctuationPoint r k i) := by
  have hbase := finiteWeilCanonicalObservableLaw_ae_iff r k
    (finiteWeilCanonicalFluctuationPoint r k) p
  constructor
  · intro hp
    exact hbase.mp ((absolutelyContinuous_tilted
      (finiteWeilCanonicalJoint_quadratic_exponential_integrable r k a b d)).ae_le hp)
  · intro hp
    exact (tilted_absolutelyContinuous
      (finiteWeilCanonicalJointProbabilityLaw r k : Measure E)
      (finiteWeilJointQuadratic a b d)).ae_le (hbase.mpr hp)

theorem finiteWeilCanonicalJointQuadraticTilt_memLp_two
    (r k : ℕ) (a b d : ℝ) (f : E → ℝ) :
    MemLp f 2 (finiteWeilCanonicalJointQuadraticTilt r k a b d : Measure E) :=
  (memLp_two_iff_integrable_sq
    (finiteWeilCanonicalJointQuadraticTilt_integrable r k a b d f).aestronglyMeasurable).mpr
    (finiteWeilCanonicalJointQuadraticTilt_integrable r k a b d (fun z => f z ^ 2))

theorem finiteWeilCanonicalJointQuadraticTilt_variance_eq_zero_iff_values
    (r k : ℕ) (a b d : ℝ) (f : E → ℝ) :
    variance f (finiteWeilCanonicalJointQuadraticTilt r k a b d : Measure E) = 0 ↔
      ∀ i, f (finiteWeilCanonicalFluctuationPoint r k i) =
        f (finiteWeilCanonicalFluctuationPoint r k 0) := by
  rw [variance_eq_zero_iff_ae_const (finiteWeilCanonicalJointQuadraticTilt_memLp_two r k a b d f)]
  simp only [finiteWeilCanonicalJointQuadraticTilt_ae_iff]
  constructor
  · rintro ⟨c, hc⟩ i
    exact (hc i).trans (hc 0).symm
  · intro h
    exact ⟨_, h⟩

theorem finiteWeilCanonicalJointQuadraticTilt_variance_eq_zero_iff
    (r k : ℕ) (a b d A B D : ℝ) (f : E → ℝ) :
    variance f (finiteWeilCanonicalJointQuadraticTilt r k a b d : Measure E) = 0 ↔
      variance f (finiteWeilCanonicalJointQuadraticTilt r k A B D : Measure E) = 0 :=
  (finiteWeilCanonicalJointQuadraticTilt_variance_eq_zero_iff_values r k a b d f).trans
    (finiteWeilCanonicalJointQuadraticTilt_variance_eq_zero_iff_values r k A B D f).symm

end RHTower
