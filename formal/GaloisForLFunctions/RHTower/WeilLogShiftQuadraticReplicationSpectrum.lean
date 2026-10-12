import GaloisForLFunctions.HTGeometry.AffinityReplicationSpectrum
import GaloisForLFunctions.HTGeometry.ProbabilityAffinityRigidity
import GaloisForLFunctions.RHTower.WeilLogShiftQuadraticAffinityLimit

/-! Exact attainable replication limits of the actual finite Weil quadratic tilted laws. -/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology GaloisForLFunctions.HTGeometry
open scoped ENNReal
local notation "E" => EuclideanSpace ℝ (Fin 2)

namespace RHTower

theorem exists_finiteWeilCanonicalJointQuadraticTilt_replication_limit_iff
    (t : ℕ → ℕ) (a b : ℝ) (d : {d : ℝ // a + 2 * b + d < 2})
    (A B : ℝ) (D : {D : ℝ // A + 2 * B + D < 2}) (q : ℝ≥0∞) :
    (∃ m : ℕ → ℕ, Tendsto m atTop atTop ∧
      Tendsto (fun r => bhattacharyya
        (Measure.pi (fun _ : Fin (m r) =>
          (finiteWeilCanonicalJointQuadraticTilt r (2 * (r + 1) ^ 2 + t r) a b d.val : Measure E)))
        (Measure.pi (fun _ : Fin (m r) =>
          (finiteWeilCanonicalJointQuadraticTilt r (2 * (r + 1) ^ 2 + t r) A B D.val : Measure E))))
        atTop (𝓝 q)) ↔
      (a + 2 * b + d.val ≠ A + 2 * B + D.val ∧ q = 0) ∨
        (a + 2 * b + d.val = A + 2 * B + D.val ∧
          (q = 1 ∨ (q < 1 ∧ ∀ᶠ r in atTop,
            (finiteWeilCanonicalJointQuadraticTilt r (2 * (r + 1) ^ 2 + t r) a b d.val : Measure E) ≠
              (finiteWeilCanonicalJointQuadraticTilt r (2 * (r + 1) ^ 2 + t r) A B D.val : Measure E)))) := by
  have h := exists_ennreal_powers_tendsto_iff (q := q)
    (fun r => bhattacharyya_le_one
      (finiteWeilCanonicalJointQuadraticTilt r (2 * (r + 1) ^ 2 + t r) a b d.val : Measure E)
      (finiteWeilCanonicalJointQuadraticTilt r (2 * (r + 1) ^ 2 + t r) A B D.val : Measure E))
    (tendsto_finiteWeilCanonicalJointQuadraticTilt_bhattacharyya t a b d A B D)
  simpa only [bhattacharyya_pi, ENNReal.ofReal_lt_one, ENNReal.ofReal_eq_one,
    finiteWeilQuadraticTiltAffinity_lt_one_iff, finiteWeilQuadraticTiltAffinity_eq_one_iff,
    bhattacharyya_lt_one_iff] using h

end RHTower
