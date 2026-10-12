import GaloisForLFunctions.HTGeometry.FastAffinityReplication
import GaloisForLFunctions.HTGeometry.ProbabilityAffinityRigidity
import GaloisForLFunctions.RHTower.WeilLogShiftQuadraticTiltLaw

/-! Eventual finite-law inequality exactly characterizes fast separating replication. -/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology GaloisForLFunctions.HTGeometry
local notation "E" => EuclideanSpace ℝ (Fin 2)

namespace RHTower

theorem finiteWeilCanonicalJointQuadraticTilt_bhattacharyya_eq_one_iff
    (r k : ℕ) (a b d A B D : ℝ) :
    bhattacharyya (finiteWeilCanonicalJointQuadraticTilt r k a b d : Measure E)
      (finiteWeilCanonicalJointQuadraticTilt r k A B D : Measure E) = 1 ↔
        (finiteWeilCanonicalJointQuadraticTilt r k a b d : Measure E) =
          (finiteWeilCanonicalJointQuadraticTilt r k A B D : Measure E) :=
  bhattacharyya_eq_one_iff _ _

theorem exists_finiteWeilCanonicalJointQuadraticTilt_fast_replication_iff
    (k : ℕ → ℕ) (a b d A B D : ℝ) :
    (∃ m : ℕ → ℕ, Monotone m ∧ (∀ r, r ≤ m r) ∧ Tendsto m atTop atTop ∧
      Tendsto (fun r => bhattacharyya
        (Measure.pi (fun _ : Fin (m r) =>
          (finiteWeilCanonicalJointQuadraticTilt r (k r) a b d : Measure E)))
        (Measure.pi (fun _ : Fin (m r) =>
          (finiteWeilCanonicalJointQuadraticTilt r (k r) A B D : Measure E))))
        atTop (𝓝 0)) ↔ ∀ᶠ r in atTop,
      (finiteWeilCanonicalJointQuadraticTilt r (k r) a b d : Measure E) ≠
        (finiteWeilCanonicalJointQuadraticTilt r (k r) A B D : Measure E) := by
  have h := exists_monotone_ennreal_fast_powers_zero_iff (fun r =>
    bhattacharyya (finiteWeilCanonicalJointQuadraticTilt r (k r) a b d : Measure E)
      (finiteWeilCanonicalJointQuadraticTilt r (k r) A B D : Measure E))
  simpa only [bhattacharyya_pi, bhattacharyya_lt_one_iff] using h

end RHTower
