import GaloisForLFunctions.RHTower.WeilLogShiftQuadraticTiltEquality
import GaloisForLFunctions.RHTower.WeilLogShiftQuadraticFastReplication
import GaloisForLFunctions.RHTower.WeilLogShiftQuadraticReplicationSpectrum

/-! Replication criteria expressed entirely through finite quadratic-potential witnesses. -/

open MeasureTheory ProbabilityTheory Filter Topology GaloisForLFunctions.HTGeometry
open scoped ENNReal
local notation "E" => EuclideanSpace ℝ (Fin 2)

namespace RHTower

theorem exists_finiteWeilCanonicalJointQuadraticTilt_fast_replication_iff_witness
    (k : ℕ → ℕ) (a b d A B D : ℝ) :
    (∃ m : ℕ → ℕ, Monotone m ∧ (∀ r, r ≤ m r) ∧ Tendsto m atTop atTop ∧
      Tendsto (fun r => bhattacharyya
        (Measure.pi (fun _ : Fin (m r) =>
          (finiteWeilCanonicalJointQuadraticTilt r (k r) a b d : Measure E)))
        (Measure.pi (fun _ : Fin (m r) =>
          (finiteWeilCanonicalJointQuadraticTilt r (k r) A B D : Measure E))))
        atTop (𝓝 0)) ↔ ∀ᶠ r in atTop, ∃ i : Fin (r + 1),
      finiteWeilJointQuadratic (a - A) (b - B) (d - D)
        (finiteWeilCanonicalFluctuationPoint r (k r) i) ≠
      finiteWeilJointQuadratic (a - A) (b - B) (d - D)
        (finiteWeilCanonicalFluctuationPoint r (k r) 0) := by
  simpa only [finiteWeilCanonicalJointQuadraticTilt_ne_iff_witness] using
    exists_finiteWeilCanonicalJointQuadraticTilt_fast_replication_iff k a b d A B D

theorem exists_finiteWeilCanonicalJointQuadraticTilt_replication_limit_iff_witness
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
          (q = 1 ∨ (q < 1 ∧ ∀ᶠ r in atTop, ∃ i : Fin (r + 1),
            finiteWeilJointQuadratic (a - A) (b - B) (d.val - D.val)
              (finiteWeilCanonicalFluctuationPoint r (2 * (r + 1) ^ 2 + t r) i) ≠
            finiteWeilJointQuadratic (a - A) (b - B) (d.val - D.val)
              (finiteWeilCanonicalFluctuationPoint r (2 * (r + 1) ^ 2 + t r) 0)))) := by
  simpa only [finiteWeilCanonicalJointQuadraticTilt_ne_iff_witness] using
    exists_finiteWeilCanonicalJointQuadraticTilt_replication_limit_iff t a b d A B D q

end RHTower
