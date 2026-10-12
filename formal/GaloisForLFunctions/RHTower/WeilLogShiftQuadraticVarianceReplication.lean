import GaloisForLFunctions.RHTower.WeilLogShiftQuadraticVarianceRigidity
import GaloisForLFunctions.RHTower.WeilLogShiftQuadraticFastReplication

/-! Positive variance under arbitrary changing probe tilts exactly detects fast separating replication. -/

open MeasureTheory ProbabilityTheory Filter Topology GaloisForLFunctions.HTGeometry
local notation "E" => EuclideanSpace ℝ (Fin 2)

namespace RHTower

theorem exists_finiteWeilCanonicalJointQuadraticTilt_fast_replication_iff_variance
    (k : ℕ → ℕ) (a b d A B D : ℝ) (u v w : ℕ → ℝ) :
    (∃ m : ℕ → ℕ, Monotone m ∧ (∀ r, r ≤ m r) ∧ Tendsto m atTop atTop ∧
      Tendsto (fun r => bhattacharyya
        (Measure.pi (fun _ : Fin (m r) =>
          (finiteWeilCanonicalJointQuadraticTilt r (k r) a b d : Measure E)))
        (Measure.pi (fun _ : Fin (m r) =>
          (finiteWeilCanonicalJointQuadraticTilt r (k r) A B D : Measure E))))
        atTop (𝓝 0)) ↔ ∀ᶠ r in atTop,
      0 < variance (finiteWeilJointQuadratic (a - A) (b - B) (d - D))
        (finiteWeilCanonicalJointQuadraticTilt r (k r) (u r) (v r) (w r) : Measure E) := by
  rw [exists_finiteWeilCanonicalJointQuadraticTilt_fast_replication_iff]
  constructor
  · intro h
    exact h.mono fun r hr =>
      (finiteWeilCanonicalJointQuadraticTilt_ne_iff_variance_pos
        r (k r) a b d A B D (u r) (v r) (w r)).mp hr
  · intro h
    exact h.mono fun r hr =>
      (finiteWeilCanonicalJointQuadraticTilt_ne_iff_variance_pos
        r (k r) a b d A B D (u r) (v r) (w r)).mpr hr

end RHTower
