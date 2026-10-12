import GaloisForLFunctions.HTGeometry.AdaptiveAffinityReplication
import GaloisForLFunctions.RHTower.WeilLogShiftQuadraticAffinityLimit

/-! Diagonal equality exactly characterizes stable adaptive replication of finite Weil tilts. -/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology GaloisForLFunctions.HTGeometry
local notation "E" => EuclideanSpace ℝ (Fin 2)

namespace RHTower

theorem exists_finiteWeilCanonicalJointQuadraticTilt_stable_replication_iff
    (t : ℕ → ℕ) (a b : ℝ) (d : {d : ℝ // a + 2 * b + d < 2})
    (A B : ℝ) (D : {D : ℝ // A + 2 * B + D < 2}) :
    (∃ m : ℕ → ℕ, Monotone m ∧ (∀ r, m r ≤ r) ∧ Tendsto m atTop atTop ∧
      Tendsto (fun r => bhattacharyya
        (Measure.pi (fun _ : Fin (m r) =>
          (finiteWeilCanonicalJointQuadraticTilt r (2 * (r + 1) ^ 2 + t r) a b d.val : Measure E)))
        (Measure.pi (fun _ : Fin (m r) =>
          (finiteWeilCanonicalJointQuadraticTilt r (2 * (r + 1) ^ 2 + t r) A B D.val : Measure E))))
        atTop (𝓝 1)) ↔ a + 2 * b + d.val = A + 2 * B + D.val := by
  constructor
  · rintro ⟨m, _, _, hm, h1⟩
    by_contra hne
    have h0 := tendsto_ennreal_powers_zero_of_tendsto_lt_one
      (tendsto_finiteWeilCanonicalJointQuadraticTilt_bhattacharyya t a b d A B D)
      (ENNReal.ofReal_lt_one.mpr ((finiteWeilQuadraticTiltAffinity_lt_one_iff _ _).mpr hne)) hm
    simp_rw [bhattacharyya_pi] at h1
    exact zero_ne_one (tendsto_nhds_unique h0 h1)
  · intro heq
    obtain ⟨m, hmono, hle, hm, hpow⟩ := exists_monotone_ennreal_powers_tendsto_one
      ((tendsto_finiteWeilCanonicalJointQuadraticTilt_bhattacharyya_one_iff t a b d A B D).mpr heq)
    refine ⟨m, hmono, hle, hm, ?_⟩
    simpa only [bhattacharyya_pi] using hpow

theorem forall_finiteWeilCanonicalJointQuadraticTilt_replication_zero_iff
    (t : ℕ → ℕ) (a b : ℝ) (d : {d : ℝ // a + 2 * b + d < 2})
    (A B : ℝ) (D : {D : ℝ // A + 2 * B + D < 2}) :
    (∀ m : ℕ → ℕ, Tendsto m atTop atTop →
      Tendsto (fun r => bhattacharyya
        (Measure.pi (fun _ : Fin (m r) =>
          (finiteWeilCanonicalJointQuadraticTilt r (2 * (r + 1) ^ 2 + t r) a b d.val : Measure E)))
        (Measure.pi (fun _ : Fin (m r) =>
          (finiteWeilCanonicalJointQuadraticTilt r (2 * (r + 1) ^ 2 + t r) A B D.val : Measure E))))
        atTop (𝓝 0)) ↔ a + 2 * b + d.val ≠ A + 2 * B + D.val := by
  constructor
  · intro hzero heq
    obtain ⟨m, _, _, hm, h1⟩ :=
      (exists_finiteWeilCanonicalJointQuadraticTilt_stable_replication_iff t a b d A B D).mpr heq
    exact zero_ne_one (tendsto_nhds_unique (hzero m hm) h1)
  · intro hne m hm
    have h0 := tendsto_ennreal_powers_zero_of_tendsto_lt_one
      (tendsto_finiteWeilCanonicalJointQuadraticTilt_bhattacharyya t a b d A B D)
      (ENNReal.ofReal_lt_one.mpr ((finiteWeilQuadraticTiltAffinity_lt_one_iff _ _).mpr hne)) hm
    simpa only [bhattacharyya_pi] using h0

end RHTower
