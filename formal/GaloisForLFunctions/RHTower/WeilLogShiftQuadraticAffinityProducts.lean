import GaloisForLFunctions.RHTower.WeilLogShiftQuadraticAffinityLimit
import GaloisForLFunctions.RHTower.WeilLogShiftQuadraticTiltEntropyLimit

/-! Independent products separate distinct diagonal tilts; affinity records symmetric KL. -/

noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory Filter Topology GaloisForLFunctions.HTGeometry
local notation "E" => EuclideanSpace ℝ (Fin 2)

namespace RHTower

theorem tendsto_finiteWeilCanonicalJointQuadraticTilt_product_bhattacharyya
    (n : ℕ) (t : ℕ → ℕ) (a b : ℝ) (d : {d : ℝ // a + 2 * b + d < 2})
    (A B : ℝ) (D : {D : ℝ // A + 2 * B + D < 2}) :
    Tendsto (fun r => bhattacharyya
      (Measure.pi (fun _ : Fin n =>
        (finiteWeilCanonicalJointQuadraticTilt r (2 * (r + 1) ^ 2 + t r) a b d.val : Measure E)))
      (Measure.pi (fun _ : Fin n =>
        (finiteWeilCanonicalJointQuadraticTilt r (2 * (r + 1) ^ 2 + t r) A B D.val : Measure E))))
      atTop (𝓝 (ENNReal.ofReal (finiteWeilQuadraticTiltAffinity
        ⟨a + 2 * b + d.val, d.property⟩ ⟨A + 2 * B + D.val, D.property⟩) ^ n)) := by
  simp_rw [bhattacharyya_pi]
  exact (ENNReal.continuous_pow n).tendsto _ |>.comp
    (tendsto_finiteWeilCanonicalJointQuadraticTilt_bhattacharyya t a b d A B D)

theorem tendsto_finiteWeilCanonicalJointQuadraticTilt_growing_product_bhattacharyya_zero
    (t : ℕ → ℕ) (a b : ℝ) (d : {d : ℝ // a + 2 * b + d < 2})
    (A B : ℝ) (D : {D : ℝ // A + 2 * B + D < 2 ∧
      a + 2 * b + d.val ≠ A + 2 * B + D}) :
    Tendsto (fun r => bhattacharyya
      (Measure.pi (fun _ : Fin r =>
        (finiteWeilCanonicalJointQuadraticTilt r (2 * (r + 1) ^ 2 + t r) a b d.val : Measure E)))
      (Measure.pi (fun _ : Fin r =>
        (finiteWeilCanonicalJointQuadraticTilt r (2 * (r + 1) ^ 2 + t r) A B D.val : Measure E))))
      atTop (𝓝 0) := by
  simp_rw [bhattacharyya_pi]
  apply tendsto_varying_ennreal_pow_zero
    (tendsto_finiteWeilCanonicalJointQuadraticTilt_bhattacharyya t a b d A B ⟨D.val, D.property.1⟩)
  exact ENNReal.ofReal_lt_one.mpr
    ((finiteWeilQuadraticTiltAffinity_lt_one_iff _ _).mpr D.property.2)

theorem tendsto_finiteWeilCanonicalJointQuadraticTilt_affinity_jeffreys
    (t : ℕ → ℕ) (a b : ℝ) (d : {d : ℝ // a + 2 * b + d < 2})
    (A B : ℝ) (D : {D : ℝ // A + 2 * B + D < 2}) :
    Tendsto (fun r =>
      (bhattacharyya
        (finiteWeilCanonicalJointQuadraticTilt r (2 * (r + 1) ^ 2 + t r) a b d.val : Measure E)
        (finiteWeilCanonicalJointQuadraticTilt r (2 * (r + 1) ^ 2 + t r) A B D.val : Measure E)).toReal ^ 4 *
      (1 + ((klDiv
        (finiteWeilCanonicalJointQuadraticTilt r (2 * (r + 1) ^ 2 + t r) a b d.val : Measure E)
        (finiteWeilCanonicalJointQuadraticTilt r (2 * (r + 1) ^ 2 + t r) A B D.val : Measure E)).toReal +
        (klDiv
          (finiteWeilCanonicalJointQuadraticTilt r (2 * (r + 1) ^ 2 + t r) A B D.val : Measure E)
          (finiteWeilCanonicalJointQuadraticTilt r (2 * (r + 1) ^ 2 + t r) a b d.val : Measure E)).toReal) / 2))
      atTop (𝓝 1) := by
  have hH := tendsto_finiteWeilCanonicalJointQuadraticTilt_bhattacharyya_toReal t a b d A B D
  have hJ := tendsto_finiteWeilCanonicalJointQuadraticTilt_symmetric_klDiv t a b d A B D
  have h1 : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
  have h := (hH.pow 4).mul (h1.add (hJ.div_const 2))
  rw [finiteWeilQuadraticTiltAffinity_jeffreys
    ⟨a + 2 * b + d.val, d.property⟩ ⟨A + 2 * B + D.val, D.property⟩] at h
  exact h

end RHTower
