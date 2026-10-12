import GaloisForLFunctions.HTGeometry.IntegralFatouDivergence
import GaloisForLFunctions.RHTower.WeilLogShiftJointQuadraticLimit

/-! The entire quadratic exponential phase diagram is determined by the diagonal coefficient. -/

open MeasureTheory ProbabilityTheory Set Filter Topology
open GaloisForLFunctions.HTGeometry

namespace RHTower

theorem tendsto_finiteWeilCanonicalJoint_quadratic_exponential_critical
    (t : ℕ → ℕ) (a b : ℝ) (d : {d : ℝ // 2 ≤ a + 2 * b + d}) :
    Tendsto (fun r => ∫ z, Real.exp (finiteWeilJointQuadratic a b d.val z)
      ∂(finiteWeilCanonicalJointProbabilityLaw r (2 * (r + 1) ^ 2 + t r) :
        Measure (EuclideanSpace ℝ (Fin 2)))) atTop atTop := by
  let F := fun r u => Real.exp (finiteWeilJointQuadratic a b d.val
    (finiteWeilCanonicalJointQuantile r (2 * (r + 1) ^ 2 + t r) u))
  let G := fun u => Real.exp (finiteWeilJointQuadratic a b d.val (finiteWeilDiagonalGaussianQuantile u))
  have hGm : AEStronglyMeasurable G (volume.restrict (Ioo (0 : ℝ) 1)) :=
    ((Real.continuous_exp.comp (continuous_finiteWeilJointQuadratic a b d.val)).measurable.comp
      finiteWeilDiagonalGaussianQuantile_measurable).aestronglyMeasurable
  have hG : ¬ Integrable G (volume.restrict (Ioo (0 : ℝ) 1)) := by
    intro hi
    exact (not_lt_of_ge d.property)
      ((finiteWeilDiagonalGaussianQuantile_quadratic_exponential_integrable_iff a b d.val).mp hi)
  have h := tendsto_integral_atTop_of_ae_nonnegative_nonintegrable_limit
    (μ := volume.restrict (Ioo (0 : ℝ) 1)) (f := F) (g := G)
    (fun r => finiteWeilCanonicalJointQuantile_quadratic_exponential_integrable
      r (2 * (r + 1) ^ 2 + t r) a b d.val)
    (fun _ => Eventually.of_forall fun _ => (Real.exp_pos _).le)
    hGm (Eventually.of_forall fun _ => (Real.exp_pos _).le) hG
    (ae_tendsto_finiteWeilCanonicalJointQuantile_quadratic_exponential t a b d.val)
  dsimp only [F] at h
  simpa only [finiteWeilCanonicalJointQuantile_quadratic_exponential_integral] using h

theorem tendsto_finiteWeilCanonicalJoint_quadratic_exponential_extended
    (t : ℕ → ℕ) (a b d : ℝ) :
    Tendsto (fun r => ∫⁻ z, ENNReal.ofReal (Real.exp (finiteWeilJointQuadratic a b d z))
      ∂(finiteWeilCanonicalJointProbabilityLaw r (2 * (r + 1) ^ 2 + t r) :
        Measure (EuclideanSpace ℝ (Fin 2)))) atTop
      (𝓝 (if a + 2 * b + d < 2 then ENNReal.ofReal (Real.sqrt (2 / (2 - (a + 2 * b + d)))) else ⊤)) := by
  have h : Tendsto (fun r => ENNReal.ofReal (∫ z, Real.exp (finiteWeilJointQuadratic a b d z)
      ∂(finiteWeilCanonicalJointProbabilityLaw r (2 * (r + 1) ^ 2 + t r) :
        Measure (EuclideanSpace ℝ (Fin 2))))) atTop
      (𝓝 (if a + 2 * b + d < 2 then ENNReal.ofReal (Real.sqrt (2 / (2 - (a + 2 * b + d)))) else ⊤)) := by
    by_cases hd : a + 2 * b + d < 2
    · rw [if_pos hd]
      exact (ENNReal.continuous_ofReal.tendsto _).comp
        (tendsto_finiteWeilCanonicalJoint_quadratic_exponential_subcritical t a b ⟨d, hd⟩)
    · rw [if_neg hd]
      exact ENNReal.tendsto_ofReal_atTop.comp
        (tendsto_finiteWeilCanonicalJoint_quadratic_exponential_critical t a b ⟨d, le_of_not_gt hd⟩)
  exact h.congr fun r => ofReal_integral_eq_lintegral_ofReal
    (finiteWeilCanonicalJoint_quadratic_exponential_integrable r _ a b d)
    (Eventually.of_forall fun _ => (Real.exp_pos _).le)

theorem bddAbove_finiteWeilCanonicalJoint_quadratic_exponential_iff
    (t : ℕ → ℕ) (a b d : ℝ) :
    BddAbove (range (fun r => ∫ z, Real.exp (finiteWeilJointQuadratic a b d z)
      ∂(finiteWeilCanonicalJointProbabilityLaw r (2 * (r + 1) ^ 2 + t r) :
        Measure (EuclideanSpace ℝ (Fin 2))))) ↔ a + 2 * b + d < 2 := by
  constructor
  · intro h
    by_contra hd
    exact (not_bddAbove_of_tendsto_atTop
      (tendsto_finiteWeilCanonicalJoint_quadratic_exponential_critical t a b ⟨d, le_of_not_gt hd⟩)) h
  · intro hd
    exact (tendsto_finiteWeilCanonicalJoint_quadratic_exponential_subcritical t a b
      ⟨d, hd⟩).isBoundedUnder_le.bddAbove_range

theorem bddAbove_finiteWeilCanonicalJoint_radial_exponential_iff (t : ℕ → ℕ) (c : ℝ) :
    BddAbove (range (fun r => ∫ z : EuclideanSpace ℝ (Fin 2), Real.exp (c * ‖z‖ ^ 2)
      ∂(finiteWeilCanonicalJointProbabilityLaw r (2 * (r + 1) ^ 2 + t r) : Measure _))) ↔ c < 1 := by
  have h := bddAbove_finiteWeilCanonicalJoint_quadratic_exponential_iff t c 0 c
  simp only [finiteWeilJointQuadratic_radial, mul_zero, add_zero] at h
  exact h.trans (by constructor <;> intro hc <;> linarith)

end RHTower
