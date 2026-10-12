import GaloisForLFunctions.HTGeometry.IntegralVariableDomination
import GaloisForLFunctions.RHTower.WeilLogShiftJointQuadraticLaw

/-! Every joint quadratic exponential in the full subcritical half-space has its Gaussian limit. -/

open MeasureTheory ProbabilityTheory Set Filter Topology
open GaloisForLFunctions.HTGeometry

namespace RHTower

theorem tendsto_finiteWeilCanonicalJoint_quadratic_exponential_subcritical
    (t : ℕ → ℕ) (a b : ℝ) (d : {d : ℝ // a + 2 * b + d < 2}) :
    Tendsto (fun r => ∫ z, Real.exp (finiteWeilJointQuadratic a b d.val z)
      ∂(finiteWeilCanonicalJointProbabilityLaw r (2 * (r + 1) ^ 2 + t r) :
        Measure (EuclideanSpace ℝ (Fin 2)))) atTop
          (𝓝 (Real.sqrt (2 / (2 - (a + 2 * b + d.val))))) := by
  let ε := (2 - (a + 2 * b + d.val)) / 2
  let p := a + 2 * b + d.val + ε
  let K := Real.exp (4 * (b + d.val) ^ 2 / ε + 4 * |d.val|)
  have hε : 0 < ε := by dsimp [ε]; linarith only [d.property]
  have hp : p < 2 := by dsimp [p, ε]; linarith only [d.property]
  let U := volume.restrict (Ioo (0 : ℝ) 1)
  let f := fun r u => Real.exp (finiteWeilJointQuadratic a b d.val
    (finiteWeilCanonicalJointQuantile r (2 * (r + 1) ^ 2 + t r) u))
  let F := fun u => Real.exp (finiteWeilJointQuadratic a b d.val (finiteWeilDiagonalGaussianQuantile u))
  let g := fun r u => K * Real.exp (p * quantile
    (finiteWeilCanonicalProjectedProbabilityLaw r (2 * (r + 1) ^ 2 + t r) 1 0 : Measure ℝ) u ^ 2)
  let G := fun u => K * Real.exp (p * quantile (finiteWeilProjectedGaussian 1 0 : Measure ℝ) u ^ 2)
  have hfi (r : ℕ) : Integrable (f r) U :=
    finiteWeilCanonicalJointQuantile_quadratic_exponential_integrable r _ a b d.val
  have hFi : Integrable F U :=
    (finiteWeilDiagonalGaussianQuantile_quadratic_exponential_integrable_iff a b d.val).mpr d.property
  have hgi (r : ℕ) : Integrable (g r) U :=
    (finiteWeilCanonicalProjectedIndex_quantile_quadratic_exponential_integrable r _ p).const_mul K
  have hGi0 : Integrable (fun u => Real.exp
      (p * quantile (finiteWeilProjectedGaussian 1 0 : Measure ℝ) u ^ 2)) U := by
    have h := (finiteWeilDiagonalGaussianQuantile_quadratic_exponential_integrable_iff p 0 0).mpr
      (by simpa only [mul_zero, add_zero] using hp)
    simpa only [finiteWeilDiagonalGaussianQuantile, finiteWeilJointQuadratic_diagonal,
      mul_zero, add_zero] using h
  have hGi : Integrable G U := hGi0.const_mul K
  have hdom (r : ℕ) : ∀ᵐ u ∂U, ‖f r u‖ ≤ g r u := by
    refine (ae_restrict_iff' measurableSet_Ioo).mpr (Eventually.of_forall fun u hu => ?_)
    dsimp only [f, g]
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact finiteWeilCanonicalJointQuantile_quadratic_envelope r (t r) a b d.val hε ⟨u, hu⟩
  have hint : Tendsto (fun r => ∫ u, g r u ∂U) atTop (𝓝 (∫ u, G u ∂U)) := by
    dsimp only [g, G]
    simp_rw [integral_const_mul]
    apply Tendsto.const_mul
    dsimp only [U]
    simp_rw [finiteWeil_integral_quadratic_exponential_quantile,
      finiteWeilProjectedIndexGaussian_quadratic_exponential_integral]
    exact tendsto_finiteWeilCanonicalProjectedIndex_quadratic_exponential_subcritical t ⟨p, hp⟩
  have h : Tendsto (fun r => ∫ u, f r u ∂U) atTop (𝓝 (∫ u, F u ∂U)) := by
    apply tendsto_integral_of_variable_envelope hfi hFi hdom hgi hGi
    · exact Eventually.of_forall fun _ => mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le
    · exact ae_tendsto_finiteWeilCanonicalJointQuantile_quadratic_exponential t a b d.val
    · exact (ae_tendsto_finiteWeilCanonicalProjectedIndex_quantile_quadratic_exponential t p).mono
        fun _ hu => hu.const_mul K
    · exact hint
  dsimp only [f, F, U] at h
  simpa only [finiteWeilCanonicalJointQuantile_quadratic_exponential_integral,
    finiteWeilDiagonalGaussianQuantile_quadratic_exponential_integral] using h

theorem tendsto_finiteWeilCanonicalJoint_transverse_exponential (t : ℕ → ℕ) (c : ℝ) :
    Tendsto (fun r => ∫ z : EuclideanSpace ℝ (Fin 2), Real.exp (c * (z 0 - z 1) ^ 2)
      ∂(finiteWeilCanonicalJointProbabilityLaw r (2 * (r + 1) ^ 2 + t r) : Measure _))
        atTop (𝓝 1) := by
  have h := tendsto_finiteWeilCanonicalJoint_quadratic_exponential_subcritical t c (-c)
    ⟨c, by linarith⟩
  simpa only [finiteWeilJointQuadratic_transverse, show c + 2 * -c + c = 0 by ring,
    sub_zero, div_self (by norm_num : (2 : ℝ) ≠ 0), Real.sqrt_one] using h

end RHTower
