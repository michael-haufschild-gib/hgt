import GaloisForLFunctions.RHTower.WeilLogShiftProjectedMomentBounds
import GaloisForLFunctions.HTGeometry.MomentConvergence

/-! Every integer moment of the actual centered index law converges to its Gaussian moment. -/

open MeasureTheory ProbabilityTheory Filter Topology

namespace RHTower

theorem finiteWeilProjectedGaussian_integrable_abs_pow (a b : ℝ) (p : ℕ) :
    Integrable (fun x : ℝ => |x| ^ p) (finiteWeilProjectedGaussian a b : Measure ℝ) := by
  by_cases hp : p = 0
  · subst p
    simpa only [pow_zero] using
      (integrable_const (1 : ℝ) : Integrable (fun _ : ℝ => (1 : ℝ))
        (finiteWeilProjectedGaussian a b : Measure ℝ))
  have hmem : MemLp (id : ℝ → ℝ) (p : ENNReal) (finiteWeilProjectedGaussian a b : Measure ℝ) := by
    simpa [finiteWeilProjectedGaussian] using (memLp_id_gaussianReal (μ := 0)
      (v := NNReal.mk ((a + b) ^ 2 / 4) (by positivity)) (p : NNReal))
  simpa only [id_eq, Real.norm_eq_abs] using hmem.integrable_norm_pow hp

theorem finiteWeilProjectedGaussian_integrable_pow (a b : ℝ) (p : ℕ) :
    Integrable (fun x : ℝ => x ^ p) (finiteWeilProjectedGaussian a b : Measure ℝ) := by
  apply (finiteWeilProjectedGaussian_integrable_abs_pow a b p).mono'
    (continuous_pow p).aestronglyMeasurable
  exact Eventually.of_forall fun x => by simp only [Real.norm_eq_abs, abs_pow, le_refl]

theorem tendsto_finiteWeilCanonicalProjectedIndex_moment (t : ℕ → ℕ) (p : ℕ) :
    Tendsto (fun r => ∫ x : ℝ, x ^ p
      ∂(finiteWeilCanonicalProjectedProbabilityLaw r (2 * (r + 1) ^ 2 + t r) 1 0 : Measure ℝ))
      atTop (𝓝 (∫ x : ℝ, x ^ p ∂(finiteWeilProjectedGaussian 1 0 : Measure ℝ))) := by
  by_cases hp : p = 0
  · subst p
    simp
  let B := ((2 * p).factorial : ℝ) * (8 * Real.exp (9 / 8 : ℝ))
  let G := ∫ x : ℝ, x ^ (2 * p) ∂(finiteWeilProjectedGaussian 1 0 : Measure ℝ)
  apply HTGeometry.tendsto_integral_pow_of_uniform_even_moment (by omega : 1 ≤ p)
    (M := max B G)
  · exact ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp
      (tendsto_finiteWeilCanonicalProjectedProbabilityLaw_gaussian t 1 0)
  · exact Eventually.of_forall fun r => (by
      have h : (∫ x : ℝ, x ^ (2 * p)
          ∂(finiteWeilCanonicalProjectedProbabilityLaw r (2 * (r + 1) ^ 2 + t r) 1 0 : Measure ℝ)) ≤ B := by
        simpa only [B, pow_mul, sq_abs] using
          finiteWeilCanonicalProjectedIndex_abs_moment_bound r (t r) (2 * p)
      exact h.trans (le_max_left _ _))
  · exact le_max_right _ _
  · intro r
    exact finiteWeilCanonicalProjectedProbabilityLaw_integrable _ _ _ _ _
  · intro r
    exact finiteWeilCanonicalProjectedProbabilityLaw_integrable _ _ _ _ _
  · intro R hR r
    exact finiteWeilCanonicalProjectedProbabilityLaw_integrable _ _ _ _ _
  · exact finiteWeilProjectedGaussian_integrable_pow 1 0 p
  · exact finiteWeilProjectedGaussian_integrable_pow 1 0 (2 * p)
  · intro R hR
    exact (HTGeometry.truncPowBCF R hR.le p).integrable _

end RHTower
