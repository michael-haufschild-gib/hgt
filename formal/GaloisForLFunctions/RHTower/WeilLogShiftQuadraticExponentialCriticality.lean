import GaloisForLFunctions.HTGeometry.IntegralFatouDivergence
import GaloisForLFunctions.RHTower.WeilLogShiftQuadraticExponentialLimit

/-! The actual quadratic exponential moments have a sharp transition at two:
finite Gaussian limits below it, divergence at and above it. -/

open MeasureTheory ProbabilityTheory Filter Topology Set
open GaloisForLFunctions.HTGeometry

namespace RHTower

theorem tendsto_finiteWeilCanonicalProjectedIndex_quadratic_exponential_critical
    (t : ℕ → ℕ) (c : {c : ℝ // 2 ≤ c}) :
    Tendsto (fun r => ∫ x : ℝ, Real.exp (c.val * x ^ 2)
      ∂(finiteWeilCanonicalProjectedProbabilityLaw r (2 * (r + 1) ^ 2 + t r) 1 0 : Measure ℝ))
      atTop atTop := by
  let F := fun (r : ℕ) (u : ℝ) => Real.exp (c.val * quantile
    (finiteWeilCanonicalProjectedProbabilityLaw r (2 * (r + 1) ^ 2 + t r) 1 0 : Measure ℝ) u ^ 2)
  let G := fun u : ℝ => Real.exp (c.val * quantile (finiteWeilProjectedGaussian 1 0 : Measure ℝ) u ^ 2)
  have hGm : AEStronglyMeasurable G (volume.restrict (Ioo (0 : ℝ) 1)) := by
    have hm : Measurable G := Real.continuous_exp.measurable.comp
      (measurable_const.mul ((measurable_quantile
        (finiteWeilProjectedGaussian 1 0 : Measure ℝ)).pow_const 2))
    exact hm.aestronglyMeasurable
  have hG : ¬ Integrable G (volume.restrict (Ioo (0 : ℝ) 1)) := by
    intro hi
    have hmap := integrable_map_measure (μ := volume.restrict (Ioo (0 : ℝ) 1))
      (f := quantile (finiteWeilProjectedGaussian 1 0 : Measure ℝ))
      (g := fun x : ℝ => Real.exp (c.val * x ^ 2)) (by fun_prop)
      (measurable_quantile _).aemeasurable
    rw [map_quantile_eq] at hmap
    exact (not_lt_of_ge c.property)
      ((finiteWeilProjectedIndexGaussian_integrable_quadratic_exponential_iff c.val).mp
        (hmap.mpr hi))
  have h := tendsto_integral_atTop_of_ae_nonnegative_nonintegrable_limit
    (μ := volume.restrict (Ioo (0 : ℝ) 1)) (f := F) (g := G)
    (fun r => finiteWeilCanonicalProjectedIndex_quantile_quadratic_exponential_integrable
      r (2 * (r + 1) ^ 2 + t r) c.val)
    (fun _ => Eventually.of_forall fun _ => (Real.exp_pos _).le)
    hGm (Eventually.of_forall fun _ => (Real.exp_pos _).le) hG
    (ae_tendsto_finiteWeilCanonicalProjectedIndex_quantile_quadratic_exponential t c.val)
  dsimp only [F] at h
  simp_rw [finiteWeil_integral_quadratic_exponential_quantile] at h
  exact h

theorem tendsto_finiteWeilCanonicalProjectedIndex_quadratic_exponential_extended
    (t : ℕ → ℕ) (c : ℝ) :
    Tendsto (fun r => ∫⁻ x : ℝ, ENNReal.ofReal (Real.exp (c * x ^ 2))
      ∂(finiteWeilCanonicalProjectedProbabilityLaw r (2 * (r + 1) ^ 2 + t r) 1 0 : Measure ℝ))
      atTop (𝓝 (if c < 2 then ENNReal.ofReal (Real.sqrt (2 / (2 - c))) else ⊤)) := by
  have h : Tendsto (fun r => ENNReal.ofReal (∫ x : ℝ, Real.exp (c * x ^ 2)
      ∂(finiteWeilCanonicalProjectedProbabilityLaw r (2 * (r + 1) ^ 2 + t r) 1 0 : Measure ℝ)))
      atTop (𝓝 (if c < 2 then ENNReal.ofReal (Real.sqrt (2 / (2 - c))) else ⊤)) := by
    by_cases hc : c < 2
    · rw [if_pos hc]
      exact (ENNReal.continuous_ofReal.tendsto _).comp
        (tendsto_finiteWeilCanonicalProjectedIndex_quadratic_exponential_subcritical t ⟨c, hc⟩)
    · rw [if_neg hc]
      exact ENNReal.tendsto_ofReal_atTop.comp
        (tendsto_finiteWeilCanonicalProjectedIndex_quadratic_exponential_critical t
          ⟨c, le_of_not_gt hc⟩)
  exact h.congr fun r => ofReal_integral_eq_lintegral_ofReal
    (finiteWeilCanonicalProjectedProbabilityLaw_integrable _ _ _ _ _)
    (Eventually.of_forall fun _ => (Real.exp_pos _).le)

theorem bddAbove_finiteWeilCanonicalProjectedIndex_quadratic_exponential_iff
    (t : ℕ → ℕ) (c : ℝ) :
    BddAbove (range (fun r => ∫ x : ℝ, Real.exp (c * x ^ 2)
      ∂(finiteWeilCanonicalProjectedProbabilityLaw r (2 * (r + 1) ^ 2 + t r) 1 0 : Measure ℝ))) ↔
      c < 2 := by
  constructor
  · intro h
    by_contra hc
    exact (not_bddAbove_of_tendsto_atTop
      (tendsto_finiteWeilCanonicalProjectedIndex_quadratic_exponential_critical t
        ⟨c, le_of_not_gt hc⟩)) h
  · intro hc
    exact (tendsto_finiteWeilCanonicalProjectedIndex_quadratic_exponential_subcritical t
      ⟨c, hc⟩).isBoundedUnder_le.bddAbove_range

end RHTower
