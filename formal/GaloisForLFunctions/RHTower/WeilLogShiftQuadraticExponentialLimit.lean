import GaloisForLFunctions.HTGeometry.GaussianQuadraticExponential
import GaloisForLFunctions.RHTower.WeilLogShiftGaussianAveraging
import GaloisForLFunctions.RHTower.WeilLogShiftQuantileMoments

/-! Quadratic exponential moments of the actual projected index converge
throughout the full subcritical interval. -/

open MeasureTheory ProbabilityTheory Filter Topology Set
open GaloisForLFunctions.HTGeometry

namespace RHTower

theorem finiteWeilProjectedIndexGaussian_integrable_quadratic_exponential_iff (c : ℝ) :
    Integrable (fun x : ℝ => Real.exp (c * x ^ 2))
      (finiteWeilProjectedGaussian 1 0 : Measure ℝ) ↔ c < 2 := by
  change Integrable (fun x : ℝ => Real.exp (c * x ^ 2)) (gaussianReal 0 _) ↔ c < 2
  rw [gaussianZero_integrable_exp_quadratic_iff _ (by
    intro h
    have h' := congrArg (fun v : NNReal => (v : ℝ)) h
    norm_num at h')]
  norm_num

theorem finiteWeilProjectedIndexGaussian_quadratic_exponential_integral (c : ℝ) :
    (∫ x : ℝ, Real.exp (c * x ^ 2) ∂(finiteWeilProjectedGaussian 1 0 : Measure ℝ)) =
      Real.sqrt (2 / (2 - c)) := by
  change (∫ x : ℝ, Real.exp (c * x ^ 2) ∂(gaussianReal 0 _)) = _
  rw [gaussianZero_integral_exp_quadratic _ (by
    intro h
    have h' := congrArg (fun v : NNReal => (v : ℝ)) h
    norm_num at h')]
  change Real.sqrt (1 / (1 - 2 * (((1 : ℝ) + 0) ^ 2 / 4) * c)) = _
  congr 1
  rw [show 1 - 2 * (((1 : ℝ) + 0) ^ 2 / 4) * c = (2 - c) / 2 by ring,
    div_div_eq_mul_div, one_mul]

theorem finiteWeil_integral_quadratic_exponential_quantile (μ : ProbabilityMeasure ℝ) (c : ℝ) :
    (∫ u : ℝ, Real.exp (c * quantile (μ : Measure ℝ) u ^ 2)
      ∂(volume.restrict (Ioo (0 : ℝ) 1))) = ∫ x : ℝ, Real.exp (c * x ^ 2) ∂(μ : Measure ℝ) := by
  have h := integral_map (μ := volume.restrict (Ioo (0 : ℝ) 1))
    (φ := quantile (μ : Measure ℝ)) (f := fun x : ℝ => Real.exp (c * x ^ 2))
    (measurable_quantile _).aemeasurable (by fun_prop)
  rw [map_quantile_eq] at h
  exact h.symm

theorem finiteWeilCanonicalProjectedIndex_quantile_quadratic_exponential_integrable
    (r k : ℕ) (c : ℝ) :
    Integrable (fun u : ℝ => Real.exp (c * quantile
      (finiteWeilCanonicalProjectedProbabilityLaw r k 1 0 : Measure ℝ) u ^ 2))
      (volume.restrict (Ioo (0 : ℝ) 1)) := by
  have h := integrable_map_measure (μ := volume.restrict (Ioo (0 : ℝ) 1))
    (f := quantile (finiteWeilCanonicalProjectedProbabilityLaw r k 1 0 : Measure ℝ))
    (g := fun x : ℝ => Real.exp (c * x ^ 2)) (by fun_prop)
    (measurable_quantile _).aemeasurable
  rw [map_quantile_eq] at h
  exact h.mp (finiteWeilCanonicalProjectedProbabilityLaw_integrable _ _ _ _ _)

theorem ae_tendsto_finiteWeilCanonicalProjectedIndex_quantile_quadratic_exponential
    (t : ℕ → ℕ) (c : ℝ) :
    ∀ᵐ u ∂(volume.restrict (Ioo (0 : ℝ) 1)), Tendsto (fun r => Real.exp (c * quantile
      (finiteWeilCanonicalProjectedProbabilityLaw r (2 * (r + 1) ^ 2 + t r) 1 0 : Measure ℝ) u ^ 2))
      atTop (𝓝 (Real.exp (c * quantile (finiteWeilProjectedGaussian 1 0 : Measure ℝ) u ^ 2))) :=
  (ae_tendsto_finiteWeilCanonicalProjectedIndex_quantile t).mono fun _ hu =>
    (Real.continuous_exp.tendsto _).comp ((hu.pow 2).const_mul c)

theorem tendsto_finiteWeilCanonicalProjectedIndex_quadratic_exponential_nonneg
    (t : ℕ → ℕ) (c : {c : NNReal // (c : ℝ) < 2}) :
    Tendsto (fun r => ∫ x : ℝ, Real.exp ((c.val : ℝ) * x ^ 2)
      ∂(finiteWeilCanonicalProjectedProbabilityLaw r (2 * (r + 1) ^ 2 + t r) 1 0 : Measure ℝ))
      atTop (𝓝 (Real.sqrt (2 / (2 - (c.val : ℝ))))) := by
  let s := Real.sqrt (2 * (c.val : ℝ))
  let F := fun (r : ℕ) (z : ℝ) => ∫ x : ℝ, Real.exp ((s * z) * x)
    ∂(finiteWeilCanonicalProjectedProbabilityLaw r (2 * (r + 1) ^ 2 + t r) 1 0 : Measure ℝ)
  let G := fun z : ℝ => Real.exp (((c.val : ℝ) / 4) * z ^ 2)
  let B := fun z : ℝ => 4 * Real.exp (s * |z| + ((c.val : ℝ) / 4) * z ^ 2)
  have hm (r : ℕ) : AEStronglyMeasurable (F r) (gaussianReal 0 1) := by
    have hc : Continuous (F r) := by
      dsimp only [F]
      simp_rw [finiteWeilCanonicalProjectedProbabilityLaw,
        finiteWeilCanonicalObservableLaw_integral_real]
      fun_prop
    exact hc.aestronglyMeasurable
  have hb (r : ℕ) : ∀ᵐ z ∂(gaussianReal 0 1), ‖F r z‖ ≤ B z := by
    exact Eventually.of_forall fun z => by
      dsimp only [F, B]
      rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun x => (Real.exp_pos _).le)]
      have he : |s * z| + (s * z) ^ 2 / 8 = s * |z| + ((c.val : ℝ) / 4) * z ^ 2 := by
        dsimp only [s]
        rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _), mul_pow, Real.sq_sqrt (by positivity)]
        ring
      simpa only [he] using finiteWeilCanonicalProjectedIndex_exponential_bound r (t r) (s * z)
  have hB : Integrable B (gaussianReal 0 1) := by
    have hc : (c.val : ℝ) / 4 < 1 / (2 * ((1 : NNReal) : ℝ)) := by
      norm_num
      linarith [c.property]
    exact (gaussianZero_integrable_exp_abs_add_quadratic 1 (by norm_num) s
      ((c.val : ℝ) / 4) hc).const_mul 4
  have hp : ∀ᵐ z ∂(gaussianReal 0 1), Tendsto (fun r => F r z) atTop (𝓝 (G z)) := by
    exact Eventually.of_forall fun z => by
      dsimp only [F, G]
      have he : (s * z) ^ 2 / 8 = ((c.val : ℝ) / 4) * z ^ 2 := by
        dsimp only [s]
        rw [mul_pow, Real.sq_sqrt (by positivity)]
        ring
      simpa only [he] using tendsto_finiteWeilCanonicalProjectedIndex_exponential t (s * z)
  have h := tendsto_integral_filter_of_dominated_convergence B
    (Eventually.of_forall hm) (Eventually.of_forall hb) hB hp
  have hG : (∫ z, G z ∂(gaussianReal 0 1)) = Real.sqrt (2 / (2 - (c.val : ℝ))) := by
    dsimp only [G]
    rw [gaussianZero_integral_exp_quadratic 1 (by norm_num)]
    congr 1
    change 1 / (1 - 2 * (1 : ℝ) * ((c.val : ℝ) / 4)) = _
    rw [show 1 - 2 * (1 : ℝ) * ((c.val : ℝ) / 4) = (2 - (c.val : ℝ)) / 2 by ring,
      div_div_eq_mul_div, one_mul]
  rw [hG] at h
  exact h.congr fun r =>
    (finiteWeilCanonicalProjectedIndex_quadratic_gaussian_average r
      (2 * (r + 1) ^ 2 + t r) c.val).symm

theorem tendsto_finiteWeilCanonicalProjectedIndex_quadratic_exponential_nonpos
    (t : ℕ → ℕ) (c : {c : ℝ // c ≤ 0}) :
    Tendsto (fun r => ∫ x : ℝ, Real.exp (c.val * x ^ 2)
      ∂(finiteWeilCanonicalProjectedProbabilityLaw r (2 * (r + 1) ^ 2 + t r) 1 0 : Measure ℝ))
      atTop (𝓝 (Real.sqrt (2 / (2 - c.val)))) := by
  letI := isProbabilityMeasure_restrict_Ioo_zero_one
  let F := fun (r : ℕ) (u : ℝ) => Real.exp (c.val * quantile
    (finiteWeilCanonicalProjectedProbabilityLaw r (2 * (r + 1) ^ 2 + t r) 1 0 : Measure ℝ) u ^ 2)
  have hm (r : ℕ) : AEStronglyMeasurable (F r) (volume.restrict (Ioo (0 : ℝ) 1)) := by
    exact (finiteWeilCanonicalProjectedIndex_quantile_quadratic_exponential_integrable
      r (2 * (r + 1) ^ 2 + t r) c.val).aestronglyMeasurable
  have hb (r : ℕ) : ∀ᵐ u ∂(volume.restrict (Ioo (0 : ℝ) 1)), ‖F r u‖ ≤ (1 : ℝ) := by
    exact Eventually.of_forall fun u => by
      dsimp only [F]
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      simpa only [Real.exp_zero] using Real.exp_le_exp.mpr
        (mul_nonpos_of_nonpos_of_nonneg c.property (sq_nonneg _))
  have h := tendsto_integral_filter_of_dominated_convergence (fun _ : ℝ => (1 : ℝ))
    (Eventually.of_forall hm) (Eventually.of_forall hb) (integrable_const 1)
    (ae_tendsto_finiteWeilCanonicalProjectedIndex_quantile_quadratic_exponential t c.val)
  dsimp only [F] at h
  simp_rw [finiteWeil_integral_quadratic_exponential_quantile] at h
  rw [finiteWeilProjectedIndexGaussian_quadratic_exponential_integral] at h
  exact h

theorem tendsto_finiteWeilCanonicalProjectedIndex_quadratic_exponential_subcritical
    (t : ℕ → ℕ) (c : {c : ℝ // c < 2}) :
    Tendsto (fun r => ∫ x : ℝ, Real.exp (c.val * x ^ 2)
      ∂(finiteWeilCanonicalProjectedProbabilityLaw r (2 * (r + 1) ^ 2 + t r) 1 0 : Measure ℝ))
      atTop (𝓝 (Real.sqrt (2 / (2 - c.val)))) := by
  by_cases hc : 0 ≤ c.val
  · exact tendsto_finiteWeilCanonicalProjectedIndex_quadratic_exponential_nonneg t
      ⟨⟨c.val, hc⟩, c.property⟩
  · exact tendsto_finiteWeilCanonicalProjectedIndex_quadratic_exponential_nonpos t
      ⟨c.val, le_of_lt (lt_of_not_ge hc)⟩

end RHTower
