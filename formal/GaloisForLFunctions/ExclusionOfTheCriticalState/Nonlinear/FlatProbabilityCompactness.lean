import GaloisForLFunctions.ExclusionOfTheCriticalState.Nonlinear.FlatSquareCoercivity

/-!
# Probability volume restores compactness of flat critical sequences

Sharp nonlinear energy coercivity and convex tangent support imply an
explicit residual threshold: outside the L² ball of radius ε, gradient
norm is at least χ(ε)/ε. Consequently every sequence with vanishing
Fréchet gradient converges strongly to zero, without assuming bounded
norm or an energy limit. This is the finite-volume positive counterpart
of the Lebesgue-space failure of Palais–Smale compactness.
-/

open MeasureTheory Filter Topology Set
namespace GaloisForLFunctions.ExclusionOfTheCriticalState.FlatConvex
noncomputable section
variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

private theorem flat_energy_zero : integralEnergy (0 : Lp ℝ 2 μ) = 0 := by
  unfold integralEnergy
  calc
    (∫ x, potential ((0 : Lp ℝ 2 μ) x) ∂μ) = ∫ _, (0 : ℝ) ∂μ := by
      apply integral_congr_ae
      filter_upwards [Lp.coeFn_zero ℝ 2 μ] with x hx
      rw [hx]
      exact potential_zero
    _ = 0 := integral_zero _ _

/-- The tangent at a profile supports the zero minimum. -/
theorem evenIntegralEnergy_le_inner_gradient (f : Lp ℝ 2 μ) :
    evenIntegralEnergy f ≤ inner ℝ (evenGradientLp f) f := by
  have hp := integral_support (0 : Lp ℝ 2 μ) f
  have hn := integral_support (0 : Lp ℝ 2 μ) (-f)
  rw [flat_energy_zero, zero_sub, inner_neg_right] at hp hn
  have he : inner ℝ (evenGradientLp f) f =
      inner ℝ (gradientLp f) f + inner ℝ (gradientLp (-f)) (-f) := by
    rw [evenGradientLp_eq, inner_sub_left, inner_neg_right]
    ring
  rw [he, evenIntegralEnergy]
  linarith only [hp, hn]

/-- Convex tangent support controls the energy by the actual residual and profile norms. -/
theorem evenIntegralEnergy_le_gradient_norm (f : Lp ℝ 2 μ) :
    evenIntegralEnergy f ≤ ‖evenGradientLp f‖ * ‖f‖ := by
  exact (evenIntegralEnergy_le_inner_gradient f).trans ((le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using
    (norm_inner_le_norm (𝕜 := ℝ) (evenGradientLp f) f)))

private theorem potential_pos {ε : ℝ} (hε : 0 < ε) : 0 < potential ε := by
  by_contra h
  have he := le_antisymm (le_of_not_gt h) (potential_bounds ε).1
  exact (not_le_of_gt hε) ((potential_zero_iff ε).mp he)

variable [IsProbabilityMeasure μ]

/-- Every profile outside a fixed norm ball has a uniformly positive nonlinear residual. -/
theorem evenGradientLp_lower_bound {ε : ℝ} (hε : 0 < ε) (f : Lp ℝ 2 μ) (hf : ε ≤ ‖f‖) :
    potential ε / ε ≤ ‖evenGradientLp f‖ := by
  have hr : 0 < ‖f‖ := hε.trans_le hf
  have hs := potential_convex.secant_mono (mem_univ (0 : ℝ)) (mem_univ ε) (mem_univ ‖f‖)
    hε.ne' hr.ne' hf
  rw [potential_zero, sub_zero, sub_zero, sub_zero, sub_zero] at hs
  apply hs.trans
  apply (div_le_iff₀ hr).mpr
  exact (evenIntegralEnergy_probability_coercivity f).trans (evenIntegralEnergy_le_gradient_norm f)

/-- Vanishing residual forces strong convergence of the whole sequence to the unique critical point. -/
theorem evenGradientLp_tendsto_zero_implies_norm (f : ℕ → Lp ℝ 2 μ)
    (h : Tendsto (fun n => ‖evenGradientLp (f n)‖) atTop (𝓝 0)) :
    Tendsto f atTop (𝓝 0) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  have hc : 0 < potential ε / ε := div_pos (potential_pos hε) hε
  obtain ⟨N, hN⟩ := eventually_atTop.mp (h.eventually (gt_mem_nhds hc))
  refine ⟨N, fun n hn => ?_⟩
  rw [dist_zero_right]
  by_contra hf
  exact (not_le_of_gt (hN n hn)) (evenGradientLp_lower_bound hε (f n) (le_of_not_gt hf))

/-- The literal Fréchet critical residual has full strong compactness on probability spaces. -/
theorem flat_probability_critical_sequence_converges (f : ℕ → Lp ℝ 2 μ)
    (h : Tendsto (fun n => ‖fderiv ℝ evenIntegralEnergy (f n)‖) atTop (𝓝 0)) :
    Tendsto f atTop (𝓝 0) := by
  apply evenGradientLp_tendsto_zero_implies_norm f
  simpa only [(evenIntegralEnergy_hasFDerivAt _).fderiv, innerSL_apply_norm] using h

#print axioms evenIntegralEnergy_le_gradient_norm
#print axioms evenGradientLp_lower_bound
#print axioms flat_probability_critical_sequence_converges
end
end GaloisForLFunctions.ExclusionOfTheCriticalState.FlatConvex
