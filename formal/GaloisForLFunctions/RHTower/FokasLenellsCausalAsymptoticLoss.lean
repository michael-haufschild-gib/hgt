import GaloisForLFunctions.RHTower.FokasLenellsCausalStrongStability

/-! Consequences of strong causal decay for graph states, recovery, and information-loss projections. -/
open Complex MeasureTheory Set Filter Topology
open scoped NNReal
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.HTGeometry.FokasLenells
namespace RHTower.FokasLenells
noncomputable section
local instance fokasLenellsCausalAsymptoticLossInst1 : CompleteSpace (hardyL2ᗮ) := hardyL2.isClosed_orthogonal.completeSpace_coe

/-- Both the state and its actual generator derivative decay in the full graph norm. -/
theorem causalGeneratorGraphEvolution_strong_tendsto (p : causalGeneratorGraph) :
    Tendsto (fun t : ℝ≥0 => causalGeneratorGraphEvolution t p) atTop (𝓝 0) := by
  apply tendsto_subtype_rng.2
  change Tendsto (fun t : ℝ≥0 =>
    (causalLowerCauchyEvolution t p.val.1, causalLowerCauchyEvolution t p.val.2)) atTop (𝓝 (0, 0))
  exact (causalLowerCauchyEvolution_strong_tendsto p.val.1).prodMk_nhds
    (causalLowerCauchyEvolution_strong_tendsto p.val.2)

/-- The norm-preserving recovery semigroup tends weakly to zero on every actual datum. -/
theorem causalLowerRecovery_inner_tendsto (u v : hardyL2ᗮ) :
    Tendsto (fun t : ℝ≥0 => inner ℂ v (causalLowerRecovery t u)) atTop (𝓝 0) := by
  have he (t : ℝ≥0) : inner ℂ v (causalLowerRecovery t u) =
      inner ℂ (causalLowerCauchyEvolution t v) u := by
    change inner ℂ v ((causalLowerRecovery t).toContinuousLinearMap u) = _
    rw [← causalLowerCauchyEvolution_adjoint]
    exact ContinuousLinearMap.adjoint_inner_right _ _ _
  simp_rw [he]
  simpa only [inner_zero_left] using
    (causalLowerCauchyEvolution_strong_tendsto v).inner (𝕜 := ℂ) tendsto_const_nhds

/-- The actual component recoverable at time `t` tends to zero for each fixed original input. -/
theorem causalRecoveryProjection_strong_tendsto (u : hardyL2ᗮ) :
    Tendsto (fun t : ℝ≥0 => causalRecoveryProjection t u) atTop (𝓝 0) := by
  have he (t : ℝ≥0) : ‖causalRecoveryProjection t u‖ = ‖causalLowerCauchyEvolution t u‖ := by
    change ‖(causalLowerCauchyEvolution t).adjoint (causalLowerCauchyEvolution t u)‖ = _
    rw [causalLowerCauchyEvolution_adjoint]
    exact (causalLowerRecovery t).norm_map _
  apply tendsto_zero_iff_norm_tendsto_zero.2
  simpa only [he, norm_zero] using (causalLowerCauchyEvolution_strong_tendsto u).norm

/-- Over long times, the actual information-loss projection converges to the whole original input. -/
theorem causalLossProjection_strong_tendsto (u : hardyL2ᗮ) :
    Tendsto (fun t : ℝ≥0 => causalLossProjection t u) atTop (𝓝 u) := by
  change Tendsto (fun t : ℝ≥0 => u-causalRecoveryProjection t u) atTop (𝓝 u)
  simpa only [sub_zero] using tendsto_const_nhds.sub (causalRecoveryProjection_strong_tendsto u)

end
end RHTower.FokasLenells
