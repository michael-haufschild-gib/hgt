import GaloisForLFunctions.HTGeometry.FokasLenellsCutoffPhaseNormGap
import GaloisForLFunctions.RHTower.FokasLenellsCutoffCauchyPhase

/-!
# Cauchy compression does not repair the cutoff norm gap

Strong cutoff approximation holds after the actual Cauchy projection, but
the error remains exactly two at every nonzero time. No alternative operator
norm limit exists. The positive survivor is the sharp finite-cutoff stability
law already proved for this same concrete family.
-/

open MeasureTheory Filter Topology
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.HTGeometry.FokasLenells
namespace RHTower.FokasLenells
noncomputable section

/-- Cauchy compression retains the maximal cutoff approximation error at every nonzero time. -/
theorem norm_cutoffCauchyEvolution_sub_raw (a t : ℝ) :
    ‖cutoffCauchyEvolution a t - cauchyEvolution t‖ = if t = 0 then 0 else 2 := by
  rw [cutoffCauchyEvolution_eq_cauchyLinfty,cauchyEvolution_eq_cauchyLinftyMultiplier,
    ← map_sub,norm_cauchyLinftyMultiplier,norm_cutoffPhaseLinfty_sub_raw]

/-- The cutoff Cauchy approximation converges in operator norm precisely at time zero. -/
theorem cutoffCauchyEvolution_operator_tendsto_iff (t : ℝ) :
    Tendsto (fun a => cutoffCauchyEvolution a t) atBot (𝓝 (cauchyEvolution t)) ↔ t = 0 := by
  constructor
  · intro h
    by_contra ht
    have hn := tendsto_iff_norm_sub_tendsto_zero.mp h
    simp only [norm_cutoffCauchyEvolution_sub_raw,if_neg ht] at hn
    have he : (2:ℝ) = 0 := tendsto_nhds_unique tendsto_const_nhds hn
    norm_num at he
  · intro ht
    have he (a : ℝ) : cutoffCauchyEvolution a t = cauchyEvolution t := by
      apply sub_eq_zero.mp
      apply norm_eq_zero.mp
      rw [norm_cutoffCauchyEvolution_sub_raw,if_pos ht]
    simpa only [he] using
      (tendsto_const_nhds : Tendsto (fun _ : ℝ => cauchyEvolution t) atBot (𝓝 (cauchyEvolution t)))

/-- No other bounded Cauchy operator can be the cutoff norm limit at a nonzero time. -/
theorem cutoffCauchyEvolution_exists_operator_limit_iff (t : ℝ) :
    (∃ A : SoninL2 →L[ℂ] SoninL2,
      Tendsto (fun a => cutoffCauchyEvolution a t) atBot (𝓝 A)) ↔ t = 0 := by
  constructor
  · rintro ⟨A,hA⟩
    have he : A = cauchyEvolution t := by
      apply ContinuousLinearMap.ext
      intro u
      have h := (ContinuousLinearMap.apply ℂ SoninL2 u).continuous.continuousAt.tendsto.comp hA
      exact tendsto_nhds_unique h (cutoffCauchyEvolution_tendsto_atBot t u)
    rw [he] at hA
    exact (cutoffCauchyEvolution_operator_tendsto_iff t).1 hA
  · intro ht
    exact ⟨_,(cutoffCauchyEvolution_operator_tendsto_iff t).2 ht⟩

/-- One concrete family has sharp cutoff stability, strong raw convergence, and a maximal norm gap. -/
theorem cutoffCauchyEvolution_stability_limit_classification :
    (∀ a L : ℝ,
      (∀ s t, ‖cutoffCauchyEvolution a s - cutoffCauchyEvolution a t‖ ≤ L * ‖s-t‖) ↔
      cutoffPhaseBudget a ≤ L) ∧
    (∀ t : ℝ, ∀ u : SoninL2,
      Tendsto (fun a => cutoffCauchyEvolution a t u) atBot (𝓝 (cauchyEvolution t u))) ∧
    (∀ a t : ℝ, ‖cutoffCauchyEvolution a t - cauchyEvolution t‖ = if t = 0 then 0 else 2) ∧
    Tendsto cutoffPhaseBudget atBot atTop :=
  ⟨cutoffCauchyEvolution_lipschitz_iff,cutoffCauchyEvolution_tendsto_atBot,
    norm_cutoffCauchyEvolution_sub_raw,cutoffPhaseBudget_tendsto_atBot⟩

end
end RHTower.FokasLenells
