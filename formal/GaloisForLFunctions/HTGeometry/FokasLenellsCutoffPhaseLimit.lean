import GaloisForLFunctions.HTGeometry.FokasLenellsCutoffPhaseOperators
import GaloisForLFunctions.HTGeometry.L2MultiplierContinuity

/-!
# Removing the reciprocal-frequency cutoff

Shrinking the excluded interval recovers the raw singular evolution strongly
on every actual L2 vector. The optimal operator Lipschitz constant grows
without bound, quantifying the regularity lost when the cutoff is removed.
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal
namespace GaloisForLFunctions.HTGeometry.FokasLenells
noncomputable section

/-- The sharp cutoff constant grows exponentially as the width parameter decreases. -/
theorem cutoffPhaseBudget_eq_exp (a : ℝ) :
    cutoffPhaseBudget a = (1/2 : ℝ) * Real.exp (-a) := by
  simp [cutoffPhaseBudget,Real.exp_neg,mul_inv_rev,mul_comm]

/-- Removing the cutoff sends its optimal global Lipschitz constant to infinity. -/
theorem cutoffPhaseBudget_tendsto_atBot : Tendsto cutoffPhaseBudget atBot atTop := by
  have he := Real.tendsto_exp_atTop.comp tendsto_neg_atBot_atTop
  have h := (tendsto_const_mul_atTop_of_pos (by norm_num : (0:ℝ) < 1/2)).2 he
  change Tendsto (fun a => cutoffPhaseBudget a) atBot atTop
  simpa only [cutoffPhaseBudget_eq_exp,Function.comp_def] using h

/-- The cutoff phase converges to the actual raw singular phase at every spectral point. -/
theorem cutoffPhase_tendsto_atBot (t z : ℝ) :
    Tendsto (fun a => cutoffPhase a t z) atBot (𝓝 (phase t z)) := by
  apply tendsto_const_nhds.congr'
  by_cases hz : z = 0
  · subst z
    exact .of_forall fun a => by simp [cutoffPhase,cutoffPhaseFrequency,phase,Set.indicator]
  · filter_upwards [Real.tendsto_exp_atBot.eventually_lt_const (abs_pos.mpr hz)] with a ha
    have hm : z ∈ cutoffPhaseSet a := ha.le
    simp only [cutoffPhase,cutoffPhaseFrequency,indicator_of_mem hm,phase,div_eq_mul_inv,neg_mul]

/-- The actual cutoff unitaries converge strongly to the raw evolution as their excluded interval shrinks. -/
theorem cutoffEvolution_tendsto_atBot (t : ℝ) (u : Lp ℂ 2 (volume : Measure ℝ)) :
    Tendsto (fun a => cutoffEvolution a t u) atBot (𝓝 (evolution t u)) := by
  have ht := tendsto_lpBoundedMulCLM_apply (μ := volume)
    (fun a => measurable_cutoffPhase a t) (measurable_phase t)
    (by norm_num : (0:ℝ) ≤ 1)
    (fun a z => (norm_cutoffPhase a t z).le) (fun z => (norm_phase t z).le)
    (cutoffPhase_tendsto_atBot t) u
  have he (a : ℝ) : lpBoundedMulCLM (p := 2) (μ := volume)
      (measurable_cutoffPhase a t) (by norm_num : (0:ℝ) ≤ 1)
      (fun z => (norm_cutoffPhase a t z).le) u = cutoffEvolution a t u := by
    apply Lp.ext
    exact (lpBoundedMulCLM_coeFn (p := 2) (μ := volume)
      (measurable_cutoffPhase a t) (by norm_num : (0:ℝ) ≤ 1)
      (fun z => (norm_cutoffPhase a t z).le) u).trans (cutoffEvolution_ae a t u).symm
  have he0 : lpBoundedMulCLM (p := 2) (μ := volume)
      (measurable_phase t) (by norm_num : (0:ℝ) ≤ 1)
      (fun z => (norm_phase t z).le) u = evolution t u := by
    apply Lp.ext
    exact (lpBoundedMulCLM_coeFn (p := 2) (μ := volume)
      (measurable_phase t) (by norm_num : (0:ℝ) ≤ 1)
      (fun z => (norm_phase t z).le) u).trans (evolution_ae t u).symm
  simpa only [he,he0] using ht

/-- No finite time Lipschitz constant can cover all cutoff widths. -/
theorem cutoffEvolution_no_uniform_lipschitz_constant (L : ℝ) :
    ¬ ∀ a s t : ℝ, ‖cutoffEvolution a s - cutoffEvolution a t‖ ≤ L * ‖s-t‖ := by
  intro h
  have hb (a : ℝ) : cutoffPhaseBudget a ≤ L := (cutoffEvolution_lipschitz_iff a L).1 (h a)
  have he := cutoffPhaseBudget_tendsto_atBot.eventually_gt_atTop L
  obtain ⟨a,ha⟩ := he.exists
  exact (hb a).not_gt ha

/-- Strong approximation to the raw singular evolution coexists with diverging optimal stability constants. -/
theorem cutoffEvolution_strong_limit_unbounded_lipschitz :
    (∀ t : ℝ, ∀ u : Lp ℂ 2 (volume : Measure ℝ),
      Tendsto (fun a => cutoffEvolution a t u) atBot (𝓝 (evolution t u))) ∧
    Tendsto cutoffPhaseBudget atBot atTop ∧
    (∀ a L : ℝ, (∀ s t, ‖cutoffEvolution a s - cutoffEvolution a t‖ ≤ L * ‖s-t‖) ↔
      cutoffPhaseBudget a ≤ L) :=
  ⟨cutoffEvolution_tendsto_atBot,cutoffPhaseBudget_tendsto_atBot,cutoffEvolution_lipschitz_iff⟩

end
end GaloisForLFunctions.HTGeometry.FokasLenells
