import GaloisForLFunctions.RHTower.SuzukiOddHardEdgeSeparation
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# The ridge defect runs strictly from zero to one

For a spectral law carried by the open half line, the ridge defect `x(r) = ∫ r/(t+r) dμ` is a
probability average of the strictly increasing symbols `r ↦ r/(t+r)`, so it is strictly increasing;
and since each symbol runs from `0` to `1`, dominated convergence makes the defect run from `0` at
the origin to `1` at infinity.  Injectivity of the zero-sampling operator is what removes the atom
at the origin and hence makes the lower limit `0` rather than the mass of that atom.

Strict monotonicity and the two limits are exactly what makes the odd ridge coordinate a
well-defined reparametrization of the negative shift, which is the card's canonical ridge curve.
-/

open MeasureTheory Filter Topology
open scoped ENNReal

noncomputable section

namespace GaloisForLFunctions.RHTower

/-- The ridge symbol is strictly increasing in the shift away from the edge. -/
theorem ridgeSymbol_strictMono {t r₁ r₂ : ℝ} (ht : 0 < t) (hr₁ : 0 < r₁) (hr₁₂ : r₁ < r₂) :
    r₁ / (t + r₁) < r₂ / (t + r₂) := by
  have h1 : (0 : ℝ) < t + r₁ := by linarith
  have h2 : (0 : ℝ) < t + r₂ := by linarith
  rw [div_lt_div_iff₀ h1 h2]
  nlinarith

/-- **The ridge defect is strictly increasing.** -/
theorem stieltjesFactor_strictMono {μ : Measure ℝ} [IsProbabilityMeasure μ] {r₁ r₂ : ℝ}
    (hr₁ : 0 < r₁) (hr₁₂ : r₁ < r₂) (hsupp : ∀ᵐ t ∂μ, 0 < t)
    (hint₁ : Integrable (fun t => r₁ / (t + r₁)) μ)
    (hint₂ : Integrable (fun t => r₂ / (t + r₂)) μ) :
    stieltjesFactor μ r₁ < stieltjesFactor μ r₂ := by
  have hdiff : Integrable (fun t => r₂ / (t + r₂) - r₁ / (t + r₁)) μ := hint₂.sub hint₁
  have hnn : 0 ≤ᵐ[μ] fun t => r₂ / (t + r₂) - r₁ / (t + r₁) := by
    filter_upwards [hsupp] with t ht
    simp only [Pi.zero_apply, sub_nonneg]
    exact (ridgeSymbol_strictMono ht hr₁ hr₁₂).le
  have hcompl : μ (Set.Ioi (0 : ℝ))ᶜ = 0 := by
    have h := ae_iff.mp hsupp
    have hset : {t : ℝ | ¬ (0 < t)} = (Set.Ioi (0 : ℝ))ᶜ := by ext t; simp
    rwa [hset] at h
  have hIoi : μ (Set.Ioi (0 : ℝ)) = 1 := by
    have h := measure_add_measure_compl (μ := μ) (measurableSet_Ioi (a := (0 : ℝ)))
    rw [hcompl, add_zero, measure_univ] at h
    exact h
  have hsub : Set.Ioi (0 : ℝ)
      ⊆ Function.support (fun t => r₂ / (t + r₂) - r₁ / (t + r₁)) := by
    intro t ht
    have ht' : (0 : ℝ) < t := ht
    have hlt := ridgeSymbol_strictMono ht' hr₁ hr₁₂
    simp only [Function.mem_support, ne_eq, sub_eq_zero]
    exact fun h => absurd h (by linarith)
  have hpos : 0 < ∫ t, (r₂ / (t + r₂) - r₁ / (t + r₁)) ∂μ := by
    rw [integral_pos_iff_support_of_nonneg_ae hnn hdiff]
    calc (0 : ℝ≥0∞) < 1 := by norm_num
      _ = μ (Set.Ioi (0 : ℝ)) := hIoi.symm
      _ ≤ μ (Function.support fun t => r₂ / (t + r₂) - r₁ / (t + r₁)) := measure_mono hsub
  rw [integral_sub hint₂ hint₁] at hpos
  rw [stieltjesFactor, stieltjesFactor]
  linarith

/-! ## `(390)`: the two limits -/

/-- The ridge symbol tends to one as the shift grows. -/
theorem tendsto_ridgeSymbol_atTop {t : ℝ} (ht : 0 ≤ t) :
    Tendsto (fun r : ℝ => r / (t + r)) atTop (𝓝 1) := by
  have hden : Tendsto (fun r : ℝ => t + r) atTop atTop :=
    tendsto_atTop_add_const_left _ t tendsto_id
  have hquot : Tendsto (fun r : ℝ => t / (t + r)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hden
  have hrw : ∀ᶠ r : ℝ in atTop, r / (t + r) = 1 - t / (t + r) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
    have h1 : (0 : ℝ) < t + r := by linarith
    field_simp
    ring
  have hlim : Tendsto (fun r : ℝ => 1 - t / (t + r)) atTop (𝓝 (1 - 0)) :=
    tendsto_const_nhds.sub hquot
  rw [sub_zero] at hlim
  exact hlim.congr' (hrw.mono fun r h => h.symm)

/-- The ridge symbol tends to zero as the shift vanishes, away from the edge. -/
theorem tendsto_ridgeSymbol_nhdsGT {t : ℝ} (ht : 0 < t) :
    Tendsto (fun r : ℝ => r / (t + r)) (𝓝[>] 0) (𝓝 0) := by
  have hne : t + 0 ≠ 0 := by simpa using ne_of_gt ht
  have hcont : ContinuousAt (fun r : ℝ => r / (t + r)) 0 :=
    ContinuousAt.div continuousAt_id (continuousAt_const.add continuousAt_id) hne
  have h2 := hcont.tendsto.mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
  simpa using h2

/-! ## `(390)`: the ridge defect runs from zero to one -/

/-- **`(390)`, upper limit: the ridge defect tends to one at large shifts.** -/
theorem tendsto_stieltjesFactor_atTop {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hsupp : ∀ᵐ t ∂μ, 0 ≤ t) :
    Tendsto (fun r : ℝ => stieltjesFactor μ r) atTop (𝓝 1) := by
  have hmain : Tendsto (fun r : ℝ => ∫ t, r / (t + r) ∂μ) atTop
      (𝓝 (∫ _t : ℝ, (1 : ℝ) ∂μ)) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun _ => (1 : ℝ)) ?_ ?_
      (integrable_const _) ?_
    · filter_upwards with r
      have hm : Measurable (fun t : ℝ => r / (t + r)) := by fun_prop
      exact hm.aestronglyMeasurable
    · filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
      filter_upwards [hsupp] with t ht
      have h1 : (0 : ℝ) < t + r := by linarith
      rw [Real.norm_eq_abs, abs_of_pos (by positivity), div_le_one h1]
      linarith
    · filter_upwards [hsupp] with t ht
      exact tendsto_ridgeSymbol_atTop ht
  rw [integral_const] at hmain
  simpa [stieltjesFactor] using hmain

/-- **`(390)`, lower limit: the ridge defect tends to zero at vanishing shifts, when the spectral
law has no mass at the edge.** -/
theorem tendsto_stieltjesFactor_nhdsGT {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hsupp : ∀ᵐ t ∂μ, 0 < t) :
    Tendsto (fun r : ℝ => stieltjesFactor μ r) (𝓝[>] 0) (𝓝 0) := by
  have hmain : Tendsto (fun r : ℝ => ∫ t, r / (t + r) ∂μ) (𝓝[>] 0)
      (𝓝 (∫ _t : ℝ, (0 : ℝ) ∂μ)) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun _ => (1 : ℝ)) ?_ ?_
      (integrable_const _) ?_
    · filter_upwards with r
      have hm : Measurable (fun t : ℝ => r / (t + r)) := by fun_prop
      exact hm.aestronglyMeasurable
    · filter_upwards [self_mem_nhdsWithin] with r hr
      have hr' : (0 : ℝ) < r := hr
      filter_upwards [hsupp] with t ht
      have h1 : (0 : ℝ) < t + r := by linarith
      rw [Real.norm_eq_abs, abs_of_pos (by positivity), div_le_one h1]
      linarith
    · filter_upwards [hsupp] with t ht
      exact tendsto_ridgeSymbol_nhdsGT ht
  rw [integral_const] at hmain
  simpa [stieltjesFactor] using hmain

end GaloisForLFunctions.RHTower
