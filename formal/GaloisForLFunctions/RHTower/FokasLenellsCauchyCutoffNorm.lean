import GaloisForLFunctions.RHTower.FokasLenellsCauchyLinfty

/-!
# Sharp Cauchy norms for interval cutoffs

Every nonempty interval cutoff and its Cauchy compression have norm one.
Shrinking intervals give a concrete strong limit zero with no operator-norm
limit, even after applying the paper's Cauchy projection.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal
open GaloisForLFunctions.HTGeometry
namespace RHTower.FokasLenells
noncomputable section

private def intervalLinfty (a b : ℝ) : Lp ℂ ∞ (volume : Measure ℝ) :=
  indicatorConstLp ∞ (measurableSet_Ioo (a := a) (b := b)) (by simp [Real.volume_Ioo]) (1 : ℂ)

private theorem intervalCutoff_eq_linfty (a b : ℝ) :
    indicatorCutoff (Ioo a b) measurableSet_Ioo = lineLinftyMultiplier (intervalLinfty a b) := by
  apply ContinuousLinearMap.ext
  intro u
  apply Lp.ext
  filter_upwards [indicatorCutoff_ae (Ioo a b) measurableSet_Ioo u,
    lineLinftyMultiplier_ae (intervalLinfty a b) u,
    indicatorConstLp_coeFn (p := ∞) (μ := (volume : Measure ℝ))
      (hs := measurableSet_Ioo (a := a) (b := b))
      (hμs := by simp [Real.volume_Ioo]) (c := (1 : ℂ))] with z h0 h1 h2
  change intervalLinfty a b z = (Ioo a b).indicator (fun _ => (1 : ℂ)) z at h2
  rw [h0, h1, h2]
  by_cases hz : z ∈ Ioo a b <;> simp [hz]

private theorem norm_intervalLinfty (a b : ℝ) :
    ‖intervalLinfty a b‖ = if a < b then 1 else 0 := by
  by_cases hab : a < b
  · rw [if_pos hab]
    have hm : volume (Ioo a b) ≠ 0 := by
      rw [Real.volume_Ioo, ne_eq, ENNReal.ofReal_eq_zero]
      linarith
    simpa only [intervalLinfty, norm_one] using
      (norm_indicatorConstLp_top (hs := measurableSet_Ioo (a := a) (b := b))
        (hμs := by simp [Real.volume_Ioo]) (c := (1 : ℂ)) hm)
  · rw [if_neg hab]
    have he : intervalLinfty a b = 0 := by
      apply Lp.ext
      filter_upwards [indicatorConstLp_coeFn (p := ∞) (μ := (volume : Measure ℝ))
        (hs := measurableSet_Ioo (a := a) (b := b))
        (hμs := by simp [Real.volume_Ioo]) (c := (1 : ℂ)), Lp.coeFn_zero ℂ ∞ volume]
        with z hz h0
      change intervalLinfty a b z = (Ioo a b).indicator (fun _ => (1 : ℂ)) z at hz
      rw [hz, h0, Ioo_eq_empty_of_le (le_of_not_gt hab)]
      simp
    rw [he, norm_zero]

/-- Every interval cutoff has norm exactly one or zero according to whether the interval is empty. -/
theorem norm_indicatorCutoff_Ioo (a b : ℝ) :
    ‖indicatorCutoff (Ioo a b) measurableSet_Ioo‖ = if a < b then 1 else 0 := by
  rw [intervalCutoff_eq_linfty, norm_lineLinftyMultiplier, norm_intervalLinfty]

/-- Cauchy compression preserves the exact interval-cutoff norm. -/
theorem norm_negativeCauchy_comp_indicatorCutoff_Ioo (a b : ℝ) :
    ‖negativeCauchy.comp (indicatorCutoff (Ioo a b) measurableSet_Ioo)‖ =
      ‖indicatorCutoff (Ioo a b) measurableSet_Ioo‖ := by
  rw [intervalCutoff_eq_linfty, norm_negativeCauchy_comp_lineLinftyMultiplier, norm_lineLinftyMultiplier]

/-- Actual existing cutoff operators on intervals shrinking exponentially to the origin. -/
def shrinkingIntervalCutoff (h : ℝ) : SoninL2 →L[ℂ] SoninL2 :=
  indicatorCutoff (Ioo 0 (Real.exp (-h))) measurableSet_Ioo

/-- Every shrinking cutoff still has operator norm one. -/
theorem norm_shrinkingIntervalCutoff (h : ℝ) : ‖shrinkingIntervalCutoff h‖ = 1 := by
  rw [shrinkingIntervalCutoff, norm_indicatorCutoff_Ioo, if_pos (Real.exp_pos _)]

/-- Applying the Cauchy projection leaves that norm unchanged at every scale. -/
theorem norm_negativeCauchy_comp_shrinkingIntervalCutoff (h : ℝ) :
    ‖negativeCauchy.comp (shrinkingIntervalCutoff h)‖ = 1 := by
  rw [shrinkingIntervalCutoff, norm_negativeCauchy_comp_indicatorCutoff_Ioo]
  exact norm_shrinkingIntervalCutoff h

/-- Each fixed vector vanishes in the shrinking interval in the strong L2 topology. -/
theorem shrinkingIntervalCutoff_tendsto_zero (u : SoninL2) :
    Tendsto (fun h => shrinkingIntervalCutoff h u) atTop (𝓝 0) := by
  let φ (h z : ℝ) : ℂ := (Ioo 0 (Real.exp (-h))).indicator (fun _ => (1 : ℂ)) z
  have hm (h : ℝ) : Measurable (φ h) := measurable_const.indicator measurableSet_Ioo
  have hb (h z : ℝ) : ‖φ h z‖ ≤ (1 : ℝ) := by
    by_cases hz : z ∈ Ioo 0 (Real.exp (-h)) <;> simp [φ, hz]
  have hp (z : ℝ) : Tendsto (fun h => φ h z) atTop (𝓝 (0 : ℂ)) := by
    apply tendsto_const_nhds.congr'
    by_cases hz : 0 < z
    · filter_upwards [Real.tendsto_exp_neg_atTop_nhds_zero.eventually_lt_const hz] with h hh
      have hnot : z ∉ Ioo 0 (Real.exp (-h)) := by intro hz; linarith [hz.2]
      simp [φ, hnot]
    · exact .of_forall fun h => by simp [φ, hz]
  have ht := tendsto_lpBoundedMulCLM_apply (μ := volume) hm measurable_const
    (by positivity : (0 : ℝ) ≤ 1) hb (fun _ => by simp : ∀ z : ℝ, ‖(0 : ℂ)‖ ≤ (1 : ℝ)) hp u
  have he (h : ℝ) : lpBoundedMulCLM (p := 2) (μ := volume) (hm h)
      (by positivity : (0 : ℝ) ≤ 1) (hb h) u = shrinkingIntervalCutoff h u := by
    apply Lp.ext
    filter_upwards [lpBoundedMulCLM_coeFn (p := 2) (μ := volume) (hm h)
      (by positivity : (0 : ℝ) ≤ 1) (hb h) u,
      indicatorCutoff_ae (Ioo 0 (Real.exp (-h))) measurableSet_Ioo u] with z h0 h1
    change shrinkingIntervalCutoff h u z = _ at h1
    rw [h0, h1]
    by_cases hz : z ∈ Ioo 0 (Real.exp (-h)) <;> simp [φ, hz]
  have he0 : lpBoundedMulCLM (p := 2) (μ := volume) measurable_const
      (by positivity : (0 : ℝ) ≤ 1) (fun _ => by simp : ∀ z : ℝ, ‖(0 : ℂ)‖ ≤ (1 : ℝ)) u = 0 := by
    apply Lp.ext
    filter_upwards [lpBoundedMulCLM_coeFn (p := 2) (μ := volume) measurable_const
      (by positivity : (0 : ℝ) ≤ 1) (fun _ => by simp : ∀ z : ℝ, ‖(0 : ℂ)‖ ≤ (1 : ℝ)) u,
      Lp.coeFn_zero ℂ 2 volume] with z h0 h1
    rw [h0, h1, zero_mul, Pi.zero_apply]
  simpa only [he, he0] using ht

/-- The Cauchy-compressed cutoffs also converge strongly to zero. -/
theorem negativeCauchy_comp_shrinkingIntervalCutoff_tendsto_zero (u : SoninL2) :
    Tendsto (fun h => (negativeCauchy.comp (shrinkingIntervalCutoff h)) u) atTop (𝓝 0) := by
  have ht := negativeCauchy.continuous.continuousAt.tendsto.comp (shrinkingIntervalCutoff_tendsto_zero u)
  simpa only [map_zero, Function.comp_def, ContinuousLinearMap.comp_apply] using ht

private theorem no_norm_limit_of_strong_zero_norm_one (T : ℝ → SoninL2 →L[ℂ] SoninL2)
    (hstrong : ∀ u, Tendsto (fun h => T h u) atTop (𝓝 0)) (hnorm : ∀ h, ‖T h‖ = 1) :
    ¬ ∃ S : SoninL2 →L[ℂ] SoninL2, Tendsto T atTop (𝓝 S) := by
  rintro ⟨S, hS⟩
  have hzero : S = 0 := by
    apply ContinuousLinearMap.ext
    intro u
    have ht := (ContinuousLinearMap.apply ℂ SoninL2 u).continuous.continuousAt.tendsto.comp hS
    exact tendsto_nhds_unique ht (hstrong u)
  have ht : Tendsto (fun _ : ℝ => (1 : ℝ)) atTop (𝓝 (0 : ℝ)) := by
    simpa only [hnorm, hzero, norm_zero] using hS.norm
  exact one_ne_zero (tendsto_nhds_unique tendsto_const_nhds ht)

/-- Shrinking interval cutoffs have no operator-norm limit at all. -/
theorem shrinkingIntervalCutoff_no_operator_norm_limit :
    ¬ ∃ S : SoninL2 →L[ℂ] SoninL2, Tendsto shrinkingIntervalCutoff atTop (𝓝 S) :=
  no_norm_limit_of_strong_zero_norm_one _ shrinkingIntervalCutoff_tendsto_zero norm_shrinkingIntervalCutoff

/-- Cauchy projection does not turn the strong cutoff limit into an operator-norm limit. -/
theorem negativeCauchy_comp_shrinkingIntervalCutoff_no_operator_norm_limit :
    ¬ ∃ S : SoninL2 →L[ℂ] SoninL2,
      Tendsto (fun h => negativeCauchy.comp (shrinkingIntervalCutoff h)) atTop (𝓝 S) :=
  no_norm_limit_of_strong_zero_norm_one _ negativeCauchy_comp_shrinkingIntervalCutoff_tendsto_zero
    norm_negativeCauchy_comp_shrinkingIntervalCutoff

end
end RHTower.FokasLenells
