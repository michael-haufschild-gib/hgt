import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.Complex.Basic

/-!
# Parabolic averaging removes a translated Cauchy pole

Horizontal averaging has width `h`, while the transverse displacement is `i h^2`.
After rescaling the integration interval, a moving simple pole carries the multiplier
`i h / (-u + i h)`. It is bounded by one and tends to zero off the null endpoint `u = 0`.
Consequently averaging kills that pole, even when its residue varies continuously with
both source parameters. The unmoved endpoint retains its residue.
-/

open Complex Filter Topology MeasureTheory Set

noncomputable section
namespace GaloisForLFunctions.HTGeometry.ParabolicCauchyAveraging

def ratio (h u : ℝ) : ℂ :=
  (I * (h : ℂ)) / (-(u : ℂ) + I * (h : ℂ))

theorem norm_ratio_le_one {h : ℝ} (hh : 0 < h) (u : ℝ) :
    ‖ratio h u‖ ≤ 1 := by
  have hden : -(u : ℂ) + I * (h : ℂ) ≠ 0 := by
    intro hz
    have := congrArg Complex.im hz
    simp at this
    linarith
  rw [ratio, norm_div, div_le_one (norm_pos_iff.mpr hden)]
  have hb := Complex.abs_im_le_norm (-(u : ℂ) + I * (h : ℂ))
  simpa [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hh] using hb

theorem tendsto_ratio_zero {u : ℝ} (hu : u ≠ 0) :
    Tendsto (fun h : ℝ => ratio h u) (𝓝[>] 0) (𝓝 0) := by
  have hc : ContinuousAt (fun h : ℝ => ratio h u) 0 := by
    unfold ratio
    fun_prop (disch := simpa using hu)
  simpa [ratio] using hc.tendsto.mono_left nhdsWithin_le_nhds

theorem shrinking_pair_tendsto (u : ℝ) :
    Tendsto (fun h : ℝ => (h, h * u)) (𝓝[>] 0) (𝓝 (0, 0)) := by
  have ht : Tendsto (fun h : ℝ => h) (𝓝[>] 0) (𝓝 0) := nhdsWithin_le_nhds
  simpa using ht.prodMk_nhds (ht.mul_const u)

theorem eventually_shrinking_bound {F : ℝ × ℝ → ℂ}
    (hF : ContinuousAt F (0, 0)) :
    ∀ᶠ h : ℝ in 𝓝[>] 0, ∀ u ∈ Icc (0 : ℝ) 1,
      ‖F (h, h * u)‖ ≤ ‖F (0, 0)‖ + 1 := by
  obtain ⟨d, hd, hdist⟩ := Metric.continuousAt_iff.mp hF 1 zero_lt_one
  filter_upwards [Ioo_mem_nhdsGT hd] with h hh
  intro u hu
  have hhu : 0 ≤ h * u := mul_nonneg hh.1.le hu.1
  have hhu' : h * u ≤ h := mul_le_of_le_one_right hh.1.le hu.2
  have hnear : dist (h, h * u) (0, 0) < d := by
    rw [show (0, 0) = (0 : ℝ × ℝ) from rfl, dist_zero_right]
    rw [Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_pos hh.1, abs_of_nonneg hhu]
    exact max_lt hh.2 (hhu'.trans_lt hh.2)
  have he := hdist hnear
  have hn := norm_sub_norm_le (F (h, h * u)) (F (0, 0))
  rw [dist_eq_norm] at he
  linarith

theorem shrinking_average_tendsto {F : ℝ × ℝ → ℂ}
    (hFm : Measurable F) (hF : ContinuousAt F (0, 0)) :
    Tendsto (fun h : ℝ => ∫ u : ℝ in 0..1, F (h, h * u))
      (𝓝[>] 0) (𝓝 (F (0, 0))) := by
  have hlim := intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    (μ := volume) (a := (0 : ℝ)) (b := 1) (l := 𝓝[>] (0 : ℝ))
    (F := fun h u : ℝ => F (h, h * u))
    (f := fun _ : ℝ => F (0, 0)) (fun _ : ℝ => ‖F (0, 0)‖ + 1)
    (Filter.Eventually.of_forall fun h =>
      (hFm.comp (by fun_prop)).aestronglyMeasurable.restrict)
    ((eventually_shrinking_bound hF).mono fun h hh =>
      Filter.Eventually.of_forall fun u hu => hh u (by simpa using uIoc_subset_uIcc hu))
    intervalIntegrable_const
    (Filter.Eventually.of_forall fun u _ => hF.tendsto.comp (shrinking_pair_tendsto u))
  simpa using hlim

theorem moving_average_tendsto_zero {F : ℝ × ℝ → ℂ}
    (hFm : Measurable F) (hF : ContinuousAt F (0, 0)) :
    Tendsto (fun h : ℝ => ∫ u : ℝ in 0..1, ratio h u * F (h, h * u))
      (𝓝[>] 0) (𝓝 0) := by
  have hlim := intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    (μ := volume) (a := (0 : ℝ)) (b := 1) (l := 𝓝[>] (0 : ℝ))
    (F := fun h u : ℝ => ratio h u * F (h, h * u))
    (f := fun _ : ℝ => (0 : ℂ)) (fun _ : ℝ => ‖F (0, 0)‖ + 1)
    ?_ ?_ intervalIntegrable_const ?_
  · simpa using hlim
  · filter_upwards with h
    have hm : Measurable (fun u : ℝ => ratio h u * F (h, h * u)) := by
      apply Measurable.mul
      · unfold ratio
        fun_prop
      · exact hFm.comp (by fun_prop)
    exact hm.aestronglyMeasurable.restrict
  · filter_upwards [eventually_shrinking_bound hF, self_mem_nhdsWithin] with h hb hh
    exact Filter.Eventually.of_forall fun u hu => by
      rw [norm_mul]
      exact (mul_le_of_le_one_left (norm_nonneg _) (norm_ratio_le_one hh u)).trans
        (hb u (by simpa using uIoc_subset_uIcc hu))
  · filter_upwards with u hu
    have hu' : u ∈ Ioc (0 : ℝ) 1 := by simpa using hu
    have hm := (tendsto_ratio_zero (ne_of_gt hu'.1)).mul
      (hF.tendsto.comp (shrinking_pair_tendsto u))
    simpa using hm

/-- Both rescaled channels are genuine integrable functions near the boundary. -/
theorem eventually_intervalIntegrable {F : ℝ × ℝ → ℂ}
    (hFm : Measurable F) (hF : ContinuousAt F (0, 0)) :
    ∀ᶠ h : ℝ in 𝓝[>] 0,
      IntervalIntegrable (fun u : ℝ => F (h, h * u)) volume 0 1 ∧
      IntervalIntegrable (fun u : ℝ => ratio h u * F (h, h * u)) volume 0 1 := by
  filter_upwards [eventually_shrinking_bound hF, self_mem_nhdsWithin] with h hb hh
  have hbase : IntervalIntegrable (fun _ : ℝ => ‖F (0, 0)‖ + 1) volume 0 1 :=
    intervalIntegrable_const
  have hm : Measurable (fun u : ℝ => F (h, h * u)) := hFm.comp (by fun_prop)
  constructor
  · apply hbase.mono_fun' hm.aestronglyMeasurable.restrict
    filter_upwards [ae_restrict_mem measurableSet_uIoc] with u hu
    exact hb u (by simpa using uIoc_subset_uIcc hu)
  · have hr : Measurable (fun u : ℝ => ratio h u) := by unfold ratio; fun_prop
    apply hbase.mono_fun' (hr.mul hm).aestronglyMeasurable.restrict
    filter_upwards [ae_restrict_mem measurableSet_uIoc] with u hu
    simp only [Pi.mul_apply]
    rw [norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) (norm_ratio_le_one hh u)).trans
      (hb u (by simpa using uIoc_subset_uIcc hu))

/-- A fixed endpoint survives while the pole translated through the averaging interval vanishes.
The subtraction is performed before integration. -/
theorem difference_average_tendsto {F G : ℝ × ℝ → ℂ}
    (hFm : Measurable F) (hFc : ContinuousAt F (0, 0))
    (hGm : Measurable G) (hGc : ContinuousAt G (0, 0)) :
    Tendsto (fun h : ℝ => ∫ u : ℝ in 0..1,
      F (h, h * u) - ratio h u * G (h, h * u))
      (𝓝[>] 0) (𝓝 (F (0, 0))) := by
  have ht := (shrinking_average_tendsto hFm hFc).sub (moving_average_tendsto_zero hGm hGc)
  simp only [sub_zero] at ht
  apply ht.congr'
  filter_upwards [eventually_intervalIntegrable hFm hFc,
    eventually_intervalIntegrable hGm hGc] with h hF hG
  exact (intervalIntegral.integral_sub hF.1 hG.2).symm

end GaloisForLFunctions.HTGeometry.ParabolicCauchyAveraging
