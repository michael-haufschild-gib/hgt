import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Convolution preserves an all-height logarithmic asymptotic

A fixed translate changes `log |T|` by a relative error tending to zero.
For a function of logarithmic growth, an integrable first moment of the kernel
then gives dominated convergence at both signs of the height.
-/

open Filter Topology MeasureTheory Complex

noncomputable section

namespace GaloisForLFunctions.ConjugateDiagonalGeometry

private theorem abs_add_tendsto_atTop {ι : Type*} {l : Filter ι} {T : ι → ℝ}
    (hT : Tendsto (fun i => |T i|) l atTop) (u : ℝ) :
    Tendsto (fun i => |T i + u|) l atTop := by
  apply tendsto_atTop_mono (f := fun i => |T i| - |u|)
  · intro i
    have h : |T i| ≤ |T i + u| + |u| := by
      calc |T i| = |(T i + u) + -u| := by ring_nf
        _ ≤ |T i + u| + |-u| := abs_add_le _ _
        _ = _ := by rw [abs_neg]
    linarith only [h]
  · simpa only [sub_eq_add_neg] using hT.atTop_add (tendsto_const_nhds (x := -|u|))

/-- Fixed translations do not change the logarithmic height scale. -/
theorem tendsto_log_abs_add_div_log_abs {ι : Type*} {l : Filter ι} {T : ι → ℝ}
    (hT : Tendsto (fun i => |T i|) l atTop) (u : ℝ) :
    Tendsto (fun i => Real.log |T i + u| / Real.log |T i|) l (𝓝 1) := by
  have hlog := Real.tendsto_log_atTop.comp hT
  have hzero : Tendsto (fun i => Real.log 2 / Real.log |T i|) l (𝓝 0) :=
    hlog.const_div_atTop (Real.log 2)
  have hbound : ∀ᶠ i in l,
      |Real.log |T i + u| / Real.log |T i| - 1| ≤
        Real.log 2 / Real.log |T i| := by
    filter_upwards [hT.eventually (eventually_ge_atTop (max 2 (2 * |u|)))] with i hi
    have ht : 2 ≤ |T i| := (le_max_left _ _).trans hi
    have hu : 2 * |u| ≤ |T i| := (le_max_right _ _).trans hi
    have hlo : |T i| / 2 ≤ |T i + u| := by
      have h : |T i| ≤ |T i + u| + |u| := by
        calc |T i| = |(T i + u) + -u| := by ring_nf
          _ ≤ |T i + u| + |-u| := abs_add_le _ _
          _ = _ := by rw [abs_neg]
      linarith only [h, hu]
    have hhi : |T i + u| ≤ 2 * |T i| := by
      have h := abs_add_le (T i) u
      linarith only [h, hu, ht]
    have ht0 : 0 < |T i| := by linarith only [ht]
    have htu0 : 0 < |T i + u| := by linarith only [hlo, ht]
    have hl0 : 0 < Real.log |T i| := Real.log_pos (by linarith only [ht])
    have hloglo := Real.log_le_log (by positivity : 0 < |T i| / 2) hlo
    have hloghi := Real.log_le_log htu0 hhi
    rw [Real.log_div ht0.ne' (by norm_num)] at hloglo
    rw [Real.log_mul (by norm_num) ht0.ne'] at hloghi
    apply abs_le.mpr
    constructor
    · have he : (-(Real.log 2 / Real.log |T i|) + 1) * Real.log |T i| =
          Real.log |T i| - Real.log 2 := by field_simp; ring
      have h := (le_div_iff₀ hl0).mpr (show
          (-(Real.log 2 / Real.log |T i|) + 1) * Real.log |T i| ≤
            Real.log |T i + u| by rw [he]; exact hloglo)
      linarith only [h]
    · have h := div_le_div_of_nonneg_right hloghi hl0.le
      have he : (Real.log 2 + Real.log |T i|) / Real.log |T i| =
          Real.log 2 / Real.log |T i| + 1 := by field_simp
      rw [he] at h
      linarith only [h]
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simpa only [Real.norm_eq_abs] using
    squeeze_zero' (Eventually.of_forall fun i => abs_nonneg _) hbound hzero

/-- A logarithmic growth bound remains integrably dominated after translation. -/
theorem log_height_translate_ratio_le {T u : ℝ} (hT : 2 ≤ |T|) :
    Real.log (2 + |T + u|) / Real.log |T| ≤ 2 + |u| / Real.log 2 := by
  have hT0 : 0 < |T| := by linarith only [hT]
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlT : Real.log 2 ≤ Real.log |T| := Real.log_le_log (by norm_num) hT
  have hprod : 2 + |T + u| ≤ 2 * |T| * (1 + |u|) := by
    have ha := abs_add_le T u
    have hp := mul_nonneg (show 0 ≤ 2 * |T| - 1 by linarith only [hT]) (abs_nonneg u)
    nlinarith only [ha, hp, hT]
  have hh := Real.log_le_log (by positivity : 0 < 2 + |T + u|) hprod
  rw [Real.log_mul (mul_ne_zero (by norm_num) hT0.ne') (by positivity),
    Real.log_mul (by norm_num) hT0.ne'] at hh
  have hu := Real.log_le_sub_one_of_pos (by positivity : 0 < 1 + |u|)
  have hb : Real.log (2 + |T + u|) ≤ 2 * Real.log |T| + |u| := by
    linarith only [hh, hu, hlT]
  calc Real.log (2 + |T + u|) / Real.log |T|
      ≤ (2 * Real.log |T| + |u|) / Real.log |T| :=
        div_le_div_of_nonneg_right hb (hl2.le.trans hlT)
    _ = 2 + |u| / Real.log |T| := by field_simp [(hl2.trans_le hlT).ne']
    _ ≤ 2 + |u| / Real.log 2 := by
      exact add_le_add_right (div_le_div_of_nonneg_left (abs_nonneg u) hl2 hlT) 2

/-- Fixed translates preserve an all-height logarithmic asymptotic. -/
theorem tendsto_translated_log_normalized {ι : Type*} {l : Filter ι} {T : ι → ℝ}
    {f : ℝ → ℂ} {L : ℂ}
    (hT : Tendsto (fun i => |T i|) l atTop)
    (hf : Tendsto (fun t => f t / (Real.log |t| : ℂ))
      (Filter.comap abs atTop) (𝓝 L)) (u : ℝ) :
    Tendsto (fun i => f (T i + u) / (Real.log |T i| : ℂ)) l (𝓝 L) := by
  have hs := abs_add_tendsto_atTop hT u
  have hc : Tendsto (fun i => T i + u) l (Filter.comap abs atTop) :=
    tendsto_comap_iff.mpr hs
  have hratio := Complex.continuous_ofReal.continuousAt.tendsto.comp
    (tendsto_log_abs_add_div_log_abs hT u)
  have hp := (hf.comp hc).mul hratio
  simp only [Complex.ofReal_one, mul_one] at hp
  apply hp.congr'
  filter_upwards [hs.eventually (eventually_ge_atTop 2)] with i hi
  have hne : (Real.log |T i + u| : ℂ) ≠ 0 := by
    exact_mod_cast (Real.log_pos (by linarith only [hi] : 1 < |T i + u|)).ne'
  dsimp only [Function.comp_def]
  push_cast
  field_simp [hne]

/-- An integrable first moment transports an all-height logarithmic asymptotic
through convolution. The domination is uniform in both signs of the height. -/
theorem tendsto_integral_mul_log_normalized {ι : Type*} {l : Filter ι}
    [l.IsCountablyGenerated] {T : ι → ℝ} {f k : ℝ → ℂ} {L : ℂ} {C : ℝ}
    (hT : Tendsto (fun i => |T i|) l atTop) (hfcont : Continuous f)
    (hf : Tendsto (fun t => f t / (Real.log |t| : ℂ))
      (Filter.comap abs atTop) (𝓝 L))
    (hC : 0 ≤ C) (hgrowth : ∀ t, ‖f t‖ ≤ C * Real.log (2 + |t|))
    (hk : AEStronglyMeasurable k)
    (hweight : Integrable (fun u => ‖k u‖ * (2 + |u| / Real.log 2))) :
    Tendsto (fun i => (∫ u, k u * f (T i + u)) / (Real.log |T i| : ℂ))
      l (𝓝 ((∫ u, k u) * L)) := by
  have hmeas : ∀ᶠ i in l, AEStronglyMeasurable
      (fun u => k u * (f (T i + u) / (Real.log |T i| : ℂ))) := by
    apply Eventually.of_forall
    intro i
    exact hk.mul ((hfcont.comp (continuous_const.add continuous_id)).div_const _).aestronglyMeasurable
  have hbound : ∀ᶠ i in l, ∀ᵐ u,
      ‖k u * (f (T i + u) / (Real.log |T i| : ℂ))‖ ≤
        C * (‖k u‖ * (2 + |u| / Real.log 2)) := by
    filter_upwards [hT.eventually (eventually_ge_atTop 2)] with i hi
    apply Eventually.of_forall
    intro u
    have hlog : 0 < Real.log |T i| := Real.log_pos (by linarith only [hi])
    rw [norm_mul, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hlog]
    have hb := log_height_translate_ratio_le (u := u) hi
    have hg := div_le_div_of_nonneg_right (hgrowth (T i + u)) hlog.le
    have hc := mul_le_mul_of_nonneg_left hb hC
    have hn : ‖f (T i + u)‖ / Real.log |T i| ≤ C * (2 + |u| / Real.log 2) := by
      calc _ ≤ (C * Real.log (2 + |T i + u|)) / Real.log |T i| := hg
        _ = C * (Real.log (2 + |T i + u|) / Real.log |T i|) := by ring
        _ ≤ _ := hc
    simpa only [mul_assoc, mul_left_comm C] using
      mul_le_mul_of_nonneg_left hn (norm_nonneg (k u))
  have hp : ∀ᵐ u, Tendsto
      (fun i => k u * (f (T i + u) / (Real.log |T i| : ℂ))) l (𝓝 (k u * L)) := by
    apply Eventually.of_forall
    intro u
    exact (tendsto_translated_log_normalized hT hf u).const_mul (k u)
  have hdct := tendsto_integral_filter_of_dominated_convergence
    (fun u => C * (‖k u‖ * (2 + |u| / Real.log 2)))
    hmeas hbound (hweight.const_mul C) hp
  simpa only [← mul_div_assoc, integral_div, integral_mul_const] using hdct

end GaloisForLFunctions.ConjugateDiagonalGeometry

#print axioms GaloisForLFunctions.ConjugateDiagonalGeometry.tendsto_integral_mul_log_normalized
