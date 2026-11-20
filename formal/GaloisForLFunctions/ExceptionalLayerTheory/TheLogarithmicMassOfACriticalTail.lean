import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.Layercake

/-!
# Logarithmic mass at the critical weak moment

A finite measure with tail asymptotic A/t has clipped first moment
asymptotic A log T. The proof compares the integral of the tail with
two multiples of 1/t. It permits jumps at every threshold. This is the
finite-measure analogue of the logarithmic trace of a weak-Lorentz
spectrum in Ponge, arXiv:2605.25591, Theorems C and E.
-/
noncomputable section
open Filter MeasureTheory Set Topology
namespace GaloisForLFunctions.ExceptionalLayerTheory

private theorem primitive_lower_bound (f : ℝ → ℝ)
    (hf : ∀ a b : ℝ, IntervalIntegrable f volume a b) {C : ℝ}
    (h : Tendsto (fun t => t*f t) atTop (𝓝 C)) {b : ℝ} (hb : b<C) :
    ∀ᶠ T : ℝ in atTop, b < (∫ t in (0:ℝ)..T, f t)/Real.log T := by
  obtain ⟨k,hbk,hk⟩ := exists_between hb
  obtain ⟨d₀,hd₀⟩ := eventually_atTop.mp (h.eventually_const_lt hk)
  let d := max 1 d₀
  have hd : 0<d := zero_lt_one.trans_le (le_max_left ..)
  let A := (∫ t in (0:ℝ)..d, f t) - k*Real.log d
  have hconst : Tendsto (fun T : ℝ => A/Real.log T) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop Real.tendsto_log_atTop
  have hl : Tendsto (fun T : ℝ => k+A/Real.log T) atTop (𝓝 k) := by
    simpa only [add_zero] using hconst.const_add k
  filter_upwards [hl.eventually_const_lt hbk,eventually_gt_atTop d,
    eventually_gt_atTop (1:ℝ)] with T hT hTd hT1
  have hp := hd.trans hTd
  have hi : IntervalIntegrable (fun t : ℝ => k*t⁻¹) volume d T := by
    apply ContinuousOn.intervalIntegrable_of_Icc hTd.le
    exact continuousOn_const.mul (continuousOn_id.inv₀ fun t ht => (hd.trans_le ht.1).ne')
  have htail := intervalIntegral.integral_mono_on hTd.le hi (hf d T)
    (fun t ht => by
      have hpos := hd.trans_le ht.1
      change k*t⁻¹ ≤ f t
      rw [←div_eq_mul_inv]
      exact (div_le_iff₀ hpos).mpr (by
        rw [mul_comm (f t) t]
        exact (hd₀ t ((le_max_right 1 d₀).trans ht.1)).le))
  rw [intervalIntegral.integral_const_mul,integral_inv_of_pos hd hp,
    Real.log_div hp.ne' hd.ne'] at htail
  have he := intervalIntegral.integral_add_adjacent_intervals (hf 0 d) (hf d T)
  apply hT.trans_le
  apply (le_div_iff₀ (Real.log_pos hT1)).mpr
  rw [add_mul,div_mul_cancel₀ _ (Real.log_pos hT1).ne',←he]
  dsimp only [A]
  linarith only [htail]

/-- Logarithmic Cesàro asymptotics for locally integrable tails with
arbitrary jump discontinuities. -/
theorem critical_tail_primitive (f : ℝ → ℝ) (hf : ∀ a b : ℝ, IntervalIntegrable f volume a b)
    {C : ℝ} (h : Tendsto (fun t => t*f t) atTop (𝓝 C)) :
    Tendsto (fun T : ℝ => (∫ t in (0:ℝ)..T, f t)/Real.log T) atTop (𝓝 C) := by
  apply tendsto_order.mpr
  refine ⟨fun _ hb => primitive_lower_bound f hf h hb,?_⟩
  intro b hb
  have hn : Tendsto (fun t => t*(-f t)) atTop (𝓝 (-C)) := by
    simpa only [mul_neg] using h.neg
  have hh := primitive_lower_bound (fun t => -f t) (fun a b => (hf a b).neg) hn (neg_lt_neg hb)
  filter_upwards [hh] with T hT
  simpa only [intervalIntegral.integral_neg,neg_div,neg_lt_neg_iff] using hT

/-- Integrating a clipped nonnegative observable equals integration of
its strict superlevel measures up to the clipping threshold. -/
theorem integral_clipped_eq_tail {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [IsFiniteMeasure μ] (f : α → ℝ) (hf : Measurable f) (hpos : ∀ x, 0≤f x)
    {T : ℝ} (hT : 0≤T) :
    (∫ x, min (f x) T ∂μ) = ∫ t in (0:ℝ)..T, μ.real {x | t<f x} := by
  let F := fun t : ℝ => μ.real {x | t<f x}
  have hcap : Integrable (fun x => min (f x) T) μ :=
    (integrable_const T).mono' ((hf.min measurable_const).aestronglyMeasurable)
      (.of_forall fun x => by rw [Real.norm_of_nonneg (le_min (hpos x) hT)]; exact min_le_right ..)
  have he (t : ℝ) : μ.real {x | t<min (f x) T} = (Iio T).indicator F t := by
    by_cases ht : t<T
    · rw [indicator_of_mem (show t ∈ Iio T from ht)]
      change μ.real _ = μ.real _
      congr 1
      ext x
      simp only [mem_setOf_eq,lt_min_iff,ht,and_true]
    · rw [indicator_of_notMem (show t ∉ Iio T from ht)]
      have hz : {x | t<min (f x) T} = ∅ := Set.eq_empty_iff_forall_notMem.mpr
        (fun x hx => ht (hx.trans_le (min_le_right ..)))
      rw [hz,measureReal_empty]
  rw [hcap.integral_eq_integral_meas_lt (.of_forall fun x => le_min (hpos x) hT)]
  simp_rw [he]
  rw [integral_indicator measurableSet_Iio,Measure.restrict_restrict measurableSet_Iio,
    inter_comm (Iio T) (Ioi 0),Ioi_inter_Iio,intervalIntegral.integral_of_le hT,
    integral_Ioc_eq_integral_Ioo]

/-- The logarithmically normalized critical moment has the same residue
as the t-normalized superlevel mass. -/
theorem clipped_moment_of_weak_tail {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [IsFiniteMeasure μ] (f : α → ℝ) (hf : Measurable f) (hpos : ∀ x, 0≤f x) {C : ℝ}
    (h : Tendsto (fun t : ℝ => t*μ.real {x | t<f x}) atTop (𝓝 C)) :
    Tendsto (fun T : ℝ => (∫ x, min (f x) T ∂μ)/Real.log T) atTop (𝓝 C) := by
  have hanti : Antitone (fun t : ℝ => μ.real {x | t<f x}) := by
    intro t u htu
    exact measureReal_mono (fun x hx => htu.trans_lt hx) (measure_ne_top μ _)
  apply (critical_tail_primitive _ (fun _ _ => hanti.intervalIntegrable) h).congr'
  filter_upwards [eventually_ge_atTop (0:ℝ)] with T hT
  rw [integral_clipped_eq_tail μ f hf hpos hT]

private theorem reciprocal_band (k l r : ℝ) (hl : 0<l) (hr : 0<r) :
    (∫ t in l..r, k/t) = k*Real.log (r/l) := by
  simp only [div_eq_mul_inv,intervalIntegral.integral_const_mul,integral_inv_of_pos hl hr]

/-- Integrating only from aT to bT cancels the bounded part of a weak
tail. Its unnormalized limit is C log(b/a). -/
theorem weak_tail_on_multiplicative_band (f : ℝ → ℝ)
    (hf : ∀ a b : ℝ, IntervalIntegrable f volume a b) {C : ℝ}
    (h : Tendsto (fun t => t*f t) atTop (𝓝 C)) {a b : ℝ} (ha : 0<a) (hab : a<b) :
    Tendsto (fun T : ℝ => ∫ t in (a*T)..(b*T), f t) atTop (𝓝 (C*Real.log (b/a))) := by
  let L := Real.log (b/a)
  have hL : 0<L := Real.log_pos ((one_lt_div ha).mpr hab)
  rw [Metric.tendsto_atTop]
  intro ε hε
  let e := ε/(2*L)
  have he : 0<e := div_pos hε (mul_pos (by norm_num) hL)
  obtain ⟨M,hM⟩ := (Metric.tendsto_atTop.mp h) e he
  refine ⟨max 1 (M/a),fun T hT => ?_⟩
  have hT0 : 0<T := zero_lt_one.trans_le ((le_max_left ..).trans hT)
  have hA : M≤a*T := by
    rw [mul_comm]
    exact (div_le_iff₀ ha).mp ((le_max_right ..).trans hT)
  have hpA := mul_pos ha hT0
  have hpB := mul_pos (ha.trans hab) hT0
  have hAB := mul_le_mul_of_nonneg_right hab.le hT0.le
  have hlocal {t : ℝ} (ht : t∈Icc (a*T) (b*T)) :
      (C-e)/t ≤ f t ∧ f t ≤ (C+e)/t := by
    have hh := hM t (hA.trans ht.1)
    rw [Real.dist_eq,abs_lt] at hh
    have hpos := hpA.trans_le ht.1
    rw [div_le_iff₀ hpos,le_div_iff₀ hpos,mul_comm (f t) t]
    constructor <;> linarith only [hh.1,hh.2]
  have hint (v : ℝ) : IntervalIntegrable (fun t : ℝ => v/t) volume (a*T) (b*T) :=
    ContinuousOn.intervalIntegrable_of_Icc hAB
      (continuousOn_const.div continuousOn_id (fun t ht => (hpA.trans_le ht.1).ne'))
  have lower := intervalIntegral.integral_mono_on hAB (hint (C-e)) (hf _ _)
    (fun _ ht => (hlocal ht).1)
  have upper := intervalIntegral.integral_mono_on hAB (hf _ _) (hint (C+e))
    (fun _ ht => (hlocal ht).2)
  have hr : (b*T)/(a*T)=b/a := by field_simp [ha.ne',hT0.ne']
  rw [reciprocal_band (C-e) _ _ hpA hpB,hr] at lower
  rw [reciprocal_band (C+e) _ _ hpA hpB,hr] at upper
  have heL : e*L=ε/2 := by dsimp only [e]; field_simp [hL.ne']
  change (C-e)*L ≤ _ at lower
  change _ ≤ (C+e)*L at upper
  rw [Real.dist_eq,abs_lt]
  change -ε < _-C*L ∧ _-C*L<ε
  constructor <;> linarith only [lower,upper,heL,hε]

/-- The difference of two clipped moments on a fixed ratio of scales
converges without logarithmic rescaling. -/
theorem clipped_moment_band_gap {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [IsFiniteMeasure μ] (f : α → ℝ) (hf : Measurable f) (hpos : ∀ x, 0≤f x) {C : ℝ}
    (h : Tendsto (fun t : ℝ => t*μ.real {x | t<f x}) atTop (𝓝 C))
    {a b : ℝ} (ha : 0<a) (hab : a<b) :
    Tendsto (fun T : ℝ => (∫ x, min (f x) (b*T) ∂μ) - ∫ x, min (f x) (a*T) ∂μ)
      atTop (𝓝 (C*Real.log (b/a))) := by
  let F (t : ℝ) := μ.real {x | t<f x}
  have hm : Antitone F := fun _ _ htu =>
    measureReal_mono (fun x hx => htu.trans_lt hx) (measure_ne_top μ _)
  apply (weak_tail_on_multiplicative_band F (fun _ _ => hm.intervalIntegrable) h ha hab).congr'
  filter_upwards [eventually_gt_atTop (0:ℝ)] with T hT
  rw [integral_clipped_eq_tail μ f hf hpos (mul_pos (ha.trans hab) hT).le,
    integral_clipped_eq_tail μ f hf hpos (mul_pos ha hT).le]
  have he := intervalIntegral.integral_add_adjacent_intervals
    (hm.intervalIntegrable (μ:=volume) (a:=0) (b:=a*T)) (hm.intervalIntegrable (μ:=volume) (a:=a*T) (b:=b*T))
  change (∫ t in (a*T)..(b*T), F t) = (∫ t in (0:ℝ)..(b*T), F t)-(∫ t in (0:ℝ)..(a*T), F t)
  linarith only [he]

#print axioms weak_tail_on_multiplicative_band
#print axioms clipped_moment_band_gap

/-- A positive weak-tail residue prevents integrability. -/
theorem integrable_weak_tail_residue_zero {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [IsFiniteMeasure μ] (f : α → ℝ) (hf : Measurable f) (hp : ∀ x, 0≤f x) {C : ℝ}
    (h : Tendsto (fun t : ℝ => t*μ.real {x | t<f x}) atTop (𝓝 C))
    (hi : Integrable f μ) : C=0 := by
  apply tendsto_nhds_unique (clipped_moment_of_weak_tail μ f hf hp h)
  have hupper : Tendsto (fun T : ℝ => (∫ x, f x ∂μ)/Real.log T) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop Real.tendsto_log_atTop
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper
  · filter_upwards [eventually_gt_atTop (1:ℝ)] with T hT
    exact div_nonneg (integral_nonneg (fun x => le_min (hp x) (zero_lt_one.trans hT).le))
      (Real.log_pos hT).le
  · filter_upwards [eventually_gt_atTop (1:ℝ)] with T hT
    have hcap : Integrable (fun x => min (f x) T) μ := hi.mono'
      ((hf.min measurable_const).aestronglyMeasurable)
      (.of_forall fun x => by
        rw [Real.norm_of_nonneg (le_min (hp x) (zero_lt_one.trans hT).le)]
        exact min_le_left ..)
    exact div_le_div_of_nonneg_right (integral_mono hcap hi (fun x => min_le_left ..))
      (Real.log_pos hT).le

#print axioms integrable_weak_tail_residue_zero
#print axioms critical_tail_primitive
#print axioms integral_clipped_eq_tail
#print axioms clipped_moment_of_weak_tail
end GaloisForLFunctions.ExceptionalLayerTheory
