import GaloisForLFunctions.RHTower.LiEvenCrossActualClockDerivative
import GaloisForLFunctions.RHTower.LiEvenCrossActualClockUnboundedResponse
import GaloisForLFunctions.RHTower.LiEvenCrossActualClockNegativeResponse
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Cofinal signs of the literal clock derivative and its massive forcing

For the actual complete-copy clock response `F`, this file treats `h = F'` and
`G = h'' - ω² h`. Under RH, the full reciprocal-frequency series gives exact
resonant Cesàro averages, quantitative positive and negative variation, threshold
densities, and divergent signed masses. Every frequency copy and both resonant
signs are retained.

Unconditionally, `h` and `G` each take both strict signs cofinally. The `G`
argument uses the admitted whole-line Green identity and the actual response's
upper and lower escape theorems. No unconditional fixed threshold is asserted.
-/
open Complex Set MeasureTheory Filter
open scoped BigOperators Topology
namespace RHTower
noncomputable section
private theorem clock_cos_integral (k L : ℝ) :
    (∫s in (0:ℝ)..L, Real.cos (k*s)) = if k=0 then L else Real.sin (k*L)/k := by
  by_cases hk : k=0
  · simp [hk]
  · rw [if_neg hk]
    have hd (s : ℝ) : HasDerivAt (fun s : ℝ => Real.sin (k*s)/k) (Real.cos (k*s)) s := by
      simpa [hk] using ((Real.hasDerivAt_sin (k*s)).comp s ((hasDerivAt_id s).const_mul k)).div_const k
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hd s)
      ((Real.continuous_cos.comp (continuous_const.mul continuous_id)).intervalIntegrable 0 L)]
    simp
private theorem clock_cos_mean (k : ℝ) :
    Tendsto (fun L : ℝ => (∫s in (0:ℝ)..L, Real.cos (k*s))/L) atTop
      (𝓝 (if k=0 then 1 else 0)) := by
  by_cases hk : k=0
  · simp only [hk, zero_mul, Real.cos_zero, intervalIntegral.integral_const,
      sub_zero, smul_eq_mul, mul_one, if_true]
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_gt_atTop (0:ℝ)] with L hL
    simp [hL.ne']
  · rw [if_neg hk]
    have hz : Tendsto (fun L : ℝ => (1/|k|)/L) atTop (𝓝 0) := by
      simpa [div_eq_mul_inv] using tendsto_inv_atTop_zero.const_mul (1/|k|)
    apply squeeze_zero_norm' _ hz
    filter_upwards [eventually_gt_atTop (0:ℝ)] with L hL
    rw [clock_cos_integral, if_neg hk, Real.norm_eq_abs, abs_div, abs_div,
      abs_of_pos hL]
    have hs := Real.abs_sin_le_one (k*L)
    apply (div_le_div_of_nonneg_right (div_le_div_of_nonneg_right hs (abs_nonneg k)) hL.le).trans_eq
    ring_nf
private theorem clock_cos_product_integral (v b L : ℝ) :
    (∫s in (0:ℝ)..L, Real.cos (v*s)*Real.cos (b*s)) =
      ((∫s in (0:ℝ)..L, Real.cos ((v+b)*s))+
        (∫s in (0:ℝ)..L, Real.cos ((v-b)*s)))/2 := by
  have hp (s : ℝ) : Real.cos (v*s)*Real.cos (b*s) =
      (Real.cos ((v+b)*s)+Real.cos ((v-b)*s))/2 := by
    rw [add_mul, sub_mul, Real.cos_add, Real.cos_sub]
    ring_nf
  simp_rw [hp]
  simp_rw [div_eq_mul_inv]
  rw [intervalIntegral.integral_mul_const, intervalIntegral.integral_add]
  · exact (Real.continuous_cos.comp (continuous_const.mul continuous_id)).intervalIntegrable _ _
  · exact (Real.continuous_cos.comp (continuous_const.mul continuous_id)).intervalIntegrable _ _
private theorem clock_cos_product_mean {b : ℝ} (hb : b≠0) (v : ℝ) :
    Tendsto (fun L : ℝ => (∫s in (0:ℝ)..L, Real.cos (v*s)*Real.cos (b*s))/L) atTop
      (𝓝 (if v=b ∨ v= -b then (1/2:ℝ) else 0)) := by
  have h := ((clock_cos_mean (v+b)).add (clock_cos_mean (v-b))).div_const 2
  have he (L : ℝ) : ((∫s in (0:ℝ)..L, Real.cos (v*s)*Real.cos (b*s))/L) =
      (((∫s in (0:ℝ)..L, Real.cos ((v+b)*s))/L)+
        ((∫s in (0:ℝ)..L, Real.cos ((v-b)*s))/L))/2 := by
    rw [clock_cos_product_integral]
    ring_nf
  simp_rw [he]
  convert h using 1
  by_cases h1 : v=b
  · subst v
    simp [show b+b≠0 by intro hz; apply hb; linarith]
  · by_cases h2 : v= -b
    · subst v
      simp [show -b-b≠0 by intro hz; apply hb; linarith]
    · have hp : v+b≠0 := by intro hz; apply h2; linarith
      have hm : v-b≠0 := sub_ne_zero.mpr h1
      simp [h1,h2,hp,hm]
private theorem clock_cos_product_mean_bound {L : ℝ} (hL : 0<L) (v b : ℝ) :
    |(∫s in (0:ℝ)..L, Real.cos (v*s)*Real.cos (b*s))/L| ≤ 1 := by
  rw [abs_div, abs_of_pos hL, div_le_iff₀ hL, one_mul]
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const
    (a:=0) (b:=L) (C:=1) (f:=fun s : ℝ => Real.cos (v*s)*Real.cos (b*s)) (by
      intro s _
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_one₀ (Real.abs_cos_le_one _) (abs_nonneg _) (Real.abs_cos_le_one _))
  simpa [Real.norm_eq_abs, abs_of_pos hL] using hb

private theorem clockCosFamily_summable {ι : Type*} (a v : ι → ℝ)
    (ha : ∀q, 0 ≤ a q) (hs : Summable a) (t : ℝ) :
    Summable (fun q => a q * Real.cos (v q*t)) := by
  apply hs.of_norm_bounded
  intro q
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (ha q)]
  exact mul_le_of_le_one_right (ha q) (Real.abs_cos_le_one _)
private theorem clockCosFamily_product_summable {ι : Type*} (a v : ι → ℝ)
    (ha : ∀q, 0 ≤ a q) (hs : Summable a) (b t : ℝ) :
    Summable (fun q => a q * (Real.cos (v q*t)*Real.cos (b*t))) := by
  apply hs.of_norm_bounded
  intro q
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (ha q)]
  apply mul_le_of_le_one_right (ha q)
  rw [abs_mul]
  exact mul_le_one₀ (Real.abs_cos_le_one _) (abs_nonneg _) (Real.abs_cos_le_one _)
private theorem clockCosFamily_product_integral {ι : Type*} [Countable ι]
    (a v : ι → ℝ) (ha : ∀q, 0 ≤ a q) (hs : Summable a) (b L : ℝ) :
    (∫s in (0:ℝ)..L, (∑'q, a q*Real.cos (v q*s))*Real.cos (b*s)) =
      ∑'q, a q*(∫s in (0:ℝ)..L, Real.cos (v q*s)*Real.cos (b*s)) := by
  have hh := intervalIntegral.hasSum_integral_of_dominated_convergence
    (a:=0) (b:=L) (μ:=volume) (F:=fun q s => a q*(Real.cos (v q*s)*Real.cos (b*s)))
    (f:=fun s => (∑'q, a q*Real.cos (v q*s))*Real.cos (b*s)) (fun q _ => a q)
    (fun q => (continuous_const.mul ((Real.continuous_cos.comp
      (continuous_const.mul continuous_id)).mul (Real.continuous_cos.comp
      (continuous_const.mul continuous_id)))).aestronglyMeasurable)
    (fun q => Filter.Eventually.of_forall fun s _ => by
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (ha q), abs_mul]
      exact mul_le_of_le_one_right (ha q)
        (mul_le_one₀ (Real.abs_cos_le_one _) (abs_nonneg _) (Real.abs_cos_le_one _)))
    (Filter.Eventually.of_forall fun _ _ => hs) intervalIntegrable_const
    (Filter.Eventually.of_forall fun s _ => by
      simpa only [mul_assoc] using
        (clockCosFamily_summable a v ha hs s).hasSum.mul_right (Real.cos (b*s)))
  simpa only [intervalIntegral.integral_const_mul] using hh.tsum_eq.symm
private theorem clockCosFamily_product_mean {ι : Type*} [Countable ι]
    (a v : ι → ℝ) (ha : ∀q, 0 ≤ a q) (hs : Summable a)
    {b : ℝ} (hb : b ≠ 0) :
    Tendsto (fun L : ℝ =>
      (∫s in (0:ℝ)..L, (∑'q, a q*Real.cos (v q*s))*Real.cos (b*s))/L)
      atTop (𝓝 (∑'q, a q*(if v q=b ∨ v q= -b then (1/2:ℝ) else 0))) := by
  have hh := tendsto_tsum_of_dominated_convergence hs
    (fun q => (clock_cos_product_mean hb (v q)).const_mul (a q)) (by
      filter_upwards [eventually_gt_atTop (0:ℝ)] with L hL q
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (ha q)]
      exact mul_le_of_le_one_right (ha q) (clock_cos_product_mean_bound hL (v q) b))
  convert hh using 1
  funext L
  rw [clockCosFamily_product_integral a v ha hs, div_eq_mul_inv, ←tsum_mul_right]
  congr 1
  ext q
  ring
private theorem clockCosFamily_integral {ι : Type*} [Countable ι]
    (a v : ι → ℝ) (ha : ∀q, 0 ≤ a q) (hs : Summable a) (L : ℝ) :
    (∫s in (0:ℝ)..L, ∑'q, a q*Real.cos (v q*s)) =
      ∑'q, a q*(∫s in (0:ℝ)..L, Real.cos (v q*s)) := by
  simpa only [zero_mul, Real.cos_zero, mul_one] using
    clockCosFamily_product_integral a v ha hs 0 L
private theorem clockCosFamily_mean {ι : Type*} [Countable ι]
    (a v : ι → ℝ) (ha : ∀q, 0 ≤ a q) (hs : Summable a) (hv : ∀q, v q ≠ 0) :
    Tendsto (fun L : ℝ => (∫s in (0:ℝ)..L, ∑'q, a q*Real.cos (v q*s))/L)
      atTop (𝓝 0) := by
  have hh := tendsto_tsum_of_dominated_convergence hs
    (fun q => by simpa only [if_neg (hv q), mul_zero] using
      (clock_cos_mean (v q)).const_mul (a q)) (by
      filter_upwards [eventually_gt_atTop (0:ℝ)] with L hL q
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (ha q)]
      apply mul_le_of_le_one_right (ha q)
      simpa only [zero_mul, Real.cos_zero, mul_one] using
        clock_cos_product_mean_bound hL (v q) 0)
  simp only [tsum_zero] at hh
  convert hh using 1
  funext L
  rw [clockCosFamily_integral a v ha hs, div_eq_mul_inv, ←tsum_mul_right]
  congr 1
  ext q
  ring_nf
/-- The oriented positive-part area of `f` on `0..L`, divided by `L`. -/
def liEvenCrossActualClockPositivePartAverage (f : ℝ → ℝ) (L : ℝ) : ℝ :=
  (∫s in (0:ℝ)..L, max (f s) 0)/L
/-- Relative volume of the strict threshold set in `Ioc 0 L`. -/
def liEvenCrossActualClockThresholdDensity (f : ℝ → ℝ) (eta L : ℝ) : ℝ :=
  (volume {s : ℝ | s ∈ Ioc 0 L ∧ eta < f s}).toReal/L
private theorem clock_positive_negative_sum (x : ℝ) : max x 0 + max (-x) 0 = |x| := by
  by_cases hx : 0 ≤ x
  · simp [max_eq_left hx, max_eq_right (neg_nonpos.mpr hx), abs_of_nonneg hx]
  · have hn : x ≤ 0 := le_of_not_ge hx
    simp [max_eq_right hn, max_eq_left (neg_nonneg.mpr hn), abs_of_nonpos hn]
private theorem clock_positive_negative_sub (x : ℝ) : max x 0 - max (-x) 0 = x := by
  by_cases hx : 0 ≤ x
  · simp [max_eq_left hx, max_eq_right (neg_nonpos.mpr hx)]
  · have hn : x ≤ 0 := le_of_not_ge hx
    simp [max_eq_right hn, max_eq_left (neg_nonneg.mpr hn)]
private theorem clock_signed_average_identities {f : ℝ → ℝ} (hf : Continuous f) (L : ℝ) :
    liEvenCrossActualClockPositivePartAverage f L +
      liEvenCrossActualClockPositivePartAverage (fun s => -f s) L =
        (∫s in (0:ℝ)..L, |f s|)/L ∧
    liEvenCrossActualClockPositivePartAverage f L -
      liEvenCrossActualClockPositivePartAverage (fun s => -f s) L =
        (∫s in (0:ℝ)..L, f s)/L := by
  have hp : IntervalIntegrable (fun s => max (f s) 0) volume 0 L :=
    (hf.max continuous_const).intervalIntegrable (0:ℝ) L
  have hn : IntervalIntegrable (fun s => max (-f s) 0) volume 0 L :=
    (hf.neg.max continuous_const).intervalIntegrable (0:ℝ) L
  constructor
  · unfold liEvenCrossActualClockPositivePartAverage
    rw [←add_div, ←intervalIntegral.integral_add hp hn]
    simp_rw [clock_positive_negative_sum]
  · unfold liEvenCrossActualClockPositivePartAverage
    rw [←sub_div, ←intervalIntegral.integral_sub hp hn]
    simp_rw [clock_positive_negative_sub]
private theorem clock_resonance_variation_bound {f : ℝ → ℝ} (hf : Continuous f)
    (b : ℝ) {L : ℝ} (hL : 0 < L) :
    |(∫s in (0:ℝ)..L, f s*Real.cos (b*s))/L| ≤
      liEvenCrossActualClockPositivePartAverage f L +
        liEvenCrossActualClockPositivePartAverage (fun s => -f s) L := by
  rw [(clock_signed_average_identities hf L).1, abs_div, abs_of_pos hL]
  apply div_le_div_of_nonneg_right _ hL.le
  apply (intervalIntegral.abs_integral_le_integral_abs hL.le).trans
  apply intervalIntegral.integral_mono_on hL.le
    ((hf.mul (Real.continuous_cos.comp (continuous_const.mul continuous_id))).abs.intervalIntegrable _ _)
    (hf.abs.intervalIntegrable _ _)
  intro s _
  change |f s*Real.cos (b*s)| ≤ |f s|
  rw [abs_mul]
  exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_cos_le_one _)
private theorem clock_signed_variation {f : ℝ → ℝ} (hf : Continuous f) (b r : ℝ)
    (hr : Tendsto (fun L : ℝ => (∫s in (0:ℝ)..L, f s*Real.cos (b*s))/L) atTop (𝓝 r))
    (hm : Tendsto (fun L : ℝ => (∫s in (0:ℝ)..L, f s)/L) atTop (𝓝 0)) :
    ∀epsilon > 0, ∀ᶠ L : ℝ in atTop,
      |r|/2-epsilon ≤ liEvenCrossActualClockPositivePartAverage f L ∧
      |r|/2-epsilon ≤ liEvenCrossActualClockPositivePartAverage (fun s => -f s) L := by
  intro epsilon hepsilon
  have hp := (hr.abs.add hm).div_const 2
  have hn := (hr.abs.sub hm).div_const 2
  simp only [add_zero, sub_zero] at hp hn
  have hpp := (tendsto_order.1 hp).1 (|r|/2-epsilon) (by linarith)
  have hnn := (tendsto_order.1 hn).1 (|r|/2-epsilon) (by linarith)
  filter_upwards [hpp, hnn, eventually_gt_atTop (0:ℝ)] with L hP hN hL
  have hb := clock_resonance_variation_bound hf b hL
  have he := (clock_signed_average_identities hf L).2
  constructor <;> linarith
private theorem clock_threshold_average_bound {f : ℝ → ℝ} (hf : Continuous f)
    {M eta L : ℝ} (hM : ∀s, |f s| ≤ M) (heta : 0 ≤ eta) (hetam : eta < M)
    (hL : 0 < L) :
    liEvenCrossActualClockPositivePartAverage f L ≤ eta+(M-eta)*
      liEvenCrossActualClockThresholdDensity f eta L := by
  let mu : Measure ℝ := volume.restrict (Ioc 0 L)
  let S : Set ℝ := {s | eta < f s}
  have hS : MeasurableSet S := measurableSet_lt measurable_const hf.measurable
  have hfp : Integrable (fun s => max (f s) 0) mu := by
    exact ((hf.max continuous_const).intervalIntegrable 0 L).1
  have hi : Integrable (S.indicator (fun _ : ℝ => (1:ℝ))) mu :=
    (integrable_const 1).indicator hS
  have hg : Integrable (fun s : ℝ => eta+(M-eta)*S.indicator (fun _ : ℝ => (1:ℝ)) s) mu :=
    (integrable_const eta).add (hi.const_mul (M-eta))
  have hh := integral_mono hfp hg (fun s => by
    by_cases hs : s ∈ S
    · simp only [Set.indicator_of_mem hs, mul_one]
      have he : eta+(M-eta)=M := by ring_nf
      rw [he]
      exact max_le (le_trans (le_abs_self _) (hM s)) (heta.trans hetam.le)
    · simp only [Set.indicator_of_notMem hs, mul_zero, add_zero]
      exact max_le (le_of_not_gt hs) heta)
  rw [integral_add (integrable_const eta) (hi.const_mul (M-eta)), integral_const,
    integral_const_mul, integral_indicator_const 1 hS, measureReal_restrict_apply hS] at hh
  have hm : mu.real univ = L := by
    simp [mu, measureReal_restrict_apply, Real.volume_real_Ioc_of_le hL.le]
  rw [hm] at hh
  have hset : S ∩ Ioc 0 L = {s : ℝ | s ∈ Ioc 0 L ∧ eta < f s} := by ext s; simp [S,and_comm]
  simp only [smul_eq_mul, mul_one, hset] at hh
  unfold liEvenCrossActualClockPositivePartAverage liEvenCrossActualClockThresholdDensity
  rw [intervalIntegral.integral_of_le hL.le]
  change (∫s, max (f s) 0 ∂mu)/L ≤ _
  have hd := div_le_div_of_nonneg_right hh hL.le
  calc
    _ ≤ (L*eta+(M-eta)*volume.real {s : ℝ | s ∈ Ioc 0 L ∧ eta < f s})/L := hd
    _ = _ := by
      dsimp only [Measure.real]
      field_simp [hL.ne']

private theorem clock_threshold_density_from_variation {f : ℝ → ℝ}
    (hf : Continuous f) {M k eta : ℝ} (hM : ∀s, |f s| ≤ M)
    (heta : 0 < eta) (hetam : eta < M)
    (hv : ∀epsilon > 0, ∀ᶠ L : ℝ in atTop,
      k-epsilon ≤ liEvenCrossActualClockPositivePartAverage f L ∧
      k-epsilon ≤ liEvenCrossActualClockPositivePartAverage (fun s => -f s) L) :
    ∀epsilon > 0, ∀ᶠ L : ℝ in atTop,
      (k-eta)/(M-eta)-epsilon ≤ liEvenCrossActualClockThresholdDensity f eta L ∧
      (k-eta)/(M-eta)-epsilon ≤
        liEvenCrossActualClockThresholdDensity (fun s => -f s) eta L := by
  intro epsilon hepsilon
  have hd : 0 < M-eta := sub_pos.mpr hetam
  filter_upwards [hv (epsilon*(M-eta)) (mul_pos hepsilon hd), eventually_gt_atTop (0:ℝ)]
    with L hV hL
  have hp := clock_threshold_average_bound hf hM heta.le hetam hL
  have hn := clock_threshold_average_bound hf.neg
    (fun s => by change |-f s| ≤ M; simpa only [abs_neg] using hM s) heta.le hetam hL
  change liEvenCrossActualClockPositivePartAverage (fun s => -f s) L ≤
    eta+(M-eta)*liEvenCrossActualClockThresholdDensity (fun s => -f s) eta L at hn
  constructor <;> rw [sub_le_iff_le_add, div_le_iff₀ hd] <;> nlinarith [hV.1,hV.2]
private theorem clock_signed_mass_from_variation {f : ℝ → ℝ} {k : ℝ} (hk : 0 < k)
    (hv : ∀epsilon > 0, ∀ᶠ L : ℝ in atTop,
      k-epsilon ≤ liEvenCrossActualClockPositivePartAverage f L ∧
      k-epsilon ≤ liEvenCrossActualClockPositivePartAverage (fun s => -f s) L) :
    Tendsto (fun L : ℝ => ∫s in (0:ℝ)..L, max (f s) 0) atTop atTop ∧
      Tendsto (fun L : ℝ => ∫s in (0:ℝ)..L, max (-f s) 0) atTop atTop := by
  have hv' := hv (k/2) (by linarith)
  have ht : Tendsto (fun L : ℝ => (k/2)*L) atTop atTop :=
    tendsto_id.const_mul_atTop (by linarith)
  constructor
  · apply tendsto_atTop_mono' atTop _ ht
    filter_upwards [hv', eventually_gt_atTop (0:ℝ)] with L hV hL
    have := (le_div_iff₀ hL).mp hV.1
    change (k/2)*L ≤ _
    linarith
  · apply tendsto_atTop_mono' atTop _ ht
    filter_upwards [hv', eventually_gt_atTop (0:ℝ)] with L hV hL
    have := (le_div_iff₀ hL).mp hV.2
    change (k/2)*L ≤ _
    linarith
private theorem clock_threshold_cofinally_from_density {f : ℝ → ℝ} {eta k : ℝ}
    (hk : 0 < k)
    (hd : ∀ᶠ L : ℝ in atTop, k ≤ liEvenCrossActualClockThresholdDensity f eta L) :
    ∀T : ℝ, ∃t > T, eta < f t := by
  intro T
  by_contra hn
  push Not at hn
  have hset (L : ℝ) : {s : ℝ | s ∈ Ioc 0 L ∧ eta < f s} ⊆ Ioc 0 (max T 0) := by
    intro s hs
    refine ⟨hs.1.1, ?_⟩
    have ht : s ≤ T := by by_contra ht; exact (not_lt_of_ge (hn s (lt_of_not_ge ht))) hs.2
    exact ht.trans (le_max_left _ _)
  have hup : ∀ᶠ L : ℝ in atTop,
      liEvenCrossActualClockThresholdDensity f eta L ≤ (max T 0)/L := by
    filter_upwards [eventually_gt_atTop (0:ℝ)] with L hL
    apply div_le_div_of_nonneg_right _ hL.le
    have hh := measureReal_mono (μ:=volume) (hset L)
      (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)
    rw [Real.volume_real_Ioc_of_le (le_max_right T 0), sub_zero] at hh
    exact hh
  have hz : Tendsto (fun L : ℝ => (max T 0)/L) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv,mul_zero] using tendsto_inv_atTop_zero.const_mul (max T 0)
  have hh : k ≤ 0 := ge_of_tendsto hz (hup.and hd |>.mono fun _ h => h.2.trans h.1)
  exact (not_le_of_gt hk) hh

private def clockRealFrequency (q : XiZeroCopy) : ℝ := ((xiSpectralPoint q)⁻¹).re
private def clockRealWeight (q : XiZeroCopy) : ℝ := ‖(xiSpectralPoint q)⁻¹‖^2
private def clockGreenWeight (q : XiZeroCopy) : ℝ :=
  clockRealWeight q*(clockRealWeight q+liEvenCrossActualClockGreenRate^2)
private theorem clockRealWeight_summable : Summable clockRealWeight := by
  change Summable (fun q : XiZeroCopy => ‖(xiSpectralPoint q)⁻¹‖^2)
  simpa [clockRealWeight,xiZeroCopyReciprocalSquare,norm_pow,norm_inv,inv_pow] using summable_xiShiftAbsoluteMass 0
private theorem clockRealWeight_nonneg (q : XiZeroCopy) : 0 ≤ clockRealWeight q := sq_nonneg _
private theorem clockRealWeight_le_one (q : XiZeroCopy) : clockRealWeight q ≤ 1 := by
  have hh := norm_xiZeroCopyReciprocalSquare_lt_one_div_oneHundredFifty q
  have he : ‖xiZeroCopyReciprocalSquare q‖ = clockRealWeight q := by
    simp [clockRealWeight,xiZeroCopyReciprocalSquare,norm_pow]
  rw [he] at hh
  linarith
private theorem clockGreenWeight_nonneg (q : XiZeroCopy) : 0 ≤ clockGreenWeight q :=
  mul_nonneg (clockRealWeight_nonneg q) (add_nonneg (clockRealWeight_nonneg q) (sq_nonneg _))
private theorem clockGreenWeight_summable : Summable clockGreenWeight := by
  apply Summable.of_nonneg_of_le clockGreenWeight_nonneg _
    (clockRealWeight_summable.mul_left (1+liEvenCrossActualClockGreenRate^2))
  intro q
  dsimp [clockGreenWeight]
  nlinarith [clockRealWeight_nonneg q,clockRealWeight_le_one q]
private theorem clockFrequency_of_rh (hRH : RiemannHypothesis) (q : XiZeroCopy) :
    (xiSpectralPoint q)⁻¹ = (clockRealFrequency q : ℂ) := by
  obtain ⟨u,hu⟩ := xiSpectralPoint_real_of_rh hRH q
  simp [clockRealFrequency,hu, ←Complex.ofReal_inv]
private theorem clockRealFrequency_ne_zero (hRH : RiemannHypothesis) (q : XiZeroCopy) :
    clockRealFrequency q ≠ 0 := by
  intro hh
  have hw := clockFrequency_of_rh hRH q
  rw [hh,Complex.ofReal_zero] at hw
  exact inv_ne_zero (xiSpectralPoint_ne_zero q) hw
private theorem clockRealWeight_of_rh (hRH : RiemannHypothesis) (q : XiZeroCopy) :
    clockRealWeight q = clockRealFrequency q^2 := by
  unfold clockRealWeight
  rw [clockFrequency_of_rh hRH q,Complex.norm_real,Real.norm_eq_abs,sq_abs]
private theorem clockDerivative_cosFamily (hRH : RiemannHypothesis) (t : ℝ) :
    liEvenCrossActualClockDerivative t =
      ∑'q, clockRealWeight q*Real.cos (clockRealFrequency q*t) := by
  rw [liEvenCrossActualClockDerivative_eq_tsum_cos]
  have he : (∑'q : XiZeroCopy, (xiSpectralPoint q)⁻¹^2*
      Complex.cos ((t:ℂ)*(xiSpectralPoint q)⁻¹)) =
      ((∑'q, clockRealWeight q*Real.cos (clockRealFrequency q*t) : ℝ):ℂ) := by
    rw [Complex.ofReal_tsum]
    congr 1
    ext q
    rw [clockFrequency_of_rh hRH q,clockRealWeight_of_rh hRH q]
    simp [mul_comm]
  rw [he,Complex.ofReal_re]
private theorem clockGreen_cosFamily (hRH : RiemannHypothesis) (t : ℝ) :
    liEvenCrossActualClockGreenForcing t =
      -(∑'q, clockGreenWeight q*Real.cos (clockRealFrequency q*t)) := by
  rw [liEvenCrossActualClockGreenForcing_eq_tsum_cos]
  have he : (∑'q : XiZeroCopy, (xiSpectralPoint q)⁻¹^2*
      ((xiSpectralPoint q)⁻¹^2+((liEvenCrossActualClockGreenRate^2:ℝ):ℂ))*
      Complex.cos ((t:ℂ)*(xiSpectralPoint q)⁻¹)) =
      ((∑'q, clockGreenWeight q*Real.cos (clockRealFrequency q*t) : ℝ):ℂ) := by
    rw [Complex.ofReal_tsum]
    congr 1
    ext q
    rw [clockFrequency_of_rh hRH q]
    unfold clockGreenWeight
    rw [clockRealWeight_of_rh hRH q]
    simp [mul_comm]
  rw [he,Complex.ofReal_re]
private theorem clockRealFrequency_tie (hRH : RiemannHypothesis) (q q0 : XiZeroCopy) :
    (clockRealFrequency q=clockRealFrequency q0 ∨
      clockRealFrequency q= -clockRealFrequency q0) ↔
      ((xiSpectralPoint q)⁻¹=(xiSpectralPoint q0)⁻¹ ∨
        (xiSpectralPoint q)⁻¹= -(xiSpectralPoint q0)⁻¹) := by
  rw [clockFrequency_of_rh hRH q,clockFrequency_of_rh hRH q0]
  norm_cast
private theorem clock_resonant_sum (hRH : RiemannHypothesis) (q0 : XiZeroCopy) :
    (∑'q, clockRealWeight q*(if clockRealFrequency q=clockRealFrequency q0 ∨
      clockRealFrequency q= -clockRealFrequency q0 then (1/2:ℝ) else 0)) =
        liEvenCrossActualClockResonantMass q0/2 := by
  classical
  unfold liEvenCrossActualClockResonantMass
  simp_rw [div_eq_mul_inv]
  rw [←tsum_mul_right]
  congr 1
  ext q
  by_cases ht : clockRealFrequency q=clockRealFrequency q0 ∨
    clockRealFrequency q= -clockRealFrequency q0
  · have hc := (clockRealFrequency_tie hRH q q0).mp ht
    simp only [if_pos ht,if_pos hc,clockRealWeight]
    ring
  · have hc : ¬((xiSpectralPoint q)⁻¹=(xiSpectralPoint q0)⁻¹ ∨
        (xiSpectralPoint q)⁻¹= -(xiSpectralPoint q0)⁻¹) := fun hh =>
      ht ((clockRealFrequency_tie hRH q q0).mpr hh)
    simp only [if_neg ht,if_neg hc,mul_zero,zero_mul]
private theorem clock_green_resonant_sum (hRH : RiemannHypothesis) (q0 : XiZeroCopy) :
    (∑'q, clockGreenWeight q*(if clockRealFrequency q=clockRealFrequency q0 ∨
      clockRealFrequency q= -clockRealFrequency q0 then (1/2:ℝ) else 0)) =
      (clockRealFrequency q0^2+liEvenCrossActualClockGreenRate^2)*
        liEvenCrossActualClockResonantMass q0/2 := by
  classical
  have he : (clockRealFrequency q0^2+liEvenCrossActualClockGreenRate^2)*
      liEvenCrossActualClockResonantMass q0/2 =
      (clockRealFrequency q0^2+liEvenCrossActualClockGreenRate^2)*
        (liEvenCrossActualClockResonantMass q0/2) := by ring_nf
  rw [he,←clock_resonant_sum hRH q0,←tsum_mul_left]
  congr 1
  ext q
  by_cases ht : clockRealFrequency q=clockRealFrequency q0 ∨
      clockRealFrequency q= -clockRealFrequency q0
  · have hq : clockRealWeight q=clockRealFrequency q0^2 := by
      rw [clockRealWeight_of_rh hRH q]
      rcases ht with ht|ht
      · rw [ht]
      · simp only [ht,neg_sq]
    simp only [if_pos ht,clockGreenWeight,hq]
    ring_nf
  · simp only [if_neg ht,mul_zero]

/-- Under RH, the derivative's resonant Cesàro average is half the complete mass
of both frequency ties `w = ±w₀`. -/
 theorem tendsto_liEvenCrossActualClockDerivative_resonantAverage (hRH : RiemannHypothesis)
    (q0 : XiZeroCopy) :
    Tendsto (fun L : ℝ => (∫s in (0:ℝ)..L,
      liEvenCrossActualClockDerivative s*Real.cos (((xiSpectralPoint q0)⁻¹).re*s))/L)
      atTop (𝓝 (liEvenCrossActualClockResonantMass q0/2)) := by
  have hh := clockCosFamily_product_mean clockRealWeight clockRealFrequency
      clockRealWeight_nonneg clockRealWeight_summable (clockRealFrequency_ne_zero hRH q0)
  rw [clock_resonant_sum hRH q0] at hh
  simpa only [clockDerivative_cosFamily hRH,clockRealFrequency] using hh
/-- Under RH, the forcing's resonant Cesàro average is minus half the complete
resonant mass weighted by `b² + ω²`. -/
 theorem tendsto_liEvenCrossActualClockGreenForcing_resonantAverage (hRH : RiemannHypothesis)
    (q0 : XiZeroCopy) :
    Tendsto (fun L : ℝ => (∫s in (0:ℝ)..L,
      liEvenCrossActualClockGreenForcing s*Real.cos (((xiSpectralPoint q0)⁻¹).re*s))/L)
      atTop (𝓝 (-2*((((xiSpectralPoint q0)⁻¹).re^2+liEvenCrossActualClockGreenRate^2)*
        liEvenCrossActualClockResonantMass q0/4))) := by
  have hh := (clockCosFamily_product_mean clockGreenWeight clockRealFrequency
    clockGreenWeight_nonneg clockGreenWeight_summable (clockRealFrequency_ne_zero hRH q0)).neg
  simp only [clock_green_resonant_sum hRH q0] at hh
  convert hh using 1
  · funext L
    simp_rw [clockGreen_cosFamily hRH,neg_mul,intervalIntegral.integral_neg,neg_div]
    rfl
  · dsimp [clockRealFrequency]
    ring_nf
/-- Under RH, the full derivative has zero Cesàro mean. -/
 theorem tendsto_liEvenCrossActualClockDerivative_average_zero (hRH : RiemannHypothesis) :
    Tendsto (fun L : ℝ => (∫s in (0:ℝ)..L, liEvenCrossActualClockDerivative s)/L)
      atTop (𝓝 0) := by
  simpa only [clockDerivative_cosFamily hRH] using clockCosFamily_mean
    clockRealWeight clockRealFrequency clockRealWeight_nonneg clockRealWeight_summable
      (clockRealFrequency_ne_zero hRH)
/-- Under RH, the full massive forcing has zero Cesàro mean. -/
 theorem tendsto_liEvenCrossActualClockGreenForcing_average_zero (hRH : RiemannHypothesis) :
    Tendsto (fun L : ℝ => (∫s in (0:ℝ)..L, liEvenCrossActualClockGreenForcing s)/L)
      atTop (𝓝 0) := by
  simpa only [clockGreen_cosFamily hRH,intervalIntegral.integral_neg,neg_div,neg_zero] using
    (clockCosFamily_mean clockGreenWeight clockRealFrequency clockGreenWeight_nonneg
      clockGreenWeight_summable (clockRealFrequency_ne_zero hRH)).neg

private def clockGreenResonantFloor (q0 : XiZeroCopy) : ℝ :=
  (((xiSpectralPoint q0)⁻¹).re^2+liEvenCrossActualClockGreenRate^2)*
    liEvenCrossActualClockResonantMass q0/4
private theorem clockGreenResonantFloor_pos (q0 : XiZeroCopy) :
    0 < clockGreenResonantFloor q0 := by
  have hw := liEvenCrossActualClockGreenRate_bounds.2.1
  have hs := (liEvenCrossActualClockResonantMass_bounds q0).1
  dsimp [clockGreenResonantFloor]
  exact div_pos (mul_pos (by nlinarith [sq_nonneg (((xiSpectralPoint q0)⁻¹).re)]) hs) (by norm_num)
private theorem clockGreenResonantFloor_le_mass (hRH : RiemannHypothesis) (q0 : XiZeroCopy) :
    clockGreenResonantFloor q0 ≤ liEvenCrossActualClockGreenAbsoluteMass/4 := by
  classical
  let f := fun q => clockGreenWeight q*(if clockRealFrequency q=clockRealFrequency q0 ∨
      clockRealFrequency q= -clockRealFrequency q0 then (1/2:ℝ) else 0)
  have hs : Summable f := by
    apply clockGreenWeight_summable.of_norm_bounded
    intro q
    dsimp [f]
    by_cases ht : clockRealFrequency q=clockRealFrequency q0 ∨
      clockRealFrequency q= -clockRealFrequency q0
    · simp only [if_pos ht]
      have hh : clockGreenWeight q*(1/2) ≤ clockGreenWeight q := by
        nlinarith [clockGreenWeight_nonneg q]
      simpa only [Real.norm_eq_abs,abs_mul,abs_of_nonneg (clockGreenWeight_nonneg q),
        abs_of_pos (by norm_num : (0:ℝ)<1/2)] using hh
    · simp only [if_neg ht,mul_zero,abs_zero]
      exact clockGreenWeight_nonneg q
  have hh := hs.tsum_le_tsum (g:=fun q => clockGreenWeight q/2) (by
    intro q
    dsimp [f]
    split_ifs
    · simpa only [div_eq_mul_inv,one_mul] using (le_refl (clockGreenWeight q*2⁻¹))
    · simpa only [mul_zero] using div_nonneg (clockGreenWeight_nonneg q) (by norm_num : (0:ℝ)≤2))
    (clockGreenWeight_summable.div_const 2)
  have hm : (∑'q, clockGreenWeight q) = liEvenCrossActualClockGreenAbsoluteMass := rfl
  change (∑'q, clockGreenWeight q*(if clockRealFrequency q=clockRealFrequency q0 ∨
      clockRealFrequency q= -clockRealFrequency q0 then (1/2:ℝ) else 0)) ≤ _ at hh
  rw [clock_green_resonant_sum hRH q0,tsum_div_const,hm] at hh
  dsimp [clockGreenResonantFloor,clockRealFrequency] at hh ⊢
  linarith
/-- Under RH, both derivative signs have positive-part average at least `S/4`
up to every eventual positive error, where `S` retains all resonant copies. -/
 theorem liEvenCrossActualClockDerivative_signedVariation (hRH : RiemannHypothesis)
    (q0 : XiZeroCopy) : ∀epsilon > 0, ∀ᶠ L : ℝ in atTop,
    liEvenCrossActualClockResonantMass q0/4-epsilon ≤
      liEvenCrossActualClockPositivePartAverage liEvenCrossActualClockDerivative L ∧
    liEvenCrossActualClockResonantMass q0/4-epsilon ≤
      liEvenCrossActualClockPositivePartAverage (fun s => -liEvenCrossActualClockDerivative s) L := by
  have hh := clock_signed_variation continuous_liEvenCrossActualClockDerivative
    (((xiSpectralPoint q0)⁻¹).re) (liEvenCrossActualClockResonantMass q0/2)
    (tendsto_liEvenCrossActualClockDerivative_resonantAverage hRH q0)
    (tendsto_liEvenCrossActualClockDerivative_average_zero hRH)
  have he : |liEvenCrossActualClockResonantMass q0/2|/2 =
      liEvenCrossActualClockResonantMass q0/4 := by
    rw [abs_of_pos (div_pos (liEvenCrossActualClockResonantMass_bounds q0).1 (by norm_num))]
    ring_nf
  simpa only [he] using hh
/-- Under RH, both forcing signs have positive-part average at least
`(b² + ω²) S/4` up to every eventual positive error. -/
 theorem liEvenCrossActualClockGreenForcing_signedVariation (hRH : RiemannHypothesis)
    (q0 : XiZeroCopy) : ∀epsilon > 0, ∀ᶠ L : ℝ in atTop,
    ((((xiSpectralPoint q0)⁻¹).re^2+liEvenCrossActualClockGreenRate^2)*
      liEvenCrossActualClockResonantMass q0/4)-epsilon ≤
        liEvenCrossActualClockPositivePartAverage liEvenCrossActualClockGreenForcing L ∧
    ((((xiSpectralPoint q0)⁻¹).re^2+liEvenCrossActualClockGreenRate^2)*
      liEvenCrossActualClockResonantMass q0/4)-epsilon ≤
        liEvenCrossActualClockPositivePartAverage (fun s => -liEvenCrossActualClockGreenForcing s) L := by
  have hh := clock_signed_variation continuous_liEvenCrossActualClockGreenForcing
    (((xiSpectralPoint q0)⁻¹).re) (-2*clockGreenResonantFloor q0)
    (by simpa only [clockGreenResonantFloor] using
      tendsto_liEvenCrossActualClockGreenForcing_resonantAverage hRH q0)
    (tendsto_liEvenCrossActualClockGreenForcing_average_zero hRH)
  have he : |-2*clockGreenResonantFloor q0|/2 = clockGreenResonantFloor q0 := by
    rw [abs_of_neg (by nlinarith [clockGreenResonantFloor_pos q0])]
    ring_nf
  rw [he] at hh
  simpa only [clockGreenResonantFloor] using hh
/-- Under RH, both derivative threshold sets satisfy the quantitative density
floor from the complete resonance mass and the actual absolute mass. -/
 theorem liEvenCrossActualClockDerivative_thresholdDensity (hRH : RiemannHypothesis)
    (q0 : XiZeroCopy) {eta : ℝ} (heta : 0 < eta)
    (he : eta < liEvenCrossActualClockResonantMass q0/4) :
    ∀epsilon > 0, ∀ᶠ L : ℝ in atTop,
    (liEvenCrossActualClockResonantMass q0/4-eta)/(xiShiftAbsoluteMass 0-eta)-epsilon ≤
      liEvenCrossActualClockThresholdDensity liEvenCrossActualClockDerivative eta L ∧
    (liEvenCrossActualClockResonantMass q0/4-eta)/(xiShiftAbsoluteMass 0-eta)-epsilon ≤
      liEvenCrossActualClockThresholdDensity (fun s => -liEvenCrossActualClockDerivative s) eta L := by
  apply clock_threshold_density_from_variation continuous_liEvenCrossActualClockDerivative
    (abs_liEvenCrossActualClockDerivative_le_of_rh hRH) heta _
    (liEvenCrossActualClockDerivative_signedVariation hRH q0)
  linarith [(liEvenCrossActualClockResonantMass_bounds q0).2]
/-- Under RH, both forcing threshold sets satisfy the quantitative density
floor from the weighted resonance mass and the actual forcing absolute mass. -/
 theorem liEvenCrossActualClockGreenForcing_thresholdDensity (hRH : RiemannHypothesis)
    (q0 : XiZeroCopy) {eta : ℝ} (heta : 0 < eta)
    (he : eta < ((((xiSpectralPoint q0)⁻¹).re^2+liEvenCrossActualClockGreenRate^2)*
      liEvenCrossActualClockResonantMass q0/4)) :
    ∀epsilon > 0, ∀ᶠ L : ℝ in atTop,
    (((((xiSpectralPoint q0)⁻¹).re^2+liEvenCrossActualClockGreenRate^2)*
      liEvenCrossActualClockResonantMass q0/4)-eta)/(liEvenCrossActualClockGreenAbsoluteMass-eta)-epsilon ≤
      liEvenCrossActualClockThresholdDensity liEvenCrossActualClockGreenForcing eta L ∧
    (((((xiSpectralPoint q0)⁻¹).re^2+liEvenCrossActualClockGreenRate^2)*
      liEvenCrossActualClockResonantMass q0/4)-eta)/(liEvenCrossActualClockGreenAbsoluteMass-eta)-epsilon ≤
      liEvenCrossActualClockThresholdDensity (fun s => -liEvenCrossActualClockGreenForcing s) eta L := by
  apply clock_threshold_density_from_variation continuous_liEvenCrossActualClockGreenForcing
    (abs_liEvenCrossActualClockGreenForcing_le_of_rh hRH) heta _
    (liEvenCrossActualClockGreenForcing_signedVariation hRH q0)
  have hh := clockGreenResonantFloor_le_mass hRH q0
  dsimp [clockGreenResonantFloor] at hh
  linarith [liEvenCrossActualClockGreenAbsoluteMass_bounds.1]
private theorem clock_thresholds_from_density {f : ℝ → ℝ} {eta M k : ℝ}
    (he : eta < k) (hM : eta < M)
    (hd : ∀epsilon > 0, ∀ᶠ L : ℝ in atTop,
      (k-eta)/(M-eta)-epsilon ≤ liEvenCrossActualClockThresholdDensity f eta L ∧
      (k-eta)/(M-eta)-epsilon ≤
        liEvenCrossActualClockThresholdDensity (fun s => -f s) eta L) :
    ∀T : ℝ, (∃t > T, eta < f t) ∧ (∃t > T, f t < -eta) := by
  have hk : 0 < (k-eta)/(M-eta) := div_pos (sub_pos.mpr he) (sub_pos.mpr hM)
  have hD := hd (((k-eta)/(M-eta))/2) (half_pos hk)
  have hp := clock_threshold_cofinally_from_density (f:=f) (eta:=eta) (half_pos hk)
    (hD.mono fun _ h => by linarith [h.1])
  have hn := clock_threshold_cofinally_from_density (f:=fun s => -f s) (eta:=eta) (half_pos hk)
    (hD.mono fun _ h => by linarith [h.2])
  intro T
  refine ⟨hp T, ?_⟩
  obtain ⟨t,ht,hf⟩ := hn T
  exact ⟨t,ht,by linarith⟩
/-- Under RH, every strict threshold below `S/4` is exceeded cofinally by each
derivative sign. -/
 theorem liEvenCrossActualClockDerivative_threshold_cofinally (hRH : RiemannHypothesis)
    (q0 : XiZeroCopy) {eta : ℝ} (heta : 0 < eta)
    (he : eta < liEvenCrossActualClockResonantMass q0/4) :
    ∀T : ℝ, (∃t > T, eta < liEvenCrossActualClockDerivative t) ∧
      (∃t > T, liEvenCrossActualClockDerivative t < -eta) := by
  apply clock_thresholds_from_density he _
    (liEvenCrossActualClockDerivative_thresholdDensity hRH q0 heta he)
  linarith [(liEvenCrossActualClockResonantMass_bounds q0).2]
/-- Under RH, every strict threshold below `(b² + ω²) S/4` is exceeded
cofinally by each forcing sign. -/
 theorem liEvenCrossActualClockGreenForcing_threshold_cofinally (hRH : RiemannHypothesis)
    (q0 : XiZeroCopy) {eta : ℝ} (heta : 0 < eta)
    (he : eta < ((((xiSpectralPoint q0)⁻¹).re^2+liEvenCrossActualClockGreenRate^2)*
      liEvenCrossActualClockResonantMass q0/4)) :
    ∀T : ℝ, (∃t > T, eta < liEvenCrossActualClockGreenForcing t) ∧
      (∃t > T, liEvenCrossActualClockGreenForcing t < -eta) := by
  apply clock_thresholds_from_density he _
    (liEvenCrossActualClockGreenForcing_thresholdDensity hRH q0 heta he)
  have hh := clockGreenResonantFloor_le_mass hRH q0
  dsimp [clockGreenResonantFloor] at hh
  linarith [liEvenCrossActualClockGreenAbsoluteMass_bounds.1]
/-- Under RH, the derivative's positive and negative part areas both tend to infinity. -/
 theorem tendsto_liEvenCrossActualClockDerivative_signedMass_atTop (hRH : RiemannHypothesis)
    (q0 : XiZeroCopy) :
    Tendsto (fun L : ℝ => ∫s in (0:ℝ)..L, max (liEvenCrossActualClockDerivative s) 0) atTop atTop ∧
    Tendsto (fun L : ℝ => ∫s in (0:ℝ)..L, max (-liEvenCrossActualClockDerivative s) 0) atTop atTop := by
  exact clock_signed_mass_from_variation
    (div_pos (liEvenCrossActualClockResonantMass_bounds q0).1 (by norm_num))
    (liEvenCrossActualClockDerivative_signedVariation hRH q0)
/-- Under RH, the forcing's positive and negative part areas both tend to infinity. -/
 theorem tendsto_liEvenCrossActualClockGreenForcing_signedMass_atTop (hRH : RiemannHypothesis)
    (q0 : XiZeroCopy) :
    Tendsto (fun L : ℝ => ∫s in (0:ℝ)..L, max (liEvenCrossActualClockGreenForcing s) 0) atTop atTop ∧
    Tendsto (fun L : ℝ => ∫s in (0:ℝ)..L, max (-liEvenCrossActualClockGreenForcing s) 0) atTop atTop := by
  exact clock_signed_mass_from_variation (clockGreenResonantFloor_pos q0)
    (liEvenCrossActualClockGreenForcing_signedVariation hRH q0)

private theorem clock_integral_decay {w T t : ℝ} (hw : 0 < w) :
    (∫s in T..t, Real.exp (-w*s)) = (Real.exp (-w*T)-Real.exp (-w*t))/w := by
  have hd (s : ℝ) : HasDerivAt (fun s : ℝ => -Real.exp (-w*s)/w)
      (Real.exp (-w*s)) s := by
    simpa [hw.ne',neg_mul,div_eq_mul_inv,mul_assoc] using
      (((Real.hasDerivAt_exp (-w*s)).comp s ((hasDerivAt_id s).const_mul (-w))).neg.div_const w)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hd s)
    ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).intervalIntegrable T t)]
  ring_nf
private theorem clock_primitive_tail_upper {F h : ℝ → ℝ} (hc : Continuous h)
    (hd : ∀t, HasDerivAt F (h t) t) {w C T : ℝ} (hw : 0 < w) (hC : 0 ≤ C)
    (hh : ∀s ≥ T, h s ≤ C*Real.exp (-w*s)) :
    ∀t ≥ T, F t ≤ F T+C*Real.exp (-w*T)/w := by
  intro t ht
  have hi : (∫s in T..t, h s) ≤ (∫s in T..t, C*Real.exp (-w*s)) :=
    intervalIntegral.integral_mono_on ht (hc.intervalIntegrable T t)
    ((continuous_const.mul (Real.continuous_exp.comp
      (continuous_const.mul continuous_id))).intervalIntegrable T t) (fun s hs => hh s hs.1)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hd s)
    (hc.intervalIntegrable T t), intervalIntegral.integral_const_mul, clock_integral_decay hw] at hi
  have he : 0 ≤ C*Real.exp (-w*t)/w := div_nonneg (mul_nonneg hC (Real.exp_pos _).le) hw.le
  have hm : C*((Real.exp (-w*T)-Real.exp (-w*t))/w) =
      C*Real.exp (-w*T)/w-C*Real.exp (-w*t)/w := by ring_nf
  rw [hm] at hi
  linarith
private theorem clock_primitive_tail_lower {F h : ℝ → ℝ} (hc : Continuous h)
    (hd : ∀t, HasDerivAt F (h t) t) {w C T : ℝ} (hw : 0 < w) (hC : 0 ≤ C)
    (hh : ∀s ≥ T, -C*Real.exp (-w*s) ≤ h s) :
    ∀t ≥ T, F T-C*Real.exp (-w*T)/w ≤ F t := by
  have hu := clock_primitive_tail_upper hc.neg (fun t => (hd t).neg) hw hC
    (fun s hs => by change -h s ≤ C*Real.exp (-w*s); linarith [hh s hs])
  intro t ht
  have := hu t ht
  change -F t ≤ -F T+C*Real.exp (-w*T)/w at this
  linarith
private theorem clock_green_tail_bounds {h G : ℝ → ℝ} {w : ℝ} (hw : 0 < w)
    (hk : ∀t, Integrable (fun s : ℝ => Real.exp (-w*|t-s|)*G s))
    (he : ∀t, h t = -(1/(2*w))*(∫s : ℝ, Real.exp (-w*|t-s|)*G s)) (T : ℝ) :
    ∃C ≥ 0,
      ((∀s > T, 0 ≤ G s) → ∀t ≥ T, h t ≤ C*Real.exp (-w*t)) ∧
      ((∀s > T, G s ≤ 0) → ∀t ≥ T, -C*Real.exp (-w*t) ≤ h t) := by
  let P : ℝ := ∫s in Iic T, Real.exp (w*s)*G s
  have hp : IntegrableOn (fun s : ℝ => Real.exp (w*s)*G s) (Iic T) := by
    have hp0 : IntegrableOn
        (fun s : ℝ => Real.exp (w*T)*(Real.exp (-w*|T-s|)*G s)) (Iic T) :=
      (hk T).integrableOn.const_mul (Real.exp (w*T))
    apply hp0.congr_fun _ measurableSet_Iic
    intro s hs
    simp only [mem_Iic] at hs
    dsimp only
    rw [abs_of_nonneg (sub_nonneg.mpr hs), ←mul_assoc, ←Real.exp_add]
    congr 1
    ring_nf
  have hpre {t : ℝ} (ht : T ≤ t) :
      (∫s in Iic T, Real.exp (-w*|t-s|)*G s) = Real.exp (-w*t)*P := by
    dsimp only [P]
    rw [←integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Iic
    intro s hs
    simp only [mem_Iic] at hs
    dsimp only
    rw [abs_of_nonneg (sub_nonneg.mpr (hs.trans ht)), ←mul_assoc, ←Real.exp_add]
    congr 1
    ring_nf
  refine ⟨|P|/(2*w), div_nonneg (abs_nonneg _) (by positivity), ?_, ?_⟩
  · intro hG t ht
    have htail : 0 ≤ ∫s in Ioi T, Real.exp (-w*|t-s|)*G s := by
      apply integral_nonneg_of_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
      exact mul_nonneg (Real.exp_pos _).le (hG s hs)
    have hsplit := integral_add_compl (s:=Iic T) measurableSet_Iic (hk t)
    rw [compl_Iic,hpre ht] at hsplit
    rw [he t,←hsplit]
    have hcoeff : 0 < 1/(2*w) := by positivity
    have hP : -P ≤ |P| := neg_le_abs P
    have hx : 0 < Real.exp (-w*t) := Real.exp_pos _
    have halg : -(1/(2*w))*(Real.exp (-w*t)*P) = -P/(2*w)*Real.exp (-w*t) := by ring_nf
    calc
      _ ≤ -(1/(2*w))*(Real.exp (-w*t)*P) := by nlinarith
      _ ≤ _ := by rw [halg]; gcongr
  · intro hG t ht
    have htail : (∫s in Ioi T, Real.exp (-w*|t-s|)*G s) ≤ 0 := by
      apply integral_nonpos_of_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
      exact mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le (hG s hs)
    have hsplit := integral_add_compl (s:=Iic T) measurableSet_Iic (hk t)
    rw [compl_Iic,hpre ht] at hsplit
    rw [he t,←hsplit]
    have hcoeff : 0 < 1/(2*w) := by positivity
    have hP : P ≤ |P| := le_abs_self P
    have hx : 0 < Real.exp (-w*t) := Real.exp_pos _
    have halg : -(1/(2*w))*(Real.exp (-w*t)*P) = -P/(2*w)*Real.exp (-w*t) := by ring_nf
    calc
      _ ≤ -(1/(2*w))*(Real.exp (-w*t)*P) := by
        rw [halg]
        apply mul_le_mul_of_nonneg_right _ hx.le
        simpa only [neg_div] using neg_le_neg
          (div_le_div_of_nonneg_right hP (show 0 ≤ 2*w by positivity))
      _ ≤ _ := by nlinarith

/-- The literal clock derivative is strictly negative cofinally, unconditionally. -/
 theorem liEvenCrossActualClockDerivative_negative_cofinally :
    ∀T : ℝ, ∃t > T, liEvenCrossActualClockDerivative t < 0 := by
  classical
  let q0 : XiZeroCopy := Classical.choice nonempty_xiZeroCopy
  intro T
  by_cases hRH : RiemannHypothesis
  · obtain ⟨t,ht,hh⟩ := (liEvenCrossActualClockDerivative_threshold_cofinally hRH q0
      (eta:=liEvenCrossActualClockResonantMass q0/8)
      (div_pos (liEvenCrossActualClockResonantMass_bounds q0).1 (by norm_num))
      (by linarith [(liEvenCrossActualClockResonantMass_bounds q0).1]) T).2
    exact ⟨t,ht,by linarith [(liEvenCrossActualClockResonantMass_bounds q0).1]⟩
  · by_contra hn
    push Not at hn
    let U : ℝ := T+1
    have hu := clock_primitive_tail_lower continuous_liEvenCrossActualClockDerivative
      hasDerivAt_liEvenCrossActualClockResponse (w:=1) (C:=0) (T:=U)
      (by norm_num) le_rfl (fun s hs => by
        simpa only [neg_zero,zero_mul] using hn s (by dsimp [U] at hs; linarith))
    obtain ⟨t,ht,hh⟩ := liEvenCrossActualClock_unbounded_below_cofinally_of_not_rh hRH
      (liEvenCrossActualClockResponse U-1) U
    have hb := hu t ht
    simp only [zero_mul,zero_div,sub_zero] at hb
    linarith
/-- The literal clock derivative is strictly positive cofinally, unconditionally. -/
 theorem liEvenCrossActualClockDerivative_positive_cofinally :
    ∀T : ℝ, ∃t > T, 0 < liEvenCrossActualClockDerivative t := by
  intro T
  by_contra hn
  push Not at hn
  let U : ℝ := T+1
  have hu := clock_primitive_tail_upper continuous_liEvenCrossActualClockDerivative
    hasDerivAt_liEvenCrossActualClockResponse (w:=1) (C:=0) (T:=U)
    (by norm_num) le_rfl (fun s hs => by
      simpa only [zero_mul] using hn s (by dsimp [U] at hs; linarith))
  obtain ⟨t,ht,hh⟩ := liEvenCrossActualClockResponse_unboundedAbove_cofinally
    (liEvenCrossActualClockResponse U+1) U
  have hb := hu t ht.le
  simp only [zero_mul,zero_div,add_zero] at hb
  linarith
/-- The literal massive forcing is strictly negative cofinally, unconditionally. -/
 theorem liEvenCrossActualClockGreenForcing_negative_cofinally :
    ∀T : ℝ, ∃t > T, liEvenCrossActualClockGreenForcing t < 0 := by
  intro T
  by_contra hn
  push Not at hn
  let U : ℝ := T+1
  have hw : 0 < liEvenCrossActualClockGreenRate :=
    lt_trans (by norm_num) liEvenCrossActualClockGreenRate_bounds.2.1
  obtain ⟨C,hC,hup,_⟩ := clock_green_tail_bounds hw
    integrable_liEvenCrossActualClockGreenKernel
    liEvenCrossActualClockDerivative_eq_greenIntegral U
  have hu := clock_primitive_tail_upper continuous_liEvenCrossActualClockDerivative
    hasDerivAt_liEvenCrossActualClockResponse hw hC
    (hup (fun s hs => hn s (by dsimp [U] at hs; linarith)))
  obtain ⟨t,ht,hh⟩ := liEvenCrossActualClockResponse_unboundedAbove_cofinally
    (liEvenCrossActualClockResponse U+C*Real.exp (-liEvenCrossActualClockGreenRate*U)/
      liEvenCrossActualClockGreenRate+1) U
  have hb := hu t ht.le
  linarith
/-- The literal massive forcing is strictly positive cofinally, unconditionally. -/
 theorem liEvenCrossActualClockGreenForcing_positive_cofinally :
    ∀T : ℝ, ∃t > T, 0 < liEvenCrossActualClockGreenForcing t := by
  classical
  let q0 : XiZeroCopy := Classical.choice nonempty_xiZeroCopy
  intro T
  by_cases hRH : RiemannHypothesis
  · obtain ⟨t,ht,hh⟩ := (liEvenCrossActualClockGreenForcing_threshold_cofinally hRH q0
      (eta:=clockGreenResonantFloor q0/2) (half_pos (clockGreenResonantFloor_pos q0))
      (by change clockGreenResonantFloor q0/2 < clockGreenResonantFloor q0
          linarith [clockGreenResonantFloor_pos q0]) T).1
    exact ⟨t,ht,lt_trans (half_pos (clockGreenResonantFloor_pos q0)) hh⟩
  · by_contra hn
    push Not at hn
    let U : ℝ := T+1
    have hw : 0 < liEvenCrossActualClockGreenRate :=
      lt_trans (by norm_num) liEvenCrossActualClockGreenRate_bounds.2.1
    obtain ⟨C,hC,_,hlow⟩ := clock_green_tail_bounds hw
      integrable_liEvenCrossActualClockGreenKernel
      liEvenCrossActualClockDerivative_eq_greenIntegral U
    have hu := clock_primitive_tail_lower continuous_liEvenCrossActualClockDerivative
      hasDerivAt_liEvenCrossActualClockResponse hw hC
      (hlow (fun s hs => hn s (by dsimp [U] at hs; linarith)))
    obtain ⟨t,ht,hh⟩ := liEvenCrossActualClock_unbounded_below_cofinally_of_not_rh hRH
      (liEvenCrossActualClockResponse U-C*Real.exp (-liEvenCrossActualClockGreenRate*U)/
        liEvenCrossActualClockGreenRate-1) U
    have hb := hu t ht
    linarith

end
end RHTower
