import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.MomentResponse.Envelope
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.QuarticGrowth.ClockMasks

/-! # Critical-line response across all trace and relative moment orders -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing

open Set Filter Topology

/-- Maximum physical response when the 2q-th root of the moment deficit has inverse-height scale. -/
def normalizedMomentResponse (q : GibbsExponent) (σ t : ℝ) : ℝ := sSup (momentAmplitudes q σ t (2/t^(2*q.val)))

/-- The height exponent for every moment of squared heat of order at least one half. -/
theorem normalized_moment_bounds (q : GibbsExponent) (hq : 1/2 ≤ q.val) {σ : ℝ} (hs : 0 < σ) :
    ∃ c > (0:ℝ), ∃ C > (0:ℝ), ∀ t ≥ (1:ℝ),
      c*t^(1-2*min σ q.val) < normalizedMomentResponse q σ t ∧
      normalizedMomentResponse q σ t ≤ C*t^(1-2*min σ q.val) := by
  obtain ⟨c,hc,C,hC,h⟩ := moment_amplitude_envelope q hs
  refine ⟨c,hc,C,hC,?_⟩
  intro t ht
  have ht' := zero_lt_one.trans_le ht
  have hpow (x : ℝ) : t^(2*x) = (t^2)^x := by rw [Real.rpow_mul ht'.le,Real.rpow_two]
  have htime : t ≤ (t^2)^q.val := by
    rw [← hpow]
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le ht (show 1 ≤ 2*q.val by linarith only [hq])
  have he := h t ht (t^2) ((le_mul_of_one_le_right ht'.le ht).trans_eq (sq t).symm) htime
  have hp : t/(t^2)^(min σ q.val) = t^(1-2*min σ q.val) := by rw [Real.rpow_sub ht',Real.rpow_one,hpow]
  simpa only [normalizedMomentResponse,hpow,hp] using he

theorem normalized_moment_log_slope (q : GibbsExponent) (hq : 1/2 ≤ q.val) {σ : ℝ} (hs : 0 < σ) :
    Tendsto (fun t : ℝ => Real.log (normalizedMomentResponse q σ t)/Real.log t) atTop (𝓝 (1-2*min σ q.val)) := by
  obtain ⟨_,hc,_,hC,h⟩ := normalized_moment_bounds q hq hs
  exact log_slope_of_power_bounds hc hC (fun t ht => ⟨(h t ht).1.le,(h t ht).2⟩)

/-- Every trace-class moment, as well as every relative order strictly above one half, selects the same isometric composition law. -/
theorem moment_zero_slope_iff_split (q : GibbsExponent) (hq : 1/2 < q.val) {s : ℂ} (hs : 0 < s.re) :
    Tendsto (fun t : ℝ => Real.log (normalizedMomentResponse q s.re t)/Real.log t) atTop (𝓝 0) ↔
    ∃ T : Gas →ₗᵢ[ℂ] PairGas, ∀ f x, T f x = split s f x := by
  rw [split_isometric_iff]
  constructor
  · intro h
    have he := tendsto_nhds_unique (normalized_moment_log_slope q hq.le hs) h
    rcases le_total s.re q.val with h | h
    · rw [min_eq_left h] at he
      linarith only [he]
    · rw [min_eq_right h] at he
      linarith only [he,hq]
  · intro hs'
    have he : 1-2*min s.re q.val = 0 := by rw [hs',min_eq_left hq.le]; norm_num
    simpa only [he] using normalized_moment_log_slope q hq.le hs

/-- At and below half order a single ground attenuation fits the ceiling at every height. Absolute summability caps the response. -/
theorem low_order_summable_bounds (q : GibbsExponent) (hq : q.val ≤ 1/2) {σ : ℝ} (hs : 1 < σ) :
    ∃ c > (0:ℝ), ∃ C > (0:ℝ), ∀ t ≥ (1:ℝ), c < normalizedMomentResponse q σ t ∧ normalizedMomentResponse q σ t ≤ C := by
  let c := shortChordFactor σ/(2*(1+q.val))
  let cap (k : ℕ) := 2*occupationWeight k^σ
  have hc : 0 < c := div_pos (shortChordFactor_pos σ) (mul_pos (by norm_num) (add_pos zero_lt_one q.property))
  have hsum : Summable cap := ((summable_band_rpow_iff (hotEdge 0) σ).mpr hs).mul_left 2
  have hn (k : ℕ) : 0 ≤ cap k := mul_nonneg (by norm_num) (Real.rpow_nonneg (occupationWeight_pos k).le _)
  refine ⟨c,hc,1+∑' k,cap k,add_pos_of_pos_of_nonneg zero_lt_one (tsum_nonneg hn),?_⟩
  intro t ht
  let z : ℂ := ⟨σ,t⟩
  have ht' := zero_lt_one.trans_le ht
  have hs' := zero_lt_one.trans hs
  have hbound (x : ℝ) (hx : x ∈ momentAmplitudes q σ t (2/t^(2*q.val))) : x ≤ 1+∑' k, cap k := by
    obtain ⟨b,_,_,rfl⟩ := hx
    have hnorm := (summable_complexDrop b (z := z) hs').norm
    refine ((norm_tsum_le_tsum_norm hnorm).trans (hnorm.tsum_le_tsum (fun k => ?_) hsum)).trans (le_add_of_nonneg_left zero_le_one)
    rw [clockMask_represents]
    exact mul_le_mul_of_nonneg_left (mul_le_of_le_one_right (Real.rpow_nonneg (occupationWeight_pos k).le _) (clockMask_mem b hs'.le k).2) (by norm_num)
  obtain ⟨b,hphys,hL,hD⟩ := ground_moment_probe q hs' ht (le_refl t)
  have htq : t^(2*q.val) ≤ t := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le ht (show 2*q.val ≤ 1 by linarith only [hq])
  have hcost : momentLoss q b ≤ 2/t^(2*q.val) := hD.le.trans ((one_div_le_one_div_of_le (Real.rpow_pos_of_pos ht' _) htq).trans
    (div_le_div_of_nonneg_right (by norm_num : (1:ℝ)≤2) (Real.rpow_nonneg ht'.le _)))
  have hx : ‖relativePartition b z‖ ∈ momentAmplitudes q σ t (2/t^(2*q.val)) := ⟨b,hphys,hcost,rfl⟩
  rw [div_self ht'.ne',mul_one] at hL
  exact ⟨hL.trans_le (le_csSup ⟨_,hbound⟩ hx),csSup_le ⟨_,hx⟩ hbound⟩

/-- The exact range of relative moment orders for which zero response slope characterizes isometry at every positive real temperature. -/
theorem moment_detects_isometry_iff (q : GibbsExponent) :
    (∀ s : ℂ, 0 < s.re → (Tendsto (fun t : ℝ => Real.log (normalizedMomentResponse q s.re t)/Real.log t) atTop (𝓝 0) ↔
      ∃ T : Gas →ₗᵢ[ℂ] PairGas, ∀ f x, T f x = split s f x)) ↔ 1/2 < q.val := by
  constructor
  · intro h
    by_contra! hq
    obtain ⟨c,hc,C,hC,hb⟩ := low_order_summable_bounds q hq (by norm_num : (1:ℝ)<2)
    have hzero : Tendsto (fun t : ℝ => Real.log (normalizedMomentResponse q 2 t)/Real.log t) atTop (𝓝 0) := by
      apply log_slope_of_power_bounds hc hC
      intro t ht
      simpa only [Real.rpow_zero,mul_one] using And.intro (hb t ht).1.le (hb t ht).2
    have he := (split_isometric_iff (2:ℂ)).mp ((h 2 (by norm_num)).mp hzero)
    norm_num at he
  · exact fun hq s hs => moment_zero_slope_iff_split q hq hs

#print axioms normalized_moment_bounds
#print axioms normalized_moment_log_slope
#print axioms moment_zero_slope_iff_split
#print axioms low_order_summable_bounds
#print axioms moment_detects_isometry_iff

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing
