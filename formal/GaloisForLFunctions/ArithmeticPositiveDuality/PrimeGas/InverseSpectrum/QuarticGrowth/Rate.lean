import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.QuarticGrowth.WindowScale
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.QuarticGrowth.UpperBound
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ClockGrowth.HeightIndex

/-! # The phase diagram of the least rank-one fourth-trace coefficient -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing

open Filter Topology

/-- The best coefficient measured at fixed fourth power, on the half-plane where that power is admissible. -/
def quarticClockCoefficient (σ t : ℝ) : ℝ := traceCoefficientAt 1 (⟨σ,t⟩:ℂ) 4

private theorem fixed_quartic_lower {σ : ℝ} (hs : 1/2 ≤ σ) :
    ∃ c > (0:ℝ), ∀ t ≥ (1:ℝ), ∀ K : ℝ, traceControlsAt 1 (⟨σ,t⟩:ℂ) 4 K → c*t^(quarticClockOrder σ) ≤ K := by
  let g := 2*Real.pi
  have hg : 0 < g := mul_pos (by norm_num) Real.pi_pos
  have hσ := (by norm_num : (0:ℝ)<1/2).trans_le hs
  rcases le_total (6-4*σ) 1 with hc | hc
  · refine ⟨1/g,one_div_pos.mpr hg,?_⟩
    intro t ht K hK
    have he := ground_clock_lower 0 (z := ⟨σ,t⟩) hσ (zero_lt_one.trans_le ht) (by norm_num : (0:ℝ)≤4) hK
    rw [quarticClockOrder,max_eq_left hc,Real.rpow_one]
    exact (show (1/g)*t=t/g by ring).trans_le he
  let W := 8*(1+Real.pi)
  let q := 6-4*σ
  let B := 4^4*W^6
  have hW : 0 < W := mul_pos (by norm_num) (add_pos zero_lt_one Real.pi_pos)
  have hB : 0 < B := mul_pos (by norm_num) (pow_pos hW 6)
  have hWq := Real.rpow_pos_of_pos hW q
  let c := min (1/B) ((1/g)/W^q)
  refine ⟨c,lt_min (one_div_pos.mpr hB) (div_pos (one_div_pos.mpr hg) hWq),?_⟩
  intro t ht K hK
  rw [quarticClockOrder,max_eq_right hc]
  have ht' := zero_lt_one.trans_le ht
  rcases le_total t W with hsmall | hbig
  · have hground := ground_clock_lower 0 (z := ⟨σ,t⟩) hσ ht' (by norm_num : (0:ℝ)≤4) hK
    calc
      c*t^q ≤ ((1/g)/W^q)*W^q := mul_le_mul (min_le_right _ _)
        (Real.rpow_le_rpow ht'.le hsmall (zero_le_one.trans hc)) (Real.rpow_nonneg ht'.le _) (div_nonneg (one_div_pos.mpr hg).le hWq.le)
      _ = 1/g := div_mul_cancel₀ _ hWq.ne'
      _ ≤ t/g := div_le_div_of_nonneg_right ht hg.le
      _ ≤ K := hground
  · have htest := window_growth_lower hσ hbig hK
    have he : t^q/B ≤ K := (div_le_iff₀ hB).mpr htest
    calc
      c*t^q ≤ (1/B)*t^q := mul_le_mul_of_nonneg_right (min_le_left _ _) (Real.rpow_nonneg ht'.le _)
      _ = t^q/B := by ring
      _ ≤ K := he

/-- Uniform two-sided growth at every admissible real temperature, with no logarithmic factor at five quarters. -/
theorem quartic_clock_power_bounds {σ : ℝ} (hs : 1/2 ≤ σ) :
    ∃ c > (0:ℝ), ∃ C > (0:ℝ), ∀ t ≥ (1:ℝ),
      c*t^(quarticClockOrder σ) ≤ quarticClockCoefficient σ t ∧
      quarticClockCoefficient σ t ≤ C*t^(quarticClockOrder σ) := by
  let q := quarticClockOrder σ
  have hσ := (by norm_num : (0:ℝ)<1/2).trans_le hs
  have hq : 0 ≤ q := zero_le_one.trans (le_max_left _ _)
  obtain ⟨c,hc,hl⟩ := fixed_quartic_lower hs
  have hs' := add_pos hσ zero_lt_one
  refine ⟨c,hc,20^4*(σ+1)^q,mul_pos (by norm_num) (Real.rpow_pos_of_pos hs' _),?_⟩
  intro t ht
  let z : ℂ := ⟨σ,t⟩
  have hleast := quarticCoefficient_isLeast 0 (z := z) hs
  have he : quarticClockCoefficient σ t ≤ 20^4*‖z‖^q := hleast.2 (quartic_growth_upper (z := z) hs)
  refine ⟨hl t ht _ hleast.1,?_⟩
  have hn := Real.rpow_le_rpow (norm_nonneg z) (clock_height_norm_bounds hσ ht).2 hq
  rw [Real.mul_rpow hs'.le (zero_le_one.trans ht)] at hn
  exact he.trans ((mul_le_mul_of_nonneg_left hn (by norm_num : (0:ℝ)≤20^4)).trans_eq (mul_assoc _ _ _).symm)

/-- The logarithmic height exponent at fixed fourth power is max(1, 6−4σ). -/
theorem quartic_clock_growth_rate {σ : ℝ} (hs : 1/2 ≤ σ) :
    Tendsto (fun t : ℝ => Real.log (quarticClockCoefficient σ t)/Real.log t) atTop (𝓝 (max 1 (6-4*σ))) := by
  obtain ⟨_,hc,_,hC,h⟩ := quartic_clock_power_bounds hs
  exact log_slope_of_power_bounds hc hC h

/-- The clock coefficient grows linearly in the logarithmic scale exactly from temperature five quarters onward. -/
theorem quartic_clock_linear_iff {σ : ℝ} (hs : 1/2 ≤ σ) :
    Tendsto (fun t : ℝ => Real.log (quarticClockCoefficient σ t)/Real.log t) atTop (𝓝 1) ↔ 5/4 ≤ σ := by
  constructor
  · intro h
    have he := tendsto_nhds_unique (quartic_clock_growth_rate hs) h
    have hm := (le_max_right 1 (6-4*σ)).trans_eq he
    linarith only [hm]
  · intro hc
    simpa only [max_eq_left (show 6-4*σ ≤ 1 by linarith only [hc])] using quartic_clock_growth_rate hs

/-- Among the positive temperatures admitting a quartic bound, slope four singles out norm-preserving divisor composition. -/
theorem fixed_quartic_rate_iff_isometric {z : ℂ} (hz : 0 < z.re) :
    ((∃ K : ℝ, traceControlsAt 1 z 4 K) ∧
      Tendsto (fun t : ℝ => Real.log (quarticClockCoefficient z.re t)/Real.log t) atTop (𝓝 4)) ↔
      ∃ T : Gas →ₗᵢ[ℂ] PairGas, ∀ f x, T f x = split z f x := by
  rw [quartic_trace_control_iff 0 hz,split_isometric_iff]
  constructor
  · rintro ⟨hs,h⟩
    have he := tendsto_nhds_unique (quartic_clock_growth_rate hs) h
    rcases le_total (6-4*z.re) 1 with hc | hc
    · rw [max_eq_left hc] at he
      norm_num at he
    · rw [max_eq_right hc] at he
      linarith only [he]
  · intro he
    refine ⟨he.ge,?_⟩
    have h := quartic_clock_growth_rate he.ge
    simpa only [he,show max 1 (6-4*(1/2:ℝ)) = 4 by norm_num] using h

#print axioms quartic_clock_power_bounds
#print axioms quartic_clock_growth_rate
#print axioms quartic_clock_linear_iff
#print axioms fixed_quartic_rate_iff_isometric

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing
