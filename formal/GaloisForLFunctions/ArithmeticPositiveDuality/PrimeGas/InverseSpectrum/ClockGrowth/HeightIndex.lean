import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ClockGrowth.BestCoefficient
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ClockGrowth.LogSlope
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.TraceExponents.FullFrontier

/-! # The critical composition line as a logarithmic growth rate in imaginary time -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing

open Set Filter Topology

/-- Trace coefficient evaluated at the least admissible positive power. -/
def optimalTraceCoefficient (r : ℕ) (z : ℂ) : ℝ := traceCoefficientAt r z (max 1 (2/z.re))

private theorem optimal_warm (r : ℕ) {z : ℂ} (hz : 0 < z.re) (h₂ : z.re ≤ 2) :
    optimalTraceCoefficient r z = matchedTraceCoefficient r z := by
  change traceCoefficientAt r z (max 1 (2/z.re)) = traceCoefficientAt r z (2/z.re)
  rw [max_eq_right ((one_le_div hz).mpr h₂)]

private theorem optimal_cold (r : ℕ) {z : ℂ} (h₂ : 2 ≤ z.re) :
    optimalTraceCoefficient (r+1) z = ‖z‖/2 := by
  have hz : 0 < z.re := (by norm_num : (0:ℝ)<2).trans_le h₂
  have he : {K : ℝ | traceControlsAt (r+1) z 1 K} = Ici (‖z‖/2) := by
    ext K
    exact (linear_trace_factor_iff r hz K).trans (and_iff_right h₂)
  rw [optimalTraceCoefficient,max_eq_left ((div_le_one hz).mpr h₂),traceCoefficientAt,he,csInf_Ici]

theorem clock_height_norm_bounds {σ t : ℝ} (hσ : 0 < σ) (ht : 1 ≤ t) :
    t ≤ ‖(⟨σ,t⟩:ℂ)‖ ∧ ‖(⟨σ,t⟩:ℂ)‖ ≤ (σ+1)*t := by
  have h := Complex.norm_le_abs_re_add_abs_im (⟨σ,t⟩:ℂ)
  change _ ≤ |σ|+|t| at h
  rw [abs_of_pos hσ,abs_of_nonneg (zero_le_one.trans ht)] at h
  refine ⟨(le_abs_self t).trans (Complex.abs_im_le_norm (⟨σ,t⟩:ℂ)),?_⟩
  exact h.trans ((add_le_add (le_mul_of_one_le_right hσ.le ht) (le_refl t)).trans_eq (by ring))

/-- Fixed real inverse temperature bounds the best coefficient above and below by constant multiples of the same clock power. -/
theorem clock_coefficient_power_bounds {σ : ℝ} (hσ : 0 < σ) :
    ∃ a > (0:ℝ), ∃ b > (0:ℝ), ∀ t ≥ (1:ℝ),
      a*t^(max 1 (2/σ)) ≤ optimalTraceCoefficient 1 (⟨σ,t⟩:ℂ) ∧
        optimalTraceCoefficient 1 (⟨σ,t⟩:ℂ) ≤ b*t^(max 1 (2/σ)) := by
  rcases le_total σ 2 with h₂ | h₂
  · let p := 2/σ
    have hp : 0 < p := div_pos (by norm_num) hσ
    have h4 : 0 < 4*σ := mul_pos (by norm_num) hσ
    have hA : 0 < 1/(4*σ) := one_div_pos.mpr h4
    have hB : 0 < (σ+1)/σ := div_pos (add_pos hσ zero_lt_one) hσ
    rw [max_eq_right ((one_le_div hσ).mpr h₂)]
    refine ⟨_,Real.rpow_pos_of_pos hA p,_,Real.rpow_pos_of_pos hB p,?_⟩
    intro t ht
    let z : ℂ := ⟨σ,t⟩
    have hn := clock_height_norm_bounds hσ ht
    have he := matchedTraceCoefficient_bounds (z := z) hσ h₂
    rw [optimal_warm 1 (z := z) hσ h₂]
    have ht₀ := zero_le_one.trans ht
    have ha : (1/(4*σ))*t ≤ ‖z‖/(4*σ) := (show (1/(4*σ))*t = t/(4*σ) by ring).trans_le
      (div_le_div_of_nonneg_right hn.1 h4.le)
    have hb : ‖z‖/σ ≤ ((σ+1)/σ)*t := (div_le_div_of_nonneg_right hn.2 hσ.le).trans_eq (by ring)
    rw [← Real.mul_rpow hA.le ht₀,← Real.mul_rpow hB.le ht₀]
    exact ⟨(Real.rpow_le_rpow (mul_nonneg hA.le ht₀) ha hp.le).trans he.1,
      he.2.trans (Real.rpow_le_rpow (div_nonneg (norm_nonneg _) hσ.le) hb hp.le)⟩
  · rw [max_eq_left ((div_le_one hσ).mpr h₂)]
    refine ⟨_,(by norm_num : (0:ℝ)<1/2),_,half_pos (add_pos hσ zero_lt_one),?_⟩
    intro t ht
    rw [optimal_cold 0 (z := ⟨σ,t⟩) h₂,Real.rpow_one]
    have hn := clock_height_norm_bounds hσ ht
    constructor
    · exact (show (1/2:ℝ)*t = t/2 by ring).trans_le (div_le_div_of_nonneg_right hn.1 (by norm_num))
    · exact (div_le_div_of_nonneg_right hn.2 (by norm_num : (0:ℝ)≤2)).trans_eq (by ring)

/-- The coefficient at the optimal power is a physical bound and is the least such bound. -/
theorem optimalTraceCoefficient_isLeast (r : ℕ) {z : ℂ} (hz : 0 < z.re) :
    IsLeast {K : ℝ | traceControlsAt (r+1) z (max 1 (2/z.re)) K} (optimalTraceCoefficient (r+1) z) := by
  rcases le_total z.re 2 with h₂ | h₂
  · rw [optimal_warm (r+1) hz h₂,max_eq_right ((one_le_div hz).mpr h₂)]
    exact matchedTraceCoefficient_isLeast r hz h₂
  · rw [optimal_cold r h₂,max_eq_left ((div_le_one hz).mpr h₂)]
    have he : {K : ℝ | traceControlsAt (r+1) z 1 K} = Ici (‖z‖/2) := by
      ext K
      exact (linear_trace_factor_iff r hz K).trans (and_iff_right h₂)
    rw [he]
    exact isLeast_Ici

/-- At every positive real inverse temperature, the logarithmic clock slope equals the optimal physical power. -/
theorem optimal_trace_clock_slope {σ : ℝ} (hσ : 0 < σ) :
    Tendsto (fun t : ℝ => Real.log (optimalTraceCoefficient 1 (⟨σ,t⟩:ℂ))/Real.log t) atTop (𝓝 (max 1 (2/σ))) := by
  obtain ⟨_,ha,_,hb,h⟩ := clock_coefficient_power_bounds hσ
  exact log_slope_of_power_bounds ha hb h

/-- Fourth-order growth in imaginary time is equivalent to isometric composition at the same real temperature. -/
theorem fourth_clock_slope_iff_split_isometric {z : ℂ} (hz : 0 < z.re) :
    Tendsto (fun t : ℝ => Real.log (optimalTraceCoefficient 1 (⟨z.re,t⟩:ℂ))/Real.log t) atTop (𝓝 4) ↔
      ∃ T : Gas →ₗᵢ[ℂ] PairGas, ∀ f x, T f x = split z f x := by
  rw [← least_trace_power_four_iff_split_isometric 0 hz,admissibleTracePowers_eq 0 hz]
  constructor
  · intro h
    rw [tendsto_nhds_unique (optimal_trace_clock_slope hz) h]
    exact isLeast_Ici
  · intro h
    rw [h.unique isLeast_Ici]
    exact optimal_trace_clock_slope hz

#print axioms optimalTraceCoefficient_isLeast
#print axioms optimal_trace_clock_slope
#print axioms fourth_clock_slope_iff_split_isometric

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing
