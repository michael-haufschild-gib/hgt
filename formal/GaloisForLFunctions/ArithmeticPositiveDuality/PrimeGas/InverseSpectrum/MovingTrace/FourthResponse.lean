import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.MovingTrace.Envelope
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.MovingTrace.PowerFrontier

/-! # The isometric line from height independence of the largest inverse-fourth response -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing

open Filter Topology Set

/-- Largest physical partition change at fourth-trace deficit at most 2/t⁴. -/
def fourthWindowResponse (σ t : ℝ) : ℝ := sSup (smallWindowAmplitudes σ t (t^2))

/-- Even when the trace loss is inverse-fourth order, the maximal response grows below the critical line and decays above it. -/
theorem fourth_response_bounds {σ : ℝ} (hs : 0 < σ) :
    ∃ c > (0:ℝ), ∃ C > (0:ℝ), ∀ t ≥ (1:ℝ),
      c*t^(1-2*min σ 2) < fourthWindowResponse σ t ∧ fourthWindowResponse σ t ≤ C*t^(1-2*min σ 2) := by
  obtain ⟨c,hc,C,hC,h⟩ := small_window_amplitude_envelope hs
  refine ⟨c,hc,C,hC,?_⟩
  intro t ht
  have ht' := zero_lt_one.trans_le ht
  have he := h t ht (t^2) ((le_mul_of_one_le_right ht'.le ht).trans_eq (sq t).symm)
  have hp : t/(t^2)^(min σ 2) = t^(1-2*min σ 2) := by
    rw [Real.rpow_sub ht',Real.rpow_one,Real.rpow_mul ht'.le,Real.rpow_two]
  simpa only [hp,fourthWindowResponse] using he

theorem fourth_response_log_slope {σ : ℝ} (hs : 0 < σ) :
    Tendsto (fun t : ℝ => Real.log (fourthWindowResponse σ t)/Real.log t) atTop (𝓝 (1-2*min σ 2)) := by
  obtain ⟨_,hc,_,hC,h⟩ := fourth_response_bounds hs
  exact log_slope_of_power_bounds hc hC (fun t ht => ⟨(h t ht).1.le,(h t ht).2⟩)

/-- Zero growth exponent for the maximum inverse-fourth response is equivalent to isometric divisor composition. -/
theorem fourth_response_zero_iff_isometric {s : ℂ} (hs : 0 < s.re) :
    Tendsto (fun t : ℝ => Real.log (fourthWindowResponse s.re t)/Real.log t) atTop (𝓝 0) ↔
      ∃ T : Gas →ₗᵢ[ℂ] PairGas, ∀ f x, T f x = split s f x := by
  rw [split_isometric_iff]
  constructor
  · intro h
    have he := tendsto_nhds_unique (fourth_response_log_slope hs) h
    rcases le_total s.re 2 with hc | hc
    · rw [min_eq_left hc] at he
      linarith only [he]
    · rw [min_eq_right hc] at he
      norm_num at he
  · intro he
    have hz : 1-2*min s.re 2 = 0 := by rw [he]; norm_num
    simpa only [hz] using fourth_response_log_slope hs

#print axioms fourth_response_bounds
#print axioms fourth_response_log_slope
#print axioms fourth_response_zero_iff_isometric

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing
