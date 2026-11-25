import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.GapSpectrum.BinaryOrientation.LargestPrime.Bands.Marks.FixedCount.Localization.SpectrumCost.OrderedBand
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.GapSpectrum.BinaryOrientation.LargestPrime.Bands.Marks.FixedCount.Localization.SpectrumCost.Support
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.GapSpectrum.BinaryOrientation.LargestPrime.Bands.Marks.FixedCount.Localization.SpectrumCost.Weights

/-! # Laplace asymptotics at unit inverse temperature for continuous energy observables -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.BinaryOrientation.LargestPrime.Bands.Marks.FixedCount.Localization.SpectrumCost

open Set Filter Topology MeasureTheory Endpoints _root_.RHTower

/-- Every fixed neighborhood of an admissible spectrum carries a positive amount of critical sector weight. -/
theorem eventWeight_eventually_pos {c d : ℝ} (hc : 0 < c) (hcd : c < d) {k : ℕ} {v : Fin k → ℝ}
    (hv : v ∈ orderedBand c d k) {U : Set (Fin k → ℝ)} (hU : IsOpen U) (hvU : v ∈ U) :
    ∃ a > (0:ℝ), ∀ᶠ h in criticalApproach, a ≤ eventWeight (added c d h) 1 h k U := by
  obtain ⟨m,hm,hμ⟩ := eventually_open_pos hc hcd hv.1 hv.2 hU hvU
  let B := Real.log (d/c)^k/k.factorial
  have hB : 0 < B := critical_limit_pos hc hcd k
  obtain ⟨b,hb,hbB⟩ := exists_between hB
  refine ⟨m*b,mul_pos hm hb,?_⟩
  filter_upwards [hμ,(coefficient_limit hc hcd k).eventually_const_lt hbB] with h hh hB'
  have hprob : m ≤ (thermalLaw c d h 1 k U : ℝ) := by
    simpa only [conditional,thermalLaw,zero_mul,add_zero] using hh
  have hden := hb.trans hB'
  have he := thermalLaw_event h k hU.measurableSet hden
  exact (mul_le_mul_of_nonneg_left hB'.le hm.le).trans ((le_div_iff₀ hden).mp (hprob.trans_eq he))

private theorem shifted (t a : ℝ) :
    Tendsto (fun h : Ioi (0:ℝ) => t+h.val*Real.log a) criticalApproach (𝓝 t) := by
  have h0 : Tendsto (Subtype.val : Ioi (0:ℝ) → ℝ) criticalApproach (𝓝[>] 0) := tendsto_comap
  have H := ((h0.mono_right nhdsWithin_le_nhds).mul_const (Real.log a)).const_add t
  rw [zero_mul,add_zero] at H
  exact H

private theorem log_prefactor (h : Ioi (0:ℝ)) (t : ℝ) {a : ℝ} (ha : 0 < a) :
    h.val*Real.log (Real.exp (t/h.val)*a) = t+h.val*Real.log a := by
  rw [Real.log_mul (Real.exp_pos _).ne' ha.ne',Real.log_exp,mul_add]
  field_simp [(show 0 < h.val from h.property).ne']

/-- The critical unnormalized exponential reading selects the largest value on the entire ordered band. -/
theorem critical_laplace {c d : ℝ} (hc : 0 < c) (hcd : c < d) {k : ℕ} {F : (Fin k → ℝ) → ℝ}
    (hF : ContinuousOn F (orderedBand c d k)) :
    Tendsto (fun h : Ioi (0:ℝ) => h.val*Real.log (partitionWith (added c d h) 1 h F))
      criticalApproach (𝓝 (peak c d F)) := by
  obtain ⟨v,hv,hpeak,hmax⟩ := peak_attained hcd.le hF
  rw [← hpeak]
  apply tendsto_order.mpr
  constructor
  · intro z hz
    obtain ⟨t,hzt,htv⟩ := exists_between hz
    obtain ⟨r,hr,hnear⟩ := Metric.continuousWithinAt_iff.mp (hF v hv) (F v-t) (sub_pos.mpr htv)
    let U := Metric.ball v r
    obtain ⟨a,ha,hU⟩ := eventWeight_eventually_pos hc hcd hv Metric.isOpen_ball (Metric.mem_ball_self hr)
    filter_upwards [hU,(shifted t a).eventually_const_lt hzt] with h hU' hz'
    have hl := event_lower (added c d h) h F U t (by
      intro R hR
      have hd := hnear (spectrum_mem_band h R) (Metric.mem_ball.mp hR)
      rw [Real.dist_eq] at hd
      linarith only [(abs_lt.mp hd).1])
    have he := (mul_le_mul_of_nonneg_left hU' (Real.exp_pos (t/h.val)).le).trans hl
    exact hz'.trans_le ((log_prefactor h t ha).symm.le.trans
      (mul_le_mul_of_nonneg_left (Real.log_le_log (mul_pos (Real.exp_pos _) ha) he) h.property.le))
  · intro z hz
    let B := Real.log (d/c)^k/k.factorial
    have hB : 0 < B+1 := add_pos (critical_limit_pos hc hcd k) zero_lt_one
    filter_upwards [(coefficient_limit hc hcd k).eventually_lt_const (lt_add_of_pos_right B zero_lt_one),
      eventually_positive hc hcd 1 F,(shifted (F v) (B+1)).eventually_lt_const hz] with h hB' hp hz'
    have he := (total_upper (added c d h) h F (F v) (fun R => hmax _ (spectrum_mem_band h R))).trans
      (mul_le_mul_of_nonneg_left hB'.le (Real.exp_pos _).le)
    exact ((mul_le_mul_of_nonneg_left (Real.log_le_log hp.2 he) h.property.le).trans_eq
      (log_prefactor h (F v) hB)).trans_lt hz'

#print axioms eventWeight_eventually_pos
#print axioms critical_laplace

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.BinaryOrientation.LargestPrime.Bands.Marks.FixedCount.Localization.SpectrumCost
