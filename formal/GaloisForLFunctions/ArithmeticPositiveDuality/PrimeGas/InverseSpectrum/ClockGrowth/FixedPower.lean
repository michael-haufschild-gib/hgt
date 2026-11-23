import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ClockGrowth.SublinearClock

/-! # Trace estimates at a fixed power as imaginary time increases -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing

open Filter Topology

/-- Every positive multiple of the clock power eventually controls all physical rank-one omissions. -/
def subpowerClockControl (σ p : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ t : ℝ in atTop, traceControlsAt 1 (⟨σ,t⟩:ℂ) p (ε*t^p)

private theorem above_optimal_subpower {σ p : ℝ} (hz : 0 < σ) (hq : max 1 (2/σ) < p) :
    subpowerClockControl σ p := by
  let q := max 1 (2/σ)
  let d := p-q
  have hd : 0 < d := sub_pos.mpr hq
  have hp : 0 < p := (zero_lt_one.trans_le (le_max_left _ _)).trans hq
  have hadd : d+q = p := sub_add_cancel _ _
  obtain ⟨_,_,B,hB,hbound⟩ := clock_coefficient_power_bounds hz
  intro ε hε
  let δ := (ε/B)^d⁻¹
  have hδ : 0 < δ := Real.rpow_pos_of_pos (div_pos hε hB) _
  have hscale : δ^d*B = ε := by
    rw [show δ^d = ε/B from Real.rpow_inv_rpow (div_pos hε hB).le hd.ne',div_mul_cancel₀ _ hB.ne']
  filter_upwards [uniform_sublinear_clock 1 hz hδ,eventually_ge_atTop (1:ℝ)] with t hsmall ht
  intro P hdim hc
  let b := physicalSpectrum P hdim hc
  let z : ℂ := ⟨σ,t⟩
  let X := ‖relativePartition b z‖
  let D := traceLoss (projected P)
  have hX : 0 ≤ X := norm_nonneg _
  have hXt : X ≤ δ*t := hsmall b
  have hD : 0 ≤ D := traceLoss_nonneg P hdim hc
  have hbest := (optimalTraceCoefficient_isLeast 0 (z := z) hz).1
  have hqbound : X^q ≤ (B*t^q)*D := (hbest P hdim hc).trans
    (mul_le_mul_of_nonneg_right (hbound t ht).2 hD)
  have htp : 0 < t := zero_lt_one.trans_le ht
  change X^p ≤ (ε*t^p)*D
  calc
    X^p = X^d * X^q := by
      simpa only [hadd] using Real.rpow_add' (y := d) (z := q) hX (hadd.trans_ne hp.ne')
    _ ≤ (δ*t)^d * ((B*t^q)*D) := mul_le_mul (Real.rpow_le_rpow hX hXt hd.le) hqbound
      (Real.rpow_nonneg hX _) (Real.rpow_nonneg (hX.trans hXt) _)
    _ = (δ^d*B)*(t^d*t^q)*D := by rw [Real.mul_rpow hδ.le htp.le]; ring
    _ = (ε*t^p)*D := by rw [hscale,← Real.rpow_add htp,hadd]

/-- At the least admissible power the matching lower bound precludes any uniform little-o improvement. -/
theorem optimal_not_subpower {σ : ℝ} (hσ : 0 < σ) : ¬ subpowerClockControl σ (max 1 (2/σ)) := by
  intro h
  obtain ⟨a,ha,_,_,hbound⟩ := clock_coefficient_power_bounds hσ
  obtain ⟨t,hsmall,ht⟩ := ((h (a/2) (half_pos ha)).and (eventually_ge_atTop (1:ℝ))).exists
  have he := (optimalTraceCoefficient_isLeast 0 (z := ⟨σ,t⟩) hσ).2 hsmall
  have hc := le_of_mul_le_mul_right ((hbound t ht).1.trans he) (Real.rpow_pos_of_pos (zero_lt_one.trans_le ht) _)
  exact (half_lt_self ha).not_ge hc

/-- Uniform little-o clock growth holds exactly at powers strictly greater than the least physical power. -/
theorem subpower_clock_iff {σ p : ℝ} (hσ : 0 < σ) (hp : 0 < p) :
    subpowerClockControl σ p ↔ max 1 (2/σ) < p := by
  refine ⟨fun h => ?_,above_optimal_subpower hσ⟩
  obtain ⟨t,ht⟩ := (h 1 zero_lt_one).exists
  have hle := (trace_power_iff 0 (z := ⟨σ,t⟩) hσ hp).mp ⟨_,ht⟩
  change max 1 (2/σ) ≤ p at hle
  apply hle.lt_of_ne
  intro he
  apply optimal_not_subpower hσ
  rwa [he]

/-- Existence at one height together with failure of a strict clock improvement identifies the optimal power from a fixed-power test. -/
theorem fixed_power_clock_boundary {z : ℂ} {p : ℝ} (hz : 0 < z.re) (hp : 0 < p) :
    ((∃ K : ℝ, traceControlsAt 1 z p K) ∧ ¬ subpowerClockControl z.re p) ↔ p = max 1 (2/z.re) := by
  rw [trace_power_iff 0 hz hp,subpower_clock_iff hz hp,not_lt]
  exact ⟨fun h => le_antisymm h.2 h.1,fun h => ⟨h.ge,h.le⟩⟩

#print axioms optimal_not_subpower
#print axioms subpower_clock_iff
#print axioms fixed_power_clock_boundary

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing
