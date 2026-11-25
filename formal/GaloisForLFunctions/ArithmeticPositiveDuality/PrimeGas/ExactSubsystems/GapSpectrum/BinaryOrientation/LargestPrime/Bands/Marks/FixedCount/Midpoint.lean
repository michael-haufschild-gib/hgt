import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.GapSpectrum.BinaryOrientation.LargestPrime.Bands.Marks.FixedCount.Cuts
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.GapSpectrum.BinaryOrientation.LargestPrime.Bands.Marks.Dilation

/-! # A geometric midpoint reading detects zero thermal drift after fixing the count -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.BinaryOrientation.LargestPrime.Bands.Marks.FixedCount

open Filter Topology Set MeasureTheory VacuumCalibration

private theorem adjacent_mass {c b d : ℝ} (hc : 0 < c) (hcb : c ≤ b) (hbd : b ≤ d) (a : ℝ) :
    mass c b a + mass b d a = mass c d a := by
  have hi {u v : ℝ} (hu : 0 < u) (huv : u ≤ v) :
      IntervalIntegrable (fun t : ℝ => Real.exp (-a*t)/t) volume u v := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le huv]
    exact (Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn.div continuousOn_id
      (fun _ ht => (hu.trans_le ht.1).ne')
  exact intervalIntegral.integral_add_adjacent_intervals (hi hc hcb) (hi (hc.trans_le hcb) hbd)

/-- The two halves of a geometric band have equal probability precisely at zero drift. -/
theorem midpoint_fraction_iff {c r : ℝ} (hc : 0 < c) (hr : 1 < r) (a : ℝ) :
    mass c (r*c) a / mass c (r*(r*c)) a = 1/2 ↔ a = 0 := by
  have hcb : c < r*c := lt_mul_of_one_lt_left hc hr
  have hbd : r*c < r*(r*c) := lt_mul_of_one_lt_left (hc.trans hcb) hr
  have hm := (mass_pos hc (hcb.trans hbd) a).ne'
  have hadd := adjacent_mass hc hcb.le hbd.le a
  rw [mass_dilate c (r*c) a (zero_lt_one.trans hr)] at hadd
  constructor
  · intro H
    have he := (div_eq_div_iff hm (by norm_num : (2:ℝ) ≠ 0)).mp H
    have ha := (mass_strictAnti hc hcb).injective (show mass c (r*c) (r*a) = mass c (r*c) a by
      linarith only [he,hadd])
    exact (mul_eq_zero.mp (show (r-1)*a=0 by rw [sub_mul,one_mul,ha,sub_self])).resolve_left
      (sub_ne_zero.mpr hr.ne')
  · rintro rfl
    rw [mul_zero] at hadd
    exact (div_eq_div_iff hm (by norm_num : (2:ℝ) ≠ 0)).mpr (by linarith only [hadd])

/-- Conditioning on any positive count preserves detection of the log-uniform law by one geometric cut. -/
theorem midpoint_limit_iff {c r : ℝ} (hc : 0 < c) (hr : 1 < r) (a : ℝ) {k : ℕ} (hk : 0 < k) :
    Tendsto (fun h => (conditional c (r*(r*c)) a h k (allIn k (Iic (r*c))):ℝ))
      criticalApproach (𝓝 ((1/2:ℝ)^k)) ↔ a = 0 := by
  have hcb : c < r*c := lt_mul_of_one_lt_left hc hr
  have hbd : r*c < r*(r*c) := lt_mul_of_one_lt_left (hc.trans hcb) hr
  letI : NeBot criticalApproach := criticalApproach_neBot
  have H := all_below_limit hc hcb.le hbd.le (hcb.trans hbd) a k
  constructor
  · intro h
    apply (midpoint_fraction_iff hc hr a).mp
    exact (pow_left_inj₀ (div_nonneg (mass_nonneg hc hcb.le a) (mass_nonneg hc (hcb.trans hbd).le a))
      (by norm_num) hk.ne').mp (tendsto_nhds_unique H h)
  · intro ha
    rwa [(midpoint_fraction_iff hc hr a).mpr ha] at H

#print axioms midpoint_fraction_iff
#print axioms midpoint_limit_iff

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.BinaryOrientation.LargestPrime.Bands.Marks.FixedCount
