import GaloisForLFunctions.RHTower.PaperHurwitzMovingObservation

/-! # The exact Hurwitz observation profile

The ratio of the last observed power level to the inverse wall distance
determines the complete finite-prefix norm defect.
-/

namespace RHTower
noncomputable section
open Filter Topology GaloisForLFunctions GaloisForLFunctions.HTGeometry
open scoped ENNReal

def paperHurwitzObservationProfile (r : ℝ) : ℝ :=
  1 - (1 + Real.sinh (r * Real.log 2) ^ 2)⁻¹

theorem paperHurwitzObservationProfile_zero : paperHurwitzObservationProfile 0 = 0 := by
  simp [paperHurwitzObservationProfile]

theorem paperHurwitzObservationProfile_nonneg (r : ℝ) :
    0 ≤ paperHurwitzObservationProfile r := by
  apply sub_nonneg.mpr
  apply (inv_le_one₀ (by positivity)).mpr
  linarith [sq_nonneg (Real.sinh (r * Real.log 2))]

theorem paperHurwitzObservationProfile_lt_one (r : ℝ) :
    paperHurwitzObservationProfile r < 1 := by
  have h : 0 < (1 + Real.sinh (r * Real.log 2) ^ 2)⁻¹ := inv_pos.mpr (by positivity)
  dsimp [paperHurwitzObservationProfile]
  linarith

theorem paperHurwitzObservationProfile_strictMonoOn :
    StrictMonoOn paperHurwitzObservationProfile (Set.Ici 0) := by
  intro x hx y hy hxy
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hs := Real.sinh_lt_sinh.mpr (mul_lt_mul_of_pos_right hxy hlog)
  have hx0 : 0 ≤ Real.sinh (x * Real.log 2) :=
    Real.sinh_nonneg_iff.mpr (mul_nonneg hx hlog.le)
  have hy0 : 0 ≤ Real.sinh (y * Real.log 2) :=
    Real.sinh_nonneg_iff.mpr (mul_nonneg hy hlog.le)
  have hi : (1 + Real.sinh (y * Real.log 2) ^ 2)⁻¹ <
      (1 + Real.sinh (x * Real.log 2) ^ 2)⁻¹ := by
    have hp : 1 + Real.sinh (x * Real.log 2) ^ 2 <
        1 + Real.sinh (y * Real.log 2) ^ 2 := by nlinarith
    simpa only [one_div] using one_div_lt_one_div_of_lt (by positivity) hp
  dsimp [paperHurwitzObservationProfile]
  linarith

theorem paperHurwitzObservationProfile_continuous : Continuous paperHurwitzObservationProfile := by
  have h : Continuous (fun r : ℝ => 1 + Real.sinh (r * Real.log 2) ^ 2) := by fun_prop
  exact continuous_const.sub (h.inv₀ (fun r => ne_of_gt (by positivity)))

theorem paperHurwitzObservationProfile_nat (m : ℕ) :
    paperHurwitzObservationProfile m = 1 - paperHurwitzRegularizer (3 / 2 : ℂ) m := by
  norm_num [paperHurwitzObservationProfile, paperHurwitzRegularizer, paperHurwitzPowerEnergy_eq_sinh]

theorem paperHurwitzObservationProfile_atTop :
    Tendsto paperHurwitzObservationProfile atTop (𝓝 1) := by
  have hR : Tendsto (paperHurwitzRegularizer (3 / 2 : ℂ)) atTop (𝓝 0) := by
    have h := tendsto_paperHurwitzRegularizer (3 / 2 : ℂ)
    norm_num at h
    exact h
  have hnat : Tendsto (fun m : ℕ => paperHurwitzObservationProfile m) atTop (𝓝 1) := by
    simpa only [paperHurwitzObservationProfile_nat, sub_zero] using
      (tendsto_const_nhds (x := (1 : ℝ))).sub hR
  apply tendsto_order.mpr
  constructor
  · intro c hc
    obtain ⟨N, hN⟩ := (hnat.eventually (lt_mem_nhds hc)).exists
    filter_upwards [eventually_ge_atTop (N : ℝ)] with r hr
    have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    exact hN.trans_le (paperHurwitzObservationProfile_strictMonoOn.monotoneOn
      hN0 (hN0.trans hr) hr)
  · intro c hc
    exact Eventually.of_forall fun r => (paperHurwitzObservationProfile_lt_one r).trans hc

theorem norm_paperHurwitzPrefixDefect_profile (t : ℝ) (N M : ℕ) :
    ‖paperHurwitzPrefixDefect t N M‖ =
      paperHurwitzObservationProfile ((M : ℝ) / ((N : ℝ) + 3)) := by
  rw [norm_paperHurwitzPrefixDefect, paperHurwitzRegularizer, paperHurwitzApproachPoint_energy_ratio]
  rfl

end
end RHTower
